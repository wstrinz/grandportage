import GPCensus.Listing
import GPCensus.V4Check
import GPCensus.Extension
import GP50.NarrowingAdmissionProofs
import LRATCatcher.Reflect
import LRATCatcher.Cover

/-!
The census profile (post-G2 §4, M4): the second real profile on the unchanged Kernel.

- **Statements** fix a colour count and a closed predicate, and claim one of four kinds about the
  coloured graphs on `n` vertices: EXISTS, NONE, EXHAUSTIVE(list) or COUNT = m up to isomorphism.
- **Scopes** are exact parameter sets: the vertex counts a claim covers. A receipt reaches only
  the `n` it certifies, so "none found up to n" can never be read as "none exist" (M4 §5).
- **Contexts** are those vertex counts (`Ctx := Nat`), and `Holds s n` is the statement's truth
  among coloured graphs on `n` vertices.

`fold_held_meaning` gives every held claim its meaning at every parameter of its scope, through the
Kernel's generic theorem.
-/

namespace GPCensus
open Hex Hex.GraphIso GP50

/-- A listed object as data: an edge list and one colour per vertex. -/
structure Witness where
  edges : List (Nat × Nat)
  colors : List Nat
  deriving Repr, DecidableEq, Inhabited

/-- The coloured graph a witness denotes on `n` vertices with `k` colours, if it is one: in-range
loopless edges, and a colouring of every vertex that uses every colour. An empty colour list means
every vertex has colour 0 (plain graphs). -/
def decode (n k : Nat) (w : Witness) : Option (Colored n k) := do
  let G ← Graph.ofEdges? n w.edges
  let colors := if w.colors.isEmpty then List.replicate n 0 else w.colors
  let cs ← colors.mapM fun c => if h : c < k then some (⟨c, h⟩ : Fin k) else none
  if h : cs.length = n then
    let c ← Coloring.ofVector? (⟨cs.toArray, by simpa using h⟩ : Vector (Fin k) n)
    pure ⟨G, c⟩
  else none

inductive Kind where
  | exists_
  | none_
  /-- Every satisfying object is isomorphic to a listed one, and every listed one satisfies. -/
  | exhaustive (list : List Witness)
  /-- Exactly `m` isomorphism classes satisfy the predicate. -/
  | count (m : Nat)
  /-- COUNT = `m` *assuming* the catalog `list` is complete (M4 ranks 6–7: a trusted generator or
  two-route agreement). The premise is part of the statement, so a held claim of this kind is held
  modulo a visible OPEN premise, and holding EXHAUSTIVE(`list`) discharges it. -/
  | countGiven (list : List Witness) (m : Nat)
  /-- DK V4 slice: exactly `m` isomorphism classes among the objects with DK's point action `a0` on
  points `0..pts-1` (`V4Count`, `docs/DK-V4-DESIGN.md`). -/
  | v4Count (pts : Nat) (a0 : List (List Nat)) (m : Nat)
  /-- The same, assuming the catalog `list` is complete for those objects: a visible OPEN premise
  (CELL-COMPLETE for the n = 23 cells). -/
  | v4CountGiven (pts : Nat) (a0 : List (List Nat)) (list : List Witness) (m : Nat)
  deriving Repr, DecidableEq

structure Stmt where
  colors : Nat
  pred : Formula
  kind : Kind
  deriving Repr, DecidableEq

/-- Exact parameter sets: the vertex counts a claim covers. -/
abbrev Scope := List Nat

def Scope.le (a b : Scope) : Bool := a.all b.contains

/-- The truth of a census statement among coloured graphs on `n` vertices. -/
def Holds (s : Stmt) (n : Nat) : Prop :=
  match s.kind with
  | .exists_ => ∃ G : Colored n s.colors, Sat G s.pred
  | .none_ => ∀ G : Colored n s.colors, ¬ Sat G s.pred
  | .exhaustive L =>
    (∀ w ∈ L, ∃ H, decode n s.colors w = some H ∧ Sat H s.pred) ∧
      ∀ G : Colored n s.colors, Sat G s.pred →
        ∃ w ∈ L, ∃ H, decode n s.colors w = some H ∧ Isomorphic G H
  | .count m =>
    ∃ Hs : List (Colored n s.colors), Hs.length = m ∧ (∀ H ∈ Hs, Sat H s.pred) ∧
      Hs.Pairwise (fun a b => ¬ Isomorphic a b) ∧
      ∀ G : Colored n s.colors, Sat G s.pred → ∃ H ∈ Hs, Isomorphic G H
  | .countGiven L m =>
    (∀ G : Colored n s.colors, Sat G s.pred →
        ∃ w ∈ L, ∃ H, decode n s.colors w = some H ∧ Isomorphic G H) →
      ∃ Hs : List (Colored n s.colors), Hs.length = m ∧ (∀ H ∈ Hs, Sat H s.pred) ∧
        Hs.Pairwise (fun a b => ¬ Isomorphic a b) ∧
        ∀ G : Colored n s.colors, Sat G s.pred → ∃ H ∈ Hs, Isomorphic G H
  | .v4Count pts a0 m => V4Count n s.colors pts a0 s.pred m
  | .v4CountGiven pts a0 L m =>
    (∀ G : Colored n s.colors, InS pts a0 s.pred G →
        ∃ w ∈ L, ∃ H, decode n s.colors w = some H ∧ Isomorphic G H) →
      V4Count n s.colors pts a0 s.pred m

/-- Kinds that cannot both hold at one parameter. -/
def kindContra : Kind → Kind → Bool
  | .exists_, .none_ => true
  | .exists_, .count 0 => true
  | .none_, .count (_ + 1) => true
  | _, _ => false

def contra (a b : Stmt) : Bool :=
  a.colors == b.colors && a.pred == b.pred && (kindContra a.kind b.kind || kindContra b.kind a.kind)

def ops : Semantic.ProfileOps where
  Stmt := Stmt
  Scope := Scope
  same a b := decide (a = b)
  same_sound := by intro a b h; exact of_decide_eq_true h
  le := Scope.le
  contra := contra

theorem kindContra_sound {c : Nat} {φ : Formula} {k₁ k₂ : Kind} {n : Nat}
    (h : kindContra k₁ k₂ = true) (h₁ : Holds ⟨c, φ, k₁⟩ n) (h₂ : Holds ⟨c, φ, k₂⟩ n) : False := by
  match k₁, k₂, h with
  | .exists_, .none_, _ =>
    obtain ⟨G, hG⟩ := h₁
    exact h₂ G hG
  | .exists_, .count 0, _ =>
    obtain ⟨G, hG⟩ := h₁
    obtain ⟨Hs, hlen, -, -, hall⟩ := h₂
    obtain ⟨H, hH, -⟩ := hall G hG
    rw [List.length_eq_zero_iff] at hlen
    subst hlen
    simp at hH
  | .none_, .count (m + 1), _ =>
    obtain ⟨Hs, hlen, hsat, -, -⟩ := h₂
    match Hs, hlen with
    | H :: _, _ => exact h₁ H (hsat H List.mem_cons_self)

theorem contra_sound (a b : Stmt) (n : Nat) (h : contra a b = true) (ha : Holds a n)
    (hb : Holds b n) : False := by
  obtain ⟨ca, φa, ka⟩ := a
  obtain ⟨cb, φb, kb⟩ := b
  simp only [contra, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨rfl, rfl⟩, h | h⟩ := h
  · exact kindContra_sound h ha hb
  · exact kindContra_sound h hb ha

def profile : Semantic.Profile where
  toProfileOps := ops
  Ctx := Nat
  mem n (sc : Scope) := n ∈ sc
  Holds s n := Holds s n
  le_sound := by
    intro a b n hle hn
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hle n hn)
  contra_sound := contra_sound

/-! ## Certificates and reach -/

inductive Cert where
  /-- EXISTS at `n`: an exact witness, checked directly (rank 1 in M4). -/
  | witness (n : Nat) (w : Witness)
  /-- NONE at `n`: an LRAT refutation of the CNF Lean emits for the predicate at `n` (M4 rank 2).
  A solver's exit status or a timeout is not a certificate; only a replayed refutation is. -/
  | lrat (n : Nat) (proof : String)
  /-- NONE at `n` by cube and conquer: one refutation per leaf (cube ∧ CNF) and one for the cover,
  either of the negated cubes alone or, when `relative`, of the CNF with them (M4 §4). A missing
  cube makes the cover formula satisfiable, so no cover refutation exists. -/
  | cover (n : Nat) (cubes : List LRATCatcher.Cube) (leaves : List String) (coverProof : String)
      (relative : Bool)
  /-- EXHAUSTIVE or COUNT at `n` by listing (M4 rank 3): the listed objects, the relabellings of
  the lex-leader break, and an LRAT refutation of "satisfies, meets the break, and is none of
  them". COUNT also needs pairwise-distinct canonical forms. -/
  | listed (n : Nat) (list : List Witness) (labels : List (List Nat)) (proof : String)
  /-- COUNT-given-catalog at `n`: every catalog member satisfies, and their canonical forms are
  pairwise distinct and `m` in number. The catalog's completeness stays an OPEN premise. -/
  | catalog (n : Nat)
  /-- V4 COUNT at `n` by listing: every labelled model of the normal-form listing CNF, the
  representatives with their actions, centralising relabellings, and an LRAT refutation of the CNF
  with every model blocked (`v4ListedOk`). -/
  | v4listed (n : Nat) (models : List Witness) (reps : List (Witness × List (List Nat)))
      (labels : List (List Nat)) (proof : String)
  /-- V4 COUNT given the catalog: its members with their actions (`repsOk`). -/
  | v4catalog (n : Nat) (reps : List (Witness × List (List Nat)))
  /-- NONE at `n + 1` for an extension predicate (HW61 G-5, `Extension.lean`): the base on `n`
  vertices, the degree `k`, the pattern list, and one hit per neighbourhood of the Lean generator. -/
  | extCover (n k : Nat) (base : List (Nat × Nat)) (pats : List Extension.Pattern)
      (hits : List Extension.Hit)
  deriving Repr, DecidableEq

/-- A relabelling from its array of old vertices, if it is a permutation. -/
def labelOf (n : Nat) (a : List Nat) : Option (Label n) := (Perm.ofNatArray? n a.toArray).map Label.mk

theorem mapM_some_mem_left {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ a ∈ l, ∃ b ∈ l', f a = some b
  | [], _, _, _, ha => by simp at ha
  | x :: xs, l', h, a, ha => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some bs =>
        simp only [hx, hxs, Option.bind_some, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨b, List.mem_cons_self, hx⟩
        · obtain ⟨b', hb', hf⟩ := mapM_some_mem_left hxs a ha
          exact ⟨b', List.mem_cons_of_mem _ hb', hf⟩

theorem mapM_some_mem_right {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ b ∈ l', ∃ a ∈ l, f a = some b
  | [], l', h, b, hb => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp at hb
  | x :: xs, l', h, b, hb => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some c =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some bs =>
        simp only [hx, hxs, Option.bind_some, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨x, List.mem_cons_self, hx⟩
        · obtain ⟨a, ha, hf⟩ := mapM_some_mem_right hxs b hb
          exact ⟨a, List.mem_cons_of_mem _ ha, hf⟩

theorem mapM_some_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | x :: xs, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some c =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some bs =>
        simp only [hx, hxs, Option.bind_some, Option.some.injEq] at h
        subst h
        simp [mapM_some_length hxs]

/-- A representative and its action. -/
def decodeRep (n k : Nat) (r : Witness × List (List Nat)) : Option (Colored n k × List (List Nat)) :=
  (decode n k r.1).map (·, r.2)

/-- The parameters a certificate reaches for a statement, or `none` when its check fails. -/
def reach (s : Stmt) : Cert → Option Scope
  | .witness n w =>
    match s.kind, decode n s.colors w with
    | .exists_, some G => if eval G idAct [] s.pred then some [n] else none
    | _, _ => none
  | .lrat n proof =>
    match s.kind with
    | .none_ => if LRATCatcher.checkLratCnf (cnf n s.colors s.pred) proof then some [n] else none
    | _ => none
  | .cover n cubes leaves coverProof relative =>
    match s.kind with
    | .none_ =>
      let base := cnf n s.colors s.pred
      let ok := if relative then LRATCatcher.checkCoverRel base cubes leaves coverProof
        else LRATCatcher.checkCover base cubes leaves coverProof
      if ok then some [n] else none
    | _ => none
  | .listed n list labels proof =>
    match list.mapM (decode n s.colors), labels.mapM (labelOf n) with
    | some Bs, some ls =>
      if Bs.all (fun B => eval B idAct [] s.pred) &&
          LRATCatcher.checkLratCnf (listCnf n s.colors s.pred ls Bs) proof then
        match s.kind with
        | .exhaustive L => if L == list then some [n] else none
        | .count m => if Bs.length == m && decide ((Bs.map canon).Nodup) then some [n] else none
        | _ => none
      else none
    | _, _ => none
  | .catalog n =>
    match s.kind with
    | .countGiven L m =>
      match L.mapM (decode n s.colors) with
      | some Bs =>
        if Bs.all (fun B => eval B idAct [] s.pred) && Bs.length == m && decide ((Bs.map canon).Nodup) then
          some [n] else none
      | none => none
    | _ => none
  | .v4listed n models reps labels proof =>
    match s.kind with
    | .v4Count pts a0 m =>
      match models.mapM (decode n s.colors), reps.mapM (decodeRep n s.colors), labels.mapM (labelOf n) with
      | some Bs, some Rs, some ls => if v4ListedOk pts a0 s.pred m Bs Rs ls proof then some [n] else none
      | _, _, _ => none
    | _ => none
  | .v4catalog n reps =>
    match s.kind with
    | .v4CountGiven pts a0 L m =>
      match reps.mapM (decodeRep n s.colors) with
      | some Rs => if reps.map (·.1) == L && repsOk pts a0 s.pred m Rs then some [n] else none
      | none => none
    | _ => none
  | .extCover n k base pats hits =>
    match s.kind with
    | .none_ => if Extension.extOk n k base pats hits s.pred then some [n + 1] else none
    | _ => none

theorem reach_sound {s : Stmt} {c : Cert} {r : Scope} (hr : reach s c = some r) :
    ∀ n ∈ r, Holds s n := by
  cases c with
  | witness m w =>
    unfold reach at hr
    cases hk : s.kind with
    | exists_ =>
      cases hd : decode m s.colors w with
      | none => simp [hk, hd] at hr
      | some G =>
        simp only [hk, hd] at hr
        by_cases he : eval G idAct [] s.pred = true
        · simp only [he, if_true, Option.some.injEq] at hr
          subst hr
          intro n hn
          simp only [List.mem_singleton] at hn
          subst hn
          unfold Holds
          rw [hk]
          exact ⟨G, he⟩
        · simp [he] at hr
    | none_ => simp [hk] at hr
    | exhaustive L => simp [hk] at hr
    | count c => simp [hk] at hr
    | countGiven L c => simp [hk] at hr
    | v4Count _ _ _ => simp [hk] at hr
    | v4CountGiven _ _ _ _ => simp [hk] at hr
  | lrat m proof =>
    unfold reach at hr
    cases hk : s.kind with
    | none_ =>
      simp only [hk] at hr
      by_cases hc : LRATCatcher.checkLratCnf (cnf m s.colors s.pred) proof = true
      · simp only [hc, if_true, Option.some.injEq] at hr
        subst hr
        intro n hn
        simp only [List.mem_singleton] at hn
        subst hn
        unfold Holds
        rw [hk]
        exact none_of_unsat (LRATCatcher.checkLratCnf_sound _ _ hc)
      · simp [hc] at hr
    | exists_ => simp [hk] at hr
    | exhaustive L => simp [hk] at hr
    | count c => simp [hk] at hr
    | countGiven L c => simp [hk] at hr
    | v4Count _ _ _ => simp [hk] at hr
    | v4CountGiven _ _ _ _ => simp [hk] at hr
  | cover m cubes leaves coverProof relative =>
    unfold reach at hr
    cases hk : s.kind with
    | none_ =>
      simp only [hk] at hr
      have unsat : (if relative then LRATCatcher.checkCoverRel (cnf m s.colors s.pred) cubes leaves coverProof
          else LRATCatcher.checkCover (cnf m s.colors s.pred) cubes leaves coverProof) = true →
          (cnf m s.colors s.pred).Unsat := by
        cases relative
        · exact LRATCatcher.checkCover_sound _ _ _ _
        · exact LRATCatcher.checkCoverRel_sound _ _ _ _
      by_cases hc : (if relative then LRATCatcher.checkCoverRel (cnf m s.colors s.pred) cubes leaves coverProof
          else LRATCatcher.checkCover (cnf m s.colors s.pred) cubes leaves coverProof) = true
      · simp only [hc, if_true, Option.some.injEq] at hr
        subst hr
        intro n hn
        simp only [List.mem_singleton] at hn
        subst hn
        unfold Holds
        rw [hk]
        exact none_of_unsat (unsat hc)
      · simp only [hc] at hr
        simp at hr
    | exists_ => simp [hk] at hr
    | exhaustive L => simp [hk] at hr
    | count c => simp [hk] at hr
    | countGiven L c => simp [hk] at hr
    | v4Count _ _ _ => simp [hk] at hr
    | v4CountGiven _ _ _ _ => simp [hk] at hr
  | listed m list labels proof =>
    unfold reach at hr
    cases hBs : list.mapM (decode m s.colors) with
    | none => simp [hBs] at hr
    | some Bs =>
      cases hls : labels.mapM (labelOf m) with
      | none => simp [hBs, hls] at hr
      | some ls =>
        simp only [hBs, hls] at hr
        by_cases hok : (Bs.all (fun B => eval B idAct [] s.pred) &&
            LRATCatcher.checkLratCnf (listCnf m s.colors s.pred ls Bs) proof) = true
        · have hok' := hok
          simp only [Bool.and_eq_true, List.all_eq_true] at hok'
          obtain ⟨hsat, hlrat⟩ := hok'
          have complete := listed_of_unsat (LRATCatcher.checkLratCnf_sound _ _ hlrat)
          simp only [hok, if_true] at hr
          cases hk : s.kind with
          | exhaustive L =>
            simp only [hk] at hr
            by_cases hL : (L == list) = true
            · simp only [hL, if_true, Option.some.injEq] at hr
              subst hr
              have hL' : L = list := by simpa using hL
              subst hL'
              intro n hn
              simp only [List.mem_singleton] at hn
              subst hn
              unfold Holds
              rw [hk]
              refine ⟨fun w hw => ?_, fun G hG => ?_⟩
              · obtain ⟨B, hB, hd⟩ := mapM_some_mem_left hBs w hw
                exact ⟨B, hd, hsat B hB⟩
              · obtain ⟨B, hB, hiso⟩ := complete G hG
                obtain ⟨w, hw, hd⟩ := mapM_some_mem_right hBs B hB
                exact ⟨w, hw, B, hd, hiso⟩
            · simp [hL] at hr
          | count c =>
            simp only [hk] at hr
            by_cases hc : (Bs.length == c && decide ((Bs.map canon).Nodup)) = true
            · simp only [hc, if_true, Option.some.injEq] at hr
              subst hr
              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
              intro n hn
              simp only [List.mem_singleton] at hn
              subst hn
              unfold Holds
              rw [hk]
              exact ⟨Bs, hc.1, hsat, pairwise_noniso_of_canon hc.2, complete⟩
            · simp only [hc] at hr
              simp at hr
          | exists_ => simp [hk] at hr
          | none_ => simp [hk] at hr
          | countGiven L c => simp [hk] at hr
          | v4Count _ _ _ => simp [hk] at hr
          | v4CountGiven _ _ _ _ => simp [hk] at hr
        · simp only [hok] at hr
          simp at hr
  | catalog m =>
    unfold reach at hr
    cases hk : s.kind with
    | countGiven L c =>
      simp only [hk] at hr
      cases hBs : L.mapM (decode m s.colors) with
      | none => simp [hBs] at hr
      | some Bs =>
        simp only [hBs] at hr
        by_cases hok : (Bs.all (fun B => eval B idAct [] s.pred) && Bs.length == c &&
            decide ((Bs.map canon).Nodup)) = true
        · simp only [hok, if_true, Option.some.injEq] at hr
          subst hr
          simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
          obtain ⟨⟨hsat, hlen⟩, hnd⟩ := hok
          intro n hn
          simp only [List.mem_singleton] at hn
          subst hn
          unfold Holds
          rw [hk]
          intro hcomplete
          refine ⟨Bs, hlen, hsat, pairwise_noniso_of_canon hnd, fun G hG => ?_⟩
          obtain ⟨w, hw, H, hd, hiso⟩ := hcomplete G hG
          obtain ⟨B, hB, hdB⟩ := mapM_some_mem_left hBs w hw
          rw [hd] at hdB
          cases hdB
          exact ⟨H, hB, hiso⟩
        · simp only [hok] at hr
          simp at hr
    | exists_ => simp [hk] at hr
    | none_ => simp [hk] at hr
    | exhaustive L => simp [hk] at hr
    | count c => simp [hk] at hr
    | v4Count _ _ _ => simp [hk] at hr
    | v4CountGiven _ _ _ _ => simp [hk] at hr
  | v4listed m models reps labels proof =>
    unfold reach at hr
    cases hk : s.kind with
    | v4Count pts a0 c =>
      simp only [hk] at hr
      cases hBs : models.mapM (decode m s.colors) with
      | none => simp [hBs] at hr
      | some Bs =>
        cases hRs : reps.mapM (decodeRep m s.colors) with
        | none => simp [hBs, hRs] at hr
        | some Rs =>
          cases hls : labels.mapM (labelOf m) with
          | none => simp [hBs, hRs, hls] at hr
          | some ls =>
            simp only [hBs, hRs, hls] at hr
            by_cases hok : v4ListedOk pts a0 s.pred c Bs Rs ls proof = true
            · simp only [hok, if_true, Option.some.injEq] at hr
              subst hr
              intro n hn
              simp only [List.mem_singleton] at hn
              subst hn
              unfold Holds
              rw [hk]
              exact v4ListedOk_sound hok
            · simp [hok] at hr
    | exists_ => simp [hk] at hr
    | none_ => simp [hk] at hr
    | exhaustive L => simp [hk] at hr
    | count c => simp [hk] at hr
    | countGiven L c => simp [hk] at hr
    | v4CountGiven _ _ _ _ => simp [hk] at hr
  | v4catalog m reps =>
    unfold reach at hr
    cases hk : s.kind with
    | v4CountGiven pts a0 L c =>
      simp only [hk] at hr
      cases hRs : reps.mapM (decodeRep m s.colors) with
      | none => simp [hRs] at hr
      | some Rs =>
        simp only [hRs] at hr
        by_cases hok : (reps.map (·.1) == L && repsOk pts a0 s.pred c Rs) = true
        · simp only [hok, if_true, Option.some.injEq] at hr
          subst hr
          simp only [Bool.and_eq_true, beq_iff_eq] at hok
          obtain ⟨hL, hreps⟩ := hok
          intro n hn
          simp only [List.mem_singleton] at hn
          subst hn
          unfold Holds
          rw [hk]
          intro hcomplete
          apply v4CatalogOk_sound hreps
          intro G hG
          obtain ⟨w, hw, H, hd, hiso⟩ := hcomplete G hG
          rw [← hL] at hw
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
          obtain ⟨R, hR, hdR⟩ := mapM_some_mem_left hRs r hr
          simp only [decodeRep, hd, Option.map_some, Option.some.injEq] at hdR
          subst hdR
          exact ⟨H, List.mem_map_of_mem hR, hiso⟩
        · simp [hok] at hr
    | exists_ => simp [hk] at hr
    | none_ => simp [hk] at hr
    | exhaustive L => simp [hk] at hr
    | count c => simp [hk] at hr
    | countGiven L c => simp [hk] at hr
    | v4Count _ _ _ => simp [hk] at hr
  | extCover m k base pats hits =>
    unfold reach at hr
    cases hk : s.kind with
    | none_ =>
      simp only [hk] at hr
      by_cases hc : Extension.extOk m k base pats hits s.pred = true
      · simp only [hc, if_true, Option.some.injEq] at hr
        subst hr
        intro n hn
        simp only [List.mem_singleton] at hn
        subst hn
        unfold Holds
        rw [hk]
        simp only [Extension.extOk, Bool.and_eq_true, decide_eq_true_eq] at hc
        intro G hG
        rw [hc.1] at hG
        exact Extension.extCover_sound hc.2 G hG
      · simp [hc] at hr
    | exists_ => simp [hk] at hr
    | exhaustive L => simp [hk] at hr
    | count c => simp [hk] at hr
    | countGiven L c => simp [hk] at hr
    | v4Count _ _ _ => simp [hk] at hr
    | v4CountGiven _ _ _ _ => simp [hk] at hr

def check (s : Stmt) (scope : Scope) (c : Cert) : Bool :=
  match reach s c with
  | some r => Scope.le scope r
  | none => false

theorem check_sound {s : Stmt} {scope : Scope} {c : Cert} (h : check s scope c = true) :
    ∀ n ∈ scope, Holds s n := by
  unfold check at h
  split at h
  · rename_i r hr
    simp only [Scope.le, List.all_eq_true, List.contains_iff_mem] at h
    exact fun n hn => reach_sound hr n (h n hn)
  · contradiction

/-! ## Admission -/

abbrev Clause := Semantic.Clause ops

structure Receipt where
  name : String
  claim : Nat
  version : Nat
  binding : Binding
  cert : Cert
  deriving Repr, DecidableEq

def wellFormed (clauses : List Clause) (receipts : List Receipt) : Bool :=
  (clauses.map (·.key)).eraseDups.length == clauses.length &&
    (receipts.map (·.name)).eraseDups.length == receipts.length

def accepts (clauses : List Clause) (receipts : List Receipt) (w : Warrant) (name : String) : Bool :=
  wellFormed clauses receipts &&
    clauses.any fun c => c.key == w.claim && c.version == w.version && decide (c.binding = w.binding) &&
      receipts.any fun r => r.name == name && r.claim == c.key && r.version == c.version &&
        decide (r.binding = c.binding) && check c.stmt c.scope r.cert

def admission (clauses : List Clause) (receipts : List Receipt) : Admission :=
  Semantic.withNarrowing ops clauses { Admission.refuseAll with receipt := accepts clauses receipts }

/-! ## Meaning of held claims -/

theorem accepts_claim_meaning (clauses : List Clause) (receipts : List Receipt)
    (w : Warrant) (name : String) (accepted : accepts clauses receipts w name = true) :
    Semantic.ClaimMeaning profile clauses w.claim := by
  unfold accepts at accepted
  simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, decide_eq_true_eq] at accepted
  obtain ⟨wf, c, hc, ⟨⟨hkey, -⟩, -⟩, r, -, hok⟩ := accepted
  have nodup : (clauses.map (·.key)).Nodup := by
    unfold wellFormed at wf
    simp only [Bool.and_eq_true, beq_iff_eq] at wf
    exact nodup_of_eraseDups_length_eq _ (by simpa only [List.length_map] using wf.1)
  have means : Semantic.Means profile c.stmt c.scope := fun n hn => check_sound hok.2 n (by exact hn)
  refine ⟨⟨c, hc, hkey⟩, fun c' hc' hkey' => ?_⟩
  have := key_unique_of_nodup clauses (·.key) nodup c' c hc' hc (hkey'.trans hkey.symm)
  exact this ▸ means

theorem base_validator_sound (clauses : List Clause) (receipts : List Receipt) (snapshot : Snapshot) :
    Semantic.BaseValidatorSound profile clauses
      { Admission.refuseAll with receipt := accepts clauses receipts } snapshot := by
  constructor
  · intro w member name accepted
    exact ⟨w, member, rfl, accepts_claim_meaning clauses receipts w name accepted⟩
  · intros; contradiction
  · intros; contradiction

/-- Fold soundness for the census profile: a held claim's statement holds at every parameter its
scope lists. -/
theorem fold_held_meaning (clauses : List Clause) (receipts : List Receipt)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission clauses receipts) events = .ok state)
    (heldClaim : held state claim = true) :
    (∃ c ∈ clauses, c.key = claim) ∧
      ∀ c ∈ clauses, c.key = claim → ∀ n, n ∈ (show List Nat from c.scope) → Holds c.stmt n :=
  have h := Semantic.fold_held_meaning profile clauses _ events state claim
    (base_validator_sound clauses receipts state.snapshot) folded heldClaim
  ⟨h.1, fun c hc hk n hn => h.2 c hc hk n hn⟩

end GPCensus
