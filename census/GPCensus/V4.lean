import GPCensus.Listing

/-!
The DK V4 slice (`docs/DK-V4-DESIGN.md`): incidence structures carrying a Klein four-group action
in DK's normal form.

An object is a coloured graph whose points are vertices `0..pts-1` (colour 0) and whose lines are
the rest (colour 1), with no edge inside either side (`Normal`). A statement fixes DK's point action
`a0`, the three involutions as lists over points. `InS pts a0 φ G` asks for maps `A 0, A 1, A 2`
that agree with `a0` on points, send lines to lines, are injective and preserve adjacency, and under
which `φ` holds. Its action atoms read `A`.

Isomorphism classes are counted among these labelled objects. "Admits some V4 action with DK's point
inventory" is the same as "is isomorphic to a member" exactly when such actions are conjugate to
`a0`. That is the classification of V4-sets, the named premise V4-NORMAL-FORM, outside these claims.

Listing (`v4_listed_of_unsat`) fixes the point action in the CNF and breaks only relabellings that
commute with it (`Centralizing`): the least such relabelling of a member is a member (`InS_relabel`), meets every
centralising lex constraint (`orbit_min_fix`), and so equals a listed object when the listing CNF is
refuted. The CNF's extra constraints need only hold for members; they never define the claim.
-/

namespace GPCensus
open Hex Hex.GraphIso

variable {n k : Nat}

/-! ## The statement -/

/-- DK's point action: the image of point `v` under map `g`, or `v` itself off the table. -/
def pointAct (a0 : List (List Nat)) (g v : Nat) : Nat := (a0.getD g []).getD v v

/-- Points `0..pts-1` take colour 0, lines colour 1, and no edge joins two points or two lines. -/
def Normal (pts : Nat) (G : Colored n k) : Prop :=
  (∀ v : Fin n, (G.coloring.cells[v]).val = if v.val < pts then 0 else 1) ∧
    ∀ u v : Fin n, (u.val < pts ↔ v.val < pts) → G.graph.adj u v = false

/-- `A` extends DK's point action by injective, side-preserving maps that preserve adjacency. Maps
from the fourth on are the identity. -/
def ValidAct (pts : Nat) (a0 : List (List Nat)) (G : Colored n k) (A : Act n) : Prop :=
  (∀ g, 3 ≤ g → ∀ v, A g v = v) ∧
  ∀ g, g < 3 →
    (∀ v : Fin n, v.val < pts → (A g v).val = pointAct a0 g v.val ∧ (A g v).val < pts) ∧
    (∀ v : Fin n, pts ≤ v.val → pts ≤ (A g v).val) ∧
    (∀ u v, A g u = A g v → u = v) ∧
    ∀ u v, G.graph.adj (A g u) (A g v) = G.graph.adj u v

/-- The labelled members of a V4 statement. -/
def InS (pts : Nat) (a0 : List (List Nat)) (φ : Formula) (G : Colored n k) : Prop :=
  Normal pts G ∧ ∃ A, ValidAct pts a0 G A ∧ eval G A [] φ = true

/-! ## Checking a member -/

/-- The action a certificate supplies: maps `g < 3` read from `acts`, the identity elsewhere. -/
def actOf (acts : List (List Nat)) : Act n := fun g v =>
  if g < 3 then
    if h : (acts.getD g []).getD v.val v.val < n then ⟨_, h⟩ else v
  else v

def normalB (pts : Nat) (G : Colored n k) : Bool :=
  (List.finRange n).all fun v =>
    (G.coloring.cells[v]).val == (if v.val < pts then 0 else 1) &&
      (List.finRange n).all fun u => decide (u.val < pts) != decide (v.val < pts) || !G.graph.adj u v

def validB (pts : Nat) (a0 : List (List Nat)) (G : Colored n k) (A : Act n) : Bool :=
  (List.range 3).all fun g => (List.finRange n).all fun v =>
    (if v.val < pts then (A g v).val == pointAct a0 g v.val && decide ((A g v).val < pts)
      else decide (pts ≤ (A g v).val)) &&
    (List.finRange n).all fun u => (A g u != A g v || u == v) && G.graph.adj (A g u) (A g v) == G.graph.adj u v

def memberB (pts : Nat) (a0 : List (List Nat)) (φ : Formula) (G : Colored n k) (acts : List (List Nat)) :
    Bool :=
  normalB pts G && validB pts a0 G (actOf acts) && eval G (actOf acts) [] φ

theorem normalB_sound {pts : Nat} {G : Colored n k} (h : normalB pts G = true) : Normal pts G := by
  simp only [normalB, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
  refine ⟨fun v => (h v).1, fun u v huv => ?_⟩
  rcases (h v).2 u with hne | hadj
  · exact absurd (decide_eq_decide.mpr huv) hne
  · exact hadj

theorem validB_sound {pts : Nat} {a0 : List (List Nat)} {G : Colored n k} {acts : List (List Nat)}
    (h : validB pts a0 G (actOf acts) = true) : ValidAct pts a0 G (actOf acts) := by
  refine ⟨fun g hg v => by simp [actOf, Nat.not_lt.mpr hg], fun g hg => ?_⟩
  simp only [validB, List.all_eq_true, List.mem_range, List.mem_finRange, true_implies,
    Bool.and_eq_true] at h
  have hv := h g hg
  refine ⟨fun v hp => ?_, fun v hl => ?_, fun u v huv => ?_, fun u v => ?_⟩
  · have := (hv v).1
    simp only [hp, if_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact this
  · have := (hv v).1
    simp only [Nat.not_lt.mpr hl, if_false, decide_eq_true_eq] at this
    exact this
  · have := ((hv v).2 u).1
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
    exact this.resolve_left fun h => h huv
  · have := ((hv v).2 u).2
    simpa using this

theorem memberB_sound {pts : Nat} {a0 : List (List Nat)} {φ : Formula} {G : Colored n k}
    {acts : List (List Nat)} (h : memberB pts a0 φ G acts = true) : InS pts a0 φ G := by
  simp only [memberB, Bool.and_eq_true] at h
  exact ⟨normalB_sound h.1.1, actOf acts, validB_sound h.1.2, h.2⟩

/-! ## Centralising relabellings -/

/-- `l` keeps points as points and commutes with DK's point action, so relabelling by it keeps the
normal form. Point-fixing relabellings (line transpositions) are the special case. -/
def Centralizing (pts : Nat) (a0 : List (List Nat)) (l : Label n) : Prop :=
  (∀ v : Fin n, (l.get v).val < pts ↔ v.val < pts) ∧
  ∀ g, g < 3 → ∀ v w : Fin n, v.val < pts → w.val = pointAct a0 g v.val →
    (l.get w).val = pointAct a0 g (l.get v).val

def centB (pts : Nat) (a0 : List (List Nat)) (l : Label n) : Bool :=
  (List.finRange n).all fun v => decide ((l.get v).val < pts) == decide (v.val < pts) &&
    (List.range 3).all fun g => (List.finRange n).all fun w =>
      !(decide (v.val < pts) && w.val == pointAct a0 g v.val) || (l.get w).val == pointAct a0 g (l.get v).val

theorem centB_sound {pts : Nat} {a0 : List (List Nat)} {l : Label n} (h : centB pts a0 l = true) :
    Centralizing pts a0 l := by
  simp only [centB, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  refine ⟨fun v => decide_eq_decide.mp (h v).1, fun g hg v w hv hw => ?_⟩
  rcases (h v).2 g hg w with (h1 | h1) | h1
  · exact absurd hv h1
  · exact absurd hw (by simpa using h1)
  · exact h1

theorem Centralizing.id (pts : Nat) (a0 : List (List Nat)) : Centralizing pts a0 (Label.id n) :=
  ⟨fun v => by simp, fun g _ v w _ hw => by simp [hw]⟩

theorem Centralizing.comp {pts : Nat} {a0 : List (List Nat)} {l m : Label n} (hl : Centralizing pts a0 l)
    (hm : Centralizing pts a0 m) : Centralizing pts a0 (l.comp m) :=
  ⟨fun v => by simp only [Label.get_comp]; rw [hl.1, hm.1], fun g hg v w hv hw => by
    simp only [Label.get_comp]
    exact hl.2 g hg (m.get v) (m.get w) ((hm.1 v).mpr hv) (hm.2 g hg v w hv hw)⟩

theorem Centralizing.inv_side {pts : Nat} {a0 : List (List Nat)} {l : Label n} (hl : Centralizing pts a0 l)
    (v : Fin n) : (l.toPerm.get v).val < pts ↔ v.val < pts := by
  have := hl.1 (l.toPerm.get v)
  rw [Label.get_toPerm_get] at this
  exact this.symm

/-- Relabelling a member by a centralising labelling gives a member, with the conjugate action. -/
theorem InS_relabel {pts : Nat} {a0 : List (List Nat)} {φ : Formula} {G : Colored n k} {l : Label n}
    (hG : InS pts a0 φ G) (hl : Centralizing pts a0 l) : InS pts a0 φ (G.relabel l) := by
  obtain ⟨⟨hcol, hside⟩, A, ⟨hhi, hA⟩, hev⟩ := hG
  let A' : Act n := fun g v => l.toPerm.get (A g (l.get v))
  refine ⟨⟨fun v => ?_, fun u v huv => ?_⟩, A', ⟨fun g hg v => ?_, fun g hg => ?_⟩, ?_⟩
  · simp only [Fin.getElem_fin, Colored.cells_relabel, Fin.eta]
    have := hcol (l.get v)
    simp only [Fin.getElem_fin] at this
    rw [this]
    simp only [hl.1 v]
  · rw [Colored.adj_relabel]
    exact hside _ _ (by rw [hl.1 u, hl.1 v]; exact huv)
  · simp [A', hhi g hg]
  · obtain ⟨hpt, hln, hinj, hadj⟩ := hA g hg
    refine ⟨fun v hv => ?_, fun v hv => ?_, fun u v huv => ?_, fun u v => ?_⟩
    · obtain ⟨h1, h2⟩ := hpt v hv
      have hc : l.get (A g v) = A g (l.get v) :=
        Fin.ext ((hl.2 g hg v (A g v) hv h1).trans ((hpt _ ((hl.1 v).mpr hv)).1).symm)
      simp only [A', ← hc, Label.toPerm_get_get]
      exact ⟨h1, h2⟩
    · simp only [A']
      have hlv : pts ≤ (l.get v).val := Nat.not_lt.mp fun h => Nat.not_lt.mpr hv ((hl.1 v).mp h)
      exact Nat.not_lt.mp fun h => Nat.not_lt.mpr (hln _ hlv) ((hl.inv_side _).mp h)
    · simp only [A'] at huv
      have := hinj _ _ (l.toPerm.get_inj huv)
      exact l.perm.get_inj this
    · simp only [A', Colored.adj_relabel, Label.get_toPerm_get]
      exact hadj _ _
  · have hiso := isIso_relabel G l
    have := eval_iso hiso (A := A) (B := A') (fun g v => by simp [A']) φ []
    simpa using this.trans hev

/-- The least relabelling among the centralising ones. -/
theorem orbit_min_fix (G : Colored n k) (pts : Nat) (a0 : List (List Nat)) :
    ∃ l₀ : Label n, Centralizing pts a0 l₀ ∧
      ∀ l : Label n, Centralizing pts a0 l → key (vec (G.relabel l₀)) ≤ key (vec (G.relabel l)) := by
  suffices ∀ c, ∀ l : Label n, Centralizing pts a0 l → key (vec (G.relabel l)) = c →
      ∃ l₀ : Label n, Centralizing pts a0 l₀ ∧
        ∀ l', Centralizing pts a0 l' → key (vec (G.relabel l₀)) ≤ key (vec (G.relabel l')) from
    this _ (Label.id n) (Centralizing.id pts a0) rfl
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro l hl hc
    by_cases hmin : ∀ l', Centralizing pts a0 l' → key (vec (G.relabel l)) ≤ key (vec (G.relabel l'))
    · exact ⟨l, hl, hmin⟩
    · obtain ⟨l', hl'⟩ := Classical.not_forall.mp hmin
      obtain ⟨hfix, hlt⟩ := Classical.not_imp.mp hl'
      exact ih _ (by omega) l' hfix rfl

/-! ## The listing CNF -/

/-- Action atoms follow the edge and colour atoms. -/
def actBase (n k : Nat) : Nat := n * n + n * k

def actVar (n k g a b : Nat) : Nat := actBase n k + (g * n + a) * n + b

/-- Action atoms: fixed on points by `a0`, variables between lines, false across sides. -/
def actPV (n k pts : Nat) (a0 : List (List Nat)) : Nat → Fin n → Fin n → PExpr := fun g a b =>
  if g < 3 then
    if a.val < pts then .const (decide (pointAct a0 g a.val = b.val))
    else if pts ≤ b.val then .atom (actVar n k g a.val b.val) else .const false
  else .const (decide (a = b))

def iffP (x y : PExpr) : PExpr := .or (.and x y) (.and (.not x) (.not y))

def pointsOf (n pts : Nat) : List (Fin n) := (List.finRange n).filter fun v => decide (v.val < pts)

def linesOf (n pts : Nat) : List (Fin n) := (List.finRange n).filter fun v => decide (pts ≤ v.val)

/-- Colours by side, and no edge within a side. -/
def normalP (n k pts : Nat) : PExpr :=
  bigAnd ((List.finRange n).map fun v =>
    .and (.atom (colorVar n k v (if v.val < pts then 0 else 1)))
      (bigAnd ((List.finRange n).map fun u =>
        if decide (u.val < pts) = decide (v.val < pts) then
          if u = v then .const true else .not (.atom (edgeVar n u v))
        else .const true)))

/-- Each map sends each line to exactly one line, injectively, carrying incidence with `a0`. -/
def validP (n k pts : Nat) (a0 : List (List Nat)) : PExpr :=
  bigAnd ((List.range 3).map fun g =>
    bigAnd ((linesOf n pts).map fun a =>
      .and (bigOr ((linesOf n pts).map fun b => .atom (actVar n k g a.val b.val)))
        (.and (amo ((linesOf n pts).map fun b => .atom (actVar n k g a.val b.val)))
          (.and (amo ((linesOf n pts).map fun b => .atom (actVar n k g b.val a.val)))
            (bigAnd ((linesOf n pts).map fun b =>
              .or (.not (.atom (actVar n k g a.val b.val)))
                (bigAnd ((pointsOf n pts).map fun p =>
                  if h : pointAct a0 g p.val < pts ∧ pointAct a0 g p.val < n then
                    iffP (.atom (edgeVar n p a)) (.atom (edgeVar n ⟨_, h.2⟩ b))
                  else .const true))))))))

def v4ListCnf (n k pts : Nat) (a0 : List (List Nat)) (φ : Formula) (ls : List (Label n))
    (Bs : List (Colored n k)) : Std.Sat.CNF Nat :=
  (bigAnd ([colorValid n k, normalP n k pts, validP n k pts a0, groundA n k (actPV n k pts a0) [] φ,
    symBreak n k ls] ++ Bs.map fun B => .not (eqP n k B))).toCNF

/-! ## A member's own assignment -/

/-- A member's assignment: its edges and colours, then its action between lines. -/
def asgA (G : Colored n k) (A : Act n) (v : Nat) : Bool :=
  if v < actBase n k then assignment G v
  else
    let w := v - actBase n k
    if ha : w / n % n < n then
      if hb : w % n < n then decide ((A (w / n / n) ⟨w / n % n, ha⟩).val = w % n) else false
    else false

theorem asgA_agrees (G : Colored n k) (A : Act n) : Agrees G (asgA G A) := by
  constructor
  · intro a b hab
    have hlt : edgeVar n a b < actBase n k := by
      unfold edgeVar actBase
      have ha := a.isLt; have hb := b.isLt
      have : ∀ x y : Nat, x < n → y < n → x * n + y < n * n := fun x y hx hy => by
        have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hx)
        rw [Nat.succ_mul] at this; omega
      split
      · exact Nat.lt_of_lt_of_le (this a b ha hb) (Nat.le_add_right _ _)
      · exact Nat.lt_of_lt_of_le (this b a hb ha) (Nat.le_add_right _ _)
    simp only [asgA, if_pos hlt]
    exact assignment_edge G a b hab
  · intro v c hc
    have hlt : colorVar n k v c < actBase n k := by
      unfold colorVar actBase
      have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt v.isLt)
      rw [Nat.succ_mul] at this
      have : v.val * k + c < n * k := by omega
      omega
    simp only [asgA, if_pos hlt]
    exact assignment_color G v c hc

theorem asgA_act (G : Colored n k) (A : Act n) (g : Nat) (a b : Fin n) :
    asgA G A (actVar n k g a.val b.val) = decide ((A g a).val = b.val) := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have hw : actVar n k g a.val b.val - actBase n k = (g * n + a.val) * n + b.val := by
    unfold actVar; omega
  have h1 : ((g * n + a.val) * n + b.val) / n = g * n + a.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt b.isLt, Nat.zero_add]
  have h2 : ((g * n + a.val) * n + b.val) % n = b.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.isLt]
  have h3 : (g * n + a.val) % n = a.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]
  have h4 : (g * n + a.val) / n = g := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt a.isLt, Nat.zero_add]
  have hge : ¬ actVar n k g a.val b.val < actBase n k := by unfold actVar; omega
  simp only [asgA, if_neg hge, hw, h1, h2, h3, h4, dif_pos a.isLt, dif_pos b.isLt]

/-! ## Members satisfy the listing CNF's constraints -/

theorem amo_map_eval {α : Type} (asg : Nat → Bool) (f : α → PExpr) :
    ∀ L : List α, L.Nodup → (∀ i ∈ L, ∀ j ∈ L, (f i).eval asg = true → (f j).eval asg = true → i = j) →
      (amo (L.map f)).eval asg = true
  | [], _, _ => rfl
  | x :: xs, hnd, hu => by
    simp only [List.map_cons, amo, PExpr.eval, bigOr_eval, List.any_map, Bool.and_eq_true,
      Bool.not_eq_true', Bool.and_eq_false_iff]
    refine ⟨?_, amo_map_eval asg f xs (List.nodup_cons.mp hnd).2
      fun i hi j hj => hu i (List.mem_cons_of_mem _ hi) j (List.mem_cons_of_mem _ hj)⟩
    by_cases hx : (f x).eval asg = true
    · right
      rw [List.any_eq_false]
      intro y hy hfy
      have := hu x List.mem_cons_self y (List.mem_cons_of_mem _ hy) hx (by simpa using hfy)
      exact (List.nodup_cons.mp hnd).1 (this ▸ hy)
    · left; simpa using hx

theorem normalP_eval {pts : Nat} {G : Colored n k} (hk : 2 ≤ k) (hN : Normal pts G) {asg : Nat → Bool}
    (hG : Agrees G asg) : (normalP n k pts).eval asg = true := by
  simp only [normalP, bigAnd_eval, List.all_map, List.all_eq_true, List.mem_finRange, true_implies]
  intro v
  simp only [Function.comp, PExpr.eval, Bool.and_eq_true, bigAnd_eval, List.all_map, List.all_eq_true,
    List.mem_finRange, true_implies]
  refine ⟨?_, fun u => ?_⟩
  · rw [hG.color v _ (by split <;> omega)]
    have := hN.1 v
    simp only [Fin.getElem_fin] at this
    simp [Fin.getElem_fin, this]
  · split
    · rename_i hs
      split
      · rfl
      · rename_i huv
        simp only [PExpr.eval, hG.edge u v huv, Bool.not_eq_true']
        exact hN.2 u v (decide_eq_decide.mp hs)
    · rfl

theorem mem_linesOf {pts : Nat} {v : Fin n} : v ∈ linesOf n pts ↔ pts ≤ v.val := by
  simp [linesOf]

theorem mem_pointsOf {pts : Nat} {v : Fin n} : v ∈ pointsOf n pts ↔ v.val < pts := by
  simp [pointsOf]

theorem linesOf_nodup (pts : Nat) : (linesOf n pts).Nodup := (List.nodup_finRange n).filter _

theorem validP_eval {pts : Nat} {a0 : List (List Nat)} {G : Colored n k} {A : Act n}
    (hV : ValidAct pts a0 G A) {asg : Nat → Bool} (hG : Agrees G asg)
    (hact : ∀ g (a b : Fin n), asg (actVar n k g a.val b.val) = decide ((A g a).val = b.val)) :
    (validP n k pts a0).eval asg = true := by
  simp only [validP, bigAnd_eval, List.all_map, List.all_eq_true, List.mem_range]
  intro g hg
  obtain ⟨hpt, hln, hinj, hadj⟩ := hV.2 g hg
  simp only [Function.comp, bigAnd_eval, List.all_map, List.all_eq_true]
  intro a ha
  have hal := mem_linesOf.mp ha
  simp only [PExpr.eval, Bool.and_eq_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bigOr_eval, List.any_map, List.any_eq_true]
    refine ⟨A g a, mem_linesOf.mpr (hln a hal), ?_⟩
    simp [Function.comp, PExpr.eval, hact]
  · apply amo_map_eval asg _ _ (linesOf_nodup pts)
    intro i _ j _ hi hj
    simp only [PExpr.eval, hact, decide_eq_true_eq] at hi hj
    exact Fin.ext (hi.symm.trans hj)
  · apply amo_map_eval asg _ _ (linesOf_nodup pts)
    intro i _ j _ hi hj
    simp only [PExpr.eval, hact, decide_eq_true_eq] at hi hj
    exact hinj _ _ (Fin.ext (hi.trans hj.symm))
  · rw [bigAnd_eval, List.all_eq_true]
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    simp only [PExpr.eval, hact, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    by_cases hab : (A g a).val = b.val
    · right
      have hAb : A g a = b := Fin.ext hab
      rw [bigAnd_eval, List.all_eq_true]
      intro y hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
      have hpp := mem_pointsOf.mp hp
      split
      · rename_i h
        obtain ⟨h1, h2⟩ := hpt p hpp
        have hq : A g p = ⟨pointAct a0 g p.val, h.2⟩ := Fin.ext h1
        have hpa : p ≠ a := fun e => by subst e; omega
        have hqb : (⟨pointAct a0 g p.val, h.2⟩ : Fin n) ≠ b := fun e => by
          rw [← e] at hb; have := mem_linesOf.mp hb; simp at this; omega
        simp only [iffP, PExpr.eval, hG.edge p a hpa, hG.edge _ b hqb]
        rw [← hq, ← hAb, hadj]
        cases G.graph.adj p a <;> rfl
      · rfl
    · left; exact hab

theorem actPV_eval {pts : Nat} {a0 : List (List Nat)} {G : Colored n k} {A : Act n}
    (hV : ValidAct pts a0 G A) {asg : Nat → Bool}
    (hact : ∀ g (a b : Fin n), asg (actVar n k g a.val b.val) = decide ((A g a).val = b.val))
    (g : Nat) (a b : Fin n) : (actPV n k pts a0 g a b).eval asg = decide (A g a = b) := by
  unfold actPV
  split
  · rename_i hg
    obtain ⟨hpt, hln, -, -⟩ := hV.2 g hg
    split
    · rename_i ha
      simp only [PExpr.eval]
      rw [← (hpt a ha).1]
      exact decide_eq_decide.mpr ⟨fun h => Fin.ext h, fun h => h ▸ rfl⟩
    · rename_i ha
      split
      · simp only [PExpr.eval, hact]
        exact decide_eq_decide.mpr ⟨fun h => Fin.ext h, fun h => h ▸ rfl⟩
      · rename_i hb
        simp only [PExpr.eval]
        have := hln a (Nat.not_lt.mp ha)
        symm
        rw [decide_eq_false_iff_not]
        intro h
        rw [h] at this
        exact hb this
  · rename_i hg
    simp only [PExpr.eval, hV.1 g (Nat.not_lt.mp hg)]

/-! ## Listing -/

/-- If "a member in normal form, meeting the centralising break, and none of the listed objects" is
unsatisfiable, every member is isomorphic to a listed object. -/
theorem v4_listed_of_unsat {pts : Nat} {a0 : List (List Nat)} {φ : Formula} {ls : List (Label n)}
    {Bs : List (Colored n k)} (hk : 2 ≤ k) (hls : ∀ l ∈ ls, Centralizing pts a0 l)
    (h : (v4ListCnf n k pts a0 φ ls Bs).Unsat) :
    ∀ G : Colored n k, InS pts a0 φ G → ∃ B ∈ Bs, Isomorphic G B := by
  intro G hG
  obtain ⟨l₀, hfix, hmin⟩ := orbit_min_fix G pts a0
  let H := G.relabel l₀
  have hiso : Isomorphic G H := isomorphic_relabel G l₀
  obtain ⟨hN, A, hV, hev⟩ := InS_relabel hG hfix
  let asg := asgA H A
  have hagr : Agrees H asg := asgA_agrees H A
  have hact : ∀ g (a b : Fin n), asg (actVar n k g a.val b.val) = decide ((A g a).val = b.val) :=
    asgA_act H A
  have hbreak : (symBreak n k ls).eval asg = true := by
    rw [symBreak_eval H hagr, List.all_eq_true]
    intro l hl
    rw [lexLeB_iff _ _ (by simp [vec_length])]
    have := hmin (l₀.comp l) (hfix.comp (hls l hl))
    rwa [← Colored.relabel_relabel] at this
  have hg : (groundA n k (actPV n k pts a0) [] φ).eval asg = true := by
    rw [groundA_eval H A _ asg hagr.edge hagr.color (actPV_eval hV hact)]
    exact hev
  have hf := PExpr.eval_false_of_unsat h asg
  simp only [bigAnd_eval, List.all_append, List.all_cons, List.all_nil, List.all_map, Bool.and_true,
    colorValid_eval H hagr, normalP_eval hk hN hagr, validP_eval hV hagr hact, hg, hbreak,
    Bool.true_and] at hf
  rw [List.all_eq_false] at hf
  obtain ⟨B, hB, hne⟩ := hf
  simp only [Function.comp, PExpr.eval, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at hne
  simp only [eqP_eval H _ hagr, List.all_eq_true, beq_iff_eq] at hne
  have : H = B := eq_of_atoms hne
  exact ⟨B, hB, this ▸ hiso⟩

end GPCensus
