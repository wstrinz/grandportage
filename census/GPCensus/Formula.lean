import HexGraphIso

/-!
Census predicates (M4 §1; Will, 2026-10-04: relabelling-invariant predicates only).

A predicate is a first-order formula over adjacency, equality and vertex colour, with counting
quantifiers, evaluated on a HexGraphIso coloured graph. Graphs use one colour; incidence structures
are 2-coloured Levi graphs (points, then lines). Variables are de Bruijn indices; an unbound
variable makes its atom false. Its meaning is `eval`, a structural Boolean evaluation over `Fin n`.

`eval_iso` is the one generic invariance theorem: every formula has the same value on isomorphic
coloured graphs. So "up to isomorphism" is well defined for every census statement, and no
per-predicate invariance proof is needed.

Action atoms (DK V4 slice, `docs/DK-V4-DESIGN.md`): `act g i j` reads "the action's map `g` sends `i`
to `j`". `eval` takes the action as a parameter. Plain statements use the identity action `idAct`,
under which `act g i j` means `i = j`; their meaning is unchanged. `eval_iso` covers actions
conjugated by the isomorphism.
-/

namespace GPCensus
open Hex Hex.GraphIso

inductive Formula where
  | tt
  | adj (i j : Nat)
  | eq (i j : Nat)
  | color (i c : Nat)
  | not (φ : Formula)
  | and (φ ψ : Formula)
  | or (φ ψ : Formula)
  | ex (φ : Formula)
  | all (φ : Formula)
  /-- At least `m` vertices `x` satisfy `φ`, with `x` bound as variable 0. -/
  | atLeast (m : Nat) (φ : Formula)
  /-- The action's map `g` sends variable `i` to variable `j`. -/
  | act (g i j : Nat)
  deriving Repr, DecidableEq, Inhabited

variable {n k : Nat}

/-- An action on the vertices: map `g` for each index `g`. -/
abbrev Act (n : Nat) := Nat → Fin n → Fin n

/-- The identity action: plain statements. -/
def idAct : Act n := fun _ v => v

/-- The meaning of a formula in a coloured graph with an action, under an environment of vertices. -/
def eval (G : Colored n k) (A : Act n) : List (Fin n) → Formula → Bool
  | _, .tt => true
  | env, .adj i j =>
    match env[i]?, env[j]? with
    | some a, some b => G.graph.adj a b
    | _, _ => false
  | env, .eq i j =>
    match env[i]?, env[j]? with
    | some a, some b => decide (a = b)
    | _, _ => false
  | env, .color i c =>
    match env[i]? with
    | some a => decide ((G.coloring.cells[a]).val = c)
    | none => false
  | env, .not φ => !eval G A env φ
  | env, .and φ ψ => eval G A env φ && eval G A env ψ
  | env, .or φ ψ => eval G A env φ || eval G A env ψ
  | env, .ex φ => (List.finRange n).any fun v => eval G A (v :: env) φ
  | env, .all φ => (List.finRange n).all fun v => eval G A (v :: env) φ
  | env, .atLeast m φ => decide (m ≤ (List.finRange n).countP fun v => eval G A (v :: env) φ)
  | env, .act g i j =>
    match env[i]?, env[j]? with
    | some a, some b => decide (A g a = b)
    | _, _ => false

/-- `G` satisfies the closed formula `φ`. -/
def Sat (G : Colored n k) (φ : Formula) : Prop := eval G idAct [] φ = true

/-! ## Invariance under colour-preserving relabelling -/

theorem map_finRange_perm (p : Perm n) : ((List.finRange n).map p.get).Perm (List.finRange n) := by
  have hmap : (List.finRange n).map p.get = p.vec.toList := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [List.getElem_map, List.getElem_finRange]
      exact (p.get_toList ⟨i, by simpa using h₁⟩).symm
  rw [hmap]
  refine (List.perm_ext_iff_of_nodup p.nodup (List.nodup_finRange n)).mpr fun a => ?_
  exact ⟨fun _ => List.mem_finRange a, fun _ => p.complete a⟩

/-- An isomorphism carries an action to its conjugate (`hA`) and preserves every formula. -/
theorem eval_iso {G H : Colored n k} {p : Perm n} (hp : IsIso G H p) {A B : Act n}
    (hA : ∀ g v, B g (p.get v) = p.get (A g v)) :
    ∀ (φ : Formula) (env : List (Fin n)), eval H B (env.map p.get) φ = eval G A env φ := by
  have hperm := map_finRange_perm p
  intro φ
  induction φ with
  | tt => intro env; rfl
  | adj i j =>
    intro env
    simp only [eval, List.getElem?_map]
    cases env[i]? <;> cases env[j]? <;> simp [hp.2]
  | eq i j =>
    intro env
    simp only [eval, List.getElem?_map]
    cases env[i]? <;> cases env[j]? <;> simp
    exact ⟨fun h => p.get_inj h, fun h => h ▸ rfl⟩
  | color i c =>
    intro env
    simp only [eval, List.getElem?_map]
    cases env[i]? <;> simp [hp.1]
  | not φ ih => intro env; simp [eval, ih]
  | and φ ψ ih₁ ih₂ => intro env; simp [eval, ih₁, ih₂]
  | or φ ψ ih₁ ih₂ => intro env; simp [eval, ih₁, ih₂]
  | ex φ ih =>
    intro env
    simp only [eval]
    rw [← hperm.any_eq, List.any_map]
    congr 1
    funext u
    exact ih (u :: env)
  | all φ ih =>
    intro env
    simp only [eval]
    rw [← hperm.all_eq, List.all_map]
    congr 1
    funext u
    exact ih (u :: env)
  | atLeast m φ ih =>
    intro env
    simp only [eval]
    rw [← hperm.countP_eq, List.countP_map]
    congr 3
    funext u
    exact ih (u :: env)
  | act g i j =>
    intro env
    simp only [eval, List.getElem?_map]
    cases env[i]? <;> cases env[j]? <;> simp [hA]
    exact ⟨fun h => p.get_inj h, fun h => h ▸ rfl⟩

/-- Isomorphic coloured graphs satisfy the same formulas. -/
theorem sat_iff_of_isomorphic {G H : Colored n k} (h : Isomorphic G H) (φ : Formula) :
    Sat G φ ↔ Sat H φ := by
  obtain ⟨p, hp⟩ := h
  unfold Sat
  rw [← eval_iso hp (A := idAct) (B := idAct) (fun _ _ => rfl) φ []]
  rfl

end GPCensus
