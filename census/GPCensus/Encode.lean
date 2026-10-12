import GPCensus.Formula
import GPCensus.Circuit

/-!
The census encoder (M4 §3): a Lean function from a predicate and a vertex count to a CNF, with its
model-expansion theorem.

`ground` unfolds the quantifiers over `Fin n` into a propositional expression over two kinds of
atoms: one per vertex pair (adjacency) and one per vertex and colour. `assignment G` reads those atoms
off a coloured graph, and `ground_eval` proves the expression then takes the formula's value. So
every satisfying object yields a satisfying assignment of `cnf n k φ` (model expansion), and an
unsatisfiable `cnf` proves NONE (`none_of_unsat`). No symmetry breaking is involved, so no WLOG
argument is needed.

Counting quantifiers expand by the recurrence `≥ m+1 of x :: xs ⇔ (≥ m+1 of xs) ∨ (x ∧ ≥ m of xs)`.
The circuit's cache shares the repeated subterms, but the expression itself grows with the binomial
coefficient, so large counts belong to the direct-witness and list routes.
-/

namespace GPCensus
open Hex Hex.GraphIso

variable {n k : Nat}

/-- The atom of the vertex pair `{a, b}`. -/
def edgeVar (n : Nat) (a b : Fin n) : Nat := if a.val < b.val then a.val * n + b.val else b.val * n + a.val

/-- The atom of "vertex `v` has colour `c`". -/
def colorVar (n k : Nat) (v : Fin n) (c : Nat) : Nat := n * n + v.val * k + c

def bigOr : List PExpr → PExpr
  | [] => .const false
  | x :: xs => .or x (bigOr xs)

def bigAnd : List PExpr → PExpr
  | [] => .const true
  | x :: xs => .and x (bigAnd xs)

/-- At least `m` of the expressions hold. -/
def atLeastP : Nat → List PExpr → PExpr
  | 0, _ => .const true
  | _ + 1, [] => .const false
  | m + 1, x :: xs => .or (atLeastP (m + 1) xs) (.and x (atLeastP m xs))

/-- Grounding with action atoms read by `actP` (DK V4 slice). -/
def groundA (n k : Nat) (actP : Nat → Fin n → Fin n → PExpr) : List (Fin n) → Formula → PExpr
  | _, .tt => .const true
  | env, .adj i j =>
    match env[i]?, env[j]? with
    | some a, some b => if a = b then .const false else .atom (edgeVar n a b)
    | _, _ => .const false
  | env, .eq i j =>
    match env[i]?, env[j]? with
    | some a, some b => .const (decide (a = b))
    | _, _ => .const false
  | env, .color i c =>
    match env[i]? with
    | some a => if c < k then .atom (colorVar n k a c) else .const false
    | none => .const false
  | env, .not φ => .not (groundA n k actP env φ)
  | env, .and φ ψ => .and (groundA n k actP env φ) (groundA n k actP env ψ)
  | env, .or φ ψ => .or (groundA n k actP env φ) (groundA n k actP env ψ)
  | env, .ex φ => bigOr ((List.finRange n).map fun v => groundA n k actP (v :: env) φ)
  | env, .all φ => bigAnd ((List.finRange n).map fun v => groundA n k actP (v :: env) φ)
  | env, .atLeast m φ => atLeastP m ((List.finRange n).map fun v => groundA n k actP (v :: env) φ)
  | env, .act g i j =>
    match env[i]?, env[j]? with
    | some a, some b => actP g a b
    | _, _ => .const false

/-- Action atoms under the identity action. -/
def plainAct : Nat → Fin n → Fin n → PExpr := fun _ a b => .const (decide (a = b))

/-- Grounding for plain statements: the identity action. -/
def ground (n k : Nat) (env : List (Fin n)) (φ : Formula) : PExpr := groundA n k plainAct env φ

/-- The atoms' values in a coloured graph. -/
def assignment (G : Colored n k) (v : Nat) : Bool :=
  if h : v < n * n then
    G.graph.adj ⟨v / n, Nat.div_lt_of_lt_mul h⟩
      ⟨v % n, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by subst h0; simp at h)⟩
  else
    let w := v - n * n
    if h₂ : w / k < n then decide ((G.coloring.cells[w / k]'h₂).val = w % k) else false

/-! ## Correctness of grounding -/

theorem bigOr_eval (a : Nat → Bool) (l : List PExpr) : (bigOr l).eval a = l.any (·.eval a) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [bigOr, PExpr.eval, ih]

theorem bigAnd_eval (a : Nat → Bool) (l : List PExpr) : (bigAnd l).eval a = l.all (·.eval a) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [bigAnd, PExpr.eval, ih]

theorem atLeastP_eval (a : Nat → Bool) :
    ∀ (m : Nat) (l : List PExpr), (atLeastP m l).eval a = decide (m ≤ l.countP (·.eval a))
  | 0, _ => by simp [atLeastP, PExpr.eval]
  | _ + 1, [] => by simp [atLeastP, PExpr.eval]
  | m + 1, x :: xs => by
    simp only [atLeastP, PExpr.eval, atLeastP_eval a (m + 1) xs, atLeastP_eval a m xs,
      List.countP_cons]
    cases x.eval a <;> simp <;> omega

theorem assignment_edge (G : Colored n k) (a b : Fin n) (hab : a ≠ b) :
    assignment G (edgeVar n a b) = G.graph.adj a b := by
  have key : ∀ x y : Fin n, assignment G (x.val * n + y.val) = G.graph.adj x y := by
    intro x y
    have hlt : x.val * n + y.val < n * n := by
      have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt x.isLt)
      rw [Nat.succ_mul] at this
      have := y.isLt
      rw [Nat.mul_comm n n]; omega
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
    have hd : (x.val * n + y.val) / n = x.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt y.isLt, Nat.zero_add]
    have hm : (x.val * n + y.val) % n = y.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt y.isLt]
    unfold assignment
    rw [dif_pos hlt]
    congr 1 <;> exact Fin.ext (by simp [hd, hm])
  unfold edgeVar
  split
  · exact key a b
  · rw [key b a, G.graph.adj_symm]

theorem assignment_color (G : Colored n k) (v : Fin n) (c : Nat) (hc : c < k) :
    assignment G (colorVar n k v c) = decide ((G.coloring.cells[v]).val = c) := by
  unfold assignment colorVar
  rw [dif_neg (by omega)]
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) hc
  have hw : n * n + v.val * k + c - n * n = v.val * k + c := by omega
  have hd : (v.val * k + c) / k = v.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hm : (v.val * k + c) % k = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  simp only [hw, hd, hm]
  rw [dif_pos v.isLt]
  rfl

/-- `asg` reads `G`'s edge and colour atoms. Encodings that add atoms of their own (the V4 slice's
action atoms) state their lemmas for any agreeing assignment. -/
structure Agrees (G : Colored n k) (asg : Nat → Bool) : Prop where
  edge : ∀ a b : Fin n, a ≠ b → asg (edgeVar n a b) = G.graph.adj a b
  color : ∀ (v : Fin n) (c : Nat), c < k → asg (colorVar n k v c) = decide ((G.coloring.cells[v]).val = c)

theorem agrees_assignment (G : Colored n k) : Agrees G (assignment G) :=
  ⟨assignment_edge G, assignment_color G⟩

/-- Grounding is faithful under any assignment that agrees with `G` on edges and colours and with `A`
on the action atoms. -/
theorem groundA_eval (G : Colored n k) (A : Act n) (actP : Nat → Fin n → Fin n → PExpr) (asg : Nat → Bool)
    (hE : ∀ a b : Fin n, a ≠ b → asg (edgeVar n a b) = G.graph.adj a b)
    (hC : ∀ (v : Fin n) (c : Nat), c < k → asg (colorVar n k v c) = decide ((G.coloring.cells[v]).val = c))
    (hA : ∀ g (a b : Fin n), (actP g a b).eval asg = decide (A g a = b)) :
    ∀ (φ : Formula) (env : List (Fin n)), (groundA n k actP env φ).eval asg = eval G A env φ := by
  intro φ
  induction φ with
  | tt => intro env; rfl
  | adj i j =>
    intro env
    simp only [groundA, eval]
    cases env[i]? <;> cases env[j]? <;> simp only [PExpr.eval]
    rename_i a b
    split
    · subst_vars; simp [PExpr.eval]
    · rename_i hab; simp [PExpr.eval, hE a b hab]
  | eq i j =>
    intro env
    simp only [groundA, eval]
    cases env[i]? <;> cases env[j]? <;> simp [PExpr.eval]
  | color i c =>
    intro env
    simp only [groundA, eval]
    cases env[i]? with
    | none => simp [PExpr.eval]
    | some a =>
      simp only
      split
      · rename_i hc; simp [PExpr.eval, hC a c hc]
      · rename_i hc
        simp only [PExpr.eval]
        have : (G.coloring.cells[a]).val ≠ c := fun h => hc (h ▸ (G.coloring.cells[a]).isLt)
        simpa [Fin.getElem_fin] using this
  | not φ ih => intro env; simp [groundA, eval, PExpr.eval, ih]
  | and φ ψ ih₁ ih₂ => intro env; simp [groundA, eval, PExpr.eval, ih₁, ih₂]
  | or φ ψ ih₁ ih₂ => intro env; simp [groundA, eval, PExpr.eval, ih₁, ih₂]
  | ex φ ih =>
    intro env
    simp only [groundA, eval, bigOr_eval, List.any_map]
    congr 1; funext v; exact ih (v :: env)
  | all φ ih =>
    intro env
    simp only [groundA, eval, bigAnd_eval, List.all_map]
    congr 1; funext v; exact ih (v :: env)
  | atLeast m φ ih =>
    intro env
    simp only [groundA, eval, atLeastP_eval, List.countP_map]
    congr 3; funext v; exact ih (v :: env)
  | act g i j =>
    intro env
    simp only [groundA, eval]
    cases env[i]? <;> cases env[j]? <;> simp [PExpr.eval, hA]

theorem ground_eval (G : Colored n k) (φ : Formula) (env : List (Fin n)) :
    (ground n k env φ).eval (assignment G) = eval G idAct env φ :=
  groundA_eval G idAct plainAct (assignment G) (assignment_edge G) (assignment_color G)
    (fun _ _ _ => by simp only [plainAct, PExpr.eval, idAct]; exact decide_eq_decide.mpr Iff.rfl) φ env

/-! ## Valid colourings -/

/-- At most one of the expressions holds. -/
def amo : List PExpr → PExpr
  | [] => .const true
  | x :: xs => .and (.not (.and x (bigOr xs))) (amo xs)

/-- Every vertex has exactly one colour below `k`. Without it a solver could leave a colour atom
unset and slip past a block; every object's own assignment satisfies it. -/
def colorValid (n k : Nat) : PExpr :=
  bigAnd ((List.finRange n).map fun v =>
    .and (bigOr ((List.range k).map fun c => .atom (colorVar n k v c)))
      (amo ((List.range k).map fun c => .atom (colorVar n k v c))))

theorem amo_eval (G : Colored n k) {asg : Nat → Bool} (hG : Agrees G asg) (v : Fin n) :
    ∀ l : List Nat, l.Nodup → (∀ c ∈ l, c < k) →
      (amo (l.map fun c => .atom (colorVar n k v c))).eval asg = true
  | [], _, _ => rfl
  | c :: cs, hnd, hlt => by
    simp only [List.map_cons, amo, PExpr.eval, bigOr_eval, List.any_map, Bool.and_eq_true,
      Bool.not_eq_true', Bool.and_eq_false_iff]
    refine ⟨?_, amo_eval G hG v cs (List.nodup_cons.mp hnd).2 fun c' h => hlt c' (List.mem_cons_of_mem _ h)⟩
    by_cases hc : (G.coloring.cells[v]).val = c
    · right
      rw [List.any_eq_false]
      intro c' hc'
      simp only [Function.comp, PExpr.eval, hG.color v c' (hlt c' (List.mem_cons_of_mem _ hc'))]
      intro h
      have : c' = c := by rw [← hc]; exact (of_decide_eq_true h).symm
      exact (List.nodup_cons.mp hnd).1 (this ▸ hc')
    · left
      simpa [hG.color v c (hlt c List.mem_cons_self), Fin.getElem_fin] using hc

theorem colorValid_eval (G : Colored n k) {asg : Nat → Bool} (hG : Agrees G asg) :
    (colorValid n k).eval asg = true := by
  simp only [colorValid, bigAnd_eval, List.all_map, List.all_eq_true]
  intro v _
  simp only [Function.comp, PExpr.eval, Bool.and_eq_true]
  refine ⟨?_, amo_eval G hG v _ List.nodup_range fun c h => List.mem_range.mp h⟩
  rw [bigOr_eval, List.any_map, List.any_eq_true]
  refine ⟨(G.coloring.cells[v]).val, List.mem_range.mpr (G.coloring.cells[v]).isLt, ?_⟩
  simp only [Function.comp, PExpr.eval]
  rw [hG.color v _ (G.coloring.cells[v]).isLt]
  simp

/-! ## The CNF and model expansion -/

/-- The CNF for "some coloured graph on `n` vertices with `k` colours satisfies `φ`". -/
def cnf (n k : Nat) (φ : Formula) : Std.Sat.CNF Nat := (PExpr.and (colorValid n k) (ground n k [] φ)).toCNF

/-- Model expansion, carried back: an unsatisfiable `cnf` proves that no object satisfies `φ`. -/
theorem none_of_unsat {φ : Formula} (h : (cnf n k φ).Unsat) : ∀ G : Colored n k, ¬ Sat G φ := by
  intro G hG
  have hf := PExpr.eval_false_of_unsat h (assignment G)
  simp only [PExpr.eval, colorValid_eval G (agrees_assignment G), ground_eval, Bool.true_and] at hf
  unfold Sat at hG
  rw [hG] at hf
  exact Bool.noConfusion hf

end GPCensus
