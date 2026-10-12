import GPCensus.Encode

/-!
EXHAUSTIVE and COUNT by listing (M4 §1, rank 3): block-and-refute with a lex-leader symmetry break.

An object's atom vector lists its adjacency bits (pairs `a < b`) and colour bits in a fixed order.
For any set of relabellings `ls`, the symmetry break asks that the vector be lexicographically no
greater than its relabelling by each `l ∈ ls`. The relabelling with the least vector meets every
such constraint (`orbit_min`), whatever `ls` is, so the break is sound for existence without any
argument about which symmetries were chosen. A poor choice only makes the refutation harder to find.

`listed_of_unsat`: if "satisfies `φ`, meets the break, and equals none of the listed objects" is
unsatisfiable, every satisfying object is isomorphic to a listed one. COUNT adds pairwise-distinct
HexGraphIso canonical forms (`iso_iff_canon_eq`). No count of models is ever used, so the trap
"symmetry-broken model count read as an isomorphism-class count" has no path to a held claim.
-/

namespace GPCensus
open Hex Hex.GraphIso

variable {n k : Nat}

inductive Atom (n : Nat) where
  | edge (a b : Fin n)
  | col (v : Fin n) (c : Nat)

/-- The atoms of objects on `n` vertices with `k` colours, in a fixed order. -/
def atoms (n k : Nat) : List (Atom n) :=
  ((List.finRange n).flatMap fun a => ((List.finRange n).filter fun b => decide (a < b)).map (.edge a ·)) ++
    ((List.finRange n).flatMap fun v => (List.range k).map (.col v ·))

def Atom.val (G : Colored n k) : Atom n → Bool
  | .edge a b => G.graph.adj a b
  | .col v c => decide ((G.coloring.cells[v]).val = c)

def Atom.expr (k : Nat) : Atom n → PExpr
  | .edge a b => if a = b then .const false else .atom (edgeVar n a b)
  | .col v c => if c < k then .atom (colorVar n k v c) else .const false

def Atom.map (l : Label n) : Atom n → Atom n
  | .edge a b => .edge (l.get a) (l.get b)
  | .col v c => .col (l.get v) c

theorem Atom.expr_eval (G : Colored n k) {asg : Nat → Bool} (hG : Agrees G asg) (x : Atom n) :
    (x.expr k).eval asg = x.val G := by
  cases x with
  | edge a b =>
    simp only [Atom.expr, Atom.val]
    split
    · subst_vars; simp [PExpr.eval]
    · rename_i hab; simp [PExpr.eval, hG.edge a b hab]
  | col v c =>
    simp only [Atom.expr, Atom.val]
    split
    · rename_i hc; simp [PExpr.eval, hG.color v c hc]
    · rename_i hc
      have : (G.coloring.cells[v]).val ≠ c := fun h => hc (h ▸ (G.coloring.cells[v]).isLt)
      simpa [PExpr.eval, Fin.getElem_fin] using this

theorem Atom.val_relabel (G : Colored n k) (l : Label n) (x : Atom n) :
    x.val (G.relabel l) = (x.map l).val G := by
  cases x <;> simp [Atom.val, Atom.map, Fin.getElem_fin]

/-- The atom vector of an object. -/
def vec (G : Colored n k) : List Bool := (atoms n k).map (Atom.val G)

theorem vec_relabel (G : Colored n k) (l : Label n) :
    vec (G.relabel l) = (atoms n k).map fun x => (x.map l).val G := by
  simp only [vec]
  apply List.map_congr_left
  intro x _
  exact Atom.val_relabel G l x

/-! ## Lexicographic order and its numeric key -/

def lexLeB : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => true
  | x :: xs, y :: ys => (!x && y) || (x == y && lexLeB xs ys)

/-- Big-endian binary value of a bit vector. -/
def key : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 2 ^ bs.length else 0) + key bs

theorem key_lt : ∀ bs : List Bool, key bs < 2 ^ bs.length
  | [] => by simp [key]
  | b :: bs => by
    have := key_lt bs
    cases b <;> simp [key, Nat.pow_succ] <;> omega

theorem lexLeB_iff : ∀ (xs ys : List Bool), xs.length = ys.length →
    (lexLeB xs ys = true ↔ key xs ≤ key ys)
  | [], [], _ => by simp [lexLeB, key]
  | x :: xs, y :: ys, h => by
    have hl : xs.length = ys.length := by simpa using h
    have ih := lexLeB_iff xs ys hl
    have h1 := key_lt xs
    have h2 := key_lt ys
    rw [hl] at h1
    cases x <;> cases y <;> simp [lexLeB, key, hl, ih] <;> omega

def lexLeP : List PExpr → List PExpr → PExpr
  | [], _ => .const true
  | _ :: _, [] => .const true
  | x :: xs, y :: ys =>
    .or (.and (.not x) y) (.and (.or (.and x y) (.and (.not x) (.not y))) (lexLeP xs ys))

theorem lexLeP_eval (a : Nat → Bool) : ∀ xs ys : List PExpr,
    (lexLeP xs ys).eval a = lexLeB (xs.map (·.eval a)) (ys.map (·.eval a))
  | [], _ => by simp [lexLeP, lexLeB, PExpr.eval]
  | _ :: _, [] => by simp [lexLeP, lexLeB, PExpr.eval]
  | x :: xs, y :: ys => by
    simp only [lexLeP, PExpr.eval, List.map_cons, lexLeB, lexLeP_eval a xs ys]
    cases x.eval a <;> cases y.eval a <;> simp

/-! ## The symmetry break and the blocks -/

def symBreak (n k : Nat) (ls : List (Label n)) : PExpr :=
  bigAnd (ls.map fun l => lexLeP ((atoms n k).map (·.expr k)) ((atoms n k).map fun x => (x.map l).expr k))

theorem symBreak_eval (G : Colored n k) {asg : Nat → Bool} (hG : Agrees G asg) (ls : List (Label n)) :
    (symBreak n k ls).eval asg = ls.all fun l => lexLeB (vec G) (vec (G.relabel l)) := by
  simp only [symBreak, bigAnd_eval, List.all_map]
  congr 1
  funext l
  simp only [Function.comp, lexLeP_eval, List.map_map, vec_relabel, vec]
  congr 1 <;> (apply List.map_congr_left; intro x _; simp [Atom.expr_eval G hG, Atom.val_relabel])

/-- "The object is exactly `B`", over the atoms. -/
def eqP (n k : Nat) (B : Colored n k) : PExpr :=
  bigAnd ((atoms n k).map fun x => if x.val B then x.expr k else .not (x.expr k))

theorem eqP_eval (G B : Colored n k) {asg : Nat → Bool} (hG : Agrees G asg) :
    (eqP n k B).eval asg = (atoms n k).all fun x => x.val G == x.val B := by
  simp only [eqP, bigAnd_eval, List.all_map]
  congr 1
  funext x
  simp only [Function.comp]
  split <;> simp_all [PExpr.eval, Atom.expr_eval G hG]

theorem mem_atoms_edge {a b : Fin n} (h : a < b) : Atom.edge a b ∈ atoms n k := by
  simp only [atoms, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_finRange, true_and, decide_eq_true_eq]
  exact Or.inl ⟨a, b, h, rfl⟩

theorem mem_atoms_col (v : Fin n) {c : Nat} (h : c < k) : Atom.col v c ∈ atoms n k := by
  simp only [atoms, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_finRange, true_and]
  exact Or.inr ⟨v, c, h, rfl⟩

/-- The atoms determine the object. -/
theorem eq_of_atoms {G B : Colored n k} (h : ∀ x ∈ atoms n k, x.val G = x.val B) : G = B := by
  apply Colored.ext
  · intro i j
    rcases Nat.lt_trichotomy i.val j.val with hij | hij | hij
    · exact h _ (mem_atoms_edge (Fin.lt_def.mpr hij))
    · have : i = j := Fin.ext hij
      subst this
      simp
    · rw [G.graph.adj_symm, B.graph.adj_symm]
      exact h _ (mem_atoms_edge (Fin.lt_def.mpr hij))
  · intro i
    have hb := h _ (mem_atoms_col i (B.coloring.cells[i]).isLt)
    simp only [Atom.val, decide_true, decide_eq_true_eq] at hb
    exact Fin.ext hb

/-! ## The least relabelling meets every lex constraint -/

theorem orbit_min (G : Colored n k) :
    ∃ l₀ : Label n, ∀ l : Label n, key (vec (G.relabel l₀)) ≤ key (vec (G.relabel l)) := by
  suffices ∀ c, ∀ l : Label n, key (vec (G.relabel l)) = c →
      ∃ l₀ : Label n, ∀ l', key (vec (G.relabel l₀)) ≤ key (vec (G.relabel l')) from
    this _ (Label.id n) rfl
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro l hl
    by_cases hmin : ∀ l', key (vec (G.relabel l)) ≤ key (vec (G.relabel l'))
    · exact ⟨l, hmin⟩
    · obtain ⟨l', hl'⟩ := Classical.not_forall.mp hmin
      exact ih _ (by omega) l' rfl

theorem vec_length (G : Colored n k) : (vec G).length = (atoms n k).length := by simp [vec]

/-! ## The listing CNF and its theorem -/

def listCnf (n k : Nat) (φ : Formula) (ls : List (Label n)) (Bs : List (Colored n k)) : Std.Sat.CNF Nat :=
  (bigAnd ([colorValid n k, ground n k [] φ, symBreak n k ls] ++ Bs.map fun B => .not (eqP n k B))).toCNF

theorem listed_of_unsat {φ : Formula} {ls : List (Label n)} {Bs : List (Colored n k)}
    (h : (listCnf n k φ ls Bs).Unsat) : ∀ G : Colored n k, Sat G φ → ∃ B ∈ Bs, Isomorphic G B := by
  intro G hG
  obtain ⟨l₀, hmin⟩ := orbit_min G
  let H := G.relabel l₀
  have hiso : Isomorphic G H := isomorphic_relabel G l₀
  have hH : Sat H φ := (sat_iff_of_isomorphic hiso φ).mp hG
  have hbreak : (symBreak n k ls).eval (assignment H) = true := by
    rw [symBreak_eval H (agrees_assignment H), List.all_eq_true]
    intro l _
    rw [lexLeB_iff _ _ (by simp [vec_length])]
    have := hmin (l₀.comp l)
    rwa [← Colored.relabel_relabel] at this
  have hg : (ground n k [] φ).eval (assignment H) = true := by rw [ground_eval]; exact hH
  have hf := PExpr.eval_false_of_unsat h (assignment H)
  simp only [bigAnd_eval, List.all_append, List.all_cons, List.all_nil, List.all_map, Bool.and_true,
    colorValid_eval H (agrees_assignment H), hg, hbreak, Bool.true_and] at hf
  rw [List.all_eq_false] at hf
  obtain ⟨B, hB, hne⟩ := hf
  simp only [Function.comp, PExpr.eval, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at hne
  simp only [eqP_eval H _ (agrees_assignment H), List.all_eq_true, beq_iff_eq] at hne
  have : H = B := eq_of_atoms hne
  exact ⟨B, hB, this ▸ hiso⟩

/-- Pairwise-distinct canonical forms make a list pairwise non-isomorphic. -/
theorem pairwise_noniso_of_canon {Bs : List (Colored n k)} (h : (Bs.map canon).Nodup) :
    Bs.Pairwise fun a b => ¬ Isomorphic a b := by
  have := List.Pairwise.of_map canon (fun a b (hab : canon a ≠ canon b) => hab) h
  exact this.imp fun hne hiso => hne ((iso_iff_canon_eq _ _).mp hiso)

end GPCensus
