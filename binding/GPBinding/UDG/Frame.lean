import GPBinding.UDG.System
import GPBinding.UDG.Spine
import GPBinding.Matroid.Eval
import GPProfile.UDG

/-!
ENCODING-FRAME for unit-distance graph claims (HW61 G-1, G-2). `GPProfile.UDG.Data.system` is the
Lean encoder that `tools/encode-udg.py` mirrors. `udg_frame_iff`: its system has a real point
exactly when the graph has an injective unit-distance embedding into `EuclideanSpace ℝ (Fin 2)`
(Mathlib's `SimpleGraph.UnitDistEmbedding`), with or without the gauge.

Each encoder polynomial reads back exactly through its sparse form (`readBack`, checked by the
encoder), so its explicit value at a point is the Hex polynomial's value (`Matroid.valueE_det`);
the edge and guard values are squared distances of the point's coordinate pairs. Then
`udg_system_iff` and `udg_gauge_iff` (Mathlib only) finish.

`candidate_isEmpty` is the glue a spine cites per candidate: a held EMPTY claim over ℝ on the
encoder's system gives the `IsEmpty` hypothesis of `spine_sound`. `udg_realize` is the yes
bridge's glue: a held NONEMPTY claim over ℝ on the encoder's system of a graph with at least `m`
edges gives `n` points with at least `m` unit pairs (`realize_sound`).
-/

noncomputable section

namespace GPBinding.UDG
open GPProfile GPProfile.UDG GPBinding.Binder GPBinding.Admission MvPolynomial HexMvPolyMathlib UDGRope

/-- The graph a `Data` names: distinct vertices joined by a listed edge in either orientation. -/
def _root_.GPProfile.UDG.Data.graph (D : Data) : SimpleGraph (Fin D.n) where
  Adj i j := i ≠ j ∧ D.adj i j = true
  symm := ⟨fun i j h => ⟨h.1.symm, by
    have := h.2; simp only [Data.adj, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq] at this ⊢
    obtain ⟨e, he, h'⟩ := this; exact ⟨e, he, h'.symm⟩⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

theorem mem_pairs {n i j : ℕ} : (i, j) ∈ pairs n ↔ i < j ∧ j < n := by
  simp only [pairs, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨i', -, j', ⟨hj, hij⟩, rfl, rfl⟩; exact ⟨hij, hj⟩
  · rintro ⟨hij, hj⟩; exact ⟨i, by omega, j, ⟨hj, hij⟩, rfl, rfl⟩

theorem mem_edgeList {D : Data} {i j : ℕ} : (i, j) ∈ D.edgeList ↔ i < j ∧ j < D.n ∧ D.adj i j = true := by
  simp only [Data.edgeList, List.mem_filter, mem_pairs, and_assoc]

theorem vars_length (D : Data) : D.vars.length = 2 * D.n := by
  simp only [Data.vars, List.length_flatMap, List.length_cons, List.length_nil]
  induction D.n with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp; ring

/-! ## Values of the encoder's polynomials -/

/-- Coordinate `k` of a point, `0` beyond the arity (the value of `varP`). -/
def coord {m : ℕ} (x : Fin m → ℝ) (k : ℕ) : ℝ := if h : k < m then x ⟨k, h⟩ else 0

/-- A Hex polynomial's value at a real point. -/
def E {m : ℕ} (x : Fin m → ℝ) (d : GPProfile.P m Rat) : ℝ :=
  eval₂ (Rat.castHom ℝ) x (toMvPolynomial d)

theorem toK_real {σ : Type*} (P : MvPolynomial σ ℚ) : toK (K := ℝ) P = MvPolynomial.map (Rat.castHom ℝ) P := by
  ext d; simp [coeff_map]

theorem E_varP {m : ℕ} (x : Fin m → ℝ) (k : ℕ) : E x (varP m k) = coord x k := by
  unfold E varP coord
  split <;> simp

theorem E_sqDist {m : ℕ} (x : Fin m → ℝ) (i j : ℕ) :
    E x (sqDist m i j) = (coord x (2 * i) - coord x (2 * j)) ^ 2 +
      (coord x (2 * i + 1) - coord x (2 * j + 1)) ^ 2 := by
  have h := E_varP x
  simp only [E] at h ⊢
  simp only [sqDist, toMvPolynomial_add, toMvPolynomial_sub, toMvPolynomial_mul, eval₂_add, eval₂_sub,
    eval₂_mul, h]
  ring

theorem E_sub_one {m : ℕ} (x : Fin m → ℝ) (d : GPProfile.P m Rat) : E x (d - 1) = E x d - 1 := by
  simp [E, toMvPolynomial_sub, toMvPolynomial_one]

theorem valueE_readBack {m : ℕ} {d : GPProfile.P m Rat} (h : readBack d = true) (x : Fin m → ℝ) :
    valueE ℝ m (ofHex d) x = E x d := by
  simp only [readBack, Bool.and_eq_true, beq_iff_eq] at h
  rw [GPBinding.Matroid.valueE_det d h.1 h.2, toK_real, eval_map]
  rfl

/-! ## Points and coordinate pairs -/

/-- The x and y coordinates of the vertices. -/
def X {m : ℕ} (n : ℕ) (x : Fin m → ℝ) : Fin n → ℝ := fun i => coord x (2 * i.val)
def Y {m : ℕ} (n : ℕ) (x : Fin m → ℝ) : Fin n → ℝ := fun i => coord x (2 * i.val + 1)

/-- The point with coordinate pairs `(a i, b i)`. -/
def ofPairs {n : ℕ} (a b : Fin n → ℝ) (m : ℕ) (hm : m = 2 * n) : Fin m → ℝ := fun k =>
  if k.val % 2 = 0 then a ⟨k.val / 2, by omega⟩ else b ⟨k.val / 2, by omega⟩

theorem X_ofPairs {n m : ℕ} (a b : Fin n → ℝ) (hm : m = 2 * n) : X n (ofPairs a b m hm) = a := by
  funext i
  have h1 : 2 * i.val < m := by omega
  have h2 : 2 * i.val % 2 = 0 := by omega
  simp only [X, coord, ofPairs, h1, h2, dite_true, ite_true]
  congr 1; ext; simp

theorem Y_ofPairs {n m : ℕ} (a b : Fin n → ℝ) (hm : m = 2 * n) : Y n (ofPairs a b m hm) = b := by
  funext i
  have h1 : 2 * i.val + 1 < m := by omega
  have h2 : ¬ (2 * i.val + 1) % 2 = 0 := by omega
  simp only [Y, coord, ofPairs, h1, h2, dite_true, ite_false]
  congr 1; ext; simp; omega

/-- The encoder's edges and guards hold at `x` exactly when its coordinate pairs are a point of
the unit-distance system of `D.graph`. -/
theorem edges_guards_iff (D : Data) {m : ℕ} (x : Fin m → ℝ) :
    ((∀ e ∈ D.edgeList, E x (sqDist m e.1 e.2) - 1 = 0) ∧
      ∀ e ∈ pairs D.n, E x (sqDist m e.1 e.2) ≠ 0) ↔ SysPoint D.graph (X D.n x) (Y D.n x) := by
  simp only [E_sqDist, SysPoint, X, Y]
  constructor
  · rintro ⟨he, hg⟩
    refine ⟨fun i j hij => ?_, fun i j hij => hg (i, j) (mem_pairs.mpr ⟨hij, j.2⟩)⟩
    rcases lt_or_gt_of_ne hij.1 with h | h
    · exact he (i, j) (mem_edgeList.mpr ⟨h, j.2, hij.2⟩)
    · have := he (j, i) (mem_edgeList.mpr ⟨h, i.2, hij.symm.2⟩)
      linear_combination this
  · rintro ⟨he, hg⟩
    refine ⟨fun e hmem => ?_, fun e hmem => ?_⟩
    · obtain ⟨i, j⟩ := e
      obtain ⟨hij, hj, hadj⟩ := mem_edgeList.mp hmem
      exact he ⟨i, by omega⟩ ⟨j, hj⟩ ⟨fun h => by simp [Fin.ext_iff] at h; omega, hadj⟩
    · obtain ⟨i, j⟩ := e
      obtain ⟨hij, hj⟩ := mem_pairs.mp hmem
      exact hg ⟨i, by omega⟩ ⟨j, hj⟩ hij

/-- The gauge's conditions on coordinate pairs: none, or the gauged edge pinned. -/
def GaugeOK (D : Data) (a b : Fin D.n → ℝ) : Prop :=
  match D.gaugeEdge with
  | some (i, j) => coordOf a i = 0 ∧ coordOf b i = 0 ∧ coordOf a j = 1 ∧ coordOf b j = 0
  | none => True
where coordOf (c : Fin D.n → ℝ) (k : ℕ) : ℝ := if h : k < D.n then c ⟨k, h⟩ else 0

theorem gaugeEdge_mem {D : Data} {i j : ℕ} (h : D.gaugeEdge = some (i, j)) : (i, j) ∈ D.edgeList := by
  unfold Data.gaugeEdge at h
  split at h
  · exact List.mem_of_mem_head? h
  · simp at h

theorem gauge_iff (D : Data) {m : ℕ} (x : Fin m → ℝ) :
    (∀ d ∈ D.gaugeEqs m, E x d = 0) ↔ GaugeOK D (X D.n x) (Y D.n x) := by
  unfold Data.gaugeEqs GaugeOK
  cases hge : D.gaugeEdge with
  | none => simp
  | some ij =>
    obtain ⟨i, j⟩ := ij
    obtain ⟨hij, hj, -⟩ := mem_edgeList.mp (gaugeEdge_mem hge)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, E_varP,
      E_sub_one, GaugeOK.coordOf, X, Y, hj, (show i < D.n by omega), dite_true, sub_eq_zero]

/-- The encoder's system holds at `x` exactly when the gauge and the unit-distance system hold
at its coordinate pairs. -/
theorem locus_iff (D : Data) {vars : List String} {eqs guards : List Sparse}
    (h : D.system = some (vars, eqs, guards)) (x : Fin vars.length → ℝ) :
    LocusE ℝ ⟨vars, eqs, guards, .nonempty⟩ x ↔
      GaugeOK D (X D.n x) (Y D.n x) ∧ SysPoint D.graph (X D.n x) (Y D.n x) := by
  dsimp only [Data.system] at h
  split at h
  · rename_i hok
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hrb : ∀ d ∈ D.eqPolys D.vars.length ++ D.guardPolys D.vars.length, readBack d = true :=
      fun d hd => List.all_eq_true.mp hok d hd
    rw [← edges_guards_iff, ← gauge_iff D]
    simp only [LocusE, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    have hv : ∀ d ∈ D.eqPolys D.vars.length ++ D.guardPolys D.vars.length,
        valueE ℝ D.vars.length (ofHex d) x = E x d := fun d hd => valueE_readBack (hrb d hd) x
    simp only [List.mem_append] at hv
    constructor
    · rintro ⟨he, hg⟩
      refine ⟨fun d hd => ?_, fun e hmem => ?_, fun e hmem => ?_⟩
      · have := he d (List.mem_append_left _ hd); rwa [hv d (Or.inl (List.mem_append_left _ hd))] at this
      · have hd : sqDist D.vars.length e.1 e.2 - 1 ∈ D.eqPolys D.vars.length :=
          List.mem_append_right _ (List.mem_map.mpr ⟨e, hmem, rfl⟩)
        have := he _ hd; rwa [hv _ (Or.inl hd), E_sub_one] at this
      · have hd : sqDist D.vars.length e.1 e.2 ∈ D.guardPolys D.vars.length := List.mem_map.mpr ⟨e, hmem, rfl⟩
        have := hg _ hd; rwa [hv _ (Or.inr hd)] at this
    · rintro ⟨hgauge, he, hg⟩
      refine ⟨fun d hd => ?_, fun d hd => ?_⟩
      · rw [hv d (Or.inl hd)]
        rcases List.mem_append.mp hd with hd | hd
        · exact hgauge d hd
        · obtain ⟨e, hmem, rfl⟩ := List.mem_map.mp hd
          rw [E_sub_one]; exact he e hmem
      · rw [hv d (Or.inr hd)]
        obtain ⟨e, hmem, rfl⟩ := List.mem_map.mp hd
        exact hg e hmem
  · simp at h

theorem gaugeOK_free (D : Data) :
    (∃ a b, SysPoint D.graph a b ∧ GaugeOK D a b) ↔ ∃ a b, SysPoint D.graph a b := by
  unfold GaugeOK
  cases hge : D.gaugeEdge with
  | none => simp
  | some ij =>
    obtain ⟨i, j⟩ := ij
    obtain ⟨hij, hj, hadj⟩ := mem_edgeList.mp (gaugeEdge_mem hge)
    have hadj' : D.graph.Adj ⟨i, by omega⟩ ⟨j, hj⟩ :=
      ⟨fun h => by simp [Fin.ext_iff] at h; omega, hadj⟩
    rw [udg_gauge_iff D.graph hadj']
    simp only [GaugeOK.coordOf, hj, (show i < D.n by omega), dite_true]

/-- **ENCODING-FRAME for unit-distance graphs.** The Lean encoder's system for `D` has a real
point exactly when `D.graph` has an injective unit-distance embedding into the Euclidean plane. -/
theorem udg_frame_iff (D : Data) {vars : List String} {eqs guards : List Sparse}
    (h : D.system = some (vars, eqs, guards)) :
    (∃ x, LocusE ℝ ⟨vars, eqs, guards, .nonempty⟩ x) ↔
      Nonempty (D.graph.UnitDistEmbedding (EuclideanSpace ℝ (Fin 2))) := by
  have hm : vars.length = 2 * D.n := by
    dsimp only [Data.system] at h; split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1, vars_length]
    · simp at h
  have hs : (∃ a b, SysPoint D.graph a b) ↔ Nonempty (D.graph.UnitDistEmbedding ℝ²) := udg_system_iff D.graph
  rw [← hs, ← gaugeOK_free]
  simp only [locus_iff D h]
  constructor
  · rintro ⟨x, hg, hs⟩; exact ⟨_, _, hs, hg⟩
  · rintro ⟨a, b, hs, hg⟩
    refine ⟨ofPairs a b _ hm, ?_⟩
    rw [X_ofPairs, Y_ofPairs]; exact ⟨hg, hs⟩

/-- NONEMPTY over ℝ of the encoder's system is embeddability; EMPTY is non-embeddability. -/
theorem holdsE_nonempty_iff (D : Data) {vars : List String} {eqs guards : List Sparse}
    (h : D.system = some (vars, eqs, guards)) :
    HoldsE ℝ ⟨vars, eqs, guards, .nonempty⟩ ↔ Nonempty (D.graph.UnitDistEmbedding ℝ²) :=
  udg_frame_iff D h

theorem holdsE_empty_iff (D : Data) {vars : List String} {eqs guards : List Sparse}
    (h : D.system = some (vars, eqs, guards)) :
    HoldsE ℝ ⟨vars, eqs, guards, .empty⟩ ↔ IsEmpty (D.graph.UnitDistEmbedding ℝ²) := by
  rw [← not_nonempty_iff, ← udg_frame_iff D h, not_exists]
  exact Iff.rfl

/-- The same for the Admission meaning `Holds` that 3b `orderFree` claims use: over ℝ every
rational coefficient is good, and every encoder polynomial has the system's arity. -/
theorem holds_iff_holdsE_udg (D : Data) {vars : List String} {eqs guards : List Sparse}
    (h : D.system = some (vars, eqs, guards)) (k : Kind) (hk : k = .empty ∨ k = .nonempty) :
    Holds ℝ ⟨vars, eqs, guards, k⟩ ↔ HoldsE ℝ ⟨vars, eqs, guards, k⟩ := by
  apply holds_iff_holdsE
  · dsimp only [Data.system] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rcases hk with rfl | rfl <;>
      · simp only [stmtArityOk, Stmt.polys, Kind.target?, Kind.branchPolys, Option.toList_none,
          List.append_nil, List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true,
          Function.comp_apply]
        exact ⟨fun d _ => GPBinding.Matroid.arityOk_ofHex d, fun d _ => GPBinding.Matroid.arityOk_ofHex d⟩
    · simp at h
  · intro p _ c _
    show ((c.den : ℕ) : ℝ) ≠ 0
    exact Nat.cast_ne_zero.mpr c.den_nz

/-- **Glue for `spine_sound`.** A candidate whose encoded system is EMPTY over ℝ has no
unit-distance embedding. -/
theorem candidate_isEmpty (D : Data) {vars : List String} {eqs guards : List Sparse}
    (h : D.system = some (vars, eqs, guards)) (hE : HoldsE ℝ ⟨vars, eqs, guards, .empty⟩) :
    IsEmpty (D.graph.UnitDistEmbedding ℝ²) :=
  (holdsE_empty_iff D h).mp hE

open scoped Finset in
/-- **Glue for the yes bridge.** A real point of the encoder's system for a graph with at least
`m` edges gives `D.n` points with at least `m` unit pairs (`udg_frame_iff`, `realize_sound`). -/
theorem udg_realize (D : Data) {vars : List String} {eqs guards : List Sparse}
    (h : D.system = some (vars, eqs, guards)) (hN : HoldsE ℝ ⟨vars, eqs, guards, .nonempty⟩)
    {m : ℕ} [DecidableRel D.graph.Adj] (hm : m ≤ #D.graph.edgeFinset) :
    ∃ P : Finset ℝ², P.card = D.n ∧ m ≤ unitDistNum P :=
  realize_sound D.graph ((holdsE_nonempty_iff D h).mp hN) hm

end GPBinding.UDG
