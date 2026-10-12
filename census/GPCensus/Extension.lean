import GPCensus.Formula
import GPCensus.ExtensionCheck

/-!
Extension covers (HW61 G-5): "every one-vertex extension of a pinned base graph contains a listed
pattern". A census NONE statement in the existing vocabulary, held by a receipt whose list of
extensions is generated in Lean, so no generator is trusted.

**Statement.** `extPred n t k pats` holds of a graph on `n + 1` vertices when some labelling
`z 0, …, z n` of its vertices (`exs`, all distinct) has
- `z i ~ z j` exactly when the base adjacency `t` says so, for `i ≠ j < n` (an induced copy of the
  base on `z 0..z (n-1)`);
- the vertex `z n` of degree exactly `k`; and
- no pattern of `pats`: for each pattern no injective map of its vertices sends every pattern edge
  to an edge and every required non-edge to a non-edge (`patFormula`).

NONE of it on `n + 1` vertices says: every graph that is the base plus one vertex of degree `k`
contains some pattern (as a subgraph, with the required non-edges absent). Patterns with no
required non-edges are plain subgraph patterns (L1 heredity needs only that); TU gadgets carry their
distinguished pair as a required non-edge.

**Receipt.** The generator `combos` and the per-hit checker `hitsOk` live in `ExtensionCheck`
(plain `Nat` lists, no Hex types, kernel-evaluable). `extOk` adds the statement comparison, and
`extCover_sound` carries an accepted receipt to NONE.
-/

namespace GPCensus.Extension
open Hex Hex.GraphIso GPCensus

/-! ## Statement vocabulary -/

/-- The conjunction of a list of formulas. -/
def conj : List Formula → Formula
  | [] => .tt
  | φ :: φs => .and φ (conj φs)

/-- `m` existential quantifiers: `ys[i]` is variable `i` inside. -/
def exs : Nat → Formula → Formula
  | 0, φ => φ
  | m + 1, φ => exs m (.ex φ)

/-- The ordered pairs of distinct indices below `m`. -/
def offDiag (m : Nat) : List (Nat × Nat) :=
  (List.range m).flatMap fun i => ((List.range m).filter (· != i)).map (i, ·)

/-- "The graph contains this pattern": distinct vertices, edges to edges, required non-edges to
non-edges. -/
def patFormula (P : Pattern) : Formula :=
  exs P.size (conj ((offDiag P.size).map (fun e => .not (.eq e.1 e.2)) ++
    P.edges.map (fun e => .adj e.1 e.2) ++ P.nonEdges.map (fun e => .not (.adj e.1 e.2))))

/-- The census predicate of an extension cover: see the module comment. -/
def extPred (n : Nat) (t : Array Nat) (k : Nat) (pats : List Pattern) : Formula :=
  exs (n + 1) (conj ((offDiag (n + 1)).map (fun e => .not (.eq e.1 e.2)) ++
    (offDiag n).map (fun e => if baseAdj t e.1 e.2 then .adj e.1 e.2 else .not (.adj e.1 e.2)) ++
    [.atLeast k (.adj (n + 1) 0), .not (.atLeast (k + 1) (.adj (n + 1) 0))] ++
    pats.map (fun P => .not (patFormula P))))

/-- The whole check: the statement is the extension predicate of this base, degree and pattern list,
and every neighbourhood the generator lists has a valid hit. -/
def extOk (n k : Nat) (E : List (Nat × Nat)) (pats : List Pattern) (hits : List Hit) (φ : Formula) : Bool :=
  let t := table n E
  decide (φ = extPred n t k pats) && hitsOk t n pats (combos n k) hits

/-! ## Soundness -/

section Soundness
variable {N c : Nat}

theorem eval_conj (G : Colored N c) (A : Act N) (env : List (Fin N)) :
    ∀ l : List Formula, eval G A env (conj l) = true ↔ ∀ φ ∈ l, eval G A env φ = true
  | [] => by simp [conj, eval]
  | φ :: φs => by simp [conj, eval, eval_conj G A env φs]

theorem eval_exs (G : Colored N c) (A : Act N) : ∀ (m : Nat) (φ : Formula) (env : List (Fin N)),
    eval G A env (exs m φ) = true ↔ ∃ ys : List (Fin N), ys.length = m ∧ eval G A (ys ++ env) φ = true
  | 0, φ, env => by simp [exs]
  | m + 1, φ, env => by
    rw [exs, eval_exs G A m (.ex φ) env]
    constructor
    · intro ⟨ys, hl, he⟩
      simp only [eval, List.any_eq_true] at he
      obtain ⟨v, -, hv⟩ := he
      exact ⟨v :: ys, by simp [hl], hv⟩
    · intro ⟨ys, hl, he⟩
      match ys, hl with
      | v :: ys, hl =>
        refine ⟨ys, by simpa using hl, ?_⟩
        simp only [eval, List.any_eq_true]
        exact ⟨v, List.mem_finRange v, he⟩

theorem mem_offDiag {m : Nat} {e : Nat × Nat} : e ∈ offDiag m ↔ e.1 < m ∧ e.2 < m ∧ e.1 ≠ e.2 := by
  obtain ⟨i, j⟩ := e
  simp only [offDiag, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range, bne_iff_ne,
    ne_eq, Prod.mk.injEq]
  constructor
  · intro ⟨a, ha, b, ⟨hb, hba⟩, hai, hbj⟩
    subst hai hbj
    exact ⟨ha, hb, fun h => hba h.symm⟩
  · intro ⟨hi, hj, hij⟩
    exact ⟨i, hi, j, ⟨hj, fun h => hij h.symm⟩, rfl, rfl⟩

theorem getElem?_of_lt {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) :
    l[i]? = some (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- An accepted extension cover: no graph on `n + 1` vertices satisfies the extension predicate, so
every one-vertex extension of the base by a degree-`k` vertex contains some pattern. -/
theorem extCover_sound {n k : Nat} {t : Array Nat} {pats : List Pattern} {hits : List Hit}
    (hok : hitsOk t n pats (combos n k) hits = true) (G : Colored (n + 1) c) :
    ¬ Sat G (extPred n t k pats) := by
  intro hsat
  obtain ⟨zs, hlen, hbody⟩ := (eval_exs G idAct (n + 1) _ []).mp hsat
  rw [List.append_nil, eval_conj] at hbody
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hbody
  let z : Nat → Fin (n + 1) := fun i => zs.getD i ⟨0, Nat.succ_pos n⟩
  have hz : ∀ i, i < n + 1 → zs[i]? = some (z i) := fun i hi => getElem?_of_lt _ (by omega)
  -- the labelling is injective
  have hdist : ∀ i j, i < n + 1 → j < n + 1 → i ≠ j → z i ≠ z j := by
    intro i j hi hj hij
    have := hbody _ (.inl (.inl (.inl ⟨(i, j), mem_offDiag.mpr ⟨hi, hj, hij⟩, rfl⟩)))
    simpa [eval, hz i hi, hz j hj] using this
  -- the base is induced on z 0..z (n-1)
  have hbase : ∀ i j, i < n → j < n → i ≠ j → G.graph.adj (z i) (z j) = baseAdj t i j := by
    intro i j hi hj hij
    have := hbody _ (.inl (.inl (.inr ⟨(i, j), mem_offDiag.mpr ⟨hi, hj, hij⟩, rfl⟩)))
    have hzi := hz i (Nat.lt_succ_of_lt hi)
    have hzj := hz j (Nat.lt_succ_of_lt hj)
    cases hb : baseAdj t i j <;> simp_all [eval]
  -- z n has degree k
  have hnew : ∀ v : Fin (n + 1), eval G idAct (v :: zs) (.adj (n + 1) 0) = G.graph.adj (z n) v := by
    intro v
    simp [eval, hz n (Nat.lt_succ_self n)]
  have hc : ∀ m, eval G idAct zs (.atLeast m (.adj (n + 1) 0)) =
      decide (m ≤ (List.finRange (n + 1)).countP fun u => G.graph.adj (z n) u) := by
    intro m
    show decide (m ≤ (List.finRange (n + 1)).countP fun v => eval G idAct (v :: zs) (.adj (n + 1) 0)) = _
    rw [funext hnew]
  have hdeg : (List.finRange (n + 1)).countP (fun u => G.graph.adj (z n) u) = k := by
    have h1 := hbody _ (.inl (.inr (.inl rfl)))
    have h2 := hbody _ (.inl (.inr (.inr rfl)))
    have h2' : eval G idAct zs (.atLeast (k + 1) (.adj (n + 1) 0)) = false := by
      simpa [eval] using h2
    rw [hc] at h1 h2'
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2'
    omega
  -- every vertex is some z i (pigeonhole)
  have hnd : ((List.range (n + 1)).map z).Nodup := by
    refine List.pairwise_map.mpr (List.nodup_range.imp_of_mem fun ha hb hab => ?_)
    exact hdist _ _ (List.mem_range.mp ha) (List.mem_range.mp hb) hab
  have hall : ∀ u : Fin (n + 1), u ∈ (List.range (n + 1)).map z := by
    intro u
    refine Decidable.byContradiction fun hu => ?_
    have := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨hu, hnd⟩)
      (fun x _ => List.mem_finRange x)
    simp at this
    omega
  have hperm : (List.finRange (n + 1)).Perm ((List.range (n + 1)).map z) :=
    (List.perm_ext_iff_of_nodup (List.nodup_finRange _) hnd).mpr
      fun a => ⟨fun _ => hall a, fun _ => List.mem_finRange a⟩
  -- the neighbourhood of z n, as a decreasing list
  let S := (List.range n).reverse.filter fun i => G.graph.adj (z n) (z i)
  have hSmem : ∀ i, i < n → S.contains i = G.graph.adj (z n) (z i) := by
    intro i hi
    rw [Bool.eq_iff_iff, List.contains_iff_mem]
    simp [S, List.mem_filter, hi]
  have hSsub : IsSubset n k S := by
    refine ⟨(List.pairwise_reverse.mpr List.pairwise_lt_range).filter _, ?_, fun x hx => ?_⟩
    · rw [← hdeg, hperm.countP_eq, List.countP_map, List.range_succ, List.countP_append]
      simp [S, ← List.countP_eq_length_filter, Function.comp_def]
    · simp only [S, List.mem_filter, List.mem_reverse, List.mem_range] at hx
      exact hx.1
  -- adjacency among the z's is the extension's
  have hadj : ∀ a b, a < n + 1 → b < n + 1 → G.graph.adj (z a) (z b) = extAdj t n S a b := by
    intro a b ha hb
    by_cases hab : a = b
    · subst hab
      simp [extAdj]
    rcases Nat.lt_or_ge a n with ha2 | ha2
    · rcases Nat.lt_or_ge b n with hb2 | hb2
      · simp [extAdj, hab, ha2, hb2, hbase a b ha2 hb2 hab]
      · obtain rfl : b = n := by omega
        have he : extAdj t b S a b = S.contains a := by simp [extAdj, hab, ha2]
        rw [he, hSmem a ha2, G.graph.adj_symm]
    · obtain rfl : a = n := by omega
      have hb2 : b < a := by omega
      have he : extAdj t a S a b = S.contains b := by simp [extAdj, hab, hb2]
      rw [he, hSmem b hb2]
  -- the receipt's hit for S gives a copy of some pattern
  obtain ⟨h, -, hh⟩ := hitsOk_mem hok S (mem_combos.mpr hSsub)
  unfold hitOk at hh
  simp only [Bool.and_eq_true] at hh
  obtain ⟨-, hh⟩ := hh
  split at hh
  · contradiction
  rename_i P hP
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hh
  obtain ⟨⟨⟨⟨hml, hmb⟩, hmnd⟩, hedge⟩, hnon⟩ := hh
  have hmap : ∀ i, i < P.size → h.map.getD i 0 < n + 1 := by
    intro i hi
    exact hmb _ (List.mem_of_getElem? (getElem?_of_lt 0 (hml ▸ hi)))
  have hy : ∀ i, i < P.size → (h.map.map z ++ zs)[i]? = some (z (h.map.getD i 0)) := by
    intro i hi
    rw [List.getElem?_append_left (by simpa [hml] using hi), List.getElem?_map,
      getElem?_of_lt 0 (hml ▸ hi)]
    rfl
  have hcopy : eval G idAct zs (patFormula P) = true := by
    unfold patFormula
    rw [eval_exs]
    refine ⟨h.map.map z, by simp [hml], ?_⟩
    rw [eval_conj]
    intro φ hφ
    simp only [List.mem_append, List.mem_map] at hφ
    rcases hφ with (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
    · obtain ⟨h1, h2, h12⟩ := mem_offDiag.mp he
      have hne : h.map.getD e.1 0 ≠ h.map.getD e.2 0 := by
        intro heq
        have := (List.Nodup.getElem?_inj (hml ▸ h1) hmnd (j := e.2)).mp
          (by rw [getElem?_of_lt 0 (hml ▸ h1), getElem?_of_lt 0 (hml ▸ h2), heq])
        exact h12 this
      simpa [eval, hy _ h1, hy _ h2] using hdist _ _ (hmap _ h1) (hmap _ h2) hne
    · obtain ⟨⟨h1, h2⟩, he2⟩ := hedge e he
      simp only [eval, hy _ h1, hy _ h2]
      rw [hadj _ _ (hmap _ h1) (hmap _ h2)]
      exact he2
    · obtain ⟨⟨h1, h2⟩, he2⟩ := hnon e he
      simp only [eval, hy _ h1, hy _ h2]
      rw [hadj _ _ (hmap _ h1) (hmap _ h2), he2]
      rfl
  have := hbody _ (.inr ⟨P, List.mem_of_getElem? hP, rfl⟩)
  simp [eval, hcopy] at this

end Soundness

end GPCensus.Extension
