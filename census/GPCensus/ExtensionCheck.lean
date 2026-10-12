/-!
The extension-cover generator and checker (HW61 G-5), kept free of Hex types and of the census
formula language so the kernel can evaluate them (`decide`) as well as the compiled runner.

- `combos n k` lists the `k`-subsets of `0..n-1` as strictly decreasing lists: exactly the
  `k`-subsets (`mem_combos`), each once (`nodup_combos`), `binom n k` of them (`length_combos`).
  `combos_eq_flatMap` splits it into shards by largest element.
- A receipt gives one `Hit` per generated neighbourhood, in order: the neighbourhood (compared with
  the generated one), a pattern index and a vertex map. `hitOk` checks the map is injective, lands
  in `0..n`, sends every pattern edge to an edge of the extension `extAdj` and every required
  non-edge to a non-edge.
-/

namespace GPCensus.Extension

/-! ## The generator -/

/-- The `k`-subsets of `0..n-1`, each as a strictly decreasing list. -/
def combos : Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, k + 1 => combos n (k + 1) ++ (combos n k).map (n :: ·)

/-- `S` is a `k`-subset of `0..n-1`, listed in decreasing order. -/
def IsSubset (n k : Nat) (S : List Nat) : Prop :=
  S.Pairwise (· > ·) ∧ S.length = k ∧ ∀ x ∈ S, x < n

/-- Pascal's triangle. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n (k + 1) + binom n k

theorem mem_combos_of_isSubset : ∀ {n k : Nat} {S : List Nat}, IsSubset n k S → S ∈ combos n k
  | _, 0, S, ⟨_, hl, _⟩ => by simp [combos, List.length_eq_zero_iff.mp hl]
  | 0, _ + 1, [], ⟨_, hl, _⟩ => by simp at hl
  | 0, _ + 1, x :: _, ⟨_, _, hx⟩ => absurd (hx x List.mem_cons_self) (Nat.not_lt_zero _)
  | _ + 1, _ + 1, [], ⟨_, hl, _⟩ => by simp at hl
  | n + 1, k + 1, x :: T, ⟨hp, hl, hx⟩ => by
    rw [List.pairwise_cons] at hp
    simp only [combos, List.mem_append, List.mem_map]
    have hxn : x < n + 1 := hx x List.mem_cons_self
    by_cases hxe : x = n
    · subst hxe
      exact .inr ⟨T, mem_combos_of_isSubset ⟨hp.2, by simpa using hl, fun y hy => hp.1 y hy⟩, rfl⟩
    · refine .inl (mem_combos_of_isSubset ⟨List.pairwise_cons.mpr hp, hl, fun y hy => ?_⟩)
      have : x < n := by omega
      rcases List.mem_cons.mp hy with rfl | hy
      · exact this
      · exact Nat.lt_trans (hp.1 y hy) this

theorem isSubset_of_mem_combos : ∀ {n k : Nat} {S : List Nat}, S ∈ combos n k → IsSubset n k S
  | _, 0, S, h => by simp [combos] at h; subst h; exact ⟨.nil, rfl, by simp⟩
  | 0, _ + 1, _, h => by simp [combos] at h
  | n + 1, k + 1, S, h => by
    simp only [combos, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨T, hT, rfl⟩
    · obtain ⟨hp, hl, hx⟩ := isSubset_of_mem_combos h
      exact ⟨hp, hl, fun y hy => Nat.lt_succ_of_lt (hx y hy)⟩
    · obtain ⟨hp, hl, hx⟩ := isSubset_of_mem_combos hT
      refine ⟨List.pairwise_cons.mpr ⟨fun y hy => hx y hy, hp⟩, by simp [hl], fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (hx y hy)

/-- The generator lists exactly the `k`-subsets of `0..n-1`. -/
theorem mem_combos {n k : Nat} {S : List Nat} : S ∈ combos n k ↔ IsSubset n k S :=
  ⟨isSubset_of_mem_combos, mem_combos_of_isSubset⟩

/-- … each once … -/
theorem nodup_combos : ∀ n k : Nat, (combos n k).Nodup
  | _, 0 => by simp [combos]
  | 0, _ + 1 => by simp [combos]
  | n + 1, k + 1 => by
    simp only [combos]
    refine List.nodup_append.mpr ⟨nodup_combos n (k + 1),
      List.Pairwise.map _ (fun _ _ hab heq => hab (List.cons.inj heq).2) (nodup_combos n k), ?_⟩
    · intro S hS S' hS' heq
      subst heq
      obtain ⟨T, -, rfl⟩ := List.mem_map.mp hS'
      exact Nat.lt_irrefl n ((isSubset_of_mem_combos hS).2.2 n List.mem_cons_self)

/-- … and `binom n k` of them. -/
theorem length_combos : ∀ n k : Nat, (combos n k).length = binom n k
  | n, 0 => by cases n <;> rfl
  | 0, _ + 1 => rfl
  | n + 1, k + 1 => by simp [combos, binom, length_combos n (k + 1), length_combos n k]

theorem binom_21_4 : binom 21 4 = 5985 := by decide
theorem binom_21_5 : binom 21 5 = 20349 := by decide

/-- Shards by largest element: the `(k+1)`-subsets of `0..n-1` are, for each `m < n`, `m` on top of
a `k`-subset of `0..m-1`. -/
theorem combos_eq_flatMap (k : Nat) : ∀ n : Nat,
    combos n (k + 1) = (List.range n).flatMap fun m => (combos m k).map (m :: ·)
  | 0 => rfl
  | n + 1 => by
    rw [combos, combos_eq_flatMap k n, List.range_succ, List.flatMap_append]
    simp

/-! ## Receipts -/

structure Pattern where
  size : Nat
  edges : List (Nat × Nat)
  nonEdges : List (Nat × Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The base adjacency table: one bitmask of neighbours per vertex. -/
def table (n : Nat) (E : List (Nat × Nat)) : Array Nat :=
  (List.range n).toArray.map fun i =>
    E.foldl (fun m e => if e.1 = i then m ||| (1 <<< e.2) else if e.2 = i then m ||| (1 <<< e.1) else m) 0

def baseAdj (t : Array Nat) (i j : Nat) : Bool := (t.getD i 0).testBit j

structure Hit where
  nbhd : List Nat
  pat : Nat
  map : List Nat
  deriving Repr, DecidableEq, Inhabited

/-- Adjacency in the base plus vertex `n` joined to `S`. -/
def extAdj (t : Array Nat) (n : Nat) (S : List Nat) (a b : Nat) : Bool :=
  a != b && if a < n then (if b < n then baseAdj t a b else b == n && S.contains a)
    else a == n && b < n && S.contains b

def hitOk (t : Array Nat) (n : Nat) (pats : List Pattern) (S : List Nat) (h : Hit) : Bool :=
  h.nbhd == S &&
    match pats[h.pat]? with
    | none => false
    | some P =>
      h.map.length == P.size && h.map.all (· < n + 1) && decide h.map.Nodup &&
        P.edges.all (fun e => e.1 < P.size && e.2 < P.size &&
          extAdj t n S (h.map.getD e.1 0) (h.map.getD e.2 0)) &&
        P.nonEdges.all (fun e => e.1 < P.size && e.2 < P.size &&
          !extAdj t n S (h.map.getD e.1 0) (h.map.getD e.2 0))

/-- One hit per generated neighbourhood, in order. -/
def hitsOk (t : Array Nat) (n : Nat) (pats : List Pattern) : List (List Nat) → List Hit → Bool
  | [], [] => true
  | S :: Ss, h :: hs => hitOk t n pats S h && hitsOk t n pats Ss hs
  | _, _ => false

theorem hitsOk_mem {t : Array Nat} {n : Nat} {pats : List Pattern} :
    ∀ {Ss : List (List Nat)} {hs : List Hit}, hitsOk t n pats Ss hs = true →
      ∀ S ∈ Ss, ∃ h ∈ hs, hitOk t n pats S h = true
  | [], _, _, _, hS => by simp at hS
  | _ :: _, [], H, _, _ => by simp [hitsOk] at H
  | _ :: Ss, h :: hs, H, S, hS => by
    simp only [hitsOk, Bool.and_eq_true] at H
    rcases List.mem_cons.mp hS with rfl | hS
    · exact ⟨h, List.mem_cons_self, H.1⟩
    · obtain ⟨h', hh', ok⟩ := hitsOk_mem H.2 S hS
      exact ⟨h', List.mem_cons_of_mem _ hh', ok⟩

end GPCensus.Extension
