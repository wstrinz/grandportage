import GP50.ResolveProofs
import Std.Data.HashMap
import Std.Data.HashSet

namespace GPProfile.Index

/-! ## Key indexes (post-G4 Track K, P4)

A query that scans a whole list for entries with one key becomes a lookup in an index built once.
`bucket key xs` maps each key to its entries in list order (`bucket_getD`), so `any` and `find?`
restricted to a key's bucket agree with the scan whenever the predicate fixes the key. -/

variable {α κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ]

def bucket (key : α → κ) (xs : List α) : Std.HashMap κ (List α) :=
  xs.foldr (fun x m => m.insert (key x) (x :: m.getD (key x) [])) {}

theorem bucket_getD (key : α → κ) (xs : List α) (k : κ) :
    (bucket key xs).getD k [] = xs.filter (fun x => key x == k) := by
  induction xs with
  | nil => simp [bucket]
  | cons x rest ih =>
    simp only [bucket, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getD_insert, List.filter_cons]
    by_cases hk : key x = k
    · subst hk; simp [ih]
    · simp [hk, ih]

theorem any_bucket (key : α → κ) (xs : List α) (k : κ) (p : α → Bool)
    (h : ∀ x, p x = true → key x = k) : ((bucket key xs).getD k []).any p = xs.any p := by
  rw [bucket_getD, List.any_filter]
  congr 1
  funext x
  cases hp : p x
  · simp
  · simp [h x hp]

theorem find?_bucket (key : α → κ) (xs : List α) (k : κ) (p : α → Bool)
    (h : ∀ x, p x = true → key x = k) : ((bucket key xs).getD k []).find? p = xs.find? p := by
  rw [bucket_getD, List.find?_filter]
  congr 1
  funext x
  cases hp : p x
  · simp
  · simp [h x hp]

/-- `xs.eraseDups.length == xs.length` with a hash set (`nodupB_eq`). -/
def nodupB (xs : List κ) : Bool :=
  (xs.foldl (fun (acc : Std.HashSet κ × Bool) x => (acc.1.insert x, acc.2 && !acc.1.contains x)) ({}, true)).2

omit [Hashable κ] in
theorem eraseDups_of_nodup : ∀ {xs : List κ}, xs.Nodup → xs.eraseDups = xs
  | [], _ => by simp
  | a :: as, h => by
    rw [List.nodup_cons] at h
    rw [List.eraseDups_cons]
    have hf : as.filter (fun b => !b == a) = as := by
      rw [List.filter_eq_self]
      intro b hb
      have : b ≠ a := fun e => h.1 (e ▸ hb)
      simp [this]
    rw [hf, eraseDups_of_nodup h.2]

omit [Hashable κ] in
theorem eraseDups_length_beq_iff (xs : List κ) : (xs.eraseDups.length == xs.length) = true ↔ xs.Nodup := by
  constructor
  · intro e; exact GP50.nodup_of_eraseDups_length_eq xs (by simpa using e)
  · intro h; simp [eraseDups_of_nodup h]

theorem nodupB_go [LawfulHashable κ] : ∀ (xs : List κ) (s : Std.HashSet κ) (b : Bool),
    (xs.foldl (fun (acc : Std.HashSet κ × Bool) x => (acc.1.insert x, acc.2 && !acc.1.contains x)) (s, b)).2 = true ↔
      (b = true ∧ xs.Nodup ∧ ∀ x ∈ xs, s.contains x = false)
  | [], s, b => by simp
  | x :: rest, s, b => by
    simp only [List.foldl_cons]
    rw [nodupB_go rest (s.insert x) (b && !s.contains x)]
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.nodup_cons, List.mem_cons, forall_eq_or_imp,
      Std.HashSet.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    constructor
    · rintro ⟨⟨hb, hx⟩, hnd, hall⟩
      refine ⟨hb, ⟨fun hm => (hall x hm).1 rfl, hnd⟩, hx, fun y hy => (hall y hy).2⟩
    · rintro ⟨hb, ⟨hnm, hnd⟩, hx, hall⟩
      exact ⟨⟨hb, hx⟩, hnd, fun y hy => ⟨fun e => hnm (e ▸ hy), hall y hy⟩⟩

theorem nodupB_eq [LawfulHashable κ] (xs : List κ) : nodupB xs = (xs.eraseDups.length == xs.length) := by
  apply Bool.eq_iff_iff.mpr
  rw [eraseDups_length_beq_iff, nodupB, nodupB_go]
  simp

end GPProfile.Index
