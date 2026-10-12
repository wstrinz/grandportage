set_option linter.unusedVariables false

namespace GPCert
open Polynomial

/-! Route B prelude. Polynomials in one variable are coefficient lists over `ℕ`, low degree
first; all checking is modulo `p` and modulo the monic source polynomial `fl ++ [1]`.
The checker is written with `List.rec`/`Nat.rec` and raw `Nat` operations so that kernel
evaluation (`decide +kernel`) stays cheap; each definition has `rfl` equations for proofs. -/

/-! ### List and arithmetic helpers -/

noncomputable def appendR {α : Type} (a b : List α) : List α :=
  List.rec (motive := fun _ => List α) b (fun x _ ih => x :: ih) a

noncomputable def anyR {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => or (f x) ih) l

noncomputable def nthD {α : Type} (d : α) (l : List α) (k : ℕ) : α :=
  List.rec (motive := fun _ => ℕ → α) (fun _ => d)
    (fun x _ ih k => Nat.casesOn (motive := fun _ => α) k x ih) l k

noncomputable def memN (a : ℕ) (l : List ℕ) : Bool := anyR (fun x => Nat.beq a x) l

/-- `[lo, lo + 1, …, lo + k - 1]`. -/
noncomputable def iota (lo k : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => []) (fun _ ih lo => lo :: ih (Nat.succ lo)) k lo

/-! ### Polynomials -/

noncomputable def padd (a : List ℕ) : List ℕ → List ℕ :=
  List.rec (motive := fun _ => List ℕ → List ℕ) (fun b => b)
    (fun x xs ih b => List.casesOn (motive := fun _ => List ℕ) b (x :: xs)
      (fun y ys => Nat.add x y :: ih ys)) a

noncomputable def pscale (c : ℕ) (b : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun y _ ih => Nat.mul c y :: ih) b

noncomputable def pmul (a b : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun c _ ih => padd (pscale c b) (0 :: ih)) a

/-- Every coefficient is `0` modulo `p`. -/
noncomputable def pzero (p : ℕ) (a : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => and (Nat.beq (Nat.mod x p) 0) ih) a

/-- Coefficientwise equality modulo `p` (missing coefficients are `0`). -/
noncomputable def peq (p : ℕ) (a : List ℕ) : List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun b => pzero p b)
    (fun x xs ih b => List.casesOn (motive := fun _ => Bool) b (pzero p (x :: xs))
      (fun y ys => and (Nat.beq (Nat.mod x p) (Nat.mod y p)) (ih ys))) a

/-- Base-`p` digits of `x`, low first, at most `D` of them (stops at zero). Any decoding is
sound: the theorem is about whatever columns and certificates the decoding produces. -/
noncomputable def dec (p D x : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
    (fun _ ih x => cond (Nat.beq x 0) [] (Nat.mod x p :: ih (Nat.div x p))) D x

/-- Columns encoded as one base-`p` number per coordinate, column-major. -/
noncomputable def colOf (p D : ℕ) (vecsN : List ℕ) (i j : ℕ) : List ℕ :=
  dec p D (nthD 0 vecsN (Nat.add (Nat.mul 3 i) j))

/-- A certificate `g + B q`. -/
noncomputable def certOf (p D B c : ℕ) : List ℕ × List ℕ := (dec p D (Nat.mod c B), dec p D (Nat.div c B))

/-- Cross product halves of columns `a`, `b`: coordinate `j` of `u × v` is `xP j - xN j`. -/
noncomputable def xP (col : ℕ → ℕ → List ℕ) (a b : ℕ) (j : ℕ) : List ℕ :=
  Nat.casesOn (motive := fun _ => List ℕ) j (pmul (col a 1) (col b 2)) fun j =>
    Nat.casesOn (motive := fun _ => List ℕ) j (pmul (col a 2) (col b 0)) fun _ => pmul (col a 0) (col b 1)

noncomputable def xN (col : ℕ → ℕ → List ℕ) (a b : ℕ) (j : ℕ) : List ℕ :=
  Nat.casesOn (motive := fun _ => List ℕ) j (pmul (col a 2) (col b 1)) fun j =>
    Nat.casesOn (motive := fun _ => List ℕ) j (pmul (col a 0) (col b 2)) fun _ => pmul (col a 1) (col b 0)

/-- Positive and negative halves of the 3×3 determinant of columns `a b c`. -/
noncomputable def detP (col : ℕ → ℕ → List ℕ) (a b c : ℕ) : List ℕ :=
  padd (pmul (xP col a b 0) (col c 0)) (padd (pmul (xP col a b 1) (col c 1)) (pmul (xP col a b 2) (col c 2)))

noncomputable def detN (col : ℕ → ℕ → List ℕ) (a b c : ℕ) : List ℕ :=
  padd (pmul (xN col a b 0) (col c 0)) (padd (pmul (xN col a b 1) (col c 1)) (pmul (xN col a b 2) (col c 2)))

/-! ### The checker -/

/-- A line given by element indices, as a `Finset (Fin n)`. -/
def toFS {n : ℕ} (l : List ℕ) : Finset (Fin n) :=
  (l.filterMap fun k => if h : k < n then some ⟨k, h⟩ else none).toFinset

/-- Whether some line (as index lists) contains `a`, `b` and `c`. -/
noncomputable def onN (linesN : List (List ℕ)) (a b c : ℕ) : Bool :=
  anyR (fun l => and (memN a l) (and (memN b l) (memN c l))) linesN

/-- One triple: on a line, `detP ≡ detN + q f`; off every line, `g detP ≡ 1 + g detN + q f`,
so `g` inverts the determinant modulo `(f, p)`. -/
noncomputable def checkTriple (linesN : List (List ℕ)) (p : ℕ) (f : List ℕ)
    (col : ℕ → ℕ → List ℕ) (a b c : ℕ) (cert : List ℕ × List ℕ) : Bool :=
  cond (onN linesN a b c)
    (peq p (detP col a b c) (padd (detN col a b c) (pmul cert.2 f)))
    (peq p (pmul cert.1 (detP col a b c))
      (padd [1] (padd (pmul cert.1 (detN col a b c)) (pmul cert.2 f))))

noncomputable def lenR (l : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) l

/-- Equality of index lists. -/
noncomputable def listBeq (a : List ℕ) : List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool)
    (fun b => List.casesOn (motive := fun _ => Bool) b true (fun _ _ => false))
    (fun x _ ih b => List.casesOn (motive := fun _ => Bool) b false (fun y ys => and (Nat.beq x y) (ih ys))) a

/-! The triple loops bind `a`, `b`, `c` directly to entries of the literal index list, so the
kernel sees the same closed terms (`col 3 0`, the cross product of columns `3, 4`, …) again and
again and can reuse its cached reductions. Certificates come as a stream `S` in base `M`; which
slot a triple reads does not matter for soundness. -/

noncomputable def allC (f : ℕ → ℕ → ℕ → ℕ → Bool) (M a b : ℕ) (l : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun c _ ih S => and (f a b c (Nat.mod S M)) (ih (Nat.div S M))) l

noncomputable def allB (f : ℕ → ℕ → ℕ → ℕ → Bool) (M a : ℕ) (l : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun b rest ih S => and (allC f M a b rest S) (ih (Nat.div S (Nat.pow M (lenR rest))))) l

noncomputable def allA (f : ℕ → ℕ → ℕ → ℕ → Bool) (M : ℕ) (L : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun a rest ih S => and (allB f M a rest S)
      (ih (Nat.div S (Nat.pow M (Nat.div (Nat.mul (lenR rest) (Nat.sub (lenR rest) 1)) 2))))) L

/-- The checker: the challenge's lines are `linesN` (as index lists), the source polynomial
`fl ++ [1]` is monic of degree at least one, `L` is `[0, …, n - 1]`, and every triple
`a < b < c` has a passing certificate `dc s`. -/
noncomputable def certOk {n : ℕ} (lines : List (Finset (Fin n))) (linesN : List (List ℕ))
    (p : ℕ) (fl : List ℕ) (col : ℕ → ℕ → List ℕ) (dc : ℕ → List ℕ × List ℕ) (M : ℕ)
    (L : List ℕ) (S : ℕ) : Bool :=
  and (List.casesOn (motive := fun _ => Bool) fl false (fun _ _ => true))
    (and (decide (lines = linesN.map toFS))
      (and (listBeq L (iota 0 n))
        (allA (fun a b c s => checkTriple linesN p (appendR fl [1]) col a b c (dc s)) M L S)))

/-! ### Soundness -/

theorem appendR_eq {α : Type} (b : List α) : ∀ a, appendR a b = a ++ b
  | [] => rfl
  | x :: xs => congrArg (x :: ·) (appendR_eq b xs)

theorem anyR_iff {α : Type} (f : α → Bool) : ∀ l, anyR f l = true ↔ ∃ x ∈ l, f x = true
  | [] => by show false = true ↔ _; simp
  | x :: xs => by
      show (f x || anyR f xs) = true ↔ _
      rw [Bool.or_eq_true, anyR_iff f xs]; simp

theorem memN_iff (a : ℕ) (l : List ℕ) : memN a l = true ↔ a ∈ l := by
  simp [memN, anyR_iff, Nat.beq_eq]

theorem mem_iota (x : ℕ) : ∀ k lo, x ∈ iota lo k ↔ lo ≤ x ∧ x < lo + k
  | 0, lo => by show x ∈ ([] : List ℕ) ↔ _; simp
  | k + 1, lo => by
      show x ∈ lo :: iota (lo + 1) k ↔ _
      rw [List.mem_cons, mem_iota x k (lo + 1)]; omega

theorem xP_0 (col : ℕ → ℕ → List ℕ) (a b : ℕ) : xP col a b 0 = pmul (col a 1) (col b 2) := rfl
theorem xP_1 (col : ℕ → ℕ → List ℕ) (a b : ℕ) : xP col a b 1 = pmul (col a 2) (col b 0) := rfl
theorem xP_2 (col : ℕ → ℕ → List ℕ) (a b : ℕ) : xP col a b 2 = pmul (col a 0) (col b 1) := rfl
theorem xN_0 (col : ℕ → ℕ → List ℕ) (a b : ℕ) : xN col a b 0 = pmul (col a 2) (col b 1) := rfl
theorem xN_1 (col : ℕ → ℕ → List ℕ) (a b : ℕ) : xN col a b 1 = pmul (col a 0) (col b 2) := rfl
theorem xN_2 (col : ℕ → ℕ → List ℕ) (a b : ℕ) : xN col a b 2 = pmul (col a 1) (col b 0) := rfl

theorem listBeq_eq : ∀ a b : List ℕ, listBeq a b = true → a = b
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => by cases (h : false = true)
  | _ :: _, [] => fun h => by cases (h : false = true)
  | x :: xs, y :: ys => fun h => by
      have h' : (Nat.beq x y && listBeq xs ys) = true := h
      rw [Bool.and_eq_true, Nat.beq_eq] at h'
      rw [h'.1, listBeq_eq xs ys h'.2]

theorem iota_pairwise : ∀ k lo, (iota lo k).Pairwise (· < ·)
  | 0, lo => List.Pairwise.nil
  | k + 1, lo => by
      show (lo :: iota (lo + 1) k).Pairwise (· < ·)
      refine List.Pairwise.cons (fun y hy => ?_) (iota_pairwise k (lo + 1))
      have := (mem_iota y k (lo + 1)).mp hy; omega

theorem allC_spec (f : ℕ → ℕ → ℕ → ℕ → Bool) (M a b c : ℕ) :
    ∀ l S, allC f M a b l S = true → c ∈ l → ∃ s, f a b c s = true
  | [], _, _, hm => by simp at hm
  | x :: r, S, h, hm => by
      have h' : (f a b x (S % M) && allC f M a b r (S / M)) = true := h
      rw [Bool.and_eq_true] at h'
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨_, h'.1⟩
      · exact allC_spec f M a b c r _ h'.2 hm

theorem allB_spec (f : ℕ → ℕ → ℕ → ℕ → Bool) (M a b c : ℕ) :
    ∀ l S, allB f M a l S = true → l.Pairwise (· < ·) → b ∈ l → c ∈ l → b < c →
      ∃ s, f a b c s = true
  | [], _, _, _, hb, _, _ => by simp at hb
  | x :: r, S, h, hp, hb, hc, hbc => by
      have h' : (allC f M a x r S && allB f M a r (S / M ^ lenR r)) = true := h
      rw [Bool.and_eq_true] at h'
      rw [List.pairwise_cons] at hp
      rcases List.mem_cons.mp hb with rfl | hb
      · rcases List.mem_cons.mp hc with rfl | hc
        · omega
        · exact allC_spec f M a b c r S h'.1 hc
      · have hxb := hp.1 b hb
        rcases List.mem_cons.mp hc with rfl | hc
        · omega
        · exact allB_spec f M a b c r _ h'.2 hp.2 hb hc hbc

theorem allA_spec (f : ℕ → ℕ → ℕ → ℕ → Bool) (M a b c : ℕ) :
    ∀ L S, allA f M L S = true → L.Pairwise (· < ·) → a ∈ L → b ∈ L → c ∈ L → a < b → b < c →
      ∃ s, f a b c s = true
  | [], _, _, _, ha, _, _, _, _ => by simp at ha
  | x :: r, S, h, hp, ha, hb, hc, hab, hbc => by
      have h' : (allB f M x r S && allA f M r
          (S / M ^ (lenR r * (lenR r - 1) / 2))) = true := h
      rw [Bool.and_eq_true] at h'
      rw [List.pairwise_cons] at hp
      rcases List.mem_cons.mp ha with rfl | ha
      · have hb' : b ∈ r := by
          rcases List.mem_cons.mp hb with rfl | hb
          · omega
          · exact hb
        have hc' : c ∈ r := by
          rcases List.mem_cons.mp hc with rfl | hc
          · omega
          · exact hc
        exact allB_spec f M a b c r S h'.1 hp.2 hb' hc' hbc
      · have hxa := hp.1 a ha
        have hb' : b ∈ r := by
          rcases List.mem_cons.mp hb with rfl | hb
          · omega
          · exact hb
        have hc' : c ∈ r := by
          rcases List.mem_cons.mp hc with rfl | hc
          · omega
          · exact hc
        exact allA_spec f M a b c r _ h'.2 hp.2 ha hb' hc' hab hbc

theorem mem_toFS {n : ℕ} (l : List ℕ) (a : Fin n) :
    a ∈ (toFS l : Finset (Fin n)) ↔ (a : ℕ) ∈ l := by
  simp only [toFS, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, h⟩
    split at h
    · cases h; exact hk
    · cases h
  · intro h
    exact ⟨a, h, by simp [a.isLt]⟩

theorem onN_iff {n : ℕ} (linesN : List (List ℕ)) (a b c : Fin n) :
    onN linesN a b c = true ↔ ∃ l ∈ linesN.map toFS, a ∈ l ∧ b ∈ l ∧ c ∈ l := by
  simp only [onN, anyR_iff, Bool.and_eq_true, memN_iff]
  simp [mem_toFS]

section Sound
variable {K : Type*} [Field K]

/-- Evaluation of a coefficient list at `r`. -/
def ev (r : K) : List ℕ → K
  | [] => 0
  | c :: cs => (c : K) + r * ev r cs

theorem ev_padd (r : K) : ∀ a b, ev r (padd a b) = ev r a + ev r b
  | [], b => by show ev r b = ev r [] + ev r b; simp [ev]
  | x :: xs, [] => by show ev r (x :: xs) = ev r (x :: xs) + ev r []; simp [ev]
  | x :: xs, y :: ys => by
      show ev r ((x + y) :: padd xs ys) = _
      simp only [ev, ev_padd r xs ys]; push_cast; ring

theorem ev_pscale (r : K) (c : ℕ) : ∀ b, ev r (pscale c b) = c * ev r b
  | [] => by show ev r [] = c * ev r []; simp [ev]
  | y :: ys => by
      show ev r ((c * y) :: pscale c ys) = _
      simp only [ev, ev_pscale r c ys]; push_cast; ring

theorem ev_pmul (r : K) : ∀ a b, ev r (pmul a b) = ev r a * ev r b
  | [], b => by show ev r [] = ev r [] * ev r b; simp [ev]
  | c :: cs, b => by
      show ev r (padd (pscale c b) (0 :: pmul cs b)) = _
      simp only [ev_padd, ev_pscale, ev, ev_pmul r cs b]; push_cast; ring

theorem ev_append_one (r : K) : ∀ l : List ℕ, ev r (l ++ [1]) = ev r l + r ^ l.length
  | [] => by simp [ev]
  | c :: cs => by simp only [List.cons_append, ev, ev_append_one r cs, List.length_cons]; ring

theorem ev_of_pzero {p : ℕ} [CharP K p] (r : K) : ∀ a, pzero p a = true → ev r a = 0
  | [] => fun _ => rfl
  | x :: xs => by
      intro h
      have h' : (Nat.beq (x % p) 0 && pzero p xs) = true := h
      rw [Bool.and_eq_true, Nat.beq_eq] at h'
      have h0 : (x : K) = 0 := (CharP.cast_eq_zero_iff K p x).mpr (Nat.dvd_of_mod_eq_zero h'.1)
      simp only [ev, h0, ev_of_pzero r xs h'.2]; ring

theorem ev_of_peq {p : ℕ} [CharP K p] (r : K) : ∀ a b, peq p a b = true → ev r a = ev r b
  | [], b => fun h => by rw [ev_of_pzero r b (h : pzero p b = true)]; rfl
  | x :: xs, [] => fun h => by
      have h' : pzero p (x :: xs) = true := h
      rw [ev_of_pzero r _ h']; rfl
  | x :: xs, y :: ys => by
      intro h
      have h' : (Nat.beq (x % p) (y % p) && peq p xs ys) = true := h
      rw [Bool.and_eq_true, Nat.beq_eq] at h'
      have h0 : (x : K) = y := CharP.natCast_eq_natCast' K p h'.1
      simp only [ev]; rw [h0, ev_of_peq r xs ys h'.2]

noncomputable def toPoly : List ℕ → K[X]
  | [] => 0
  | c :: cs => C (c : K) + X * toPoly cs

theorem eval_toPoly (r : K) : ∀ l, (toPoly l).eval r = ev r l
  | [] => by simp [toPoly, ev]
  | c :: cs => by simp [toPoly, ev, eval_toPoly r cs]

theorem degree_toPoly_lt : ∀ l : List ℕ, (toPoly (K := K) l).degree < l.length
  | [] => by simp [toPoly]
  | c :: cs => by
      rw [Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      cases m with
      | zero => simp at hm
      | succ m =>
        have ih := (Polynomial.degree_lt_iff_coeff_zero _ _).mp (degree_toPoly_lt cs) m
          (by simp at hm; omega)
        simp [toPoly, ih]

theorem exists_root_of [IsAlgClosed K] (fl : List ℕ) (hne : fl ≠ []) :
    ∃ r : K, ev r (fl ++ [1]) = 0 := by
  have hlt : (toPoly (K := K) fl).degree < ((X : K[X]) ^ fl.length).degree := by
    rw [degree_X_pow]; exact degree_toPoly_lt fl
  have hdeg : ((X : K[X]) ^ fl.length + toPoly fl).degree = (fl.length : WithBot ℕ) := by
    rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
  have hlen : fl.length ≠ 0 := by simpa using hne
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root ((X : K[X]) ^ fl.length + toPoly fl)
    (by rw [hdeg]; exact_mod_cast hlen)
  refine ⟨r, ?_⟩
  rw [ev_append_one]
  simpa [IsRoot, eval_toPoly, add_comm] using hr

theorem li3' (u v w : Fin 3 → K) :
    LinearIndependent K ![u, v, w] ↔
      u 0 * v 1 * w 2 - u 0 * v 2 * w 1 - u 1 * v 0 * w 2 + u 1 * v 2 * w 0 + u 2 * v 0 * w 1
        - u 2 * v 1 * w 0 ≠ 0 := by
  have h := Matrix.linearIndependent_rows_iff_isUnit (K := K) (A := Matrix.of ![u, v, w])
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_fin_three] at h
  simp [Matrix.row] at h
  exact h

end Sound

/-- Soundness of the route B checker for the map-rule challenge shape. -/
theorem realizes_of_certOk {n : ℕ} (lines : List (Finset (Fin n))) (linesN : List (List ℕ))
    (p : ℕ) (fl : List ℕ) (col : ℕ → ℕ → List ℕ) (dc : ℕ → List ℕ × List ℕ) (M : ℕ)
    (L : List ℕ) (S : ℕ) (h : certOk lines linesN p fl col dc M L S = true)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] :
    ∃ v : Fin n → Fin 3 → K, RealizesRank3 lines v := by
  have hne : fl ≠ [] := by
    rintro rfl; cases (h : false = true)
  have h' : (decide (lines = linesN.map toFS) && (listBeq L (iota 0 n) &&
      allA (fun a b c s => checkTriple linesN p (appendR fl [1]) col a b c (dc s)) M L S)) = true := by
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne; exact h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, appendR_eq] at h'
  obtain ⟨hl, hL, hall⟩ := h'
  subst hl
  have hL := listBeq_eq _ _ hL
  subst hL
  obtain ⟨r, hr⟩ := exists_root_of (K := K) fl hne
  refine ⟨fun i j => ev r (col i j), ?_⟩
  intro a b c hab hbc
  have hab' := Fin.lt_def.mp hab; have hbc' := Fin.lt_def.mp hbc; have hcn := c.isLt
  have mem : ∀ x : ℕ, x < n → x ∈ iota 0 n := fun x hx => (mem_iota x n 0).mpr ⟨by omega, by omega⟩
  obtain ⟨c0, hc⟩ := allA_spec _ M a b c _ S hall (iota_pairwise n 0) (mem _ (by omega))
    (mem _ (by omega)) (mem _ hcn) hab' hbc'
  revert hc; generalize dc c0 = cert; intro hc
  rw [li3', ← onN_iff]
  have hD : ev r (col a 0) * ev r (col b 1) * ev r (col c 2)
      - ev r (col a 0) * ev r (col b 2) * ev r (col c 1)
      - ev r (col a 1) * ev r (col b 0) * ev r (col c 2)
      + ev r (col a 1) * ev r (col b 2) * ev r (col c 0)
      + ev r (col a 2) * ev r (col b 0) * ev r (col c 1)
      - ev r (col a 2) * ev r (col b 1) * ev r (col c 0)
      = ev r (detP col a b c) - ev r (detN col a b c) := by
    simp only [detP, detN, xP_0, xP_1, xP_2, xN_0, xN_1, xN_2, ev_padd, ev_pmul]; ring
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [hD]
  simp only [checkTriple] at hc
  cases hon : onN linesN a b c
  · rw [hon, Bool.cond_false] at hc
    have e := ev_of_peq r _ _ hc
    rw [ev_pmul, ev_padd, ev_padd, ev_pmul, ev_pmul, hr, mul_zero, add_zero] at e
    simp only [Bool.false_eq_true, not_false_eq_true, iff_true]
    intro h0
    have : ev r cert.1 * (ev r (detP col a b c) - ev r (detN col a b c)) = ev r [1] := by
      rw [mul_sub, e]; ring
    rw [h0, mul_zero] at this
    simp [ev] at this
  · rw [hon, Bool.cond_true] at hc
    have e := ev_of_peq r _ _ hc
    rw [ev_padd, ev_pmul, hr, mul_zero, add_zero] at e
    simp [e]

end GPCert
/-! ## GPCert part 2: a given root, and integer certificates outside a set of primes

The map-rule shards at characteristic `p` use part 1 alone. Points use the source polynomial `X`
with root `0`. Outside a prime set `S` (and in characteristic `0`) the checker works over `ℤ`:
on a line the determinant is `q f`; off every line `g det = U + q f`, where `U` is a product of
powers of members of `S` (each checked prime), so `U ≠ 0` in every field with `ringChar ∉ S`. -/

namespace GPCert
open Polynomial

/-- Part 1's conclusion at a given root `r` of the source polynomial (no algebraic closure). -/
theorem realizes_of_certOk_at {n : ℕ} (lines : List (Finset (Fin n))) (linesN : List (List ℕ))
    (p : ℕ) (fl : List ℕ) (col : ℕ → ℕ → List ℕ) (dc : ℕ → List ℕ × List ℕ) (M : ℕ)
    (L : List ℕ) (S : ℕ) (h : certOk lines linesN p fl col dc M L S = true)
    (K : Type*) [Field K] [CharP K p] (r : K) (hr : ev r (fl ++ [1]) = 0) :
    ∃ v : Fin n → Fin 3 → K, RealizesRank3 lines v := by
  have hne : fl ≠ [] := by
    rintro rfl; cases (h : false = true)
  have h' : (decide (lines = linesN.map toFS) && (listBeq L (iota 0 n) &&
      allA (fun a b c s => checkTriple linesN p (appendR fl [1]) col a b c (dc s)) M L S)) = true := by
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne; exact h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, appendR_eq] at h'
  obtain ⟨hl, hL, hall⟩ := h'
  subst hl
  have hL := listBeq_eq _ _ hL
  subst hL
  refine ⟨fun i j => ev r (col i j), ?_⟩
  intro a b c hab hbc
  have hab' := Fin.lt_def.mp hab; have hbc' := Fin.lt_def.mp hbc; have hcn := c.isLt
  have mem : ∀ x : ℕ, x < n → x ∈ iota 0 n := fun x hx => (mem_iota x n 0).mpr ⟨by omega, by omega⟩
  obtain ⟨c0, hc⟩ := allA_spec _ M a b c _ S hall (iota_pairwise n 0) (mem _ (by omega))
    (mem _ (by omega)) (mem _ hcn) hab' hbc'
  revert hc; generalize dc c0 = cert; intro hc
  rw [li3', ← onN_iff]
  have hD : ev r (col a 0) * ev r (col b 1) * ev r (col c 2)
      - ev r (col a 0) * ev r (col b 2) * ev r (col c 1)
      - ev r (col a 1) * ev r (col b 0) * ev r (col c 2)
      + ev r (col a 1) * ev r (col b 2) * ev r (col c 0)
      + ev r (col a 2) * ev r (col b 0) * ev r (col c 1)
      - ev r (col a 2) * ev r (col b 1) * ev r (col c 0)
      = ev r (detP col a b c) - ev r (detN col a b c) := by
    simp only [detP, detN, xP_0, xP_1, xP_2, xN_0, xN_1, xN_2, ev_padd, ev_pmul]; ring
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [hD]
  simp only [checkTriple] at hc
  cases hon : onN linesN a b c
  · rw [hon, Bool.cond_false] at hc
    have e := ev_of_peq r _ _ hc
    rw [ev_pmul, ev_padd, ev_padd, ev_pmul, ev_pmul, hr, mul_zero, add_zero] at e
    simp only [Bool.false_eq_true, not_false_eq_true, iff_true]
    intro h0
    have : ev r cert.1 * (ev r (detP col a b c) - ev r (detN col a b c)) = ev r [1] := by
      rw [mul_sub, e]; ring
    rw [h0, mul_zero] at this
    simp [ev] at this
  · rw [hon, Bool.cond_true] at hc
    have e := ev_of_peq r _ _ hc
    rw [ev_padd, ev_pmul, hr, mul_zero, add_zero] at e
    simp [e]

/-- Points at characteristic `p`: constant columns, source polynomial `X`, root `0`. -/
theorem realizes_of_certOk_X {n : ℕ} (lines : List (Finset (Fin n))) (linesN : List (List ℕ))
    (p : ℕ) (col : ℕ → ℕ → List ℕ) (dc : ℕ → List ℕ × List ℕ) (M : ℕ) (L : List ℕ) (S : ℕ)
    (h : certOk lines linesN p [0] col dc M L S = true) (K : Type*) [Field K] [CharP K p] :
    ∃ v : Fin n → Fin 3 → K, RealizesRank3 lines v :=
  realizes_of_certOk_at lines linesN p [0] col dc M L S h K 0 (by simp [ev])

/-! ### Integer polynomials (low degree first) -/

noncomputable def zadd (a : List ℤ) : List ℤ → List ℤ :=
  List.rec (motive := fun _ => List ℤ → List ℤ) (fun b => b)
    (fun x xs ih b => List.casesOn (motive := fun _ => List ℤ) b (x :: xs)
      (fun y ys => Int.add x y :: ih ys)) a

noncomputable def zscale (c : ℤ) (b : List ℤ) : List ℤ :=
  List.rec (motive := fun _ => List ℤ) [] (fun y _ ih => Int.mul c y :: ih) b

noncomputable def zmul (a b : List ℤ) : List ℤ :=
  List.rec (motive := fun _ => List ℤ) [] (fun c _ ih => zadd (zscale c b) (Int.ofNat 0 :: ih)) a

noncomputable def zneg (a : List ℤ) : List ℤ :=
  List.rec (motive := fun _ => List ℤ) [] (fun x _ ih => Int.neg x :: ih) a

noncomputable def isZ (x : ℤ) : Bool := Int.casesOn (motive := fun _ => Bool) x (fun m => Nat.beq m 0) (fun _ => false)

/-- `a = b` as integer polynomials. -/
noncomputable def zeq (a b : List ℤ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => and (isZ x) ih) (zadd a (zneg b))

/-- Zigzag decoding: `2k ↦ k`, `2k + 1 ↦ -(k + 1)`. -/
noncomputable def zz (m : ℕ) : ℤ :=
  cond (Nat.beq (Nat.mod m 2) 0) (Int.ofNat (Nat.div m 2)) (Int.negSucc (Nat.div m 2))

/-- Base-`B` zigzag digits of `x`, low first, at most `D` of them (stops at zero). -/
noncomputable def decZ (B D x : ℕ) : List ℤ :=
  Nat.rec (motive := fun _ => ℕ → List ℤ) (fun _ => [])
    (fun _ ih x => cond (Nat.beq x 0) [] (zz (Nat.mod x B) :: ih (Nat.div x B))) D x

noncomputable def colOfZ (B D : ℕ) (vecsN : List ℕ) (i j : ℕ) : List ℤ :=
  decZ B D (nthD 0 vecsN (Nat.add (Nat.mul 3 i) j))

noncomputable def certOfZ (B D G c : ℕ) : List ℤ × List ℤ := (decZ B D (Nat.mod c G), decZ B D (Nat.div c G))

/-- Coordinate `j` of the cross product of columns `a`, `b`. -/
noncomputable def zx (col : ℕ → ℕ → List ℤ) (a b j : ℕ) : List ℤ :=
  Nat.casesOn (motive := fun _ => List ℤ) j (zadd (zmul (col a 1) (col b 2)) (zneg (zmul (col a 2) (col b 1))))
    fun j => Nat.casesOn (motive := fun _ => List ℤ) j
      (zadd (zmul (col a 2) (col b 0)) (zneg (zmul (col a 0) (col b 2))))
      fun _ => zadd (zmul (col a 0) (col b 1)) (zneg (zmul (col a 1) (col b 0)))

theorem zx_0 (col : ℕ → ℕ → List ℤ) (a b : ℕ) :
    zx col a b 0 = zadd (zmul (col a 1) (col b 2)) (zneg (zmul (col a 2) (col b 1))) := rfl
theorem zx_1 (col : ℕ → ℕ → List ℤ) (a b : ℕ) :
    zx col a b 1 = zadd (zmul (col a 2) (col b 0)) (zneg (zmul (col a 0) (col b 2))) := rfl
theorem zx_2 (col : ℕ → ℕ → List ℤ) (a b : ℕ) :
    zx col a b 2 = zadd (zmul (col a 0) (col b 1)) (zneg (zmul (col a 1) (col b 0))) := rfl

noncomputable def zdet (col : ℕ → ℕ → List ℤ) (a b c : ℕ) : List ℤ :=
  zadd (zmul (zx col a b 0) (col c 0)) (zadd (zmul (zx col a b 1) (col c 1)) (zmul (zx col a b 2) (col c 2)))

noncomputable def checkTripleZ (linesN : List (List ℕ)) (U : ℕ) (f : List ℤ)
    (col : ℕ → ℕ → List ℤ) (a b c : ℕ) (cert : List ℤ × List ℤ) : Bool :=
  cond (onN linesN a b c)
    (zeq (zdet col a b c) (zmul cert.2 f))
    (zeq (zmul cert.1 (zdet col a b c)) (zadd [Int.ofNat U] (zmul cert.2 f)))

noncomputable def allR {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => and (f x) ih) l

/-- Trial division. -/
noncomputable def primeB (s : ℕ) : Bool :=
  and (Nat.ble 2 s) (allR (fun m => not (Nat.beq (Nat.mod s m) 0)) (iota 2 (Nat.sub s 2)))

/-- `∏ s_i ^ e_i` over the scope list `Sl` and exponents `es`. -/
noncomputable def unitOf (Sl : List ℕ) : List ℕ → ℕ :=
  List.rec (motive := fun _ => List ℕ → ℕ) (fun _ => 1)
    (fun s _ ih es => List.casesOn (motive := fun _ => ℕ) es 1 (fun e es => Nat.mul (Nat.pow s e) (ih es))) Sl

/-- The integer checker: every member of `Sl` is prime, the lines and index list are the
challenge's, and every triple has a passing certificate for `U = unitOf Sl es`. -/
noncomputable def certOkZ {n : ℕ} (lines : List (Finset (Fin n))) (linesN : List (List ℕ))
    (Sl es : List ℕ) (fl : List ℤ) (col : ℕ → ℕ → List ℤ) (dc : ℕ → List ℤ × List ℤ) (M : ℕ)
    (L : List ℕ) (S : ℕ) : Bool :=
  and (List.casesOn (motive := fun _ => Bool) fl false (fun _ _ => true))
    (and (allR primeB Sl) (and (decide (lines = linesN.map toFS))
      (and (listBeq L (iota 0 n))
        (allA (fun a b c s => checkTripleZ linesN (unitOf Sl es) (appendR fl [Int.ofNat 1]) col a b c (dc s))
          M L S))))

/-! ### Soundness of the integer checker -/

theorem allR_iff {α : Type} (f : α → Bool) : ∀ l, allR f l = true ↔ ∀ x ∈ l, f x = true
  | [] => by simp [allR]
  | x :: xs => by
      show (f x && allR f xs) = true ↔ _
      rw [Bool.and_eq_true, allR_iff f xs]; simp

theorem prime_of_primeB (s : ℕ) (h : primeB s = true) : s.Prime := by
  have h' : (Nat.ble 2 s && allR (fun m => !Nat.beq (s % m) 0) (iota 2 (s - 2))) = true := h
  rw [Bool.and_eq_true, Nat.ble_eq, allR_iff] at h'
  refine Nat.prime_def_lt'.mpr ⟨h'.1, fun m hm hms hd => ?_⟩
  have := h'.2 m ((mem_iota m (s - 2) 2).mpr ⟨hm, by omega⟩)
  simp [Nat.mod_eq_zero_of_dvd hd] at this

theorem unitOf_ne_zero {K : Type*} [Field K] (Sl : List ℕ) (hS : ∀ s ∈ Sl, s.Prime)
    (hK : ringChar K ∉ Sl) : ∀ es, ((unitOf Sl es : ℕ) : K) ≠ 0 := by
  induction Sl with
  | nil => intro es; simp [unitOf]
  | cons s Sl ih =>
    intro es
    cases es with
    | nil => simp [unitOf]
    | cons e es =>
      show (((s ^ e * unitOf Sl es : ℕ)) : K) ≠ 0
      have hs : (s : K) ≠ 0 := by
        intro h0
        have hd := ringChar.dvd h0
        rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | hq
        · exact hK (by rw [(Nat.prime_dvd_prime_iff_eq hq (hS s (by simp))).mp hd]; simp)
        · rw [hq, zero_dvd_iff] at hd; exact (hS s (by simp)).ne_zero hd
      push_cast
      exact mul_ne_zero (pow_ne_zero _ hs)
        (ih (fun t ht => hS t (by simp [ht])) (fun h => hK (by simp [h])) es)

section SoundZ
variable {K : Type*} [Field K]

/-- Evaluation of an integer coefficient list at `r`. -/
def evZ (r : K) : List ℤ → K
  | [] => 0
  | c :: cs => (c : K) + r * evZ r cs

theorem evZ_zadd (r : K) : ∀ a b, evZ r (zadd a b) = evZ r a + evZ r b
  | [], b => by show evZ r b = evZ r [] + evZ r b; simp [evZ]
  | x :: xs, [] => by show evZ r (x :: xs) = evZ r (x :: xs) + evZ r []; simp [evZ]
  | x :: xs, y :: ys => by
      show evZ r ((x + y) :: zadd xs ys) = _
      simp only [evZ, evZ_zadd r xs ys]; push_cast; ring

theorem evZ_zscale (r : K) (c : ℤ) : ∀ b, evZ r (zscale c b) = c * evZ r b
  | [] => by show evZ r [] = c * evZ r []; simp [evZ]
  | y :: ys => by
      show evZ r ((c * y) :: zscale c ys) = _
      simp only [evZ, evZ_zscale r c ys]; push_cast; ring

theorem evZ_zmul (r : K) : ∀ a b, evZ r (zmul a b) = evZ r a * evZ r b
  | [], b => by show evZ r [] = evZ r [] * evZ r b; simp [evZ]
  | c :: cs, b => by
      show evZ r (zadd (zscale c b) (0 :: zmul cs b)) = _
      simp only [evZ_zadd, evZ_zscale, evZ, evZ_zmul r cs b]; push_cast; ring

theorem evZ_zneg (r : K) : ∀ a, evZ r (zneg a) = - evZ r a
  | [] => by show evZ r [] = - evZ r []; simp [evZ]
  | x :: xs => by
      show evZ r ((-x) :: zneg xs) = _
      simp only [evZ, evZ_zneg r xs]; push_cast; ring

theorem evZ_of_zero (r : K) : ∀ a : List ℤ,
    List.rec (motive := fun _ => Bool) true (fun x _ ih => and (isZ x) ih) a = true → evZ r a = 0
  | [] => fun _ => rfl
  | x :: xs => by
      intro h
      have h' : (isZ x && List.rec (motive := fun _ => Bool) true (fun x _ ih => and (isZ x) ih) xs) = true := h
      rw [Bool.and_eq_true] at h'
      have hx : x = 0 := by
        cases x with
        | ofNat m => have : Nat.beq m 0 = true := h'.1; rw [Nat.beq_eq] at this; subst this; rfl
        | negSucc m => cases (h'.1 : false = true)
      simp [evZ, hx, evZ_of_zero r xs h'.2]

theorem evZ_of_zeq (r : K) (a b : List ℤ) (h : zeq a b = true) : evZ r a = evZ r b := by
  have := evZ_of_zero r _ h
  rw [evZ_zadd, evZ_zneg] at this
  linear_combination this

theorem evZ_append_one (r : K) : ∀ l : List ℤ, evZ r (l ++ [1]) = evZ r l + r ^ l.length
  | [] => by simp [evZ]
  | c :: cs => by simp only [List.cons_append, evZ, evZ_append_one r cs, List.length_cons]; ring

noncomputable def toPolyZ : List ℤ → K[X]
  | [] => 0
  | c :: cs => C (c : K) + X * toPolyZ cs

theorem eval_toPolyZ (r : K) : ∀ l, (toPolyZ l).eval r = evZ r l
  | [] => by simp [toPolyZ, evZ]
  | c :: cs => by simp [toPolyZ, evZ, eval_toPolyZ r cs]

theorem degree_toPolyZ_lt : ∀ l : List ℤ, (toPolyZ (K := K) l).degree < l.length
  | [] => by simp [toPolyZ]
  | c :: cs => by
      rw [Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      cases m with
      | zero => simp at hm
      | succ m =>
        have ih := (Polynomial.degree_lt_iff_coeff_zero _ _).mp (degree_toPolyZ_lt cs) m
          (by simp at hm; omega)
        simp only [toPolyZ, coeff_add, coeff_C_succ, coeff_X_mul, ih, add_zero]

theorem exists_rootZ [IsAlgClosed K] (fl : List ℤ) (hne : fl ≠ []) :
    ∃ r : K, evZ r (fl ++ [1]) = 0 := by
  have hlt : (toPolyZ (K := K) fl).degree < ((X : K[X]) ^ fl.length).degree := by
    rw [degree_X_pow]; exact degree_toPolyZ_lt fl
  have hdeg : ((X : K[X]) ^ fl.length + toPolyZ fl).degree = (fl.length : WithBot ℕ) := by
    rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
  have hlen : fl.length ≠ 0 := by simpa using hne
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root ((X : K[X]) ^ fl.length + toPolyZ fl)
    (by rw [hdeg]; exact_mod_cast hlen)
  refine ⟨r, ?_⟩
  rw [evZ_append_one]
  simpa [IsRoot, eval_toPolyZ, add_comm] using hr

end SoundZ

/-- Soundness of the integer checker at a given root, for every field with `ringChar K ∉ Sl`. -/
theorem realizesZ_of_certOk_at {n : ℕ} (lines : List (Finset (Fin n))) (linesN : List (List ℕ))
    (Sl es : List ℕ) (fl : List ℤ) (col : ℕ → ℕ → List ℤ) (dc : ℕ → List ℤ × List ℤ) (M : ℕ)
    (L : List ℕ) (S : ℕ) (h : certOkZ lines linesN Sl es fl col dc M L S = true)
    (K : Type*) [Field K] (hK : ringChar K ∉ Sl) (r : K) (hr : evZ r (fl ++ [1]) = 0) :
    ∃ v : Fin n → Fin 3 → K, RealizesRank3 lines v := by
  have hne : fl ≠ [] := by
    rintro rfl; cases (h : false = true)
  have h' : (allR primeB Sl && (decide (lines = linesN.map toFS) && (listBeq L (iota 0 n) &&
      allA (fun a b c s => checkTripleZ linesN (unitOf Sl es) (appendR fl [Int.ofNat 1]) col a b c (dc s))
        M L S))) = true := by
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne; exact h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, appendR_eq, allR_iff] at h'
  obtain ⟨hS, hl, hL, hall⟩ := h'
  have hU := unitOf_ne_zero (K := K) Sl (fun s hs => prime_of_primeB s (hS s hs)) hK es
  subst hl
  have hL := listBeq_eq _ _ hL
  subst hL
  have hr' : evZ r (fl ++ [Int.ofNat 1]) = 0 := hr
  refine ⟨fun i j => evZ r (col i j), ?_⟩
  intro a b c hab hbc
  have hab' := Fin.lt_def.mp hab; have hbc' := Fin.lt_def.mp hbc; have hcn := c.isLt
  have mem : ∀ x : ℕ, x < n → x ∈ iota 0 n := fun x hx => (mem_iota x n 0).mpr ⟨by omega, by omega⟩
  obtain ⟨c0, hc⟩ := allA_spec _ M a b c _ S hall (iota_pairwise n 0) (mem _ (by omega))
    (mem _ (by omega)) (mem _ hcn) hab' hbc'
  revert hc; generalize dc c0 = cert; intro hc
  rw [li3', ← onN_iff]
  have hD : evZ r (col a 0) * evZ r (col b 1) * evZ r (col c 2)
      - evZ r (col a 0) * evZ r (col b 2) * evZ r (col c 1)
      - evZ r (col a 1) * evZ r (col b 0) * evZ r (col c 2)
      + evZ r (col a 1) * evZ r (col b 2) * evZ r (col c 0)
      + evZ r (col a 2) * evZ r (col b 0) * evZ r (col c 1)
      - evZ r (col a 2) * evZ r (col b 1) * evZ r (col c 0)
      = evZ r (zdet col a b c) := by
    simp only [zdet, zx_0, zx_1, zx_2, evZ_zadd, evZ_zmul, evZ_zneg]; ring
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [hD]
  simp only [checkTripleZ] at hc
  cases hon : onN linesN a b c
  · rw [hon, Bool.cond_false] at hc
    have e := evZ_of_zeq r _ _ hc
    rw [evZ_zmul, evZ_zadd, evZ_zmul, hr', mul_zero, add_zero] at e
    simp only [Bool.false_eq_true, not_false_eq_true, iff_true]
    intro h0
    rw [h0, mul_zero] at e
    apply hU
    have : evZ r [Int.ofNat (unitOf Sl es)] = ((unitOf Sl es : ℕ) : K) := by simp [evZ]
    rw [← this, ← e]
  · rw [hon, Bool.cond_true] at hc
    have e := evZ_of_zeq r _ _ hc
    rw [evZ_zmul, hr', mul_zero] at e
    simp [e]

/-- The integer checker over algebraically closed fields outside `Sl`. -/
theorem realizesZ_of_certOk {n : ℕ} (lines : List (Finset (Fin n))) (linesN : List (List ℕ))
    (Sl es : List ℕ) (fl : List ℤ) (col : ℕ → ℕ → List ℤ) (dc : ℕ → List ℤ × List ℤ) (M : ℕ)
    (L : List ℕ) (S : ℕ) (h : certOkZ lines linesN Sl es fl col dc M L S = true)
    (K : Type*) [Field K] [IsAlgClosed K] (hK : ringChar K ∉ Sl) :
    ∃ v : Fin n → Fin 3 → K, RealizesRank3 lines v := by
  have hne : fl ≠ [] := by
    rintro rfl; cases (h : false = true)
  obtain ⟨r, hr⟩ := exists_rootZ (K := K) fl hne
  exact realizesZ_of_certOk_at lines linesN Sl es fl col dc M L S h K hK r hr

/-- Integer points outside `Sl`: constant columns, source polynomial `X`, root `0`. -/
theorem realizesZ_of_certOk_X {n : ℕ} (lines : List (Finset (Fin n))) (linesN : List (List ℕ))
    (Sl es : List ℕ) (col : ℕ → ℕ → List ℤ) (dc : ℕ → List ℤ × List ℤ) (M : ℕ) (L : List ℕ) (S : ℕ)
    (h : certOkZ lines linesN Sl es [0] col dc M L S = true) (K : Type*) [Field K]
    (hK : ringChar K ∉ Sl) : ∃ v : Fin n → Fin 3 → K, RealizesRank3 lines v :=
  realizesZ_of_certOk_at lines linesN Sl es [0] col dc M L S h K hK 0 (by simp [evZ])

end GPCert
