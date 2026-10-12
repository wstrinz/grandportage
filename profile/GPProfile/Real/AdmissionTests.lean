import GPProfile.Real.Admission

/-!
Build-time checks (`#guard`) of 3b admission: receipts per family and scope, the refusing controls
(GP-A10-C: an SOS certificate offered at a characteristic-0 `alg` scope), 3a receipts and rules on
`alg` clauses, binding discipline, and the kind-1 rules K1a and K1b with their controls.
-/

namespace GPProfile.Real.AdmissionTests
open GPProfile GPProfile.Real GP50

private def p (vars : List String) (t : String) : Sparse :=
  match parse vars t with
  | .ok q => (canonical vars.length q).getD q
  | .error _ => []

private def x := ["x"]

private def bind (k : Nat) : Binding := ⟨s!"stmt{k}", s!"scope{k}", "model", [], "gp", 1, 50⟩

private def clause (k : Nat) (s : Stmt3) (sc : Scope3) : Clause3 := ⟨k, 1, bind k, s, sc⟩

private def warrant (id k : Nat) (e : Evidence) : Warrant := ⟨id, k, 1, bind k, e⟩

private def receipt (name : String) (k : Nat) (c : Cert3) : Receipt3 := ⟨name, k, 1, bind k, c⟩

/-- Does admission accept a receipt for claim `k` alone? -/
private def acceptsOne (s : Stmt3) (sc : Scope3) (c : Cert3) : Bool :=
  (admission3 [clause 1 s sc] [receipt "r" 1 c] []).receipt (warrant 0 1 (.receipt "r")) "r"

/-! ## SOS receipts: GP-A10-Q, GP-A10-R, and the refusing control GP-A10-C -/

-- x² + 1 = 0 has no point; 1 + x² − (x² + 1) = 0.
private def a10 : Stmt := ⟨x, [p x "x^2+1"], [], .empty⟩
private def a10Cert : PCert := ⟨[p x "-1"], 0, [.squares [(1, p x "x")]], none⟩

-- GP-A10-Q (ℚ is semireal) and GP-A10-R: accepted at `semireal` and at `real`.
#guard acceptsOne (.orderFree a10) .semireal (.sos a10Cert)
#guard acceptsOne (.orderFree a10) .real (.sos a10Cert)
-- GP-A10-C, GP-X345: the same certificate at a characteristic-0 `alg` scope is refused, for the
-- 3a statement and for the order-free one.
#guard !acceptsOne (.alg a10) (.alg Scope.char0Only) (.sos a10Cert)
#guard !acceptsOne (.orderFree a10) (.alg Scope.char0Only) (.sos a10Cert)
#guard !acceptsOne (.alg a10) .semireal (.sos a10Cert)
-- A false certificate is refused (GP-X01).
#guard !acceptsOne (.orderFree a10) .semireal (.sos ⟨[p x "1"], 0, [.squares [(1, p x "x")]], none⟩)

/-! ## 3a receipts on `alg` -/

-- x² = 1 has the rational point 1.
private def circ : Stmt := ⟨x, [p x "x^2-1"], [], .nonempty⟩
#guard acceptsOne (.alg circ) (.alg (Scope.outside [])) (.alg (.point .rat [1]))
#guard !acceptsOne (.alg circ) (.alg (Scope.outside [])) (.alg (.point .rat [2]))
-- A 3a certificate never supports the real family.
#guard !acceptsOne (.orderFree circ) .real (.alg (.point .rat [1]))
#guard !acceptsOne (.orderFree circ) .semireal (.alg (.point .rat [1]))

/-! ## `algPoint` receipts: NOT_IN_IDEAL(1) at characteristic 0 -/

-- x² + 1 = 0, x ≠ 0: θ = i, m = t² + 1, x = t; −t·t + 1·(t² + 1) = 1.
private def iCircle : Stmt := ⟨x, [p x "x^2+1"], [p x "x"], .notInIdeal (oneP 1)⟩
private def iCert : AlgPointCert := ⟨[1, 0, 1], [[0, 1]], [([0, -1], [1])]⟩
#guard acceptsOne (.alg iCircle) (.alg Scope.char0Only) (.algPoint iCert)
-- Refused at any scope containing a prime, and outside the `alg` family.
#guard !acceptsOne (.alg iCircle) (.alg (Scope.outside [])) (.algPoint iCert)
#guard !acceptsOne (.alg iCircle) (.alg ⟨true, .finite [5]⟩) (.algPoint iCert)
#guard !acceptsOne (.alg iCircle) (.alg (Scope.only 2)) (.algPoint iCert)
#guard !acceptsOne (.orderFree iCircle) .real (.algPoint iCert)
#guard !acceptsOne (.orderFree iCircle) .semireal (.algPoint iCert)
-- A wrong Bezout certificate is refused.
#guard !acceptsOne (.alg iCircle) (.alg Scope.char0Only) (.algPoint ⟨[1, 0, 1], [[0, 1]], [([0, 1], [1])]⟩)

/-! ## Point receipts -/

-- √2: x² − 2 = 0, x > 0, at the root of x² − 2 in [1, 2].
private def sqrt2 : RealSys := ⟨x, [p x "x^2-2"], [], [(p x "x", 1)]⟩
private def theta : RealWitness := ⟨[-2, 0, 1], 1, 2, [[0, 1]]⟩
#guard acceptsOne (.real sqrt2 .nonempty) .real (.point theta)
-- The wrong sign, an EMPTY claim, and the `semireal` scope (ℚ has no √2) are refused.
#guard !acceptsOne (.real { sqrt2 with signs := [(p x "x", -1)] } .nonempty) .real (.point theta)
#guard !acceptsOne (.real sqrt2 .empty) .real (.point theta)
#guard !acceptsOne (.real sqrt2 .nonempty) .semireal (.point theta)
-- Order-free NONEMPTY at `real` by a point; refused at `semireal` and for an EMPTY statement.
private def two : Stmt := ⟨x, [p x "x^2-2"], [], .nonempty⟩
#guard acceptsOne (.orderFree two) .real (.point theta)
#guard !acceptsOne (.orderFree two) .semireal (.point theta)
#guard !acceptsOne (.orderFree { two with kind := .empty }) .real (.point theta)
#guard !acceptsOne (.alg two) (.alg Scope.char0Only) (.point theta)

/-! ## Binding discipline -/

private def a10Clause : Clause3 := clause 1 (.orderFree a10) .semireal
-- A receipt naming another claim, version or binding is refused (detached receipts, GP-X02).
#guard !(admission3 [a10Clause] [receipt "r" 2 (.sos a10Cert)] []).receipt (warrant 0 1 (.receipt "r")) "r"
#guard !(admission3 [a10Clause] [{ receipt "r" 1 (.sos a10Cert) with version := 2 }] []).receipt
  (warrant 0 1 (.receipt "r")) "r"
#guard !(admission3 [a10Clause] [{ receipt "r" 1 (.sos a10Cert) with binding := bind 2 }] []).receipt
  (warrant 0 1 (.receipt "r")) "r"
-- A warrant whose binding differs from the clause's is refused.
#guard !(admission3 [a10Clause] [receipt "r" 1 (.sos a10Cert)] []).receipt
  { warrant 0 1 (.receipt "r") with binding := bind 2 } "r"
-- Duplicate claim keys or receipt names refuse everything.
#guard !(admission3 [a10Clause, a10Clause] [receipt "r" 1 (.sos a10Cert)] []).receipt
  (warrant 0 1 (.receipt "r")) "r"
#guard !(admission3 [a10Clause] [receipt "r" 1 (.sos a10Cert), receipt "r" 1 (.sos a10Cert)] []).receipt
  (warrant 0 1 (.receipt "r")) "r"

/-! ## Kind-1 rules -/

-- x² = 0, x ≠ 0 is empty in every field: x² = 1·x² (C1 with guard power 2).
private def e0 : Stmt := ⟨x, [p x "x^2"], [p x "x"], .empty⟩
private def e0Cert : Cert := .ideal .rat [p x "1"] 0 2
#guard acceptsOne (.alg e0) (.alg Scope.char0Only) (.alg e0Cert)

/-- Does the single rule `name` derive claim 2 from claim 1? -/
private def derives (prem concl : Clause3) (d : RuleData3) : Bool :=
  (admission3 [prem, concl] [] [⟨"k", 2, [1], d⟩]).rule (warrant 1 2 (.derived [0] "k"))
    [warrant 0 1 (.receipt "r")] "k"

-- K1a from an EMPTY claim at characteristic 0 only: accepted, at `semireal` and at `real`.
#guard derives (clause 1 (.alg e0) (.alg Scope.char0Only)) (clause 2 (.orderFree e0) .semireal) .k1Empty
#guard derives (clause 1 (.alg e0) (.alg (Scope.outside []))) (clause 2 (.orderFree e0) .real) .k1Empty
-- K1a from a scope without characteristic 0 is refused.
#guard !derives (clause 1 (.alg e0) (.alg (Scope.only 2))) (clause 2 (.orderFree e0) .semireal) .k1Empty
-- K1a refuses another statement, another kind, an `alg` conclusion, and an `alg` target scope.
#guard !derives (clause 1 (.alg e0) (.alg Scope.char0Only)) (clause 2 (.orderFree a10) .semireal) .k1Empty
#guard !derives (clause 1 (.alg circ) (.alg Scope.char0Only)) (clause 2 (.orderFree circ) .semireal) .k1Empty
#guard !derives (clause 1 (.alg e0) (.alg Scope.char0Only)) (clause 2 (.alg e0) .semireal) .k1Empty
#guard !derives (clause 1 (.alg e0) (.alg Scope.char0Only)) (clause 2 (.orderFree e0) (.alg Scope.char0Only))
  .k1Empty
-- K1b: NONEMPTY at characteristic 0 reaches `real`, and only `real`.
#guard derives (clause 1 (.alg circ) (.alg Scope.char0Only)) (clause 2 (.orderFree circ) .real) .k1Nonempty
#guard !derives (clause 1 (.alg circ) (.alg Scope.char0Only)) (clause 2 (.orderFree circ) .semireal) .k1Nonempty
#guard !derives (clause 1 (.alg circ) (.alg (Scope.only 3))) (clause 2 (.orderFree circ) .real) .k1Nonempty
#guard !derives (clause 1 (.alg e0) (.alg Scope.char0Only)) (clause 2 (.orderFree e0) .real) .k1Nonempty
-- No rule goes back: the real family never derives an `alg` claim.
#guard !derives (clause 1 (.orderFree e0) .semireal) (clause 2 (.alg e0) (.alg Scope.char0Only)) .k1Empty

/-! ## 3a rules, lifted -/

-- The bridge: NONEMPTY gives NOT_IN_IDEAL(1) on the same system.
private def circNI : Stmt := { circ with kind := .notInIdeal (oneP 1) }
#guard derives (clause 1 (.alg circ) (.alg (Scope.outside []))) (clause 2 (.alg circNI) (.alg Scope.char0Only))
  (.lift .witness)
-- The conclusion scope must lie inside the premise's (3a's check).
#guard !derives (clause 1 (.alg circ) (.alg Scope.char0Only)) (clause 2 (.alg circNI) (.alg (Scope.outside [])))
  (.lift .witness)
-- 3a rules never act on the real family.
#guard !derives (clause 1 (.orderFree circ) .real) (clause 2 (.orderFree circNI) .real) (.lift .witness)
#guard !derives (clause 1 (.alg circ) (.alg (Scope.outside []))) (clause 2 (.orderFree circNI) .real)
  (.lift .witness)

/-! ## End to end: a held 3a EMPTY claim reaches `semireal` by K1a, and `real` by narrowing -/

private def e2eClauses : List Clause3 :=
  [clause 1 (.alg e0) (.alg Scope.char0Only), clause 2 (.orderFree e0) .semireal,
    { clause 3 (.orderFree e0) .real with binding := { bind 2 with scopeHash := "scope3" } }]

private def e2eEvents (w1 : Warrant) : List Event :=
  [.declareClaim 1, .current ⟨1, 1, bind 1⟩, .warrant w1,
   .declareClaim 2, .current ⟨2, 1, bind 2⟩, .warrant (warrant 11 2 (.derived [10] "k1a")),
   .declareClaim 3, .current ⟨3, 1, { bind 2 with scopeHash := "scope3" }⟩,
   .warrant ⟨12, 3, 1, { bind 2 with scopeHash := "scope3" }, .narrow 11⟩]

private def e2eHeld (w1 : Warrant) (receipts : List Receipt3) : List Bool :=
  match fold (admission3 e2eClauses receipts [⟨"k1a", 2, [1], .k1Empty⟩]) (e2eEvents w1) with
  | .ok st => [held st 1, held st 2, held st 3]
  | .error _ => []

#guard e2eHeld (warrant 10 1 (.receipt "r1")) [receipt "r1" 1 (.alg e0Cert)] == [true, true, true]
-- Without the 3a receipt nothing is held.
#guard e2eHeld (warrant 10 1 (.receipt "r1")) [] == [false, false, false]

end GPProfile.Real.AdmissionTests
