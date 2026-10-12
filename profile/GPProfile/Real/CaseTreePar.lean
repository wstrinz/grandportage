import GPProfile.Real.CaseTree

/-!
A case tree replayed with its node checks in parallel (ud22 performance, DECISIONS 2026-10-10).
`caseTreeCheckPar` evaluates every collision, unit-step and ordered-leaf check of `caseTreeGo` in its
own task and conjoins them; it is proved equal to `caseTreeCheck` (`caseTreeCheckPar_eq`), which it
replaces in compiled code (`@[csimp]`). `GPBinding.Real.CaseTree.caseTreeCheck_sound` applies unchanged.
-/

namespace GPProfile.Real
open GPProfile

/-- The checks `caseTreeGo` conjoins, one per collision, unit step and ordered leaf, in its order. -/
def caseTreeObl (pts : List (Nat × Nat)) : RealSys → CaseTree → List (Unit → Bool)
  | r, .collision c => [fun _ => collisionOk r.vars.length pts r c]
  | r, .unit d t => (fun _ => unitOk r.vars.length pts r d) :: caseTreeObl pts (r.addEq (unitEq r.vars.length pts d)) t
  | r, .ordered c => [fun _ => orderedCheck r c]
  | r, .zero p t f => caseTreeObl pts (r.addEq p) t ++ caseTreeObl pts (r.addGuard p) f
  | r, .sign p n z q =>
    caseTreeObl pts (r.addSign p (-1)) n ++ caseTreeObl pts (r.addSign p 0) z ++ caseTreeObl pts (r.addSign p 1) q

theorem caseTreeGo_obl (pts : List (Nat × Nat)) (r : RealSys) (t : CaseTree) :
    caseTreeGo pts r t = (caseTreeObl pts r t).all (· ()) := by
  induction t generalizing r with
  | collision c => simp [caseTreeGo, caseTreeObl]
  | unit d t ih => simp [caseTreeGo, caseTreeObl, ih]
  | ordered c => simp [caseTreeGo, caseTreeObl]
  | zero p t f iht ihf => simp [caseTreeGo, caseTreeObl, iht, ihf, List.all_append]
  | sign p n z q ihn ihz ihq => simp [caseTreeGo, caseTreeObl, ihn, ihz, ihq, List.all_append, Bool.and_assoc]

/-- `caseTreeCheck` with the node checks evaluated in parallel, one task each. -/
def caseTreeCheckPar (r : RealSys) (c : CaseTreeCert) : Bool :=
  pointsOk r c.points && (parEach (· ()) (caseTreeObl c.points r c.tree)).all id

theorem caseTreeCheckPar_eq (r : RealSys) (c : CaseTreeCert) : caseTreeCheckPar r c = caseTreeCheck r c := by
  simp [caseTreeCheckPar, caseTreeCheck, parEach_eq, caseTreeGo_obl, List.all_map, Function.comp_def]

@[csimp] theorem caseTreeCheck_eq_par : @caseTreeCheck = @caseTreeCheckPar := by
  funext r c
  exact (caseTreeCheckPar_eq r c).symm

end GPProfile.Real
