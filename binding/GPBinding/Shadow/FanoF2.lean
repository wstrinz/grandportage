import GPBinding.Shadow.Common

namespace GPBinding.Shadow
open GPBinding.Shadow

/-- GP-FANO-F2: the F_2 witness satisfies every incidence and no guard vanishes. -/
theorem fano_f2 : ∃ x5 y4 z4 z5 y7 z7 : ZMod 2, (z4 = 0 ∧ x5 = 0 ∧ 1 - y4 = 0 ∧ -x5*y4*z7 + x5*y7*z4 + y4*z5 - y7*z5 - z4 + z7 = 0 ∧ 1 - z5 = 0 ∧ 1 - z7 = 0 ∧ -y7 = 0) ∧ (z5 ≠ 0 ∧ z7 ≠ 0 ∧ -y4 ≠ 0 ∧ y4*z5 - z4 ≠ 0 ∧ y4 - z4 ≠ 0 ∧ y4*z7 - y7*z4 ≠ 0 ∧ -y7*z5 + z7 ≠ 0 ∧ -y7 + z7 ≠ 0 ∧ x5*z4 - z5 ≠ 0 ∧ z4 - 1 ≠ 0 ∧ z4 - z7 ≠ 0 ∧ -x5 + z5 ≠ 0 ∧ -x5*z7 + z5 ≠ 0 ∧ -x5*y4 + 1 ≠ 0 ∧ -y4 + y7 ≠ 0 ∧ x5 - 1 ≠ 0 ∧ x5*y7 - 1 ≠ 0 ∧ y7 - 1 ≠ 0 ∧ -x5*y4 + x5*z4 + y4*z5 - z4 - z5 + 1 ≠ 0 ∧ -y4*z7 + y4 + y7*z4 - y7 - z4 + z7 ≠ 0 ∧ -x5*y7 + x5*z7 + y7*z5 - z5 - z7 + 1 ≠ 0) :=
  ⟨0, 1, 0, 1, 0, 1, by decide⟩

end GPBinding.Shadow
