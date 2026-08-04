/-
# The valuation spine of the JC `dm4` polynomial-lift conjecture

Let `a = dm1`, `b = dm2`, `c = dm3`, and `q = dm4`. At an irreducible
polynomial where a rational `q` has a pole, write their valuations as
`alpha`, `beta`, `gamma`, and `delta`, with the first three nonnegative and
`delta < 0`.

For nonzero `a`, `b`, and `c`, unique-minimum cancellation in G1 and G2 forces

  alpha + delta = beta + gamma
  beta + delta = 2 * gamma.

The exact payoff is that `v(c*q) = gamma + delta` is strictly below the lower
bounds for every other G3 term. Thus `c*q` is the unique minimum and G3 cannot
vanish. This file proves that integer-arithmetic spine. A full polynomial
theorem must still derive the balances using a genuine valuation and handle
the zero charts.
-/

import GrandPortage.RelationalTransport

namespace GrandPortage

structure JCDm4PolePattern where
  alpha : Int
  beta : Int
  gamma : Int
  delta : Int
  alpha_nonnegative : 0 ≤ alpha
  beta_nonnegative : 0 ≤ beta
  gamma_nonnegative : 0 ≤ gamma
  delta_is_pole : delta < 0
  g1_balance : alpha + delta = beta + gamma
  g2_balance : beta + delta = 2 * gamma

def JCDm4PolePattern.cqValuation (p : JCDm4PolePattern) : Int :=
  p.gamma + p.delta

theorem jcDm4_cq_is_unique_g3_minimum (p : JCDm4PolePattern) :
    p.cqValuation < p.alpha + p.beta ∧
    p.cqValuation < 2 * p.beta ∧
    p.cqValuation < 3 * p.alpha := by
  rcases p with
    ⟨alpha, beta, gamma, delta, hAlpha, hBeta, hGamma, hDelta,
      hG1, hG2⟩
  simp only [JCDm4PolePattern.cqValuation]
  omega

theorem jcDm4_no_cancellable_pole_pattern
    (p : JCDm4PolePattern)
    (g3_must_cancel :
      p.alpha + p.beta ≤ p.cqValuation ∨
      2 * p.beta ≤ p.cqValuation ∨
      3 * p.alpha ≤ p.cqValuation) :
    False := by
  have unique := jcDm4_cq_is_unique_g3_minimum p
  rcases g3_must_cancel with first | second | third
  · omega
  · omega
  · omega

end GrandPortage
