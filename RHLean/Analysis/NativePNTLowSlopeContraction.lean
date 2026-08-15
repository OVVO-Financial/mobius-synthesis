import Mathlib
import RHLean.Analysis.NativePNTErdosContraction

/-!
# Sharpen the native PNT cubic coefficient at low slope

The global PNT recurrence uses the convenient choice `beta = alpha / 6`.
For `alpha <= 3/2`, the existing deficit is proportional to
`(alpha-beta) * beta^2`, so the optimal admissible choice is
`beta = 2*alpha/3`.  This improves the cubic coefficient by `32/5 = 6.4`
without changing any analytic premise.
-/

noncomputable section

namespace RHLean.Analysis

/-- Improved cubic constant available once the affine PNT slope is at most
`3/2`. -/
def nativePNTLowSlopeCubicConstant : ℝ := 1 / 175500000

/-- The low-slope constant is exactly `32/5` times the global one. -/
theorem nativePNTLowSlopeCubicConstant_eq_scaled :
    nativePNTLowSlopeCubicConstant =
      (32 / 5 : ℝ) * nativePNTCubicConstant := by
  norm_num [nativePNTLowSlopeCubicConstant, nativePNTCubicConstant]

/-- **Sharpened low-slope PNT contraction.**  For `0 < alpha <= 3/2`, choosing
`beta = 2*alpha/3` improves one affine-envelope step from the global cubic
constant `1/1123200000` to `1/175500000`. -/
theorem nativePNTHasAffineEnvelope_lowSlope_cubic_step
    (alpha : ℝ) (halpha : 0 < alpha) (halphaSmall : alpha ≤ 3 / 2)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
      (alpha - nativePNTLowSlopeCubicConstant * alpha ^ 3) := by
  let beta : ℝ := 2 * alpha / 3
  have hbeta : 0 < beta := by
    dsimp [beta]
    positivity
  have hbeta0 : 0 ≤ beta := hbeta.le
  have hbeta1 : beta ≤ 1 := by
    dsimp [beta]
    nlinarith
  have hba : beta < alpha := by
    dsimp [beta]
    nlinarith
  let c : ℝ := beta ^ 2 / 6500000
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hprod : 0 ≤ beta * (1 - beta) :=
    mul_nonneg hbeta0 (sub_nonneg.mpr hbeta1)
  have hsq : beta ^ 2 ≤ 1 := by
    nlinarith
  have hc1 : c ≤ 1 := by
    dsimp [c]
    nlinarith
  have hgood : ∀ᶠ N : ℕ in Filter.atTop,
      c * (Real.log (N : ℝ)) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N beta := by
    simpa [c] using
      nativeLambdaTwoGoodRecipMass_eventually_quadratic_rate
        beta hbeta hbeta1
  have himp := nativePNTHasAffineEnvelope_improve_of_goodMass
    alpha beta c halpha hbeta0 hba hc hc1 hgood henv
  have hcoef :
      alpha - (alpha - beta) * c / 4 =
        alpha - nativePNTLowSlopeCubicConstant * alpha ^ 3 := by
    dsimp [beta, c, nativePNTLowSlopeCubicConstant]
    ring
  rw [hcoef] at himp
  exact himp

end RHLean.Analysis
