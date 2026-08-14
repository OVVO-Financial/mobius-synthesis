import RHLean.Analysis.NativePNTReciprocalSquareCore
import RHLean.Analysis.NativePNTSquarePrefixCubic

/-!
# Quadratic iteration budget for the rederived square-prefix PNT path

The independent square-prefix PNT recurrence is exact and positive, so the same
reciprocal-square argument improves its finite budget from `eta^(-3)` to
`eta^(-2)` without importing the legacy PNT conclusion.
-/

noncomputable section

namespace RHLean.Analysis

/-- The rederived square-prefix cubic slope has linear reciprocal-square growth. -/
theorem nativePNTSquarePrefixRederivedCubicSlope_inv_sq_rate (n : ℕ) :
    (1 : ℝ) / 36 +
        2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) ≤
      1 / (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 := by
  have h := inv_sq_rate_of_exact_cubic_recurrence
    nativePNTSquarePrefixRederivedCubicSlope
    nativePNTSquarePrefixRederivedCubicConstant
    (by norm_num [nativePNTSquarePrefixRederivedCubicConstant])
    (fun m => (nativePNTSquarePrefixRederivedCubicSlope_spec m).1)
    (fun m => nativePNTSquarePrefixRederivedCubicSlope_succ m) n
  have h6 : (6 : ℝ) ^ 2 = 36 := by norm_num
  simpa [nativePNTSquarePrefixRederivedCubicSlope_zero, h6] using h

/-- Equivalent direct square-prefix rate: `2 C n a_n^2 <= 1`. -/
theorem nativePNTSquarePrefixRederivedCubicSlope_quadratic_rate (n : ℕ) :
    2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) *
        (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 ≤ 1 := by
  have hinv := nativePNTSquarePrefixRederivedCubicSlope_inv_sq_rate n
  have hdrop :
      2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) ≤
        1 / (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 := by
    have hbase : 0 ≤ (1 : ℝ) / 36 := by norm_num
    linarith
  have hslope : 0 < nativePNTSquarePrefixRederivedCubicSlope n :=
    (nativePNTSquarePrefixRederivedCubicSlope_spec n).1
  have hmul := mul_le_mul_of_nonneg_right hdrop
    (sq_nonneg (nativePNTSquarePrefixRederivedCubicSlope n))
  calc
    2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) *
          (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 ≤
        (1 / (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2) *
          (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 := by
      simpa [mul_assoc] using hmul
    _ = 1 := by
      field_simp [ne_of_gt hslope]

/-- **Quadratic square-prefix iteration budget.** -/
theorem nativePNTSquarePrefixRederivedHasAffineEnvelope_of_quadratic_budget
    (eta : ℝ) (heta : 0 < eta) (n : ℕ)
    (hbudget :
      1 < 2 * nativePNTSquarePrefixRederivedCubicConstant *
        (n : ℝ) * eta ^ 2) :
    nativePNTHasAffineEnvelope eta := by
  have hspec := nativePNTSquarePrefixRederivedCubicSlope_spec n
  have hrate := nativePNTSquarePrefixRederivedCubicSlope_quadratic_rate n
  have hslopeEta : nativePNTSquarePrefixRederivedCubicSlope n ≤ eta := by
    by_contra hnot
    have hetaSlope : eta < nativePNTSquarePrefixRederivedCubicSlope n :=
      lt_of_not_ge hnot
    have hsq : eta ^ 2 ≤ (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 :=
      pow_le_pow_left₀ heta.le hetaSlope.le 2
    have hcoef0 :
        0 ≤ 2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) := by
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (by norm_num [nativePNTSquarePrefixRederivedCubicConstant]))
        (by positivity)
    have hmul :
        2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) * eta ^ 2 ≤
          2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) *
            (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcoef0
    have hone :
        1 < 2 * nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) *
          (nativePNTSquarePrefixRederivedCubicSlope n) ^ 2 :=
      hbudget.trans_le hmul
    linarith
  exact nativePNTHasAffineEnvelope_mono hslopeEta hspec.2.2

end RHLean.Analysis
