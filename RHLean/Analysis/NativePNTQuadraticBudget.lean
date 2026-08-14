import RHLean.Analysis.NativePNTReciprocalSquareCore
import RHLean.Analysis.NativePNTErdosContraction

/-!
# Quadratic iteration budget for the native PNT cubic slope

The already-proved exact recurrence gives a stronger finite rate than the
existing `eta^(-3)` budget: reciprocal-square growth yields an `eta^(-2)`
iteration budget with no new number-theoretic premise.
-/

noncomputable section

namespace RHLean.Analysis

/-- The original native PNT cubic sequence has linear reciprocal-square growth. -/
theorem nativePNTCubicSlope_inv_sq_rate (n : ℕ) :
    (1 : ℝ) / 36 + 2 * nativePNTCubicConstant * (n : ℝ) ≤
      1 / (nativePNTCubicSlope n) ^ 2 := by
  have h := inv_sq_rate_of_exact_cubic_recurrence
    nativePNTCubicSlope nativePNTCubicConstant
    (by norm_num [nativePNTCubicConstant])
    (fun m => (nativePNTCubicSlope_spec m).1)
    (fun m => nativePNTCubicSlope_succ m) n
  have h6 : (6 : ℝ) ^ 2 = 36 := by norm_num
  simpa [nativePNTCubicSlope_zero, h6] using h

/-- Equivalent direct rate: `2 C n a_n^2 <= 1`. -/
theorem nativePNTCubicSlope_quadratic_rate (n : ℕ) :
    2 * nativePNTCubicConstant * (n : ℝ) *
        (nativePNTCubicSlope n) ^ 2 ≤ 1 := by
  have hinv := nativePNTCubicSlope_inv_sq_rate n
  have hdrop :
      2 * nativePNTCubicConstant * (n : ℝ) ≤
        1 / (nativePNTCubicSlope n) ^ 2 := by
    have hbase : 0 ≤ (1 : ℝ) / 36 := by norm_num
    linarith
  have hslope : 0 < nativePNTCubicSlope n :=
    (nativePNTCubicSlope_spec n).1
  have hmul := mul_le_mul_of_nonneg_right hdrop
    (sq_nonneg (nativePNTCubicSlope n))
  calc
    2 * nativePNTCubicConstant * (n : ℝ) *
          (nativePNTCubicSlope n) ^ 2 ≤
        (1 / (nativePNTCubicSlope n) ^ 2) *
          (nativePNTCubicSlope n) ^ 2 := by
      simpa [mul_assoc] using hmul
    _ = 1 := by
      field_simp [ne_of_gt hslope]

/-- **Quadratic iteration budget.**  A budget of order `eta^(-2)` suffices to
produce an affine Chebyshev envelope with slope `eta`. -/
theorem nativePNTHasAffineEnvelope_of_quadratic_budget
    (eta : ℝ) (heta : 0 < eta) (n : ℕ)
    (hbudget :
      1 < 2 * nativePNTCubicConstant * (n : ℝ) * eta ^ 2) :
    nativePNTHasAffineEnvelope eta := by
  have hspec := nativePNTCubicSlope_spec n
  have hrate := nativePNTCubicSlope_quadratic_rate n
  have hslopeEta : nativePNTCubicSlope n ≤ eta := by
    by_contra hnot
    have hetaSlope : eta < nativePNTCubicSlope n := lt_of_not_ge hnot
    have hsq : eta ^ 2 ≤ (nativePNTCubicSlope n) ^ 2 :=
      pow_le_pow_left₀ heta.le hetaSlope.le 2
    have hcoef0 :
        0 ≤ 2 * nativePNTCubicConstant * (n : ℝ) := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) (by norm_num [nativePNTCubicConstant]))
        (by positivity)
    have hmul :
        2 * nativePNTCubicConstant * (n : ℝ) * eta ^ 2 ≤
          2 * nativePNTCubicConstant * (n : ℝ) *
            (nativePNTCubicSlope n) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcoef0
    have hone :
        1 < 2 * nativePNTCubicConstant * (n : ℝ) *
          (nativePNTCubicSlope n) ^ 2 := hbudget.trans_le hmul
    linarith
  exact nativePNTHasAffineEnvelope_mono hslopeEta hspec.2.2

end RHLean.Analysis
