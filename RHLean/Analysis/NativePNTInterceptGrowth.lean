import Mathlib
import RHLean.Analysis.NativePNTInterceptRecurrence

/-!
# Growth diagnostics for the explicit native PNT intercept

The exact recurrence is `D_(n+1) = D_n + C * a_n^3 * M_n`.  This module
records the onset scale forced by the current lower-order absorption argument.
-/

noncomputable section

namespace RHLean.Analysis

/-- Exact logarithmic onset condition at step `n`. -/
theorem nativePNTCubicIntercept_onset_log_lower (n : ℕ) :
    (3000 * nativePNTCubicSlope n +
        784 * nativePNTCubicIntercept n + 3000) /
        (3 * (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3)) ≤
      Real.log
        ((nativePNTCubicStepOnset
          (nativePNTCubicSlope n) (nativePNTCubicIntercept n) : ℕ) : ℝ) := by
  have hspec := nativePNTCubicSlope_spec n
  have hD := nativePNTCubicIntercept_nonneg n
  have h := nativePNTCubicStepOnset_log_lower
    (nativePNTCubicSlope n) (nativePNTCubicIntercept n)
    hspec.1 hspec.2.1 hD
  simpa [nativePNTCubicStepC0, nativePNTCubicStepDelta_eq] using h

/-- Exponentiated form of the onset condition. -/
theorem nativePNTCubicIntercept_onset_exp_lower (n : ℕ) :
    Real.exp
      ((3000 * nativePNTCubicSlope n +
          784 * nativePNTCubicIntercept n + 3000) /
        (3 * (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3))) ≤
      (nativePNTCubicStepOnset
        (nativePNTCubicSlope n) (nativePNTCubicIntercept n) : ℝ) := by
  have hspec := nativePNTCubicSlope_spec n
  have hD := nativePNTCubicIntercept_nonneg n
  have h := nativePNTCubicStepOnset_exp_lower
    (nativePNTCubicSlope n) (nativePNTCubicIntercept n)
    hspec.1 hspec.2.1 hD
  simpa [nativePNTCubicStepC0, nativePNTCubicStepDelta_eq] using h

/-- The current proof's intercept increment is at least the cubic decrement
multiplied by the exponential absorption scale. -/
theorem nativePNTCubicInterceptIncrement_exp_lower (n : ℕ) :
    (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3) *
        Real.exp
          ((3000 * nativePNTCubicSlope n +
              784 * nativePNTCubicIntercept n + 3000) /
            (3 * (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3))) ≤
      nativePNTCubicInterceptIncrement n := by
  have hscale := nativePNTCubicIntercept_onset_exp_lower n
  have hcoef :
      0 ≤ nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3 := by
    exact mul_nonneg
      (by norm_num [nativePNTCubicConstant])
      (pow_nonneg (nativePNTCubicSlope_spec n).1.le 3)
  have hmul := mul_le_mul_of_nonneg_left hscale hcoef
  simpa [nativePNTCubicInterceptIncrement, mul_assoc] using hmul

end RHLean.Analysis
