import Mathlib
import RHLean.Analysis.NativePNTOptimalInterceptStep
import RHLean.Analysis.NativePNTQuadraticBudget

noncomputable section

namespace RHLean.Analysis

/-- The current absorption threshold survives after replacing the propagated
witness by the genuinely optimal old intercept. -/
theorem nativePNTCubicOptimalIntercept_onset_log_lower (n : ℕ) :
    (3000 * nativePNTCubicSlope n +
        784 * nativePNTCubicOptimalIntercept n + 3000) /
        (3 * (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3)) ≤
      Real.log
        ((nativePNTCubicStepOnset
          (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) : ℕ) : ℝ) := by
  have hspec := nativePNTCubicSlope_spec n
  have henv := nativePNTCubicOptimalIntercept_envelope n
  have h := nativePNTCubicStepOnset_log_lower
    (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n)
    hspec.1 hspec.2.1 henv.1
  simpa [nativePNTCubicStepC0, nativePNTCubicStepDelta_eq] using h

/-- At the first contraction the present proof already requires an enormous
onset: `log M_0 >= 36,400,000,000`. -/
theorem nativePNTCubicOptimalIntercept_onset_zero_log_lower :
    (36400000000 : ℝ) ≤
      Real.log
        ((nativePNTCubicStepOnset 6 0 : ℕ) : ℝ) := by
  have h := nativePNTCubicOptimalIntercept_onset_log_lower 0
  norm_num [nativePNTCubicSlope_zero, nativePNTCubicConstant] at h
  exact h

/-- A polynomial lower bound already follows from the current logarithmic
absorption threshold.  In particular the onset cannot have any of the mild
scales needed for linear or quadratic intercept propagation. -/
theorem nativePNTCubicOptimalIntercept_onset_poly_lower (n : ℕ) :
    (1000 : ℝ) /
        (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3) ≤
      (nativePNTCubicStepOnset
        (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) : ℝ) := by
  have hspec := nativePNTCubicSlope_spec n
  have ha : 0 < nativePNTCubicSlope n := hspec.1
  have hD : 0 ≤ nativePNTCubicOptimalIntercept n :=
    (nativePNTCubicOptimalIntercept_envelope n).1
  have hC : 0 < nativePNTCubicConstant := by
    norm_num [nativePNTCubicConstant]
  have hden :
      0 < 3 *
        (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3) := by
    positivity
  have hnum :
      (3000 : ℝ) ≤
        3000 * nativePNTCubicSlope n +
          784 * nativePNTCubicOptimalIntercept n + 3000 := by
    nlinarith [ha.le, hD]
  have hfrac :
      (3000 : ℝ) /
          (3 * (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3)) ≤
        (3000 * nativePNTCubicSlope n +
            784 * nativePNTCubicOptimalIntercept n + 3000) /
          (3 * (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3)) :=
    (div_le_div_iff_of_pos_right hden).2 hnum
  have hrewrite :
      (1000 : ℝ) /
          (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3) =
        (3000 : ℝ) /
          (3 * (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3)) := by
    field_simp [ne_of_gt hC, ne_of_gt ha]
    norm_num
  have hlog := nativePNTCubicOptimalIntercept_onset_log_lower n
  have hM3 := nativePNTCubicStepOnset_three_le
    (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n)
    ha hspec.2.1 hD
  have hMposNat :
      0 < nativePNTCubicStepOnset
        (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) := by
    omega
  have hMpos :
      (0 : ℝ) <
        (nativePNTCubicStepOnset
          (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) : ℝ) := by
    exact_mod_cast hMposNat
  have hlogle := Real.log_le_sub_one_of_pos hMpos
  calc
    (1000 : ℝ) /
          (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3) =
        (3000 : ℝ) /
          (3 * (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3)) := hrewrite
    _ ≤ (3000 * nativePNTCubicSlope n +
            784 * nativePNTCubicOptimalIntercept n + 3000) /
          (3 * (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3)) := hfrac
    _ ≤ Real.log
          ((nativePNTCubicStepOnset
            (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) : ℕ) : ℝ) := hlog
    _ ≤ (nativePNTCubicStepOnset
          (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) : ℝ) := by
      linarith

/-- The onset scale sufficient for a linear-in-`a_n` intercept update is in
fact at least `1000 / a_n` in the current proof. -/
theorem nativePNTCubicOptimalIntercept_linear_onset_scale_lower (n : ℕ) :
    (1000 : ℝ) / nativePNTCubicSlope n ≤
      nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 2 *
        (nativePNTCubicStepOnset
          (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) : ℝ) := by
  have ha : 0 < nativePNTCubicSlope n :=
    (nativePNTCubicSlope_spec n).1
  have hC : 0 < nativePNTCubicConstant := by
    norm_num [nativePNTCubicConstant]
  have hM := nativePNTCubicOptimalIntercept_onset_poly_lower n
  have hcoef :
      0 ≤ nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 2 := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hM hcoef
  calc
    (1000 : ℝ) / nativePNTCubicSlope n =
        (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 2) *
          ((1000 : ℝ) /
            (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3)) := by
      field_simp [ne_of_gt hC, ne_of_gt ha]
    _ ≤ (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 2) *
          (nativePNTCubicStepOnset
            (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) : ℝ) := hmul
    _ = nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 2 *
          (nativePNTCubicStepOnset
            (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) : ℝ) := by
      ring

/-- The stronger onset scale sufficient for a quadratic-in-`a_n` intercept
update is at least `1000 / a_n^2`. -/
theorem nativePNTCubicOptimalIntercept_quadratic_onset_scale_lower (n : ℕ) :
    (1000 : ℝ) / (nativePNTCubicSlope n) ^ 2 ≤
      nativePNTCubicConstant * nativePNTCubicSlope n *
        (nativePNTCubicStepOnset
          (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) : ℝ) := by
  have ha : 0 < nativePNTCubicSlope n :=
    (nativePNTCubicSlope_spec n).1
  have hC : 0 < nativePNTCubicConstant := by
    norm_num [nativePNTCubicConstant]
  have hM := nativePNTCubicOptimalIntercept_onset_poly_lower n
  have hcoef :
      0 ≤ nativePNTCubicConstant * nativePNTCubicSlope n := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hM hcoef
  calc
    (1000 : ℝ) / (nativePNTCubicSlope n) ^ 2 =
        (nativePNTCubicConstant * nativePNTCubicSlope n) *
          ((1000 : ℝ) /
            (nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3)) := by
      field_simp [ne_of_gt hC, ne_of_gt ha]
    _ ≤ (nativePNTCubicConstant * nativePNTCubicSlope n) *
          (nativePNTCubicStepOnset
            (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) : ℝ) := hmul
    _ = nativePNTCubicConstant * nativePNTCubicSlope n *
          (nativePNTCubicStepOnset
            (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) : ℝ) := by
      ring

/-- Combining the previous obstruction with reciprocal-square growth shows
that the scale needed for a quadratic intercept update already grows at least
linearly in the iteration index. -/
theorem nativePNTCubicOptimalIntercept_quadratic_onset_scale_linear_lower
    (n : ℕ) :
    1000 * ((1 : ℝ) / 36 +
        2 * nativePNTCubicConstant * (n : ℝ)) ≤
      nativePNTCubicConstant * nativePNTCubicSlope n *
        (nativePNTCubicStepOnset
          (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) : ℝ) := by
  have hinv := nativePNTCubicSlope_inv_sq_rate n
  have hmul := mul_le_mul_of_nonneg_left hinv
    (show (0 : ℝ) ≤ 1000 by norm_num)
  calc
    1000 * ((1 : ℝ) / 36 +
          2 * nativePNTCubicConstant * (n : ℝ)) ≤
        1000 * (1 / (nativePNTCubicSlope n) ^ 2) := hmul
    _ = (1000 : ℝ) / (nativePNTCubicSlope n) ^ 2 := by ring
    _ ≤ nativePNTCubicConstant * nativePNTCubicSlope n *
          (nativePNTCubicStepOnset
            (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) : ℝ) :=
      nativePNTCubicOptimalIntercept_quadratic_onset_scale_lower n

end RHLean.Analysis
