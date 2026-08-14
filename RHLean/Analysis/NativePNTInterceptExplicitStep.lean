import Mathlib
import RHLean.Analysis.NativePNTInterceptTail

noncomputable section

namespace RHLean.Analysis

/-- One calibrated cubic step propagates the explicit finite-prefix intercept. -/
theorem nativePNTAffineEnvelopeAt_cubic_step
    (alpha D : ℝ) (halpha : 0 < alpha) (halpha6 : alpha ≤ 6)
    (henvAt : NativePNTAffineEnvelopeAt alpha D) :
    NativePNTAffineEnvelopeAt
      (alpha - nativePNTCubicStepDelta alpha)
      (D + nativePNTCubicStepDelta alpha *
        (nativePNTCubicStepOnset alpha D : ℝ)) := by
  rcases henvAt with ⟨hD, henv⟩
  let delta : ℝ := nativePNTCubicStepDelta alpha
  let M : ℕ := nativePNTCubicStepOnset alpha D
  have hdelta : 0 < delta := by
    dsimp [delta]
    rw [nativePNTCubicStepDelta_eq]
    exact mul_pos
      (by norm_num [nativePNTCubicConstant])
      (pow_pos halpha 3)
  unfold NativePNTAffineEnvelopeAt
  change
    0 ≤ D + delta * (M : ℝ) ∧
      ∀ N : ℕ,
        |nativePNTError N| ≤
          (alpha - delta) * (N : ℝ) + (D + delta * (M : ℝ))
  refine ⟨add_nonneg hD (mul_nonneg hdelta.le (by positivity)), ?_⟩
  intro N
  by_cases hMN : M ≤ N
  · have htail := nativePNTError_abs_le_cubicStep_tail
      alpha D halpha halpha6 ⟨hD, henv⟩ N
      (by simpa [M] using hMN)
    have htail' :
        |nativePNTError N| ≤ (alpha - delta) * (N : ℝ) := by
      simpa [delta] using htail
    have hintercept0 : 0 ≤ D + delta * (M : ℝ) :=
      add_nonneg hD (mul_nonneg hdelta.le (by positivity))
    exact htail'.trans (le_add_of_nonneg_right hintercept0)
  · have hNM : N ≤ M := Nat.le_of_lt (lt_of_not_ge hMN)
    have hNMR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
    have hdeltaNM := mul_le_mul_of_nonneg_left hNMR hdelta.le
    have hold := henv N
    have htarget :
        alpha * (N : ℝ) + D ≤
          (alpha - delta) * (N : ℝ) +
            (D + delta * (M : ℝ)) := by
      nlinarith [hdeltaNM]
    exact hold.trans htarget

end RHLean.Analysis
