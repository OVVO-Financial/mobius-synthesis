import Mathlib
import RHLean.Analysis.NativePNTOptimalInterceptCore

noncomputable section

namespace RHLean.Analysis

/-- The starred intercept after `n` cubic contractions: the least admissible
intercept at the exact contracted slope `a_n`. -/
noncomputable def nativePNTCubicOptimalIntercept (n : ℕ) : ℝ :=
  nativePNTAffineOptimalIntercept (nativePNTCubicSlope n)

/-- `D_n^*` is itself a genuine affine envelope. -/
theorem nativePNTCubicOptimalIntercept_envelope (n : ℕ) :
    NativePNTAffineEnvelopeAt
      (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) := by
  unfold nativePNTCubicOptimalIntercept
  exact nativePNTAffineOptimalIntercept_envelope
    (nativePNTCubicIntercept_envelope n)

/-- The optimal intercept is no larger than the canonical propagated witness. -/
theorem nativePNTCubicOptimalIntercept_le_canonical (n : ℕ) :
    nativePNTCubicOptimalIntercept n ≤ nativePNTCubicIntercept n := by
  unfold nativePNTCubicOptimalIntercept
  exact nativePNTAffineOptimalIntercept_le_of_envelope
    (nativePNTCubicIntercept_envelope n)

/-- The initial optimal intercept is exactly zero. -/
@[simp] theorem nativePNTCubicOptimalIntercept_zero :
    nativePNTCubicOptimalIntercept 0 = 0 := by
  apply le_antisymm
  · simpa [nativePNTCubicOptimalIntercept, nativePNTCubicSlope_zero] using
      (nativePNTAffineOptimalIntercept_le_of_envelope
        nativePNTAffineEnvelopeAt_six_zero)
  · simpa [nativePNTCubicOptimalIntercept, nativePNTCubicSlope_zero] using
      (nativePNTAffineOptimalIntercept_envelope
        nativePNTAffineEnvelopeAt_six_zero).1

/-- **Optimal one-step intercept inequality.**  Removing witness-choice slack
still leaves the finite-prefix cost `delta * M` in the current proof. -/
theorem nativePNTCubicOptimalIntercept_succ_le (n : ℕ) :
    nativePNTCubicOptimalIntercept (n + 1) ≤
      nativePNTCubicOptimalIntercept n +
        nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3 *
          (nativePNTCubicStepOnset
            (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n) : ℝ) := by
  have hspec := nativePNTCubicSlope_spec n
  have henv := nativePNTCubicOptimalIntercept_envelope n
  have hstep := nativePNTAffineEnvelopeAt_cubic_step
    (nativePNTCubicSlope n) (nativePNTCubicOptimalIntercept n)
    hspec.1 hspec.2.1 henv
  have hmin := nativePNTAffineOptimalIntercept_le_of_envelope hstep
  simpa [nativePNTCubicOptimalIntercept, nativePNTCubicSlope_succ,
    nativePNTCubicStepDelta_eq, mul_assoc] using hmin

end RHLean.Analysis
