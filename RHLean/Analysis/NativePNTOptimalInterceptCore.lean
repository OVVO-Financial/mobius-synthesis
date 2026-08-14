import Mathlib
import RHLean.Analysis.NativePNTInterceptRecurrence

noncomputable section

namespace RHLean.Analysis

/-- Pointwise nonnegative residual after subtracting slope `alpha`. -/
def nativePNTAffineResidual (alpha : ℝ) (N : ℕ) : ℝ :=
  max 0 (|nativePNTError N| - alpha * (N : ℝ))

/-- Least affine-envelope intercept at slope `alpha`, when such an envelope exists. -/
noncomputable def nativePNTAffineOptimalIntercept (alpha : ℝ) : ℝ :=
  sSup (Set.range (nativePNTAffineResidual alpha))

private theorem nativePNTAffineResidual_bddAbove_of_envelope
    {alpha D : ℝ} (henv : NativePNTAffineEnvelopeAt alpha D) :
    BddAbove (Set.range (nativePNTAffineResidual alpha)) := by
  refine ⟨D, ?_⟩
  rintro x ⟨N, rfl⟩
  unfold nativePNTAffineResidual
  apply max_le
  · exact henv.1
  · linarith [henv.2 N]

/-- Every residual is bounded by the optimal intercept. -/
theorem nativePNTAffineResidual_le_optimal
    {alpha D : ℝ} (henv : NativePNTAffineEnvelopeAt alpha D) (N : ℕ) :
    nativePNTAffineResidual alpha N ≤ nativePNTAffineOptimalIntercept alpha := by
  unfold nativePNTAffineOptimalIntercept
  exact le_csSup
    (nativePNTAffineResidual_bddAbove_of_envelope henv)
    ⟨N, rfl⟩

/-- The supremum residual is itself an admissible affine intercept. -/
theorem nativePNTAffineOptimalIntercept_envelope
    {alpha D : ℝ} (henv : NativePNTAffineEnvelopeAt alpha D) :
    NativePNTAffineEnvelopeAt alpha (nativePNTAffineOptimalIntercept alpha) := by
  constructor
  · have hres := nativePNTAffineResidual_le_optimal henv 0
    have hzero : 0 ≤ nativePNTAffineResidual alpha 0 := by
      unfold nativePNTAffineResidual
      exact le_max_left _ _
    exact hzero.trans hres
  · intro N
    have hres := nativePNTAffineResidual_le_optimal henv N
    unfold nativePNTAffineResidual at hres
    have hdiff :
        |nativePNTError N| - alpha * (N : ℝ) ≤
          nativePNTAffineOptimalIntercept alpha := by
      exact (le_max_right 0
        (|nativePNTError N| - alpha * (N : ℝ))).trans hres
    linarith

/-- Minimality among all admissible nonnegative intercepts. -/
theorem nativePNTAffineOptimalIntercept_le_of_envelope
    {alpha D : ℝ} (henv : NativePNTAffineEnvelopeAt alpha D) :
    nativePNTAffineOptimalIntercept alpha ≤ D := by
  unfold nativePNTAffineOptimalIntercept
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨N, rfl⟩
  unfold nativePNTAffineResidual
  apply max_le
  · exact henv.1
  · linarith [henv.2 N]

end RHLean.Analysis
