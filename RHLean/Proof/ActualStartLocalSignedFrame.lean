import Mathlib
import RHLean.Proof.ActualStartSignedFrame

noncomputable section

open scoped BigOperators InnerProductSpace

namespace RHLean.Analysis

open RHLean.Verification

/-- Energy of the actual-start coefficients on the half-open window `[N, N + H)`. -/
def actualStartLocalFrameEnergy
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (N H : ℕ) : ℝ :=
  ∑ h ∈ Finset.range H, ‖start.actual (N + h)‖ ^ 2

/-- Prediction energy on the half-open window `[N, N + H)`. -/
def actualStartLocalPredictionFrameEnergy
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (N H : ℕ) : ℝ :=
  ∑ h ∈ Finset.range H, ‖start.prediction (N + h)‖ ^ 2

/-- Residual energy on the half-open window `[N, N + H)`. -/
def actualStartLocalResidualFrameEnergy
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (N H : ℕ) : ℝ :=
  ∑ h ∈ Finset.range H, ‖actualResidual (data (N + h))‖ ^ 2

/-- Signed prediction-residual interaction on the window `[N, N + H)`. -/
def actualStartLocalSignedInteraction
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (N H : ℕ) : ℝ :=
  2 * ∑ h ∈ Finset.range H,
    shellReInner (𝕜 := ℂ) ((2 : ℂ) • start.prediction (N + h))
      (actualResidual (data (N + h)))

/-- Exact signed energy identity on every finite window `[N, N + H)`. -/
theorem actualStart_localFrame_energy_identity
    (skeleton : ResonantProjectionSkeleton ℂ ℂ)
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (start : ActualStartConfiguration skeleton data)
    (N H : ℕ) :
    actualStartLocalFrameEnergy start N H =
      4 * actualStartLocalPredictionFrameEnergy start N H +
        actualStartLocalResidualFrameEnergy data N H +
          actualStartLocalSignedInteraction start N H := by
  unfold actualStartLocalFrameEnergy actualStartLocalPredictionFrameEnergy
    actualStartLocalResidualFrameEnergy actualStartLocalSignedInteraction
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _hh
  exact actualStart_energy_identity_at skeleton data start (N + h)

/-- A pointwise residual-energy bound gives the exact window-length residual bound. -/
theorem actualStart_localResidualFrameEnergy_le
    (skeleton : ResonantProjectionSkeleton ℂ ℂ)
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (bound : ℝ)
    (hbound : ∀ M, ‖actualResidual (data M)‖ ^ 2 ≤ bound)
    (N H : ℕ) :
    actualStartLocalResidualFrameEnergy data N H ≤ (H : ℝ) * bound := by
  unfold actualStartLocalResidualFrameEnergy
  calc
    (∑ h ∈ Finset.range H, ‖actualResidual (data (N + h))‖ ^ 2) ≤
        ∑ _h ∈ Finset.range H, bound := by
      exact Finset.sum_le_sum fun h _hh => hbound (N + h)
    _ = (H : ℝ) * bound := by simp

/--
Uniform local signed absorption. Prefix absorption from zero does not imply this
windowed condition by subtraction, so the local hypothesis is deliberately
separate from `ActualStartSignedFrameControl`.
-/
structure ActualStartLocalSignedFrameControl
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bound : ℝ) where
  interaction_le :
    ∀ N H,
      actualStartLocalSignedInteraction start N H ≤ -((H : ℝ) * bound)

/--
A uniform residual-energy bound and uniform local signed absorption give the
sharp constant-`4` frame inequality on every finite window.
-/
theorem actualStart_localSignedFrame_of_uniform_residual_bound
    (skeleton : ResonantProjectionSkeleton ℂ ℂ)
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (start : ActualStartConfiguration skeleton data)
    (bound : ℝ)
    (hbound : ∀ M, ‖actualResidual (data M)‖ ^ 2 ≤ bound)
    (frameControl : ActualStartLocalSignedFrameControl start bound) :
    ∀ N H,
      actualStartLocalFrameEnergy start N H ≤
        4 * actualStartLocalPredictionFrameEnergy start N H := by
  intro N H
  rw [actualStart_localFrame_energy_identity skeleton data start N H]
  have hresidual :=
    actualStart_localResidualFrameEnergy_le skeleton data bound hbound N H
  have hinteraction := frameControl.interaction_le N H
  linarith

/--
Uniform local actual-start signed-frame theorem obtained from the compiled
uniform residual closure. Every finite-range, asymptotic, and local signed
interaction hypothesis remains explicit.
-/
theorem actualStart_localSignedFrame
    (skeleton : ResonantProjectionSkeleton ℂ ℂ)
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (expectation : FiniteRangeCertificateExpectation)
    (realization : ActualFiniteRangeJointGramRealization
      skeleton data expectation)
    (weights : BlockLyapunovWeights)
    (forcingData : ActualForcingData)
    (asymptoticControl : ActualJointGramAsymptoticControl
      skeleton data weights forcingData
        realization.accepted.certificate.rangeEnd)
    (start : ActualStartConfiguration skeleton data)
    (frameControl : ActualStartLocalSignedFrameControl start
      (affineInvariantBound asymptoticControl.rho
        asymptoticControl.forcingBound
        (finiteRangeCertificateBaseBound realization.accepted.certificate))) :
    ∀ N H,
      actualStartLocalFrameEnergy start N H ≤
        4 * actualStartLocalPredictionFrameEnergy start N H := by
  apply actualStart_localSignedFrame_of_uniform_residual_bound
    skeleton data start
    (affineInvariantBound asymptoticControl.rho
      asymptoticControl.forcingBound
      (finiteRangeCertificateBaseBound realization.accepted.certificate))
  · exact uniform_actualResidual_energy_bound
      skeleton data expectation realization weights forcingData asymptoticControl
  · exact frameControl

/-- The uniform local frame theorem specializes to the original prefix theorem at `N = 0`. -/
theorem actualStart_signedFrame_of_localSignedFrame
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (hlocal : ∀ N H,
      actualStartLocalFrameEnergy start N H ≤
        4 * actualStartLocalPredictionFrameEnergy start N H) :
    ∀ H,
      actualStartFrameEnergy start H ≤
        4 * actualStartPredictionFrameEnergy start H := by
  intro H
  simpa [actualStartLocalFrameEnergy, actualStartLocalPredictionFrameEnergy,
    actualStartFrameEnergy, actualStartPredictionFrameEnergy] using hlocal 0 H

end RHLean.Analysis