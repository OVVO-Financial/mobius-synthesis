import Mathlib
import RHLean.Proof.HeightShellGram
import RHLean.Proof.UniformResidualBound

noncomputable section

open scoped BigOperators InnerProductSpace

namespace RHLean.Analysis

open RHLean.Verification

/--
The exact starting configuration for the signed-frame theorem. The actual
coefficient at scale `M` is the theorem-predicted leading coefficient `2 • P_M`
plus the compiled actual residual. This is an algebraic starting identity only;
it carries no orthogonality or sign claim.
-/
structure ActualStartConfiguration
    (skeleton : ResonantProjectionSkeleton ℂ ℂ)
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M) where
  prediction : ℕ → ℂ
  actual : ℕ → ℂ
  actual_eq :
    ∀ M, actual M = (2 : ℂ) • prediction M + actualResidual (data M)

/-- Prefix energy of the exact actual-start coefficients. -/
def actualStartFrameEnergy
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) (N : ℕ) : ℝ :=
  ∑ M ∈ Finset.range N, ‖start.actual M‖ ^ 2

/-- Prefix energy of the theorem-predicted leading coefficients. -/
def actualStartPredictionFrameEnergy
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) (N : ℕ) : ℝ :=
  ∑ M ∈ Finset.range N, ‖start.prediction M‖ ^ 2

/-- Prefix energy of the compiled actual residual. -/
def actualStartResidualFrameEnergy
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (N : ℕ) : ℝ :=
  ∑ M ∈ Finset.range N, ‖actualResidual (data M)‖ ^ 2

/--
The signed prediction-residual interaction retained by the exact starting
configuration. It may be negative and is not replaced by an absolute-value
estimate.
-/
def actualStartSignedInteraction
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) (N : ℕ) : ℝ :=
  2 * ∑ M ∈ Finset.range N,
    shellReInner (𝕜 := ℂ) ((2 : ℂ) • start.prediction M)
      (actualResidual (data M))

/-- Exact pointwise energy identity at the actual starting configuration. -/
theorem actualStart_energy_identity_at
    (skeleton : ResonantProjectionSkeleton ℂ ℂ)
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (start : ActualStartConfiguration skeleton data)
    (M : ℕ) :
    ‖start.actual M‖ ^ 2 =
      4 * ‖start.prediction M‖ ^ 2 +
        ‖actualResidual (data M)‖ ^ 2 +
          2 * shellReInner (𝕜 := ℂ)
            ((2 : ℂ) • start.prediction M)
            (actualResidual (data M)) := by
  rw [start.actual_eq M]
  rw [norm_add_sq (𝕜 := ℂ)]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [norm_smul, htwo]
  unfold shellReInner
  ring

/--
Exact prefix signed-frame identity. The residual energy and the signed
prediction-residual interaction remain separate terms.
-/
theorem actualStart_frame_energy_identity
    (skeleton : ResonantProjectionSkeleton ℂ ℂ)
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (start : ActualStartConfiguration skeleton data)
    (N : ℕ) :
    actualStartFrameEnergy start N =
      4 * actualStartPredictionFrameEnergy start N +
        actualStartResidualFrameEnergy data N +
          actualStartSignedInteraction start N := by
  unfold actualStartFrameEnergy actualStartPredictionFrameEnergy
    actualStartResidualFrameEnergy actualStartSignedInteraction
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro M _hM
  exact actualStart_energy_identity_at skeleton data start M

/-- A pointwise residual-energy bound gives its exact finite-prefix bound. -/
theorem actualStart_residualFrameEnergy_le
    (skeleton : ResonantProjectionSkeleton ℂ ℂ)
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (bound : ℝ)
    (hbound : ∀ M, ‖actualResidual (data M)‖ ^ 2 ≤ bound)
    (N : ℕ) :
    actualStartResidualFrameEnergy data N ≤ (N : ℝ) * bound := by
  unfold actualStartResidualFrameEnergy
  calc
    (∑ M ∈ Finset.range N, ‖actualResidual (data M)‖ ^ 2) ≤
        ∑ _M ∈ Finset.range N, bound := by
      exact Finset.sum_le_sum fun M _hM => hbound M
    _ = (N : ℝ) * bound := by simp

/--
The signed interaction required to absorb the accumulated uniform residual
budget. This condition is explicit because a residual norm bound alone cannot
imply the sharp constant-`4` frame inequality.
-/
structure ActualStartSignedFrameControl
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bound : ℝ) where
  interaction_le :
    ∀ N, actualStartSignedInteraction start N ≤ -((N : ℝ) * bound)

/--
A uniform residual-energy bound plus signed interaction absorption gives the
sharp actual-start frame inequality for every finite prefix.
-/
theorem actualStart_signedFrame_of_uniform_residual_bound
    (skeleton : ResonantProjectionSkeleton ℂ ℂ)
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (start : ActualStartConfiguration skeleton data)
    (bound : ℝ)
    (hbound : ∀ M, ‖actualResidual (data M)‖ ^ 2 ≤ bound)
    (frameControl : ActualStartSignedFrameControl start bound) :
    ∀ N,
      actualStartFrameEnergy start N ≤
        4 * actualStartPredictionFrameEnergy start N := by
  intro N
  rw [actualStart_frame_energy_identity skeleton data start N]
  have hresidual :=
    actualStart_residualFrameEnergy_le skeleton data bound hbound N
  have hinteraction := frameControl.interaction_le N
  linarith

/--
Actual-start signed-frame theorem obtained from the compiled uniform residual
closure. The finite-range realization, asymptotic full-joint control, exact
starting identity, and signed interaction absorption all remain explicit.
-/
theorem actualStart_signedFrame
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
    (frameControl : ActualStartSignedFrameControl start
      (affineInvariantBound asymptoticControl.rho
        asymptoticControl.forcingBound
        (finiteRangeCertificateBaseBound realization.accepted.certificate))) :
    ∀ N,
      actualStartFrameEnergy start N ≤
        4 * actualStartPredictionFrameEnergy start N := by
  apply actualStart_signedFrame_of_uniform_residual_bound
    skeleton data start
    (affineInvariantBound asymptoticControl.rho
      asymptoticControl.forcingBound
      (finiteRangeCertificateBaseBound realization.accepted.certificate))
  · exact uniform_actualResidual_energy_bound
      skeleton data expectation realization weights forcingData asymptoticControl
  · exact frameControl

end RHLean.Analysis
