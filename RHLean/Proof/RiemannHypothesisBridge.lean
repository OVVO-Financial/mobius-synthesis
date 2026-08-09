import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RHLean.Proof.ActualStartLocalSignedFrame

noncomputable section

namespace RHLean.Analysis

open RHLean.Verification

/-- Mathlib's formal proposition expressing the Riemann Hypothesis. -/
def RiemannHypothesisStatement : Prop := RiemannHypothesis

/-- The sharp actual-start signed-frame statement on every local window. -/
def ActualStartLocalSignedFrameStatement
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) : Prop :=
  ∀ N H,
    actualStartLocalFrameEnergy start N H ≤
      4 * actualStartLocalPredictionFrameEnergy start N H

/--
The manuscript's uniform local square-prefix criterion:
`V_loc(N,H) ≪_ε H N^(2+ε)` uniformly for `1 ≤ H ≤ N`.
-/
def ActualStartUniformLocalBoundedStatement
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        actualStartLocalFrameEnergy start N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- The pointwise square-prefix bound obtained from the local criterion at `H = 1`. -/
def ActualStartPointwiseSquareBoundedStatement
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, 1 ≤ N →
        ‖start.actual N‖ ^ 2 ≤
          C * Real.rpow (N : ℝ) (2 + ε)

/-- Taking `H = 1` in the uniform local criterion gives the pointwise bound. -/
theorem actualStart_pointwiseSquareBounded_of_uniformLocalBounded
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (hlocal : ActualStartUniformLocalBoundedStatement start) :
    ActualStartPointwiseSquareBoundedStatement start := by
  intro ε hε
  rcases hlocal ε hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N hN
  have h := hbound N 1 (by simp) hN
  simpa [actualStartLocalFrameEnergy] using h

/--
The corrected explicit analytic bridge. The elementary localization step
`uniform local → pointwise` is proved above. The remaining fields isolate:

* the prediction estimate transporting the local signed-frame theorem to the
  manuscript's uniform local bound;
* the classical RH-to-local direction;
* the pointwise square-prefix/Mertens converse to RH.

No field is introduced as an axiom or treated as already proved.
-/
structure ActualStartRHBridge
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) where
  localSignedFrame_to_uniformLocalBounded :
    ActualStartLocalSignedFrameStatement start →
      ActualStartUniformLocalBoundedStatement start
  riemannHypothesis_to_uniformLocalBounded :
    RiemannHypothesisStatement →
      ActualStartUniformLocalBoundedStatement start
  pointwiseSquareBounded_to_riemannHypothesis :
    ActualStartPointwiseSquareBoundedStatement start →
      RiemannHypothesisStatement

/--
The manuscript's uniform local square-prefix criterion is equivalent to RH once
the two classical square-prefix/Mertens directions are explicitly supplied.
-/
theorem actualStart_uniformLocalBounded_iff_riemannHypothesis
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bridge : ActualStartRHBridge start) :
    ActualStartUniformLocalBoundedStatement start ↔
      RiemannHypothesisStatement := by
  constructor
  · intro hlocal
    exact bridge.pointwiseSquareBounded_to_riemannHypothesis
      (actualStart_pointwiseSquareBounded_of_uniformLocalBounded start hlocal)
  · exact bridge.riemannHypothesis_to_uniformLocalBounded

/-- An explicit corrected bridge converts a uniform local signed-frame theorem to RH. -/
theorem riemannHypothesis_of_actualStartLocalSignedFrame
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bridge : ActualStartRHBridge start)
    (hframe : ActualStartLocalSignedFrameStatement start) :
    RiemannHypothesisStatement := by
  apply (actualStart_uniformLocalBounded_iff_riemannHypothesis start bridge).mp
  exact bridge.localSignedFrame_to_uniformLocalBounded hframe

/--
Corrected final composition theorem. It uses the compiled uniform residual
closure plus a genuinely local signed-interaction control to prove the local
frame statement. The explicit analytic bridge then applies the manuscript's
uniform local criterion rather than the insufficient global cubic average.
-/
theorem riemannHypothesis_of_compiled_actualStartClosure
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
    (localFrameControl : ActualStartLocalSignedFrameControl start
      (affineInvariantBound asymptoticControl.rho
        asymptoticControl.forcingBound
        (finiteRangeCertificateBaseBound realization.accepted.certificate)))
    (bridge : ActualStartRHBridge start) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_actualStartLocalSignedFrame start bridge
  exact actualStart_localSignedFrame
    skeleton data expectation realization weights forcingData
      asymptoticControl start localFrameControl

end RHLean.Analysis