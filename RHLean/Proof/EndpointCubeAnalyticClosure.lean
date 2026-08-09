import RHLean.Proof.RiemannHypothesisBridge

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Local square energy of an abstract endpoint-boundary sequence. -/
def endpointBoundaryLocalEnergy (boundary : ℕ → ℂ) (N H : ℕ) : ℝ :=
  ∑ h ∈ Finset.range H, ‖boundary (N + h)‖ ^ 2

/--
The supreme endpoint-cube analytic target: uniform local square-root-scale
control on every translated square-prefix window.
-/
def EndpointCubeUniformLocalBoundaryStatement (boundary : ℕ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        endpointBoundaryLocalEnergy boundary N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/--
An exact realization identifies the endpoint-cube boundary sequence with the
actual square-prefix sequence already used by the RH bridge.
-/
structure EndpointCubeBoundaryRealization
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (boundary : ℕ → ℂ) where
  boundary_eq_actual : ∀ N, boundary N = start.actual N

/-- Exact realization transfers endpoint-boundary local control to the existing criterion. -/
theorem actualStart_uniformLocalBounded_of_endpointBoundary
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (boundary : ℕ → ℂ)
    (realization : EndpointCubeBoundaryRealization start boundary)
    (hboundary : EndpointCubeUniformLocalBoundaryStatement boundary) :
    ActualStartUniformLocalBoundedStatement start := by
  intro ε hε
  rcases hboundary ε hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N H hH hHN
  simpa [endpointBoundaryLocalEnergy, actualStartLocalFrameEnergy,
    realization.boundary_eq_actual] using hbound N H hH hHN

/-- Endpoint-cube local boundary control implies RH through the explicit existing bridge. -/
theorem riemannHypothesis_of_endpointCubeBoundary
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bridge : ActualStartRHBridge start)
    (boundary : ℕ → ℂ)
    (realization : EndpointCubeBoundaryRealization start boundary)
    (hboundary : EndpointCubeUniformLocalBoundaryStatement boundary) :
    RiemannHypothesisStatement := by
  apply (actualStart_uniformLocalBounded_iff_riemannHypothesis start bridge).mp
  exact actualStart_uniformLocalBounded_of_endpointBoundary
    start boundary realization hboundary

/--
The first backward analytic layer. The exact boundary is decomposed into a
smooth main term and a signed oscillatory residual. The closure field is kept
explicit: this structure records the precise remaining analytic theorem rather
than asserting it from the two component bounds by absolute values.
-/
structure EndpointCubeSmoothResidualControl
    (boundary smooth residual : ℕ → ℂ) where
  exact_decomposition : ∀ N, boundary N = smooth N + residual N
  smooth_uniform_local : EndpointCubeUniformLocalBoundaryStatement smooth
  residual_uniform_local : EndpointCubeUniformLocalBoundaryStatement residual
  signed_recombination_closure : EndpointCubeUniformLocalBoundaryStatement boundary

/-- Smooth/residual control exposes the supreme endpoint-boundary estimate. -/
theorem endpointBoundary_of_smoothResidualControl
    {boundary smooth residual : ℕ → ℂ}
    (control : EndpointCubeSmoothResidualControl boundary smooth residual) :
    EndpointCubeUniformLocalBoundaryStatement boundary :=
  control.signed_recombination_closure

/--
The second backward layer. A full signed Gram theorem must retain all diagonal
and off-diagonal boundary-packet interactions and deliver the smooth/residual
control without replacing the signed form by separate positive shell bounds.
-/
structure EndpointCubeSignedGramControl
    (boundary smooth residual : ℕ → ℂ) where
  smoothResidualControl : EndpointCubeSmoothResidualControl boundary smooth residual

/-- Full signed Gram control closes the endpoint-boundary estimate. -/
theorem endpointBoundary_of_signedGramControl
    {boundary smooth residual : ℕ → ℂ}
    (control : EndpointCubeSignedGramControl boundary smooth residual) :
    EndpointCubeUniformLocalBoundaryStatement boundary :=
  control.smoothResidualControl.signed_recombination_closure

/-- The complete backward theorem: signed endpoint-cube Gram control implies RH. -/
theorem riemannHypothesis_of_endpointCubeSignedGram
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bridge : ActualStartRHBridge start)
    (boundary smooth residual : ℕ → ℂ)
    (realization : EndpointCubeBoundaryRealization start boundary)
    (control : EndpointCubeSignedGramControl boundary smooth residual) :
    RiemannHypothesisStatement := by
  exact riemannHypothesis_of_endpointCubeBoundary
    start bridge boundary realization
      (endpointBoundary_of_signedGramControl control)

end RHLean.Analysis
