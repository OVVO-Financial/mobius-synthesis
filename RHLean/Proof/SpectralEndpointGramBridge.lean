import RHLean.Proof.EndpointProjectionBridge
import RHLean.Proof.OrthogonalResidual

open scoped InnerProductSpace

noncomputable section

namespace RHLean.Analysis

/-- Boundary sequence obtained by testing packet vectors against a recombination vector. -/
def packetBoundary {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (packet : ℕ → E) (u : E) : ℕ → ℂ :=
  fun N => inner ℂ u (packet N)

/-- Boundary contribution from the coherent projection of `u` onto `v`. -/
def coherentPacketBoundary {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (packet : ℕ → E) (v u : E) (hv : v ≠ 0) : ℕ → ℂ :=
  fun N => inner ℂ (orthogonalCoefficient (𝕜 := ℂ) v u hv • v) (packet N)

/-- Boundary contribution from the component of `u` orthogonal to `v`. -/
def orthogonalPacketBoundary {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (packet : ℕ → E) (v u : E) (hv : v ≠ 0) : ℕ → ℂ :=
  fun N => inner ℂ (orthogonalResidual (𝕜 := ℂ) v u hv) (packet N)

/-- The packet boundary splits pointwise into coherent and orthogonal pieces. -/
theorem packetBoundary_eq_coherent_add_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (packet : ℕ → E) (v u : E) (hv : v ≠ 0) (N : ℕ) :
    packetBoundary packet u N =
      coherentPacketBoundary packet v u hv N +
        orthogonalPacketBoundary packet v u hv N := by
  have hsum := congrArg (fun x : E => inner ℂ x (packet N))
    (orthogonalResidual_add_projection (𝕜 := ℂ) v u hv)
  simpa [packetBoundary, coherentPacketBoundary, orthogonalPacketBoundary,
    inner_add_left, add_comm] using hsum.symm

/--
Spectral data for a packet family.  The coherent direction is projected exactly,
while Gram invariance is recorded as exact local-energy separation.
-/
structure SpectralEndpointGramData {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (packet : ℕ → E) (v u : E) (hv : v ≠ 0) where
  local_energy_separation : ∀ N H,
    endpointBoundaryLocalEnergy (packetBoundary packet u) N H =
      endpointBoundaryLocalEnergy (coherentPacketBoundary packet v u hv) N H +
        endpointBoundaryLocalEnergy (orthogonalPacketBoundary packet v u hv) N H
  coherent_alignment_control :
    EndpointCubeUniformLocalBoundaryStatement
      (coherentPacketBoundary packet v u hv)
  orthogonal_operator_control :
    EndpointCubeUniformLocalBoundaryStatement
      (orthogonalPacketBoundary packet v u hv)

/-- Spectral Gram data instantiate the projection bridge from an earlier layer. -/
def endpointProjectionOfSpectralGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (packet : ℕ → E) (v u : E) (hv : v ≠ 0)
    (spectral : SpectralEndpointGramData packet v u hv) :
    EndpointProjectionDecomposition
      (packetBoundary packet u)
      (coherentPacketBoundary packet v u hv)
      (orthogonalPacketBoundary packet v u hv) where
  pointwise_decomposition :=
    packetBoundary_eq_coherent_add_orthogonal packet v u hv
  local_energy_decomposition := spectral.local_energy_separation

/-- Spectral alignment and orthogonal-complement control give projection estimates. -/
def endpointProjectionEstimatesOfSpectralGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (packet : ℕ → E) (v u : E) (hv : v ≠ 0)
    (spectral : SpectralEndpointGramData packet v u hv) :
    EndpointProjectionEstimates
      (coherentPacketBoundary packet v u hv)
      (orthogonalPacketBoundary packet v u hv) where
  coherent_bound := spectral.coherent_alignment_control
  residual_bound := spectral.orthogonal_operator_control

/-- Spectral endpoint-Gram control yields the endpoint-boundary estimate. -/
theorem endpointBoundary_of_spectralGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (packet : ℕ → E) (v u : E) (hv : v ≠ 0)
    (spectral : SpectralEndpointGramData packet v u hv) :
    EndpointCubeUniformLocalBoundaryStatement (packetBoundary packet u) := by
  exact endpointBoundary_of_projectionEstimates
    (endpointProjectionOfSpectralGram packet v u hv spectral)
    (endpointProjectionEstimatesOfSpectralGram packet v u hv spectral)

/-- Complete abstract spectral route from packet realization to RH. -/
theorem riemannHypothesis_of_spectralEndpointGram
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bridge : ActualStartRHBridge start)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (packet : ℕ → E) (v u : E) (hv : v ≠ 0)
    (realization : EndpointCubeBoundaryRealization start (packetBoundary packet u))
    (spectral : SpectralEndpointGramData packet v u hv) :
    RiemannHypothesisStatement := by
  exact riemannHypothesis_of_endpointProjection
    start bridge
    (packetBoundary packet u)
    (coherentPacketBoundary packet v u hv)
    (orthogonalPacketBoundary packet v u hv)
    realization
    (endpointProjectionOfSpectralGram packet v u hv spectral)
    (endpointProjectionEstimatesOfSpectralGram packet v u hv spectral)

end RHLean.Analysis
