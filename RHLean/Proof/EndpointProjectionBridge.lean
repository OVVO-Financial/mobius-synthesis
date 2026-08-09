import RHLean.Proof.EndpointCubeAnalyticClosure

noncomputable section

namespace RHLean.Analysis

/-- Exact coherent/residual energy splitting for an endpoint boundary sequence. -/
structure EndpointProjectionDecomposition
    (boundary coherent residual : ℕ → ℂ) where
  pointwise_decomposition : ∀ N, boundary N = coherent N + residual N
  local_energy_decomposition : ∀ N H,
    endpointBoundaryLocalEnergy boundary N H =
      endpointBoundaryLocalEnergy coherent N H +
        endpointBoundaryLocalEnergy residual N H

/-- Uniform local control of the coherent and orthogonal-residual energies. -/
structure EndpointProjectionEstimates
    (coherent residual : ℕ → ℂ) where
  coherent_bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ N H : ℕ, 1 ≤ H → H ≤ N →
          endpointBoundaryLocalEnergy coherent N H ≤
            C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)
  residual_bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ N H : ℕ, 1 ≤ H → H ≤ N →
          endpointBoundaryLocalEnergy residual N H ≤
            C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/--
The bridge theorem: an exact coherent/residual energy split plus separate
uniform-local estimates yields the supreme endpoint-boundary estimate.
-/
theorem endpointBoundary_of_projectionEstimates
    {boundary coherent residual : ℕ → ℂ}
    (decomp : EndpointProjectionDecomposition boundary coherent residual)
    (estimates : EndpointProjectionEstimates coherent residual) :
    EndpointCubeUniformLocalBoundaryStatement boundary := by
  intro ε hε
  rcases estimates.coherent_bound ε hε with ⟨Cc, hCc, hc⟩
  rcases estimates.residual_bound ε hε with ⟨Cr, hCr, hr⟩
  refine ⟨Cc + Cr, add_nonneg hCc hCr, ?_⟩
  intro N H hH hHN
  rw [decomp.local_energy_decomposition]
  have hcoh := hc N H hH hHN
  have hres := hr N H hH hHN
  calc
    endpointBoundaryLocalEnergy coherent N H +
        endpointBoundaryLocalEnergy residual N H
        ≤ Cc * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) +
            Cr * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) :=
      add_le_add hcoh hres
    _ = (Cc + Cr) * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) := by ring

/-- Projection estimates close the existing endpoint-cube signed-Gram schema. -/
def endpointCubeSignedGramControlOfProjection
    {boundary coherent residual : ℕ → ℂ}
    (decomp : EndpointProjectionDecomposition boundary coherent residual)
    (estimates : EndpointProjectionEstimates coherent residual) :
    EndpointCubeSignedGramControl boundary coherent residual where
  smoothResidualControl := {
    exact_decomposition := decomp.pointwise_decomposition
    smooth_uniform_local := by
      intro ε hε
      exact estimates.coherent_bound ε hε
    residual_uniform_local := by
      intro ε hε
      exact estimates.residual_bound ε hε
    signed_recombination_closure :=
      endpointBoundary_of_projectionEstimates decomp estimates
  }

/-- The complete abstract projection route from exact realization to RH. -/
theorem riemannHypothesis_of_endpointProjection
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bridge : ActualStartRHBridge start)
    (boundary coherent residual : ℕ → ℂ)
    (realization : EndpointCubeBoundaryRealization start boundary)
    (decomp : EndpointProjectionDecomposition boundary coherent residual)
    (estimates : EndpointProjectionEstimates coherent residual) :
    RiemannHypothesisStatement := by
  exact riemannHypothesis_of_endpointCubeSignedGram
    start bridge boundary coherent residual realization
      (endpointCubeSignedGramControlOfProjection decomp estimates)

end RHLean.Analysis
