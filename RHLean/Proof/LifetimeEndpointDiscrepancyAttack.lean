import Mathlib
import RHLean.Proof.DeathShellSubpolynomial

/-!
# Lifetime endpoint discrepancy is the complete positive-scale lifetime criterion

The endpoint decomposition writes the active survivor mass as

`birth - death`.

`DeathShellSubpolynomial` already proves the death process has RH-scale
translated local energy unconditionally for every positive shell parameter
`Λ`, and already deletes that half of the endpoint package in the forward
direction.

This module proves the converse comparison as well.  Since

`active = canonicalHigh - death`,

critical local energy for the canonical high sector plus the unconditional
death estimate recovers critical local energy for the survivor discrepancy.
Thus, for `0 < Λ`, the birth-minus-death discrepancy is not merely sufficient:
it is exactly equivalent to the lifetime-flow criterion, the canonical high
criterion, and the protected square-prefix uniform-local criterion.  Given the
repository's classical Mertens criterion, it is likewise equivalent to the
existing RH terminal.
-/

noncomputable section

namespace RHLean.Proof

/-- The full lifetime-flow criterion has exactly one live analytic input at
positive shell scale: the birth-minus-death survivor discrepancy. -/
theorem lifetimeFlowUniformLocalBounded_iff_endpointDiscrepancy
    {Λ : ℝ} (hΛ : 0 < Λ) :
    LifetimeFlowUniformLocalBoundedStatement Λ ↔
      LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ := by
  rw [lifetimeFlowUniformLocalBounded_iff_endpoint,
    lifetimeEndpointUniformLocalBounded_iff_discrepancy hΛ]

private theorem lifetime_endpoint_norm_sq_sub_le_two (x y : ℂ) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm := norm_sub_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x - y‖ := norm_nonneg (x - y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Exact local-energy comparison in the reverse direction: the current
survivor population is controlled by the canonical high prefix and the death
process. -/
theorem lifetimeActive_localEnergy_le_two_canonicalHigh_add_death
    (Λ : ℝ) (N H : ℕ) :
    RHLean.Analysis.localSequenceEnergy (lifetimeActiveAtomMass Λ) N H ≤
      2 * RHLean.Analysis.localSequenceEnergy (canonicalHighPrefix Λ) N H +
        2 * RHLean.Analysis.localSequenceEnergy (lifetimeDeathMass Λ) N H := by
  unfold RHLean.Analysis.localSequenceEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hh
  rw [lifetimeActiveAtomMass_eq_birth_sub_death,
    lifetimeBirthMass_eq_canonicalHighPrefix]
  exact lifetime_endpoint_norm_sq_sub_le_two _ _

/-- Unconditional death-process control makes the implication reversible:
critical canonical-high energy recovers critical survivor-discrepancy energy. -/
theorem lifetimeEndpointDiscrepancyUniformLocalBounded_of_canonicalHigh
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hC : CanonicalHighUniformLocalBoundedStatement Λ) :
    LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ := by
  intro ε hε
  obtain ⟨CH, hCH, hHigh⟩ := hC ε hε
  obtain ⟨CD, hCD, hDeath⟩ := lifetimeDeathUniformLocalBounded hΛ ε hε
  refine ⟨2 * CH + 2 * CD, by nlinarith, ?_⟩
  intro N H hH hHN
  have hhigh := hHigh N H hH hHN
  have hdeath := hDeath N H hH hHN
  rw [← lifetimeActive_localEnergy_eq_birth_sub_death]
  calc
    RHLean.Analysis.localSequenceEnergy (lifetimeActiveAtomMass Λ) N H ≤
        2 * RHLean.Analysis.localSequenceEnergy (canonicalHighPrefix Λ) N H +
          2 * RHLean.Analysis.localSequenceEnergy (lifetimeDeathMass Λ) N H :=
      lifetimeActive_localEnergy_le_two_canonicalHigh_add_death Λ N H
    _ ≤ 2 * (CH * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) +
          2 * (CD * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) := by
      nlinarith
    _ = (2 * CH + 2 * CD) * (H : ℝ) *
        Real.rpow (N : ℝ) (2 + ε) := by ring

/-- At positive shell scale the survivor discrepancy is exactly equivalent to
the canonical high-sector local-energy criterion. -/
theorem lifetimeEndpointDiscrepancyUniformLocalBounded_iff_canonicalHigh
    {Λ : ℝ} (hΛ : 0 < Λ) :
    LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ ↔
      CanonicalHighUniformLocalBoundedStatement Λ := by
  constructor
  · intro hD
    apply lifetimeFlowUniformLocalBounded_implies_canonicalHigh Λ
    exact (lifetimeFlowUniformLocalBounded_iff_endpointDiscrepancy hΛ).2 hD
  · exact lifetimeEndpointDiscrepancyUniformLocalBounded_of_canonicalHigh hΛ

/-- Therefore the survivor discrepancy is exactly equivalent to the protected
square-prefix uniform-local criterion, not merely a sufficient condition. -/
theorem lifetimeEndpointDiscrepancyUniformLocalBounded_iff_squarePrefixUniformLocal
    {Λ : ℝ} (hΛ : 0 < Λ) :
    LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ ↔
      RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement := by
  rw [lifetimeEndpointDiscrepancyUniformLocalBounded_iff_canonicalHigh hΛ,
    canonicalHighUniformLocalBounded_iff_squarePrefixUniformLocalBounded_realized Λ]

/-- Given the repository's existing classical Mertens criterion, the same
survivor discrepancy is exactly equivalent to the existing RH terminal. -/
theorem lifetimeEndpointDiscrepancyUniformLocalBounded_iff_riemannHypothesis
    {Λ : ℝ} (hΛ : 0 < Λ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion) :
    LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ ↔
      RHLean.Analysis.RiemannHypothesisStatement := by
  rw [lifetimeEndpointDiscrepancyUniformLocalBounded_iff_canonicalHigh hΛ,
    canonicalHighUniformLocalBounded_iff_riemannHypothesis_realized Λ criterion]

end RHLean.Proof
