import Mathlib
import RHLean.Proof.LifetimeLocalEnergyCriterion

/-!
# Lifetime endpoint decomposition

The birth-high population at stage `t` is split by a single death process:
current survivors are the birth mass minus the absorbed (dead) mass.  This
module assigns explicit names to the birth and death sequences, proves the
pointwise and translated-window identities, and repackages the lifetime-flow
criterion in endpoint language.

A bound on the death process alone is deliberately not claimed to imply the
survivor discrepancy bound; that would also require independent control of the
birth process.  No analytic estimate is introduced here.
-/

noncomputable section

namespace RHLean.Proof

/-- Birth-ordered canonical high mass through stage `t`. -/
def lifetimeBirthMass (Λ : ℝ) (t : ℕ) : ℂ :=
  birthCanonicalHighAtomMass Λ t

/-- Death-ordered mass: birth-high atoms absorbed by the moving boundary by
stage `t`. -/
def lifetimeDeathMass (Λ : ℝ) (t : ℕ) : ℂ :=
  absorbedCanonicalHighAtomMass Λ t

/-- The birth process is exactly the existing canonical high prefix. -/
theorem lifetimeBirthMass_eq_canonicalHighPrefix
    (Λ : ℝ) (t : ℕ) :
    lifetimeBirthMass Λ t = canonicalHighPrefix Λ t := by
  exact birthCanonicalHighAtomMass_eq_canonicalHighPrefix Λ t

/-- The death process is exactly the existing absorbed mass. -/
theorem lifetimeDeathMass_eq_absorbed
    (Λ : ℝ) (t : ℕ) :
    lifetimeDeathMass Λ t = absorbedCanonicalHighAtomMass Λ t := by
  rfl

/-- Exact endpoint identity: survivors equal births minus deaths. -/
theorem lifetimeActiveAtomMass_eq_birth_sub_death
    (Λ : ℝ) (t : ℕ) :
    lifetimeActiveAtomMass Λ t =
      lifetimeBirthMass Λ t - lifetimeDeathMass Λ t := by
  rw [lifetimeBirthMass_eq_canonicalHighPrefix,
    lifetimeDeathMass_eq_absorbed]
  have h := canonicalHighPrefix_eq_lifetimeActive_add_absorbed Λ t
  exact eq_sub_of_add_eq h.symm

/-- Equivalent endpoint recombination. -/
theorem lifetimeBirthMass_eq_active_add_death
    (Λ : ℝ) (t : ℕ) :
    lifetimeBirthMass Λ t =
      lifetimeActiveAtomMass Λ t + lifetimeDeathMass Λ t := by
  rw [lifetimeBirthMass_eq_canonicalHighPrefix,
    lifetimeDeathMass_eq_absorbed]
  exact canonicalHighPrefix_eq_lifetimeActive_add_absorbed Λ t

/-- The survivor local energy is exactly the local energy of the birth-death
discrepancy. -/
theorem lifetimeActive_localEnergy_eq_birth_sub_death
    (Λ : ℝ) (N H : ℕ) :
    RHLean.Analysis.localSequenceEnergy (lifetimeActiveAtomMass Λ) N H =
      RHLean.Analysis.localSequenceEnergy
        (fun t => lifetimeBirthMass Λ t - lifetimeDeathMass Λ t) N H := by
  unfold RHLean.Analysis.localSequenceEnergy
  apply Finset.sum_congr rfl
  intro h hh
  rw [lifetimeActiveAtomMass_eq_birth_sub_death]

/-- The absorbed local energy is definitionally the death-process local energy. -/
theorem absorbed_localEnergy_eq_death
    (Λ : ℝ) (N H : ℕ) :
    RHLean.Analysis.localSequenceEnergy
        (absorbedCanonicalHighAtomMass Λ) N H =
      RHLean.Analysis.localSequenceEnergy (lifetimeDeathMass Λ) N H := by
  rfl

/-- RH-scale local energy for the birth-minus-death discrepancy. -/
def LifetimeEndpointDiscrepancyUniformLocalBoundedStatement (Λ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        RHLean.Analysis.localSequenceEnergy
            (fun t => lifetimeBirthMass Λ t - lifetimeDeathMass Λ t) N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- RH-scale local energy for the single death process. -/
def LifetimeDeathUniformLocalBoundedStatement (Λ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        RHLean.Analysis.localSequenceEnergy (lifetimeDeathMass Λ) N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- Endpoint-language form of the honest lifetime-flow criterion. -/
def LifetimeEndpointUniformLocalBoundedStatement (Λ : ℝ) : Prop :=
  LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ ∧
    LifetimeDeathUniformLocalBoundedStatement Λ

/-- The active-survivor premise is exactly the endpoint-discrepancy premise. -/
theorem lifetimeActiveUniformLocalBounded_iff_endpointDiscrepancy
    (Λ : ℝ) :
    LifetimeActiveUniformLocalBoundedStatement Λ ↔
      LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N H hH hHN
    rw [← lifetimeActive_localEnergy_eq_birth_sub_death]
    exact hbound N H hH hHN
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N H hH hHN
    rw [lifetimeActive_localEnergy_eq_birth_sub_death]
    exact hbound N H hH hHN

/-- The absorbed-mass premise is exactly the death-process premise. -/
theorem absorbedUniformLocalBounded_iff_death
    (Λ : ℝ) :
    AbsorbedCanonicalUniformLocalBoundedStatement Λ ↔
      LifetimeDeathUniformLocalBoundedStatement Λ := by
  rfl

/-- The two-premise lifetime-flow criterion is exactly the endpoint criterion:
one discrepancy bound and one bound for the single death process. -/
theorem lifetimeFlowUniformLocalBounded_iff_endpoint
    (Λ : ℝ) :
    LifetimeFlowUniformLocalBoundedStatement Λ ↔
      LifetimeEndpointUniformLocalBoundedStatement Λ := by
  unfold LifetimeFlowUniformLocalBoundedStatement
    LifetimeEndpointUniformLocalBoundedStatement
  rw [lifetimeActiveUniformLocalBounded_iff_endpointDiscrepancy,
    absorbedUniformLocalBounded_iff_death]

/-- Endpoint criterion implies the protected square-prefix uniform-local
criterion. -/
theorem lifetimeEndpointUniformLocalBounded_implies_squarePrefixUniformLocal
    (Λ : ℝ)
    (hendpoint : LifetimeEndpointUniformLocalBoundedStatement Λ) :
    RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement := by
  apply lifetimeFlowUniformLocalBounded_implies_squarePrefixUniformLocal Λ
  exact (lifetimeFlowUniformLocalBounded_iff_endpoint Λ).2 hendpoint

/-- Endpoint criterion implies RH through the repository's existing classical
Mertens-energy criterion. -/
theorem lifetimeEndpointUniformLocalBounded_implies_riemannHypothesis
    (Λ : ℝ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion)
    (hendpoint : LifetimeEndpointUniformLocalBoundedStatement Λ) :
    RHLean.Analysis.RiemannHypothesisStatement := by
  apply lifetimeFlowUniformLocalBounded_implies_riemannHypothesis Λ criterion
  exact (lifetimeFlowUniformLocalBounded_iff_endpoint Λ).2 hendpoint

end RHLean.Proof
