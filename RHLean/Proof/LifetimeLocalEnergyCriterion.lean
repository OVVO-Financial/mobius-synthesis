import Mathlib
import RHLean.Analysis.CanonicalHighSectorBridge
import RHLean.Proof.LifetimeActiveSet

/-!
# Lifetime local-energy criterion

The exact birth-high decomposition has two terms: the lifetime-active survivor
mass and the absorbed mass.  This module states RH-scale local-energy premises
for both terms and proves that their conjunction implies the repository's
existing canonical high-sector criterion, hence the protected square-prefix
uniform-local criterion.

No analytic estimate is proved here; the two bounds remain explicit ordinary
propositions.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- RH-scale translated-window energy control for the current lifetime-active
survivor mass. -/
def LifetimeActiveUniformLocalBoundedStatement (Λ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        RHLean.Analysis.localSequenceEnergy (lifetimeActiveAtomMass Λ) N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- RH-scale translated-window energy control for the absorbed birth-high mass. -/
def AbsorbedCanonicalUniformLocalBoundedStatement (Λ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        RHLean.Analysis.localSequenceEnergy (absorbedCanonicalHighAtomMass Λ) N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- The honest lifetime-flow premise: both current survivors and absorbed mass
have RH-scale local energy. -/
def LifetimeFlowUniformLocalBoundedStatement (Λ : ℝ) : Prop :=
  LifetimeActiveUniformLocalBoundedStatement Λ ∧
    AbsorbedCanonicalUniformLocalBoundedStatement Λ

private theorem lifetime_norm_sq_add_le_two (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm := norm_add_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x + y‖ := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Exact local-energy comparison induced by
`canonicalHighPrefix = active + absorbed`. -/
theorem canonicalHigh_localEnergy_le_two_lifetime_add_absorbed
    (Λ : ℝ) (N H : ℕ) :
    RHLean.Analysis.localSequenceEnergy (canonicalHighPrefix Λ) N H ≤
      2 * RHLean.Analysis.localSequenceEnergy (lifetimeActiveAtomMass Λ) N H +
        2 * RHLean.Analysis.localSequenceEnergy
          (absorbedCanonicalHighAtomMass Λ) N H := by
  unfold RHLean.Analysis.localSequenceEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hh
  rw [canonicalHighPrefix_eq_lifetimeActive_add_absorbed]
  exact lifetime_norm_sq_add_le_two _ _

/-- The combined lifetime-flow premise implies the existing canonical
high-sector uniform-local criterion. -/
theorem lifetimeFlowUniformLocalBounded_implies_canonicalHigh
    (Λ : ℝ)
    (hflow : LifetimeFlowUniformLocalBoundedStatement Λ) :
    CanonicalHighUniformLocalBoundedStatement Λ := by
  intro ε hε
  rcases hflow.1 ε hε with ⟨Cactive, hCactive, hactive⟩
  rcases hflow.2 ε hε with ⟨Cabsorbed, hCabsorbed, habsorbed⟩
  refine ⟨2 * Cactive + 2 * Cabsorbed, by nlinarith, ?_⟩
  intro N H hH hHN
  have ha := hactive N H hH hHN
  have hb := habsorbed N H hH hHN
  calc
    RHLean.Analysis.localSequenceEnergy (canonicalHighPrefix Λ) N H ≤
        2 * RHLean.Analysis.localSequenceEnergy (lifetimeActiveAtomMass Λ) N H +
          2 * RHLean.Analysis.localSequenceEnergy
            (absorbedCanonicalHighAtomMass Λ) N H :=
      canonicalHigh_localEnergy_le_two_lifetime_add_absorbed Λ N H
    _ ≤ 2 * (Cactive * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) +
          2 * (Cabsorbed * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) := by
      nlinarith
    _ = (2 * Cactive + 2 * Cabsorbed) * (H : ℝ) *
          Real.rpow (N : ℝ) (2 + ε) := by ring

/-- The combined lifetime-flow premise implies the protected concrete
square-prefix uniform-local criterion. -/
theorem lifetimeFlowUniformLocalBounded_implies_squarePrefixUniformLocal
    (Λ : ℝ)
    (hflow : LifetimeFlowUniformLocalBoundedStatement Λ) :
    RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement := by
  apply
    (canonicalHighUniformLocalBounded_iff_squarePrefixUniformLocalBounded_realized Λ).1
  exact lifetimeFlowUniformLocalBounded_implies_canonicalHigh Λ hflow

/-- Conditional RH implication through the repository's existing classical
Mertens-energy criterion. -/
theorem lifetimeFlowUniformLocalBounded_implies_riemannHypothesis
    (Λ : ℝ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion)
    (hflow : LifetimeFlowUniformLocalBoundedStatement Λ) :
    RHLean.Analysis.RiemannHypothesisStatement := by
  apply (canonicalHighUniformLocalBounded_iff_riemannHypothesis_realized Λ criterion).1
  exact lifetimeFlowUniformLocalBounded_implies_canonicalHigh Λ hflow

end RHLean.Proof
