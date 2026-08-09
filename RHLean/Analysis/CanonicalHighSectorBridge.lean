import Mathlib
import RHLean.Analysis.CanonicalLowOccupancy
import RHLean.Proof.GeometricRHReduction

/-!
# Canonical high-sector criterion bridge

This paper-facing analysis module packages the exact canonical arithmetic,
low/high decomposition, and unconditional low-occupancy control as the
repository's protected geometric criterion and RH bridge.

The declarations remain in namespace `RHLean.Proof` for API compatibility with
the existing downstream development; their source module now lies in the
paper-facing `Analysis` hierarchy.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- The native canonical decomposition as an exact concrete geometric partition
accepted by the already-proved local RH bridge. -/
def canonicalSquarePrefixGeometricPartition
    (Λ : ℝ) (control : CanonicalLowIncrementControl Λ) :
    RHLean.Analysis.SquarePrefixGeometricPartition where
  low := canonicalLowPrefix Λ
  high := canonicalHighPrefix Λ
  lowConstant := 4 * control.bound ^ 2
  lowConstant_nonneg := mul_nonneg (by norm_num) (sq_nonneg control.bound)
  recombine := squarePrefixMertens_eq_canonicalLow_add_high Λ
  low_energy_pointwise := canonicalLowPrefix_energy_le control

/-- The single native canonical high-sector local estimate `(HS)`. -/
def CanonicalHighUniformLocalBoundedStatement (Λ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        RHLean.Analysis.localSequenceEnergy (canonicalHighPrefix Λ) N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- The native canonical `(HS)` statement is definitionally the high-sector
criterion of the concrete canonical partition. -/
theorem canonicalHighUniformLocalBounded_iff_partition
    (Λ : ℝ) (control : CanonicalLowIncrementControl Λ) :
    CanonicalHighUniformLocalBoundedStatement Λ ↔
      RHLean.Analysis.SquarePrefixHighUniformLocalBoundedStatement
        (canonicalSquarePrefixGeometricPartition Λ control) := by
  rfl

/-- For any supplied low control, the canonical `(HS)` estimate is exactly
equivalent to the protected total uniform-local square-prefix criterion. -/
theorem canonicalHighUniformLocalBounded_iff_squarePrefixUniformLocalBounded
    (Λ : ℝ) (control : CanonicalLowIncrementControl Λ) :
    CanonicalHighUniformLocalBoundedStatement Λ ↔
      RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement := by
  rw [canonicalHighUniformLocalBounded_iff_partition Λ control]
  exact
    (RHLean.Analysis.squarePrefix_uniformLocalBounded_iff_highUniformLocalBounded
      (canonicalSquarePrefixGeometricPartition Λ control)).symm

/-- The elementary canonical low-sector obligation is now discharged internally:
`(HS)` is equivalent to the protected uniform-local criterion for every cutoff. -/
theorem canonicalHighUniformLocalBounded_iff_squarePrefixUniformLocalBounded_realized
    (Λ : ℝ) :
    CanonicalHighUniformLocalBoundedStatement Λ ↔
      RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement :=
  canonicalHighUniformLocalBounded_iff_squarePrefixUniformLocalBounded
    Λ (canonicalLowIncrementControl Λ)

/-- Exact project bridge from the native canonical `(HS)` statement to RH,
conditional only on the classical Mertens-energy equivalence supplied as an
ordinary theorem argument. -/
theorem canonicalHighUniformLocalBounded_iff_riemannHypothesis
    (Λ : ℝ) (control : CanonicalLowIncrementControl Λ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion) :
    CanonicalHighUniformLocalBoundedStatement Λ ↔
      RHLean.Analysis.RiemannHypothesisStatement := by
  rw [canonicalHighUniformLocalBounded_iff_partition Λ control]
  exact
    RHLean.Analysis.squarePrefix_highUniformLocalBounded_iff_riemannHypothesis
      (canonicalSquarePrefixGeometricPartition Λ control) criterion

/-- Canonical high-sector criterion ↔ RH with no remaining internal low-sector
hypothesis. The only external theorem argument is the ordinary classical
Mertens↔RH criterion. -/
theorem canonicalHighUniformLocalBounded_iff_riemannHypothesis_realized
    (Λ : ℝ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion) :
    CanonicalHighUniformLocalBoundedStatement Λ ↔
      RHLean.Analysis.RiemannHypothesisStatement :=
  canonicalHighUniformLocalBounded_iff_riemannHypothesis
    Λ (canonicalLowIncrementControl Λ) criterion

end RHLean.Proof
