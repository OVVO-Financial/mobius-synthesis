import Mathlib
import RHLean.Analysis.ConcreteSquarePrefixGeometry
import RHLean.Proof.RealSquareBlockIncrements

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- Degree-one upper partial mass of the real canonical square-block increments
through block `n`. -/
def squareBlockUpperPartialMass (n : ℕ) : ℝ :=
  RHLean.Analysis.upperPartialMass (Finset.range (n + 1))
    realCanonicalTotalIncrement

/-- Degree-one lower partial mass of the real canonical square-block increments
through block `n`. -/
def squareBlockLowerPartialMass (n : ℕ) : ℝ :=
  RHLean.Analysis.lowerPartialMass (Finset.range (n + 1))
    realCanonicalTotalIncrement

/-- Denominator-free degree-one imbalance of the real canonical square-block
increments. -/
def squareBlockDegreeOneBalanceNumerator (n : ℕ) : ℝ :=
  RHLean.Analysis.degreeOneBalanceNumerator (Finset.range (n + 1))
    realCanonicalTotalIncrement

/-- Degree-one upper-mass share of the real canonical square-block increments.
The denominator-free formulation below is primary; this ratio is used only under
an explicit nonzero-total-variation hypothesis. -/
def squareBlockDegreeOneBalanceRatio (n : ℕ) : ℝ :=
  RHLean.Analysis.degreeOneBalanceRatio (Finset.range (n + 1))
    realCanonicalTotalIncrement

/-- Upper minus lower degree-one partial mass is exactly the real canonical
square-block prefix. -/
theorem squareBlockUpperPartialMass_sub_lowerPartialMass_eq_prefix (n : ℕ) :
    squareBlockUpperPartialMass n - squareBlockLowerPartialMass n =
      realCanonicalTotalPrefix n := by
  rw [← finiteSignedSum_realCanonicalTotalIncrement_eq_prefix]
  exact RHLean.Analysis.upperPartialMass_sub_lowerPartialMass_eq_finiteSignedSum
    (Finset.range (n + 1)) realCanonicalTotalIncrement

/-- Upper plus lower degree-one partial mass is exactly the total variation of
the real canonical block increments. -/
theorem squareBlockUpperPartialMass_add_lowerPartialMass_eq_variation (n : ℕ) :
    squareBlockUpperPartialMass n + squareBlockLowerPartialMass n =
      realCanonicalTotalVariation n := by
  rw [← finiteAbsoluteMass_realCanonicalTotalIncrement_eq_variation]
  exact RHLean.Analysis.upperPartialMass_add_lowerPartialMass_eq_finiteAbsoluteMass
    (Finset.range (n + 1)) realCanonicalTotalIncrement

/-- The denominator-free degree-one imbalance is exactly the real canonical
square-block prefix. -/
theorem squareBlockDegreeOneBalanceNumerator_eq_prefix (n : ℕ) :
    squareBlockDegreeOneBalanceNumerator n = realCanonicalTotalPrefix n := by
  rw [← finiteSignedSum_realCanonicalTotalIncrement_eq_prefix]
  exact RHLean.Analysis.degreeOneBalanceNumerator_eq_finiteSignedSum
    (Finset.range (n + 1)) realCanonicalTotalIncrement

/-- Guarded ratio form of the exact degree-one partial-moment identity. -/
theorem realCanonicalTotalPrefix_eq_variation_mul_two_ratio_sub_one
    (n : ℕ) (hQ : realCanonicalTotalVariation n ≠ 0) :
    realCanonicalTotalPrefix n =
      realCanonicalTotalVariation n *
        (2 * squareBlockDegreeOneBalanceRatio n - 1) := by
  rw [← finiteSignedSum_realCanonicalTotalIncrement_eq_prefix,
    ← finiteAbsoluteMass_realCanonicalTotalIncrement_eq_variation]
  exact RHLean.Analysis.finiteSignedSum_eq_absoluteMass_mul_two_ratio_sub_one
    (Finset.range (n + 1)) realCanonicalTotalIncrement hQ

/-- Strong denominator-free degree-one partial-moment balance.

The squared signed imbalance is required to be at most `N^ε` times the total
unsigned block mass. This is an explicit unresolved arithmetic premise. It is
stronger than the repository's minimal square-prefix pointwise criterion and is
not asserted here. -/
def SquareBlockPartialMomentBalanceBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, 1 ≤ N →
        |squareBlockDegreeOneBalanceNumerator N| ^ 2 ≤
          C * Real.rpow (N : ℝ) ε * realCanonicalTotalVariation N

/-- Strong degree-one partial-moment balance implies the repository's existing
square-prefix pointwise criterion. -/
theorem squarePrefixCurrentPointwiseBounded_of_partialMomentBalance
    (hbalance : SquareBlockPartialMomentBalanceBoundedStatement) :
    RHLean.Analysis.SquarePrefixCurrentPointwiseBoundedStatement := by
  intro ε hε
  rcases hbalance ε hε with ⟨C, hC, hbound⟩
  refine ⟨4 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro N hN
  have hNposNat : 0 < N := by omega
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNposNat
  have hbalanceN := hbound N hN
  rw [squareBlockDegreeOneBalanceNumerator_eq_prefix] at hbalanceN
  have hvariation := realCanonicalTotalVariation_le N
  have hNaddNat : N + 1 ≤ 2 * N := by omega
  have hNadd : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hNaddNat
  have hvariationFour :
      realCanonicalTotalVariation N ≤ 4 * (N : ℝ) ^ 2 := by
    calc
      realCanonicalTotalVariation N ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := hvariation
      _ ≤ (2 * (N : ℝ)) ^ 2 := by
        nlinarith [sq_nonneg (((N + 1 : ℕ) : ℝ) - 2 * (N : ℝ))]
      _ = 4 * (N : ℝ) ^ 2 := by ring
  have hcoefficient_nonneg :
      0 ≤ C * Real.rpow (N : ℝ) ε :=
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have htwo :
      Real.rpow (N : ℝ) (2 : ℝ) = (N : ℝ) ^ (2 : ℕ) :=
    Real.rpow_natCast (N : ℝ) 2
  have hrpow_mul :
      (N : ℝ) ^ 2 * Real.rpow (N : ℝ) ε =
        Real.rpow (N : ℝ) (2 + ε) := by
    calc
      (N : ℝ) ^ 2 * Real.rpow (N : ℝ) ε =
          Real.rpow (N : ℝ) 2 * Real.rpow (N : ℝ) ε := by
        rw [htwo]
      _ = Real.rpow (N : ℝ) (2 + ε) :=
        (Real.rpow_add hNpos 2 ε).symm
  have hnormCast :
      ‖RHLean.Analysis.squarePrefixMertens N‖ =
        |realCanonicalTotalPrefix N| := by
    rw [← realCanonicalTotalPrefix_cast_eq_squarePrefixMertens]
    simp
  calc
    ‖RHLean.Analysis.squarePrefixMertens N‖ ^ 2 =
        |realCanonicalTotalPrefix N| ^ 2 := by rw [hnormCast]
    _ ≤ C * Real.rpow (N : ℝ) ε * realCanonicalTotalVariation N :=
      hbalanceN
    _ ≤ C * Real.rpow (N : ℝ) ε * (4 * (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hvariationFour hcoefficient_nonneg
    _ = (4 * C) * ((N : ℝ) ^ 2 * Real.rpow (N : ℝ) ε) := by ring
    _ = (4 * C) * Real.rpow (N : ℝ) (2 + ε) := by rw [hrpow_mul]

/-- Strong degree-one partial-moment balance implies the protected uniform-local
square-prefix criterion. -/
theorem squarePrefixUniformLocalBounded_of_partialMomentBalance
    (hbalance : SquareBlockPartialMomentBalanceBoundedStatement) :
    RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement :=
  RHLean.Analysis.squarePrefix_uniformLocalBounded_of_currentPointwise
    (squarePrefixCurrentPointwiseBounded_of_partialMomentBalance hbalance)

/-- Conditional RH implication from strong degree-one partial-moment balance and
the ordinary classical Mertens-energy equivalence. -/
theorem riemannHypothesis_of_squareBlockPartialMomentBalance
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion)
    (hbalance : SquareBlockPartialMomentBalanceBoundedStatement) :
    RHLean.Analysis.RiemannHypothesisStatement :=
  criterion.iff_riemannHypothesis.mp
    (RHLean.Analysis.squarePrefix_uniformLocalBounded_iff_mertensEnergyBounded.mp
      (squarePrefixUniformLocalBounded_of_partialMomentBalance hbalance))

end RHLean.Proof
