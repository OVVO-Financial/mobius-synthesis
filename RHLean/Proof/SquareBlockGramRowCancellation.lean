import Mathlib
import RHLean.Proof.CoherentGramVanishingTransfer

/-!
# Square-block Gram row cancellation

This module exposes a concrete sufficient criterion for suppression of the
coherent all-ones square-block Gram mode.

For each block index `i`, sum its correlations with all blocks through `N`.
The coherent Gram mass is the signed sum of these row sums.  Therefore it is
bounded by the sum of their absolute values.  Vanishing normalized absolute
row mass consequently forces coherent-mode Gram decay and hence, through the
merged transfer theorem, vanishing normalized cumulative square-block
discrepancy.

No arithmetic estimate for the actual row mass is asserted here.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace RHLean.Proof

/-- Correlation row sum for square block `i` against all blocks through `N`. -/
def squareBlockGramRowSum (N i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), squareBlockIncrementGramEntry i j

/-- Total absolute row mass of the square-block Gram kernel through `N`. -/
def squareBlockGramAbsoluteRowMass (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), |squareBlockGramRowSum N i|

/-- Absolute row mass normalized on the same quadratic block-index scale as the
coherent Gram mass. -/
def normalizedSquareBlockGramAbsoluteRowMass (N : ℕ) : ℝ :=
  squareBlockGramAbsoluteRowMass N / ((N : ℝ) ^ 2)

/-- The coherent all-ones Gram mass is exactly the signed sum of its row sums. -/
theorem squareBlockCoherentGramMass_eq_sum_rowSums (N : ℕ) :
    squareBlockCoherentGramMass N =
      ∑ i ∈ Finset.range (N + 1), squareBlockGramRowSum N i := by
  rfl

/-- The coherent Gram mass is bounded by the total absolute row mass. -/
theorem squareBlockCoherentGramMass_le_absoluteRowMass (N : ℕ) :
    squareBlockCoherentGramMass N ≤ squareBlockGramAbsoluteRowMass N := by
  have hnonneg := squareBlockCoherentGramMass_nonneg N
  calc
    squareBlockCoherentGramMass N = |squareBlockCoherentGramMass N| := by
      symm
      exact abs_of_nonneg hnonneg
    _ = |∑ i ∈ Finset.range (N + 1), squareBlockGramRowSum N i| := by
      rw [← squareBlockCoherentGramMass_eq_sum_rowSums]
    _ ≤ ∑ i ∈ Finset.range (N + 1), |squareBlockGramRowSum N i| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le (Finset.range (N + 1)) (squareBlockGramRowSum N))
    _ = squareBlockGramAbsoluteRowMass N := rfl

/-- Pointwise normalized row-mass control implies normalized coherent-Gram
control. -/
theorem normalizedSquareBlockCoherentGramMass_le_absoluteRowMass
    (N : ℕ) :
    normalizedSquareBlockCoherentGramMass N ≤
      normalizedSquareBlockGramAbsoluteRowMass N := by
  unfold normalizedSquareBlockCoherentGramMass
    normalizedSquareBlockGramAbsoluteRowMass
  exact div_le_div_of_nonneg_right
    (squareBlockCoherentGramMass_le_absoluteRowMass N)
    (sq_nonneg (N : ℝ))

/-- Epsilon/eventually formulation of vanishing normalized absolute row mass. -/
def SquareBlockGramAbsoluteRowMassVanishes : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop,
      normalizedSquareBlockGramAbsoluteRowMass N ≤ ε ^ 2

/-- Vanishing normalized absolute row mass forces coherent-mode Gram decay. -/
theorem squareBlockCoherentGramVanishes_of_absoluteRowMassVanishes
    (hrows : SquareBlockGramAbsoluteRowMassVanishes) :
    SquareBlockCoherentGramVanishes := by
  intro ε hε
  have hrowEventually := hrows ε hε
  filter_upwards [hrowEventually] with N hN
  exact le_trans
    (normalizedSquareBlockCoherentGramMass_le_absoluteRowMass N) hN

/-- Concrete row-cancellation criterion implies vanishing normalized cumulative
square-block discrepancy. -/
theorem cumulativeSquareBlockDiscrepancyVanishes_of_absoluteRowMassVanishes
    (hrows : SquareBlockGramAbsoluteRowMassVanishes) :
    CumulativeSquareBlockDiscrepancyVanishes :=
  cumulativeSquareBlockDiscrepancyVanishes_of_coherentGramVanishes
    (squareBlockCoherentGramVanishes_of_absoluteRowMassVanishes hrows)

end RHLean.Proof
