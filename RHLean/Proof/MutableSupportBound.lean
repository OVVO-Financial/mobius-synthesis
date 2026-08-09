import Mathlib
import RHLean.Arithmetic.SquareBlockParityPopulation

/-!
# Mutable-support bound for square-block discrepancy

This module isolates the deterministic final implication used by the square-block
program. If the Mobius mass on the settled interior of a square block is exactly
zero, then the whole block discrepancy is supported on the remaining mutable set.
Since every Mobius value has absolute value at most one, the mutable set can change
the block discrepancy by at most one unit per coordinate.

No estimate for the size of the mutable set is asserted here. The arithmetic
closure theorem still has to construct the genuine quotient boundary and prove
that its cardinality is `o(n)`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Every Mobius value has integer absolute value at most one. -/
theorem abs_moebius_le_one (m : ℕ) : |μ m| ≤ (1 : ℤ) := by
  rcases ArithmeticFunction.moebius_eq_or m with h | h | h <;> simp [h]

/-- The absolute Mobius mass of any finite set is bounded by its cardinality. -/
theorem abs_sum_moebius_le_card (s : Finset ℕ) :
    |∑ m ∈ s, μ m| ≤ (s.card : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      push_cast
      have ihBounds :
          -(s.card : ℤ) ≤ ∑ m ∈ s, μ m ∧
            ∑ m ∈ s, μ m ≤ (s.card : ℤ) :=
        abs_le.mp ih
      rcases ArithmeticFunction.moebius_eq_or a with h | h | h
      · rw [h, zero_add]
        exact le_trans ih (by omega)
      · rw [h]
        apply abs_le.mpr
        constructor <;> omega
      · rw [h]
        apply abs_le.mpr
        constructor <;> omega

/-- If the settled interior of square block `n` has zero Mobius mass, the complete
block discrepancy is exactly the Mobius mass carried by the mutable support. -/
theorem squareBlockMoebius_eq_sum_mutable
    {n : ℕ} {U : Finset ℕ}
    (hU : U ⊆ squareBlockInterval n)
    (hinterior : ∑ m ∈ squareBlockInterval n \ U, μ m = 0) :
    squareBlockMoebius n = ∑ m ∈ U, μ m := by
  unfold squareBlockMoebius
  rw [← Finset.sum_sdiff hU, hinterior, zero_add]

/-- A mutable support can contribute at most one unit of block discrepancy per
coordinate. This is the exact finite estimate behind the implication
`|U_n| = o(n) -> Delta_n = o(n)`. -/
theorem abs_squareBlockMoebius_le_mutable_card
    {n : ℕ} {U : Finset ℕ}
    (hU : U ⊆ squareBlockInterval n)
    (hinterior : ∑ m ∈ squareBlockInterval n \ U, μ m = 0) :
    |squareBlockMoebius n| ≤ (U.card : ℤ) := by
  rw [squareBlockMoebius_eq_sum_mutable hU hinterior]
  exact abs_sum_moebius_le_card U

/-- Pointwise version for a family of mutable supports. -/
theorem abs_squareBlockMoebius_le_mutable_card_family
    (U : ℕ → Finset ℕ)
    (hU : ∀ n, U n ⊆ squareBlockInterval n)
    (hinterior : ∀ n, ∑ m ∈ squareBlockInterval n \ U n, μ m = 0)
    (n : ℕ) :
    |squareBlockMoebius n| ≤ ((U n).card : ℤ) :=
  abs_squareBlockMoebius_le_mutable_card (hU n) (hinterior n)

end RHLean.Proof
