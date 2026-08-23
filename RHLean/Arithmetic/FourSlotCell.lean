import RHLean.Arithmetic.MoebiusDoubling

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Arithmetic

/-- The scalar sum of the complete four-slot Möbius cell indexed by `k`. -/
def fourSlotCellSum (k : ℕ) : ℤ :=
  μ (4 * k + 1) + μ (4 * k + 2) + μ (4 * k + 3) + μ (4 * k + 4)

/-- The second slot is the exact negative of its odd source. -/
theorem moebius_four_mul_add_two (k : ℕ) :
    μ (4 * k + 2) = -μ (2 * k + 1) := by
  have hodd : Odd (2 * k + 1) := odd_two_mul_add_one k
  calc
    μ (4 * k + 2) = μ (2 * (2 * k + 1)) := by
      congr 1
      ring
    _ = -μ (2 * k + 1) := moebius_two_mul_of_odd (2 * k + 1) hodd

/-- The fourth slot vanishes because it is divisible by `2^2`. -/
theorem moebius_four_mul_add_four (k : ℕ) :
    μ (4 * k + 4) = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsq
  have hnot := (Nat.squarefree_iff_prime_squarefree.mp hsq) 2 Nat.prime_two
  apply hnot
  exact ⟨k + 1, by ring⟩

/-- Exact `(+,-,+,0)` identification of every complete four-slot cell. -/
theorem exact_four_slot_cell (k : ℕ) :
    μ (4 * k + 1) = μ (4 * k + 1) ∧
    μ (4 * k + 2) = -μ (2 * k + 1) ∧
    μ (4 * k + 3) = μ (4 * k + 3) ∧
    μ (4 * k + 4) = 0 := by
  exact ⟨rfl, moebius_four_mul_add_two k, rfl, moebius_four_mul_add_four k⟩

/-- Exact scalar compression of a complete four-slot cell. -/
theorem fourSlotCellSum_eq (k : ℕ) :
    fourSlotCellSum k = μ (4 * k + 1) - μ (2 * k + 1) + μ (4 * k + 3) := by
  rw [fourSlotCellSum, moebius_four_mul_add_two, moebius_four_mul_add_four]
  ring

/-- **Signed dyadic scale descent for an arbitrary physical cell mask.**
Multiplication by any integer weight commutes with the exact `(+,-,+,0)` cell
compression.  Thus a weighted current-scale four-cell sum is exactly the two
odd current-scale coordinates minus the weighted odd coordinate at half scale.
No absolute value is introduced, so cancellations between different masks or
least-square channels remain available after the transformation. -/
theorem weightedFourSlotCellSum_eq_dyadicScaleDescent
    (F : Finset ℕ) (w : ℕ → ℤ) :
    (∑ k ∈ F, w k * fourSlotCellSum k) =
      (∑ k ∈ F,
        w k * (μ (4 * k + 1) + μ (4 * k + 3))) -
      ∑ k ∈ F, w k * μ (2 * k + 1) := by
  calc
    (∑ k ∈ F, w k * fourSlotCellSum k) =
        ∑ k ∈ F,
          (w k * (μ (4 * k + 1) + μ (4 * k + 3)) -
            w k * μ (2 * k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [fourSlotCellSum_eq]
      ring
    _ =
        (∑ k ∈ F,
          w k * (μ (4 * k + 1) + μ (4 * k + 3))) -
        ∑ k ∈ F, w k * μ (2 * k + 1) := by
      rw [Finset.sum_sub_distrib]

end RHLean.Arithmetic
