import Mathlib

noncomputable section

namespace RHLean.Arithmetic

/-!
# Prime-square collision geometry for consecutive three-slot four-cells

The active coordinates of the `k`-th four-cell are

`4*k+1`, `4*k+2`, `4*k+3`.

A labelled square collision `0_p` means that `p^2` divides at least one of
these three coordinates.  For `p > 2`, the same labelled collision cannot
occur again in the immediately following active three-slot cell.  This file
formalizes that exact zero-diagonal statement without introducing a Markov
model.
-/

/-- The `j`-th active coordinate of the `k`-th four-cell, with `j = 0,1,2`. -/
def threeSlotValue (k j : ℕ) : ℕ :=
  4 * k + (j + 1)

/-- A prime square hits at least one of the three active coordinates. -/
def primeSquareHitsThreeSlotCell (p k : ℕ) : Prop :=
  ∃ j : ℕ, j < 3 ∧ p ^ 2 ∣ threeSlotValue k j

/-- Slotwise form of the exact labelled zero-diagonal theorem.

If `p > 2`, then `p^2` cannot divide one active coordinate of a four-cell and
also one active coordinate of the immediately following four-cell.  The two
coordinates differ by an integer in `{2,3,4,5,6}`, while `p^2 >= 9`. -/
theorem samePrimeSquareCollision_nextFourCell_impossible
    (p k i j : ℕ)
    (hp : 2 < p)
    (hi : i < 3) (hj : j < 3)
    (hcur : p ^ 2 ∣ threeSlotValue k i)
    (hnext : p ^ 2 ∣ threeSlotValue (k + 1) j) :
    False := by
  have hdiff :
      p ^ 2 ∣ threeSlotValue (k + 1) j - threeSlotValue k i :=
    Nat.dvd_sub hnext hcur
  have hgap :
      threeSlotValue (k + 1) j - threeSlotValue k i = 4 + j - i := by
    unfold threeSlotValue
    omega
  rw [hgap] at hdiff
  have hgap_pos : 0 < 4 + j - i := by
    omega
  have hgap_le : 4 + j - i ≤ 6 := by
    omega
  have hp_sq_le : p ^ 2 ≤ 4 + j - i :=
    Nat.le_of_dvd hgap_pos hdiff
  have hp_sq_ge : 9 ≤ p ^ 2 := by
    nlinarith
  omega

/-- Cell-level form: a labelled `p^2` collision has zero one-step
self-transition on the active three-slot process. -/
theorem primeSquareHitsThreeSlotCell_not_next
    (p k : ℕ) (hp : 2 < p)
    (hcur : primeSquareHitsThreeSlotCell p k) :
    ¬ primeSquareHitsThreeSlotCell p (k + 1) := by
  rintro ⟨j, hj, hnext⟩
  rcases hcur with ⟨i, hi, hcur⟩
  exact samePrimeSquareCollision_nextFourCell_impossible
    p k i j hp hi hj hcur hnext

end RHLean.Arithmetic
