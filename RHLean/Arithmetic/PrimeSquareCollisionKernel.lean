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

/-- **A square collision isolates its active slot.**  If an odd prime square
hits one of the three active values in a four-cell, then the prime itself cannot
divide either of the other two active values.  Thus the local exponent pattern
for that prime has one square-kill coordinate and two genuine misses; there is
no hidden first-power hit elsewhere in the same three-slot cell. -/
theorem prime_not_dvd_other_threeSlotValue_of_square_hit
    (p k i j : ℕ)
    (hp : 2 < p)
    (hi : i < 3) (hj : j < 3)
    (hij : i ≠ j)
    (hsq : p ^ 2 ∣ threeSlotValue k i) :
    ¬ p ∣ threeSlotValue k j := by
  have hpcur : p ∣ threeSlotValue k i := by
    exact dvd_trans (dvd_pow_self p (by norm_num)) hsq
  intro hpj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hdiff : p ∣ threeSlotValue k j - threeSlotValue k i :=
      Nat.dvd_sub hpj hpcur
    have hgap :
        threeSlotValue k j - threeSlotValue k i = j - i := by
      unfold threeSlotValue
      omega
    rw [hgap] at hdiff
    have hpos : 0 < j - i := by omega
    have hple : p ≤ j - i := Nat.le_of_dvd hpos hdiff
    omega
  · have hdiff : p ∣ threeSlotValue k i - threeSlotValue k j :=
      Nat.dvd_sub hpcur hpj
    have hgap :
        threeSlotValue k i - threeSlotValue k j = i - j := by
      unfold threeSlotValue
      omega
    rw [hgap] at hdiff
    have hpos : 0 < i - j := by omega
    have hple : p ≤ i - j := Nat.le_of_dvd hpos hdiff
    omega

/-- In particular, an odd-prime square collision can occur in at most one
active slot of a given four-cell. -/
theorem primeSquareCollision_slot_unique
    (p k i j : ℕ)
    (hp : 2 < p)
    (hi : i < 3) (hj : j < 3)
    (hiSq : p ^ 2 ∣ threeSlotValue k i)
    (hjSq : p ^ 2 ∣ threeSlotValue k j) :
    i = j := by
  by_contra hij
  have hnot := prime_not_dvd_other_threeSlotValue_of_square_hit
    p k i j hp hi hj hij hiSq
  apply hnot
  exact dvd_trans (dvd_pow_self p (by norm_num)) hjSq

/-- **For `p > 6`, a current square collision forces a complete prime miss in
the next active cell.**  The next active values differ from the square-hit value
by only `2` through `6`, so none can be divisible by such a prime.  Therefore a
literal adjacent-cell realization cannot create the local exponent state `1`
for any prime `p ≥ 7`; any nontrivial `0 <-> 1` parity flip for those primes must
be realized in a different arithmetic fiber. -/
theorem prime_not_dvd_next_threeSlotValue_of_square_hit
    (p k i j : ℕ)
    (hp : 6 < p)
    (hi : i < 3) (hj : j < 3)
    (hsq : p ^ 2 ∣ threeSlotValue k i) :
    ¬ p ∣ threeSlotValue (k + 1) j := by
  have hpcur : p ∣ threeSlotValue k i := by
    exact dvd_trans (dvd_pow_self p (by norm_num)) hsq
  intro hpnext
  have hdiff :
      p ∣ threeSlotValue (k + 1) j - threeSlotValue k i :=
    Nat.dvd_sub hpnext hpcur
  have hgap :
      threeSlotValue (k + 1) j - threeSlotValue k i = 4 + j - i := by
    unfold threeSlotValue
    omega
  rw [hgap] at hdiff
  have hpos : 0 < 4 + j - i := by omega
  have hle : 4 + j - i ≤ 6 := by omega
  have hple : p ≤ 4 + j - i := Nat.le_of_dvd hpos hdiff
  omega

/-- Cell-level version: after a `p^2` collision with `p > 6`, all three active
coordinates in the following four-cell are `p`-misses. -/
theorem primeSquareHitsThreeSlotCell_next_prime_miss
    (p k : ℕ)
    (hp : 6 < p)
    (hcur : primeSquareHitsThreeSlotCell p k) :
    ∀ j : ℕ, j < 3 → ¬ p ∣ threeSlotValue (k + 1) j := by
  intro j hj
  rcases hcur with ⟨i, hi, hsq⟩
  exact prime_not_dvd_next_threeSlotValue_of_square_hit
    p k i j hp hi hj hsq

end RHLean.Arithmetic
