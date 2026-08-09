import RHLean.Arithmetic.PrimeThreeActivation

namespace RHLean.CellMask

/-- Rational indicator for divisibility by `3` in the cell-mask branch. -/
def primeThreeIndicator (n : ℕ) : ℚ :=
  if 3 ∣ n then 1 else 0

/-- The three prime-3 channel indicators in a complete four-slot cell sum to one. -/
theorem primeThreeIndicator_sum_eq_one (k : ℕ) :
    primeThreeIndicator (4 * k + 1) +
        primeThreeIndicator (4 * k + 2) +
        primeThreeIndicator (4 * k + 3) = 1 := by
  rcases RHLean.Arithmetic.prime_three_exactly_one_active_slot k with h | h | h
  · simp [primeThreeIndicator, h.1, h.2.1, h.2.2]
  · simp [primeThreeIndicator, h.1, h.2.1, h.2.2]
  · simp [primeThreeIndicator, h.1, h.2.1, h.2.2]

/-- Rational mean of the three prime-3 cell-mask channels. -/
def primeThreeCellMean (k : ℕ) : ℚ :=
  (primeThreeIndicator (4 * k + 1) +
      primeThreeIndicator (4 * k + 2) +
      primeThreeIndicator (4 * k + 3)) / 3

/-- Every complete cell has exact prime-3 mask mean `1 / 3`. -/
theorem primeThreeCellMean_eq_one_third (k : ℕ) :
    primeThreeCellMean k = 1 / 3 := by
  unfold primeThreeCellMean
  rw [primeThreeIndicator_sum_eq_one]

/-- Energy of the rational prime-3 mean mode. -/
def primeThreeCellMeanEnergy (k : ℕ) : ℚ :=
  primeThreeCellMean k ^ 2

/-- The exact rational prime-3 cell-mask mean energy is `1 / 9`. -/
theorem primeThreeCellMeanEnergy_eq_one_ninth (k : ℕ) :
    primeThreeCellMeanEnergy k = 1 / 9 := by
  rw [primeThreeCellMeanEnergy, primeThreeCellMean_eq_one_third]
  norm_num

end RHLean.CellMask
