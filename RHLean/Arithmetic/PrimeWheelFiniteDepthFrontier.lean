import Mathlib
import RHLean.Arithmetic.PrimeWheelPartialError

/-!
# Finite-depth prime-wheel frontier

The existing quotient-one frontier specializes to `upper < 2 * y^2`.  For a
quantitative modulus it is useful to keep an arbitrary fixed depth `L`.

A nonzero partial-wheel error always has unresolved part strictly larger than
`y^2`.  Hence, under `upper < L * y^2`, both the resolved cofactor and the
reciprocal quotient are strictly below `L`.  This turns the uncontrolled
small-quotient side of the wheel into a finite depth parameter rather than a
moving tail cutoff.

No primality-density or PNT estimate is used here.
-/

open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHLean.Arithmetic

/-- Any nonzero partial-wheel error has unresolved part above the square of the
wheel cutoff.  This is the scale-free part of the usual two-prime frontier
argument. -/
theorem partialPrimeWheel_nonzero_error_unresolved_gt_sq
    (y upper : ℕ) {n : ℕ}
    (hnpos : 0 < n) (hnupper : n ≤ upper)
    (herr : μ n - partialPrimeWheelSite y upper n ≠ 0) :
    y ^ 2 < primeWheelUnresolvedPart y n := by
  have hb1 : primeWheelUnresolvedPart y n ≠ 1 := by
    intro hb
    apply herr
    rw [partialPrimeWheel_error_eq y upper hnpos hnupper, if_pos hb]
  have hfactorNonzero :
      μ (primeWheelResolvedPart y n) *
          (1 + μ (primeWheelUnresolvedPart y n)) ≠ 0 := by
    intro hzero
    apply herr
    rw [partialPrimeWheel_error_eq y upper hnpos hnupper, if_neg hb1, hzero]
  have hsecond : 1 + μ (primeWheelUnresolvedPart y n) ≠ 0 := by
    intro hzero
    apply hfactorNonzero
    simp [hzero]
  have hb0 : primeWheelUnresolvedPart y n ≠ 0 :=
    primeWheelUnresolvedPart_ne_zero y n
  have hbpos : 0 < primeWheelUnresolvedPart y n := Nat.pos_of_ne_zero hb0
  have hbNotPrime : ¬ Nat.Prime (primeWheelUnresolvedPart y n) := by
    intro hbPrime
    apply hsecond
    rw [ArithmeticFunction.moebius_apply_prime hbPrime]
    norm_num
  let q := Nat.minFac (primeWheelUnresolvedPart y n)
  have hqPrime : Nat.Prime q := by
    dsimp [q]
    exact Nat.minFac_prime hb1
  have hqDvd : q ∣ primeWheelUnresolvedPart y n := by
    simpa [q] using Nat.minFac_dvd (primeWheelUnresolvedPart y n)
  have hqPF : q ∈ (primeWheelUnresolvedPart y n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hqPrime, hqDvd, hb0⟩
  have hyq : y < q := primeWheelUnresolvedPart_primeFactor_gt hqPF
  have hqSqLe : q ^ 2 ≤ primeWheelUnresolvedPart y n := by
    simpa [q] using Nat.minFac_sq_le_self hbpos hbNotPrime
  have hySqLtqSq : y ^ 2 < q ^ 2 :=
    Nat.pow_lt_pow_left hyq (by omega)
  exact hySqLtqSq.trans_le hqSqLe

/-- Under a fixed depth window `upper < L * y^2`, every nonzero wheel error has
resolved cofactor below `L`. -/
theorem partialPrimeWheel_nonzero_error_resolvedPart_lt_depth
    (L y upper : ℕ) {n : ℕ}
    (hL : 0 < L) (hscale : upper < L * y ^ 2)
    (hnpos : 0 < n) (hnupper : n ≤ upper)
    (herr : μ n - partialPrimeWheelSite y upper n ≠ 0) :
    primeWheelResolvedPart y n < L := by
  have hbgt := partialPrimeWheel_nonzero_error_unresolved_gt_sq
    y upper hnpos hnupper herr
  have hab := primeWheelResolvedPart_mul_unresolvedPart y (Nat.ne_of_gt hnpos)
  by_contra hnot
  have hLa : L ≤ primeWheelResolvedPart y n := Nat.le_of_not_gt hnot
  have hleft :
      L * y ^ 2 < L * primeWheelUnresolvedPart y n :=
    Nat.mul_lt_mul_of_pos_left hbgt hL
  have hright :
      L * primeWheelUnresolvedPart y n ≤
        primeWheelResolvedPart y n * primeWheelUnresolvedPart y n :=
    Nat.mul_le_mul_right (primeWheelUnresolvedPart y n) hLa
  have hgt : L * y ^ 2 < n := by
    calc
      L * y ^ 2 < L * primeWheelUnresolvedPart y n := hleft
      _ ≤ primeWheelResolvedPart y n * primeWheelUnresolvedPart y n := hright
      _ = n := hab
  have hnlt : n < L * y ^ 2 := hnupper.trans_lt hscale
  exact Nat.lt_asymm hgt hnlt

/-- The same finite-depth window bounds every reciprocal quotient on the
unresolved frontier by `L - 1`. -/
theorem partialPrimeWheel_nonzero_error_div_lt_depth
    (L y upper : ℕ) {n : ℕ}
    (hL : 0 < L) (hscale : upper < L * y ^ 2)
    (hnpos : 0 < n) (hnupper : n ≤ upper)
    (herr : μ n - partialPrimeWheelSite y upper n ≠ 0) :
    upper / n < L := by
  have hbgt := partialPrimeWheel_nonzero_error_unresolved_gt_sq
    y upper hnpos hnupper herr
  have ha0 : primeWheelResolvedPart y n ≠ 0 :=
    primeWheelResolvedPart_ne_zero y n
  have ha1 : 1 ≤ primeWheelResolvedPart y n :=
    Nat.one_le_iff_ne_zero.mpr ha0
  have hab := primeWheelResolvedPart_mul_unresolvedPart y (Nat.ne_of_gt hnpos)
  have hbLeN : primeWheelUnresolvedPart y n ≤ n := by
    calc
      primeWheelUnresolvedPart y n =
          1 * primeWheelUnresolvedPart y n := by simp
      _ ≤ primeWheelResolvedPart y n * primeWheelUnresolvedPart y n :=
        Nat.mul_le_mul_right (primeWheelUnresolvedPart y n) ha1
      _ = n := hab
  have hySqLtN : y ^ 2 < n := hbgt.trans_le hbLeN
  have hscaleN : upper < L * n :=
    hscale.trans (Nat.mul_lt_mul_of_pos_left hySqLtN hL)
  apply (Nat.div_lt_iff_lt_mul hnpos).2
  simpa [Nat.mul_comm] using hscaleN

/-- Combined finite-depth frontier certificate. -/
theorem partialPrimeWheel_nonzero_error_finite_depth
    (L y upper : ℕ) {n : ℕ}
    (hL : 0 < L) (hscale : upper < L * y ^ 2)
    (hnpos : 0 < n) (hnupper : n ≤ upper)
    (herr : μ n - partialPrimeWheelSite y upper n ≠ 0) :
    primeWheelResolvedPart y n < L ∧ upper / n < L := by
  exact ⟨
    partialPrimeWheel_nonzero_error_resolvedPart_lt_depth
      L y upper hL hscale hnpos hnupper herr,
    partialPrimeWheel_nonzero_error_div_lt_depth
      L y upper hL hscale hnpos hnupper herr⟩

end RHLean.Arithmetic
