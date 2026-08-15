import Mathlib
import RHLean.Arithmetic.PrimeWheelPartialError

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- Above the threshold `upper < 2 * y^2`, every nonzero partial-wheel error
has no resolved cofactor left: the source is a product of two primes strictly
above the cutoff.  The two primes may coincide. -/
theorem partialPrimeWheel_nonzero_error_factorization_of_two_mul_sq
    (y upper : ℕ) {n : ℕ}
    (hscale : upper < 2 * y ^ 2)
    (hnpos : 0 < n) (hnupper : n ≤ upper)
    (herr : μ n - partialPrimeWheelSite y upper n ≠ 0) :
    ∃ q r : ℕ,
      q.Prime ∧ r.Prime ∧ y < q ∧ y < r ∧
      primeWheelResolvedPart y n = 1 ∧ n = q * r := by
  have hn : n ≠ 0 := Nat.ne_of_gt hnpos
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
  have hbpos : 0 < primeWheelUnresolvedPart y n :=
    Nat.pos_of_ne_zero hb0
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
  have hySqLtb : y ^ 2 < primeWheelUnresolvedPart y n :=
    hySqLtqSq.trans_le hqSqLe
  have ha0 : primeWheelResolvedPart y n ≠ 0 :=
    primeWheelResolvedPart_ne_zero y n
  have hab := primeWheelResolvedPart_mul_unresolvedPart y hn
  have ha : primeWheelResolvedPart y n = 1 := by
    by_contra ha1
    have ha2 : 2 ≤ primeWheelResolvedPart y n := by
      have hapos : 0 < primeWheelResolvedPart y n := Nat.pos_of_ne_zero ha0
      omega
    have hcontr : 2 * y ^ 2 < 2 * y ^ 2 := calc
      2 * y ^ 2 < 2 * primeWheelUnresolvedPart y n := by omega
      _ ≤ primeWheelResolvedPart y n * primeWheelUnresolvedPart y n := by
        exact Nat.mul_le_mul_right (primeWheelUnresolvedPart y n) ha2
      _ = n := hab
      _ ≤ upper := hnupper
      _ < 2 * y ^ 2 := hscale
    exact (Nat.lt_irrefl _ hcontr)
  have hbEqN : primeWheelUnresolvedPart y n = n := by
    simpa [ha] using hab
  let r := primeWheelUnresolvedPart y n / q
  have hqr : q * r = primeWheelUnresolvedPart y n := by
    dsimp [r]
    exact Nat.mul_div_cancel' hqDvd
  have hqLeR : q ≤ r := by
    simpa [q, r] using Nat.minFac_le_div hbpos hbNotPrime
  have hr2 : 2 ≤ r := hqPrime.two_le.trans hqLeR
  have hrpos : 0 < r := by omega
  have hrDvdB : r ∣ primeWheelUnresolvedPart y n := by
    refine ⟨q, ?_⟩
    simpa [mul_comm] using hqr.symm
  have hrPrime : Nat.Prime r := by
    by_contra hrNotPrime
    have hr1 : r ≠ 1 := by omega
    let s := Nat.minFac r
    have hsPrime : Nat.Prime s := by
      dsimp [s]
      exact Nat.minFac_prime hr1
    have hsDvdR : s ∣ r := by
      simpa [s] using Nat.minFac_dvd r
    have hsDvdB : s ∣ primeWheelUnresolvedPart y n :=
      dvd_trans hsDvdR hrDvdB
    have hsPF : s ∈ (primeWheelUnresolvedPart y n).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hsPrime, hsDvdB, hb0⟩
    have hys : y < s := primeWheelUnresolvedPart_primeFactor_gt hsPF
    have hsSqLeR : s ^ 2 ≤ r := by
      simpa [s] using Nat.minFac_sq_le_self hrpos hrNotPrime
    have hySqLtsSq : y ^ 2 < s ^ 2 :=
      Nat.pow_lt_pow_left hys (by omega)
    have hySqLtR : y ^ 2 < r := hySqLtsSq.trans_le hsSqLeR
    have hcontr : 2 * y ^ 2 < 2 * y ^ 2 := calc
      2 * y ^ 2 < 2 * r := by omega
      _ ≤ q * r := by exact Nat.mul_le_mul_right r hqPrime.two_le
      _ = primeWheelUnresolvedPart y n := hqr
      _ = n := hbEqN
      _ ≤ upper := hnupper
      _ < 2 * y ^ 2 := hscale
    exact (Nat.lt_irrefl _ hcontr)
  have hrPF : r ∈ (primeWheelUnresolvedPart y n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hrPrime, hrDvdB, hb0⟩
  have hyr : y < r := primeWheelUnresolvedPart_primeFactor_gt hrPF
  have hnqr : n = q * r := by
    calc
      n = primeWheelUnresolvedPart y n := hbEqN.symm
      _ = q * r := hqr.symm
  exact ⟨q, r, hqPrime, hrPrime, hyq, hyr, ha, hnqr⟩

/-- Exact error-value classification above the threshold `upper < 2 * y^2`.
Every nonzero error is either a large-prime square with error `+1`, or a product
of two distinct large primes with error `+2`. -/
theorem partialPrimeWheel_nonzero_error_classification_of_two_mul_sq
    (y upper : ℕ) {n : ℕ}
    (hscale : upper < 2 * y ^ 2)
    (hnpos : 0 < n) (hnupper : n ≤ upper)
    (herr : μ n - partialPrimeWheelSite y upper n ≠ 0) :
    (∃ q : ℕ,
      q.Prime ∧ y < q ∧ n = q ^ 2 ∧
        μ n - partialPrimeWheelSite y upper n = 1) ∨
    (∃ q r : ℕ,
      q.Prime ∧ r.Prime ∧ q ≠ r ∧ y < q ∧ y < r ∧ n = q * r ∧
        μ n - partialPrimeWheelSite y upper n = 2) := by
  rcases partialPrimeWheel_nonzero_error_factorization_of_two_mul_sq
      y upper hscale hnpos hnupper herr with
    ⟨q, r, hqPrime, hrPrime, hyq, hyr, ha, hnqr⟩
  have hb1 : primeWheelUnresolvedPart y n ≠ 1 := by
    intro hb
    apply herr
    rw [partialPrimeWheel_error_eq y upper hnpos hnupper, if_pos hb]
  have hn : n ≠ 0 := Nat.ne_of_gt hnpos
  have hab := primeWheelResolvedPart_mul_unresolvedPart y hn
  have hbEqN : primeWheelUnresolvedPart y n = n := by
    simpa [ha] using hab
  have herrFormula :
      μ n - partialPrimeWheelSite y upper n = 1 + μ n := by
    rw [partialPrimeWheel_error_eq y upper hnpos hnupper, if_neg hb1]
    simp [ha, hbEqN]
  by_cases hqrEq : q = r
  · left
    subst r
    have hnq2 : n = q ^ 2 := by
      simpa [pow_two] using hnqr
    refine ⟨q, hqPrime, hyq, hnq2, ?_⟩
    have hnsq : ¬ Squarefree n := by
      rw [hnq2, Nat.squarefree_iff_prime_squarefree]
      push_neg
      exact ⟨q, hqPrime, by simp [pow_two]⟩
    have hmu0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
    rw [herrFormula, hmu0]
    norm_num
  · right
    refine ⟨q, r, hqPrime, hrPrime, hqrEq, hyq, hyr, hnqr, ?_⟩
    have hcop : q.Coprime r := by
      rw [hqPrime.coprime_iff_not_dvd]
      intro hqd
      exact hqrEq ((Nat.prime_dvd_prime_iff_eq hqPrime hrPrime).mp hqd)
    have hmuqr : μ (q * r) = 1 := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
      rw [ArithmeticFunction.moebius_apply_prime hqPrime,
        ArithmeticFunction.moebius_apply_prime hrPrime]
      norm_num
    have hmun : μ n = 1 := by
      rw [hnqr, hmuqr]
    rw [herrFormula, hmun]
    norm_num

end RHLean.Arithmetic
