import Mathlib
import RHLean.Arithmetic.PrimeWheelFiniteDepthFrontier

/-!
# Small-cofactor semiprime structure at fixed wheel depth

If the physical endpoint lies below `L * y^2` with `L <= y`, then three
unresolved prime factors would already exceed the endpoint.  Thus every
nonzero partial-wheel error has exactly two unresolved large prime factors,
while the resolved cofactor is strictly below `L`.

This extends the two-large-prime geometry of the quotient-one frontier without
forcing the resolved cofactor to be one.  For fixed `L`, the entire unresolved
frontier is therefore a finite family of small-cofactor semiprime faces.
-/

open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHLean.Arithmetic

/-- At fixed depth below the wheel cutoff, the unresolved part of every
nonzero wheel error is a product of two primes above the cutoff. -/
theorem partialPrimeWheel_nonzero_error_unresolved_semiprime_of_depth
    (L y upper : ℕ) {n : ℕ}
    (hL : 0 < L) (hLy : L ≤ y) (hscale : upper < L * y ^ 2)
    (hnpos : 0 < n) (hnupper : n ≤ upper)
    (herr : μ n - partialPrimeWheelSite y upper n ≠ 0) :
    ∃ q r : ℕ,
      q.Prime ∧ r.Prime ∧ y < q ∧ y < r ∧
        primeWheelUnresolvedPart y n = q * r := by
  have hypos : 0 < y := hL.trans_le hLy
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
    have hy3Ltqy2 : y ^ 3 < q * y ^ 2 := by
      have h := Nat.mul_lt_mul_of_pos_right hyq (pow_pos hypos 2)
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
    have hqy2Ltqr : q * y ^ 2 < q * r :=
      Nat.mul_lt_mul_of_pos_left hySqLtR hqPrime.pos
    have hy3Ltb : y ^ 3 < primeWheelUnresolvedPart y n := by
      rw [← hqr]
      exact hy3Ltqy2.trans hqy2Ltqr
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
    have hy3LtN : y ^ 3 < n := hy3Ltb.trans_le hbLeN
    have hLySq : L * y ^ 2 ≤ y ^ 3 := by
      have h := Nat.mul_le_mul_right (y ^ 2) hLy
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
    have hnlt : n < y ^ 3 := (hnupper.trans_lt hscale).trans_le hLySq
    exact Nat.lt_asymm hy3LtN hnlt
  have hrPF : r ∈ (primeWheelUnresolvedPart y n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hrPrime, hrDvdB, hb0⟩
  have hyr : y < r := primeWheelUnresolvedPart_primeFactor_gt hrPF
  exact ⟨q, r, hqPrime, hrPrime, hyq, hyr, hqr.symm⟩

/-- Full finite-depth geometry: a nonzero wheel error is a small resolved
cofactor times two unresolved primes, and its reciprocal quotient is also
strictly below the same fixed depth. -/
theorem partialPrimeWheel_nonzero_error_smallCofactor_semiprime
    (L y upper : ℕ) {n : ℕ}
    (hL : 0 < L) (hLy : L ≤ y) (hscale : upper < L * y ^ 2)
    (hnpos : 0 < n) (hnupper : n ≤ upper)
    (herr : μ n - partialPrimeWheelSite y upper n ≠ 0) :
    ∃ a q r : ℕ,
      a < L ∧ q.Prime ∧ r.Prime ∧ y < q ∧ y < r ∧
        n = a * q * r ∧ upper / n < L := by
  have ha := partialPrimeWheel_nonzero_error_resolvedPart_lt_depth
    L y upper hL hscale hnpos hnupper herr
  rcases partialPrimeWheel_nonzero_error_unresolved_semiprime_of_depth
      L y upper hL hLy hscale hnpos hnupper herr with
    ⟨q, r, hqPrime, hrPrime, hyq, hyr, hb⟩
  have hab := primeWheelResolvedPart_mul_unresolvedPart y (Nat.ne_of_gt hnpos)
  have hn :
      n = primeWheelResolvedPart y n * q * r := by
    calc
      n = primeWheelResolvedPart y n * primeWheelUnresolvedPart y n := hab.symm
      _ = primeWheelResolvedPart y n * (q * r) := by rw [hb]
      _ = primeWheelResolvedPart y n * q * r := by ring
  have hdiv := partialPrimeWheel_nonzero_error_div_lt_depth
    L y upper hL hscale hnpos hnupper herr
  exact ⟨primeWheelResolvedPart y n, q, r, ha, hqPrime, hrPrime,
    hyq, hyr, hn, hdiv⟩

end RHLean.Arithmetic
