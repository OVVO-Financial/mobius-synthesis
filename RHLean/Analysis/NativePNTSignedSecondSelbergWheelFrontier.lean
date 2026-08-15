import Mathlib
import Mathlib.Data.Finset.NatDivisors
import RHLean.Analysis.NativePNTSignedSecondSelberg
import RHLean.Arithmetic.PrimeWheelPartialErrorThreshold

/-!
# Signed second Selberg kernel on the square-root wheel frontier

The exact signed second-Selberg recurrence from `NativePNTSignedSecondSelberg`
uses the coefficient

`K₂(n) = (Lambda * Lambda)(n) - Lambda(n) log n`.

This file evaluates that exact coefficient on the arithmetic frontier already
classified by `PrimeWheelPartialErrorThreshold`: below `upper < 2*y^2`, every
nonzero partial-wheel error is either a square of one prime above the cutoff or
a product of two distinct primes above the cutoff.

The square face is the negative diagonal `-log(p)^2`; the distinct two-prime
face is the positive mixed term `2 log(p) log(q)`.  Thus the true signed second
kernel is a second-order prime-wheel face operator on the exact unresolved
frontier, rather than a positive scalar `Lambda_2` mass.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators Pointwise

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Exact value of `Lambda_2` on a prime square. -/
theorem nativeLambdaTwo_prime_sq
    (p : ℕ) (hp : p.Prime) :
    nativeLambdaTwo (p ^ 2) = 3 * (Real.log (p : ℝ)) ^ 2 := by
  rw [← nativeMobiusLogSquareDivisorFiber_eq_lambdaTwo]
  unfold nativeMobiusLogSquareDivisorFiber
  rw [hp.divisors_sq]
  simp [ArithmeticFunction.moebius_apply_prime hp, pow_two, hp.ne_zero,
    hp.ne_one, Nat.cast_mul, Real.log_mul]
  ring

/-- The signed second-Selberg kernel is negative on the one-prime square face. -/
theorem nativePNTSignedSecondSelbergKernel_prime_sq
    (p : ℕ) (hp : p.Prime) :
    nativePNTSignedSecondSelbergKernel (p ^ 2) =
      -(Real.log (p : ℝ)) ^ 2 := by
  rw [nativePNTSignedSecondSelbergKernel_eq_lambdaTwo_sub_two_log,
    nativeLambdaTwo_prime_sq p hp]
  have hlam : Λ (p ^ 2) = Real.log (p : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [hlam, Nat.cast_pow, Real.log_pow]
  norm_num
  ring

/-- Exact value of `Lambda_2` on a product of two distinct primes. -/
theorem nativeLambdaTwo_mul_distinct_primes
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    nativeLambdaTwo (p * q) =
      2 * Real.log (p : ℝ) * Real.log (q : ℝ) := by
  have hcop : p.Coprime q := by
    rw [hp.coprime_iff_not_dvd]
    intro hpdq
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpdq)
  have hmupq : μ (p * q) = 1 := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp,
      ArithmeticFunction.moebius_apply_prime hq]
    norm_num
  have hpdiv : p * q / p = q := Nat.mul_div_cancel_left q hp.pos
  have hqdiv : p * q / q = p := by
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel_left p hq.pos)
  have hpqpos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hself : p * q / (p * q) = 1 := Nat.div_self hpqpos
  have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hpq_ne_one : p * q ≠ 1 := by
    intro h
    have hpDvdOne : p ∣ 1 := by
      rw [← h]
      exact dvd_mul_right p q
    exact hp.ne_one (Nat.dvd_one.mp hpDvdOne)
  have hpq_ne_p : p * q ≠ p := by
    intro h
    have h' : p * q = p * 1 := by simpa using h
    exact hq.ne_one (Nat.mul_left_cancel hp.pos h')
  have hpq_ne_q : p * q ≠ q := by
    intro h
    have h' : q * p = q * 1 := by simpa [Nat.mul_comm] using h
    exact hp.ne_one (Nat.mul_left_cancel hq.pos h')
  have h1q : 1 ≠ q := hq.ne_one.symm
  have h1p : 1 ≠ p := hp.ne_one.symm
  have h1pq : 1 ≠ p * q := hpq_ne_one.symm
  have hqp : q ≠ p := hpq.symm
  have hq_pq : q ≠ p * q := hpq_ne_q.symm
  have hp_pq : p ≠ p * q := hpq_ne_p.symm
  have hprod :
      ({1, p} : Finset ℕ) * ({1, q} : Finset ℕ) =
        ({1, q, p, p * q} : Finset ℕ) := by
    ext x
    simp [Finset.mul_def]
    aesop
  have h1mem : 1 ∉ ({q, p, p * q} : Finset ℕ) := by
    simp [h1q, h1p, h1pq]
  have hqmem : q ∉ ({p, p * q} : Finset ℕ) := by
    simp [hqp, hq_pq]
  have hpmem : p ∉ ({p * q} : Finset ℕ) := by
    simp [hp_pq]
  rw [← nativeMobiusLogSquareDivisorFiber_eq_lambdaTwo]
  unfold nativeMobiusLogSquareDivisorFiber
  rw [Nat.divisors_mul p q, hp.divisors, hq.divisors, hprod]
  rw [Finset.sum_insert h1mem, Finset.sum_insert hqmem,
    Finset.sum_insert hpmem]
  simp [hmupq, hpdiv, hqdiv, hself,
    ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_prime hq]
  rw [Real.log_mul hp0 hq0]
  ring

/-- The signed kernel is the positive mixed face on two distinct primes. -/
theorem nativePNTSignedSecondSelbergKernel_mul_distinct_primes
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    nativePNTSignedSecondSelbergKernel (p * q) =
      2 * Real.log (p : ℝ) * Real.log (q : ℝ) := by
  rw [nativePNTSignedSecondSelbergKernel_eq_lambdaTwo_sub_two_log,
    nativeLambdaTwo_mul_distinct_primes p q hp hq hpq]
  have hnotPow : ¬ IsPrimePow (p * q) := by
    intro hpow
    rcases (isPrimePow_nat_iff (p * q)).1 hpow with ⟨s, k, hs, hk, hEq⟩
    have hpDvd : p ∣ s ^ k := by
      rw [hEq]
      exact dvd_mul_right p q
    have hqDvd : q ∣ s ^ k := by
      rw [hEq]
      exact dvd_mul_left q p
    have hpr : p = s := by
      have hprDvd : p ∣ s := hp.dvd_of_dvd_pow hpDvd
      exact (Nat.prime_dvd_prime_iff_eq hp hs).mp hprDvd
    have hqr : q = s := by
      have hqrDvd : q ∣ s := hq.dvd_of_dvd_pow hqDvd
      exact (Nat.prime_dvd_prime_iff_eq hq hs).mp hqrDvd
    exact hpq (hpr.trans hqr.symm)
  have hlam : Λ (p * q) = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnotPow
  rw [hlam]
  ring

/-- **Exact square-root wheel-frontier classification of the true signed second
Selberg kernel.**  The only nonzero partial-wheel errors are the negative
one-prime diagonal or the positive two-prime mixed face. -/
theorem nativePNTSignedSecondSelbergKernel_wheelFrontier_classification
    (y upper : ℕ) {n : ℕ}
    (hscale : upper < 2 * y ^ 2)
    (hnpos : 0 < n) (hnupper : n ≤ upper)
    (herr : μ n - partialPrimeWheelSite y upper n ≠ 0) :
    (∃ q : ℕ,
      q.Prime ∧ y < q ∧ n = q ^ 2 ∧
        μ n - partialPrimeWheelSite y upper n = 1 ∧
        nativePNTSignedSecondSelbergKernel n =
          -(Real.log (q : ℝ)) ^ 2) ∨
    (∃ q r : ℕ,
      q.Prime ∧ r.Prime ∧ q ≠ r ∧ y < q ∧ y < r ∧ n = q * r ∧
        μ n - partialPrimeWheelSite y upper n = 2 ∧
        nativePNTSignedSecondSelbergKernel n =
          2 * Real.log (q : ℝ) * Real.log (r : ℝ)) := by
  rcases partialPrimeWheel_nonzero_error_classification_of_two_mul_sq
      y upper hscale hnpos hnupper herr with hsquare | hpair
  · rcases hsquare with ⟨q, hq, hyq, hn, herrval⟩
    left
    refine ⟨q, hq, hyq, hn, herrval, ?_⟩
    rw [hn]
    exact nativePNTSignedSecondSelbergKernel_prime_sq q hq
  · rcases hpair with ⟨q, r, hq, hr, hqr, hyq, hyr, hn, herrval⟩
    right
    refine ⟨q, r, hq, hr, hqr, hyq, hyr, hn, herrval, ?_⟩
    rw [hn]
    exact nativePNTSignedSecondSelbergKernel_mul_distinct_primes q r hq hr hqr

end RHLean.Analysis
