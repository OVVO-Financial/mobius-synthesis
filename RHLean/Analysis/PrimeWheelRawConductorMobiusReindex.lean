import Mathlib
import RHLean.Analysis.DivisorUpperMobius
import RHLean.Analysis.PrimeWheelRawConductorCoefficient

/-!
# Möbius reindexing of the raw conductor coefficient

The complete periodic raw conductor coefficient is an upper-divisor tail:
for each expansion point `e`, its contribution is present exactly on conductors
`q` dividing the expansion divisor `D_e`.  Applying the upper-divisor Möbius
transform before taking any norm collapses that whole tail to the single layer
`d = D_e`.

This is finite exact cancellation only.  No estimate or triangle inequality is
used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Upper-divisor Möbius transform of the finite raw conductor family. -/
def primeWheelRawUpperMobiusTransform
    (S : Finset ℕ) (N d : ℕ) : ℂ :=
  ∑ q ∈ N.divisors,
    if d ∣ q then
      (((μ (q / d) : ℤ) : ℂ)) *
        primeWheelRawConductorArithmeticCoefficient S N q
    else 0

/-- Exact collapse of the raw conductor tail.  Once every expansion divisor is
known to divide the ambient modulus, the upper-divisor Möbius transform keeps
only expansion points whose divisor is exactly `d`. -/
theorem primeWheelRawUpperMobiusTransform_eq_exactExpansionDivisor
    (S : Finset ℕ) (N d : ℕ)
    (hN : N ≠ 0) (hdpos : 0 < d)
    (hdiv : ∀ e : PrimeWheelRawExpansionPoint S,
      primeWheelRawExpansionDivisor S e ∣ N) :
    primeWheelRawUpperMobiusTransform S N d =
      -∑ e : PrimeWheelRawExpansionPoint S,
        primeWheelRawExpansionWeight S e *
          (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ)) *
          (if d = primeWheelRawExpansionDivisor S e then 1 else 0) := by
  classical
  unfold primeWheelRawUpperMobiusTransform
    primeWheelRawConductorArithmeticCoefficient
  calc
    (∑ q ∈ N.divisors,
      if d ∣ q then
        (((μ (q / d) : ℤ) : ℂ)) *
          (-∑ e : PrimeWheelRawExpansionPoint S,
            primeWheelRawExpansionWeight S e *
              (if q ∣ primeWheelRawExpansionDivisor S e then
                (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ))
              else 0))
      else 0) =
      -∑ q ∈ N.divisors,
        ∑ e : PrimeWheelRawExpansionPoint S,
          if d ∣ q then
            (((μ (q / d) : ℤ) : ℂ)) *
              (primeWheelRawExpansionWeight S e *
                (if q ∣ primeWheelRawExpansionDivisor S e then
                  (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ))
                else 0))
          else 0 := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro q hq
            by_cases hdq : d ∣ q
            · simp only [hdq, if_true]
              rw [mul_neg, Finset.mul_sum]
            · simp [hdq]
    _ =
      -∑ e : PrimeWheelRawExpansionPoint S,
        ∑ q ∈ N.divisors,
          if d ∣ q then
            (((μ (q / d) : ℤ) : ℂ)) *
              (primeWheelRawExpansionWeight S e *
                (if q ∣ primeWheelRawExpansionDivisor S e then
                  (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ))
                else 0))
          else 0 := by
            congr 1
            rw [Finset.sum_comm]
    _ =
      -∑ e : PrimeWheelRawExpansionPoint S,
        (primeWheelRawExpansionWeight S e *
          (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ))) *
          (∑ q ∈ N.divisors,
            if d ∣ q then
              if q ∣ primeWheelRawExpansionDivisor S e then
                (((μ (q / d) : ℤ) : ℂ))
              else 0
            else 0) := by
              congr 1
              apply Fintype.sum_congr
              intro e
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro q hq
              by_cases hdq : d ∣ q
              · by_cases hqD : q ∣ primeWheelRawExpansionDivisor S e
                · simp [hdq, hqD]
                  ring
                · simp [hdq, hqD]
              · simp [hdq]
    _ =
      -∑ e : PrimeWheelRawExpansionPoint S,
        primeWheelRawExpansionWeight S e *
          (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ)) *
          (if d = primeWheelRawExpansionDivisor S e then 1 else 0) := by
            congr 1
            apply Fintype.sum_congr
            intro e
            rw [sum_complex_moebius_upper_divisors_ambient_eq_one_or_zero
              (hdiv e) hN hdpos]

end RHLean.Analysis
