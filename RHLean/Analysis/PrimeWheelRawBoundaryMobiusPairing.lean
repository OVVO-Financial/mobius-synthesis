import Mathlib
import RHLean.Analysis.PrimeWheelRawConductorMobiusReindex

/-!
# Reindex the raw conductor-boundary pairing

The all-conductor raw packet pairs the conductor coefficient `A(q)` with a
Möbius divisor-boundary packet.  Before taking any norm, exchange the conductor
and boundary-divisor sums.  The inner conductor sum is exactly the upper-divisor
Möbius transform proved in `PrimeWheelRawConductorMobiusReindex`.

This is the algebraic bridge from the conductor packet formula to the collapsed
raw expansion layers.  No estimate is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Pairing a raw conductor coefficient family with an arbitrary complex-valued
Möbius divisor packet is exactly pairing its upper-divisor Möbius transform with
the boundary-divisor family. -/
theorem sum_rawConductorCoefficient_mul_mobiusPacket_eq_upperMobiusPairing
    (S : Finset ℕ) (N : ℕ) (hN : N ≠ 0) (B : ℕ → ℂ) :
    (∑ q ∈ N.divisors,
      primeWheelRawConductorArithmeticCoefficient S N q *
        (∑ d ∈ q.divisors,
          (((μ (q / d) : ℤ) : ℂ)) * B d)) =
      ∑ d ∈ N.divisors,
        primeWheelRawUpperMobiusTransform S N d * B d := by
  classical
  calc
    (∑ q ∈ N.divisors,
      primeWheelRawConductorArithmeticCoefficient S N q *
        (∑ d ∈ q.divisors,
          (((μ (q / d) : ℤ) : ℂ)) * B d)) =
      ∑ q ∈ N.divisors,
        ∑ d ∈ N.divisors,
          if d ∣ q then
            primeWheelRawConductorArithmeticCoefficient S N q *
              ((((μ (q / d) : ℤ) : ℂ)) * B d)
          else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            have hqN : q ∣ N := Nat.dvd_of_mem_divisors hq
            rw [← Nat.divisors_filter_dvd_of_dvd hN hqN]
            rw [Finset.mul_sum, Finset.sum_filter]
    _ =
      ∑ d ∈ N.divisors,
        ∑ q ∈ N.divisors,
          if d ∣ q then
            primeWheelRawConductorArithmeticCoefficient S N q *
              ((((μ (q / d) : ℤ) : ℂ)) * B d)
          else 0 := by
            rw [Finset.sum_comm]
    _ =
      ∑ d ∈ N.divisors,
        (∑ q ∈ N.divisors,
          if d ∣ q then
            (((μ (q / d) : ℤ) : ℂ)) *
              primeWheelRawConductorArithmeticCoefficient S N q
          else 0) * B d := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro q hq
            by_cases hdq : d ∣ q
            · simp [hdq]
              ring
            · simp [hdq]
    _ =
      ∑ d ∈ N.divisors,
        primeWheelRawUpperMobiusTransform S N d * B d := by
          rfl

/-- Integer-valued boundary specialization used by the actual divisor-boundary
packets in the primorial residual. -/
theorem sum_rawConductorCoefficient_mul_intMobiusPacket_eq_upperMobiusPairing
    (S : Finset ℕ) (N : ℕ) (hN : N ≠ 0) (B : ℕ → ℤ) :
    (∑ q ∈ N.divisors,
      primeWheelRawConductorArithmeticCoefficient S N q *
        (((∑ d ∈ q.divisors, μ (q / d) * B d : ℤ) : ℂ))) =
      ∑ d ∈ N.divisors,
        primeWheelRawUpperMobiusTransform S N d * (((B d : ℤ) : ℂ)) := by
  have hcast (q : ℕ) :
      (((∑ d ∈ q.divisors, μ (q / d) * B d : ℤ) : ℂ)) =
        ∑ d ∈ q.divisors,
          (((μ (q / d) : ℤ) : ℂ)) * (((B d : ℤ) : ℂ)) := by
    push_cast
    rfl
  simp_rw [hcast]
  exact sum_rawConductorCoefficient_mul_mobiusPacket_eq_upperMobiusPairing
    S N hN (fun d => (((B d : ℤ) : ℂ)))

end RHLean.Analysis
