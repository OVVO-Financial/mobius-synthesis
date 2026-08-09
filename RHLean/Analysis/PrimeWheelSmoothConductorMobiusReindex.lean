import Mathlib
import RHLean.Analysis.DivisorUpperMobius
import RHLean.Analysis.PrimeWheelRamanujanBoundaryBulkReduction

/-!
# Möbius reindexing of the smooth conductor packets

Summing a divisor-form Ramanujan packet over every conductor dividing a fixed
ambient modulus produces a second Möbius cancellation.  After exchanging the
finite conductor and boundary-divisor sums, the upper-divisor Möbius sum is a
Kronecker delta at the ambient modulus.  Thus every smooth boundary divisor
strictly below the torus modulus disappears before any norm is taken.

The conductor-one bulk is kept separately and survives exactly once.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Summing a Möbius divisor packet over all divisor conductors collapses to the
single top boundary divisor. -/
theorem sum_moebius_divisorPackets_eq_top
    (N : ℕ) (hN : N ≠ 0) (F : ℕ → ℤ) :
    (∑ q ∈ N.divisors,
      ∑ d ∈ q.divisors, μ (q / d) * F d) = F N := by
  classical
  calc
    (∑ q ∈ N.divisors,
      ∑ d ∈ q.divisors, μ (q / d) * F d) =
      ∑ q ∈ N.divisors,
        ∑ d ∈ N.divisors,
          if d ∣ q then μ (q / d) * F d else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            have hqN : q ∣ N := Nat.dvd_of_mem_divisors hq
            rw [← Nat.divisors_filter_dvd_of_dvd hN hqN]
            rw [Finset.sum_filter]
    _ =
      ∑ d ∈ N.divisors,
        ∑ q ∈ N.divisors,
          if d ∣ q then μ (q / d) * F d else 0 := by
            rw [Finset.sum_comm]
    _ =
      ∑ d ∈ N.divisors,
        (∑ q ∈ N.divisors,
          if d ∣ q then μ (q / d) else 0) * F d := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro q hq
            by_cases hdq : d ∣ q <;> simp [hdq]
    _ =
      ∑ d ∈ N.divisors,
        (if d = N then 1 else 0) * F d := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [sum_moebius_upper_divisors_eq_one_or_zero
              (Nat.dvd_of_mem_divisors hd) (Nat.pos_of_mem_divisors hd) hN]
    _ = F N := by
      have hNmem : N ∈ N.divisors := Nat.mem_divisors_self N hN
      simp [hNmem]

/-- The complete family of smooth divisor-boundary packets collapses to the
single boundary packet at the ambient torus modulus. -/
theorem sum_primeWheelSmoothBoundaryPacket_divisors_eq_top
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    (∑ q ∈ W.modulus.divisors,
      primeWheelSmoothBoundaryPacket W x q) =
      ∑ a ∈ primeWheelSmoothDivisorSites W,
        -(μ a) *
          divisorIntervalBoundary W.modulus a W.lower x := by
  classical
  unfold primeWheelSmoothBoundaryPacket
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.mul_sum]
  congr 1
  exact sum_moebius_divisorPackets_eq_top
    W.modulus (Nat.ne_of_gt W.modulus_pos)
    (fun d => divisorIntervalBoundary d a W.lower x)

/-- The all-conductor smooth arithmetic packet, including the retained
conductor-one bulk, is therefore one top-divisor boundary packet plus one bulk
term. -/
theorem sum_primeWheelSmoothBoundary_add_bulk_divisors
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    (∑ q ∈ W.modulus.divisors,
      (primeWheelSmoothBoundaryPacket W x q +
        primeWheelSmoothBulkMass W *
          ((Finset.Ioc W.lower x).card : ℤ) *
          (if q = 1 then 1 else 0))) =
      (∑ a ∈ primeWheelSmoothDivisorSites W,
        -(μ a) *
          divisorIntervalBoundary W.modulus a W.lower x) +
        primeWheelSmoothBulkMass W *
          ((Finset.Ioc W.lower x).card : ℤ) := by
  classical
  rw [Finset.sum_add_distrib,
    sum_primeWheelSmoothBoundaryPacket_divisors_eq_top]
  congr 1
  have h1mem : 1 ∈ W.modulus.divisors :=
    (Nat.one_mem_divisors).2 (Nat.ne_of_gt W.modulus_pos)
  calc
    (∑ q ∈ W.modulus.divisors,
      primeWheelSmoothBulkMass W *
        ((Finset.Ioc W.lower x).card : ℤ) *
        (if q = 1 then 1 else 0)) =
      ∑ q ∈ W.modulus.divisors,
        if q = 1 then
          primeWheelSmoothBulkMass W *
            ((Finset.Ioc W.lower x).card : ℤ)
        else 0 := by
          apply Finset.sum_congr rfl
          intro q hq
          by_cases hq1 : q = 1 <;> simp [hq1]
    _ = primeWheelSmoothBulkMass W *
        ((Finset.Ioc W.lower x).card : ℤ) := by
          simp [h1mem]

end RHLean.Analysis
