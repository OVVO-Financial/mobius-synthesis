import Mathlib
import RHLean.Analysis.RamanujanDivisorBoundary

/-!
# Ramanujan divisor boundaries with the conductor-one bulk retained

The nontrivial-conductor boundary identity in `RamanujanDivisorBoundary`
uses `q > 1` to cancel the common interval bulk.  For full-conductor
recombination we instead keep that bulk explicitly.  The complementary
Möbius sum is the Kronecker delta at conductor one, so every conductor admits
one uniform exact formula:

`Ramanujan packet = boundary packet + conductor-one bulk`.

This is finite algebra only.  No estimate or norm inequality is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Complementary-divisor form of the Möbius Kronecker delta, valid for every
natural conductor. -/
theorem sum_moebius_complementary_divisors_eq_one_or_zero (q : ℕ) :
    (∑ d ∈ q.divisors, μ (q / d)) = if q = 1 then 1 else 0 := by
  calc
    (∑ d ∈ q.divisors, μ (q / d)) =
        ∑ d ∈ q.divisors, μ d := by
          exact Nat.sum_div_divisors q (fun d : ℕ => μ d)
    _ = if q = 1 then 1 else 0 :=
      sum_moebius_divisors_eq_one_or_zero q

/-- Exact Ramanujan divisor-boundary decomposition with the common bulk kept
explicitly.  For `q > 1` the final term vanishes; for `q = 1` it is exactly the
interval cardinality. -/
theorem ramanujanDivisorSumOn_eq_boundary_add_bulk
    (q a : ℕ) (I : Finset ℕ) :
    ramanujanDivisorSumOn q a I =
      (∑ d ∈ q.divisors,
        μ (q / d) * divisorResidueBoundary I d a) +
      (I.card : ℤ) * (if q = 1 then 1 else 0) := by
  classical
  rw [ramanujanDivisorSumOn_eq_residueCounts]
  have hmu :
      (∑ d ∈ q.divisors, μ (q / d)) = if q = 1 then 1 else 0 :=
    sum_moebius_complementary_divisors_eq_one_or_zero q
  unfold divisorResidueBoundary
  calc
    (∑ d ∈ q.divisors,
        ((d : ℤ) * μ (q / d)) * divisorResidueCount I d a) =
      ∑ d ∈ q.divisors,
        (μ (q / d) *
            ((d : ℤ) * divisorResidueCount I d a - (I.card : ℤ)) +
          μ (q / d) * (I.card : ℤ)) := by
            apply Finset.sum_congr rfl
            intro d hd
            ring
    _ =
      (∑ d ∈ q.divisors,
        μ (q / d) *
          ((d : ℤ) * divisorResidueCount I d a - (I.card : ℤ))) +
      ∑ d ∈ q.divisors, μ (q / d) * (I.card : ℤ) := by
        rw [Finset.sum_add_distrib]
    _ =
      (∑ d ∈ q.divisors,
        μ (q / d) *
          ((d : ℤ) * divisorResidueCount I d a - (I.card : ℤ))) +
      (I.card : ℤ) * (∑ d ∈ q.divisors, μ (q / d)) := by
        congr 1
        calc
          (∑ d ∈ q.divisors, μ (q / d) * (I.card : ℤ)) =
              ∑ d ∈ q.divisors, (I.card : ℤ) * μ (q / d) := by
                apply Finset.sum_congr rfl
                intro d hd
                ring
          _ = (I.card : ℤ) * (∑ d ∈ q.divisors, μ (q / d)) := by
            rw [Finset.mul_sum]
    _ =
      (∑ d ∈ q.divisors,
        μ (q / d) *
          ((d : ℤ) * divisorResidueCount I d a - (I.card : ℤ))) +
      (I.card : ℤ) * (if q = 1 then 1 else 0) := by
        rw [hmu]

/-- Pinned interval form of the all-conductor boundary-plus-bulk identity. -/
theorem ramanujanDivisorInterval_eq_boundary_add_bulk
    (q a lower upper : ℕ) :
    ramanujanDivisorInterval q a lower upper =
      (∑ d ∈ q.divisors,
        μ (q / d) * divisorIntervalBoundary d a lower upper) +
      ((Finset.Ioc lower upper).card : ℤ) *
        (if q = 1 then 1 else 0) := by
  exact ramanujanDivisorSumOn_eq_boundary_add_bulk
    q a (Finset.Ioc lower upper)

/-- The existing nontrivial-conductor boundary formula is recovered by
specializing the all-conductor identity. -/
theorem ramanujanDivisorInterval_eq_boundary_of_one_lt
    {q : ℕ} (hq : 1 < q) (a lower upper : ℕ) :
    ramanujanDivisorInterval q a lower upper =
      ∑ d ∈ q.divisors,
        μ (q / d) * divisorIntervalBoundary d a lower upper := by
  rw [ramanujanDivisorInterval_eq_boundary_add_bulk]
  simp [Nat.ne_of_gt hq]

end RHLean.Analysis
