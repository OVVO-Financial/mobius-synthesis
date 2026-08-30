import Mathlib
import RHLean.Proof.SquareRootLowPrimeMatchedFrontierBound

/-!
# Exact real telescope for the low-prime running state

The fresh-layer theorems are indexed only by primes.  To recover the actual
change of running state across an interval, this file proves that a composite
cutoff contributes no step: a canonical largest prime factor greater than one
cannot equal a composite integer.

Consequently the full arithmetic telescope reduces exactly to the fresh-prime
sum:

`T(K) - T(U) = sum_{K<p<=U} Delta_p`.

Combining this with the complete matched-frontier theorem gives a direct bound
on the processed real response, not merely on an auxiliary atom sum.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- A canonical largest prime factor cannot equal a composite integer greater
than one. -/
theorem canonicalLargestPrimeFactor_ne_of_one_lt_not_prime
    {c p : ℕ} (hp : 1 < p) (hnot : ¬ p.Prime) :
    canonicalLargestPrimeFactor c ≠ p := by
  intro heq
  by_cases hc : 1 < c
  · have hlpfPrime : (canonicalLargestPrimeFactor c).Prime :=
      canonicalLargestPrimeFactor_prime hc
    exact hnot (heq ▸ hlpfPrime)
  · have hlpfOne : canonicalLargestPrimeFactor c = 1 := by
      unfold canonicalLargestPrimeFactor
      rw [dif_neg hc]
    omega

/-- Across a composite cutoff greater than one, the condition `P+(c) <= p` is
unchanged from the predecessor cutoff. -/
theorem canonicalLargestPrimeFactor_le_composite_iff_le_pred
    {c p : ℕ} (hp : 1 < p) (hnot : ¬ p.Prime) :
    canonicalLargestPrimeFactor c ≤ p ↔
      canonicalLargestPrimeFactor c ≤ p - 1 := by
  constructor
  · intro hle
    have hne := canonicalLargestPrimeFactor_ne_of_one_lt_not_prime
      (c := c) hp hnot
    omega
  · intro hle
    exact hle.trans (Nat.sub_le p 1)

/-- The complex running response is constant across a composite cutoff greater
than one. -/
theorem squareRootBornPostTailRunningLowPrimeResponse_eq_pred_of_not_prime
    (R K j p : ℕ) (hp : 1 < p) (hnot : ¬ p.Prime) :
    squareRootBornPostTailRunningLowPrimeResponse R K j p =
      squareRootBornPostTailRunningLowPrimeResponse R K j (p - 1) := by
  unfold squareRootBornPostTailRunningLowPrimeResponse
  congr 1
  · apply Finset.sum_congr rfl
    intro c _hc
    simp only [canonicalLargestPrimeFactor_le_composite_iff_le_pred hp hnot]
  · apply Finset.sum_congr rfl
    intro c _hc
    simp only [canonicalLargestPrimeFactor_le_composite_iff_le_pred hp hnot]

/-- Hence the real running imbalance has zero composite step. -/
theorem squareRootLowPrimeRunningImbalanceReal_eq_pred_of_not_prime
    (R K j p : ℕ) (hp : 1 < p) (hnot : ¬ p.Prime) :
    squareRootLowPrimeRunningImbalanceReal R K j p =
      squareRootLowPrimeRunningImbalanceReal R K j (p - 1) := by
  unfold squareRootLowPrimeRunningImbalanceReal
    squareRootLowPrimeRunningImbalance
  rw [squareRootBornPostTailRunningLowPrimeResponse_eq_pred_of_not_prime
    R K j p hp hnot]

/-- Generic arithmetic telescope on a natural interval. -/
theorem real_pred_sub_telescope
    (T : ℕ → ℝ) (K n : ℕ) :
    (∑ p ∈ Finset.Ioc K (K + n), (T (p - 1) - T p)) =
      T K - T (K + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hset :
          Finset.Ioc K (K + (n + 1)) =
            insert (K + n + 1) (Finset.Ioc K (K + n)) := by
        ext p
        simp
        omega
      have hnotmem : K + n + 1 ∉ Finset.Ioc K (K + n) := by
        simp
      rw [hset, Finset.sum_insert hnotmem, ih]
      have hpred : K + n + 1 - 1 = K + n := by omega
      rw [hpred]
      ring

/-- Interval form of the generic arithmetic telescope. -/
theorem real_pred_sub_telescope_Ioc
    (T : ℕ → ℝ) {K U : ℕ} (hKU : K ≤ U) :
    (∑ p ∈ Finset.Ioc K U, (T (p - 1) - T p)) = T K - T U := by
  have h := real_pred_sub_telescope T K (U - K)
  simpa [Nat.add_sub_of_le hKU] using h

/-- **Exact fresh-prime telescope.**  Composite arithmetic cutoffs contribute
zero, so the actual running-state change is exactly the prime-filtered fresh
increment sum. -/
theorem squareRootLowPrimeRunningImbalanceReal_sub_eq_freshIncrement_sum
    {R K j U : ℕ} (hK : 1 ≤ K) (hKU : K ≤ U) :
    squareRootLowPrimeRunningImbalanceReal R K j K -
        squareRootLowPrimeRunningImbalanceReal R K j U =
      ∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p := by
  have htelescope := real_pred_sub_telescope_Ioc
    (squareRootLowPrimeRunningImbalanceReal R K j) hKU
  calc
    squareRootLowPrimeRunningImbalanceReal R K j K -
        squareRootLowPrimeRunningImbalanceReal R K j U =
      ∑ p ∈ Finset.Ioc K U,
        (squareRootLowPrimeRunningImbalanceReal R K j (p - 1) -
          squareRootLowPrimeRunningImbalanceReal R K j p) := htelescope.symm
    _ = ∑ p ∈ Finset.Ioc K U,
        if p.Prime then squareRootLowPrimeFreshIncrementReal R K j p else 0 := by
      apply Finset.sum_congr rfl
      intro p hpIoc
      have hpGt : 1 < p := by
        have hKp := (Finset.mem_Ioc.mp hpIoc).1
        omega
      by_cases hpPrime : p.Prime
      · rw [if_pos hpPrime]
        exact squareRootLowPrimeRunningImbalanceReal_step_eq_freshIncrementReal
          R K j p hpPrime
      · rw [if_neg hpPrime,
          squareRootLowPrimeRunningImbalanceReal_eq_pred_of_not_prime
            R K j p hpGt hpPrime]
        ring
    _ = ∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p := by
      unfold squareRootLowPrimeFreshPrimeSet
      rw [Finset.sum_filter]

/-- **Processed-response bound by the complete matching frontier.** -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_sub_le_matchingFrontierCard
    {R K j U : ℕ} (hR : 2 ≤ R) (hK : 1 ≤ K)
    (hKU : K ≤ U) (hUR : U < R) :
    |squareRootLowPrimeRunningImbalanceReal R K j K -
        squareRootLowPrimeRunningImbalanceReal R K j U| ≤
      ((squareRootLowPrimeOwnedResponseMatchingFrontier R K U).card : ℝ) := by
  rw [squareRootLowPrimeRunningImbalanceReal_sub_eq_freshIncrement_sum
    hK hKU]
  exact abs_squareRootLowPrimeFreshIncrementReal_sum_le_matchingFrontierCard
    hR hUR

/-- Terminal absolute value bounded by the shallow state and the complete
matched frontier. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_shallow_add_frontierCard
    {R K j U : ℕ} (hR : 2 ≤ R) (hK : 1 ≤ K)
    (hKU : K ≤ U) (hUR : U < R) :
    |squareRootLowPrimeRunningImbalanceReal R K j U| ≤
      |squareRootLowPrimeRunningImbalanceReal R K j K| +
        ((squareRootLowPrimeOwnedResponseMatchingFrontier R K U).card : ℝ) := by
  have hdiff :=
    abs_squareRootLowPrimeRunningImbalanceReal_sub_le_matchingFrontierCard
      (R := R) (K := K) (j := j) (U := U) hR hK hKU hUR
  rw [show squareRootLowPrimeRunningImbalanceReal R K j U =
      squareRootLowPrimeRunningImbalanceReal R K j K -
        (squareRootLowPrimeRunningImbalanceReal R K j K -
          squareRootLowPrimeRunningImbalanceReal R K j U) by ring]
  calc
    |squareRootLowPrimeRunningImbalanceReal R K j K -
        (squareRootLowPrimeRunningImbalanceReal R K j K -
          squareRootLowPrimeRunningImbalanceReal R K j U)| ≤
      |squareRootLowPrimeRunningImbalanceReal R K j K| +
        |squareRootLowPrimeRunningImbalanceReal R K j K -
          squareRootLowPrimeRunningImbalanceReal R K j U| := by
            simpa only [abs_neg] using abs_sub
              (squareRootLowPrimeRunningImbalanceReal R K j K)
              (squareRootLowPrimeRunningImbalanceReal R K j K -
                squareRootLowPrimeRunningImbalanceReal R K j U)
    _ ≤ |squareRootLowPrimeRunningImbalanceReal R K j K| +
        ((squareRootLowPrimeOwnedResponseMatchingFrontier R K U).card : ℝ) :=
      add_le_add_left hdiff _

end RHLean.Proof
