import Mathlib
import RHLean.Analysis.PrimeSievePNTCentering

/-!
# Quotient-fibre reindexing of the prime-sieve PNT error

This module reindexes the exact prime-first PNT error by the quotient

```text
d = floor (x / q).
```

For positive `d`, the fibre is the reciprocal integer interval

```text
max y (floor (x / (d+1))) < q <= floor (x / d).
```

The singleton logarithmic-integral masses from `PrimeSievePNTCentering`
telescope across each complete interval.  Consequently the reindexed PNT error
is exactly a lower-scale Mertens weight times a prime-count-minus-Li discrepancy
on this reciprocal interval family.

Everything here is finite algebra.  No prime-number-theorem error estimate,
short-interval estimate, large-sieve estimate, or power saving is asserted.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- Quotients that can occur for `y < q <= x`. -/
def primeSieveQuotientSupport (y x : ℕ) : Finset ℕ :=
  Finset.Icc 1 (x / (y + 1))

/-- The literal quotient fibre before identifying its reciprocal interval. -/
def primeSieveQuotientFiber (y x d : ℕ) : Finset ℕ :=
  (Finset.Ioc y x).filter fun q => x / q = d

/-- Lower endpoint of the reciprocal quotient interval. -/
def primeSieveReciprocalLower (y x d : ℕ) : ℕ :=
  max y (x / (d + 1))

/-- Upper endpoint of the reciprocal quotient interval. -/
def primeSieveReciprocalUpper (x d : ℕ) : ℕ :=
  x / d

/-- Integer interval on which `floor (x/q)` is the fixed positive quotient `d`,
with the original lower prime cutoff `y` retained. -/
def primeSieveReciprocalInterval (y x d : ℕ) : Finset ℕ :=
  Finset.Ioc (primeSieveReciprocalLower y x d)
    (primeSieveReciprocalUpper x d)

@[simp] theorem mem_primeSieveQuotientFiber
    {y x d q : ℕ} :
    q ∈ primeSieveQuotientFiber y x d ↔
      y < q ∧ q ≤ x ∧ x / q = d := by
  simp [primeSieveQuotientFiber, and_assoc]

@[simp] theorem mem_primeSieveReciprocalInterval
    {y x d q : ℕ} :
    q ∈ primeSieveReciprocalInterval y x d ↔
      primeSieveReciprocalLower y x d < q ∧
        q ≤ primeSieveReciprocalUpper x d := by
  simp [primeSieveReciprocalInterval]

/-- Exact reciprocal-interval characterization of a positive quotient fibre. -/
theorem primeSieveQuotientFiber_eq_reciprocalInterval
    (y x d : ℕ) (hd : 0 < d) :
    primeSieveQuotientFiber y x d =
      primeSieveReciprocalInterval y x d := by
  ext q
  rw [mem_primeSieveQuotientFiber, mem_primeSieveReciprocalInterval]
  constructor
  · rintro ⟨hyq, hqx, hdiv⟩
    have hqpos : 0 < q := by omega
    have hleft : x / (d + 1) < q := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < d + 1)).2
      have h := Nat.lt_mul_div_succ x hqpos
      simpa [hdiv, Nat.mul_comm] using h
    have hright : q ≤ x / d := by
      apply (Nat.le_div_iff_mul_le hd).2
      have h := Nat.mul_div_le x q
      simpa [hdiv, Nat.mul_comm] using h
    exact ⟨max_lt hyq hleft, hright⟩
  · rintro ⟨hlower, hupper⟩
    have hyq : y < q :=
      lt_of_le_of_lt (le_max_left y (x / (d + 1))) hlower
    have hleft : x / (d + 1) < q :=
      lt_of_le_of_lt (le_max_right y (x / (d + 1))) hlower
    have hqpos : 0 < q := by omega
    have hlo : d * q ≤ x := by
      have h := (Nat.le_div_iff_mul_le hd).1 hupper
      simpa [Nat.mul_comm] using h
    have hhi : x < (d + 1) * q := by
      have h := (Nat.div_lt_iff_lt_mul (by omega : 0 < d + 1)).1 hleft
      simpa [Nat.mul_comm] using h
    have hdiv : x / q = d := Nat.div_eq_of_lt_le hlo hhi
    have hd1 : 1 ≤ d := by omega
    have hqx : q ≤ x := by
      calc
        q = 1 * q := by simp
        _ ≤ d * q := Nat.mul_le_mul_right q hd1
        _ ≤ x := hlo
    exact ⟨hyq, hqx, hdiv⟩

/-- Every quotient actually produced by `y < q <= x` lies in the finite support. -/
theorem div_mem_primeSieveQuotientSupport_of_mem_Ioc
    {y x q : ℕ} (hq : q ∈ Finset.Ioc y x) :
    x / q ∈ primeSieveQuotientSupport y x := by
  rcases Finset.mem_Ioc.mp hq with ⟨hyq, hqx⟩
  have hqpos : 0 < q := by omega
  have hlow : 1 ≤ x / q :=
    (Nat.one_le_div_iff hqpos).2 hqx
  have hyq' : y + 1 ≤ q := by omega
  have hhigh : x / q ≤ x / (y + 1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < y + 1)).2
    calc
      (x / q) * (y + 1) ≤ (x / q) * q :=
        Nat.mul_le_mul_left (x / q) hyq'
      _ ≤ x := Nat.div_mul_le_self x q
  exact Finset.mem_Icc.mpr ⟨hlow, hhigh⟩

/-- Generic finite quotient reindexing for a prime-coordinate weight. -/
theorem sum_mertens_div_eq_quotientFibers
    (y x : ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc y x, a q * mertensSummatory (x / q)) =
      ∑ d ∈ primeSieveQuotientSupport y x,
        (∑ q ∈ primeSieveQuotientFiber y x d, a q) *
          mertensSummatory d := by
  classical
  calc
    (∑ q ∈ Finset.Ioc y x, a q * mertensSummatory (x / q)) =
        ∑ q ∈ Finset.Ioc y x,
          ∑ d ∈ primeSieveQuotientSupport y x,
            if x / q = d then a q * mertensSummatory d else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      have hd := div_mem_primeSieveQuotientSupport_of_mem_Ioc hq
      simp [hd]
    _ = ∑ d ∈ primeSieveQuotientSupport y x,
        ∑ q ∈ Finset.Ioc y x,
          if x / q = d then a q * mertensSummatory d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ primeSieveQuotientSupport y x,
        ∑ q ∈ primeSieveQuotientFiber y x d,
          a q * mertensSummatory d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [primeSieveQuotientFiber, Finset.sum_filter]
    _ = ∑ d ∈ primeSieveQuotientSupport y x,
        (∑ q ∈ primeSieveQuotientFiber y x d, a q) *
          mertensSummatory d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_mul]

/-- The generic quotient reindexing with each positive fibre replaced by its
explicit reciprocal interval. -/
theorem sum_mertens_div_eq_reciprocalIntervals
    (y x : ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc y x, a q * mertensSummatory (x / q)) =
      ∑ d ∈ primeSieveQuotientSupport y x,
        (∑ q ∈ primeSieveReciprocalInterval y x d, a q) *
          mertensSummatory d := by
  rw [sum_mertens_div_eq_quotientFibers]
  apply Finset.sum_congr rfl
  intro d hdmem
  have hd : 0 < d := by
    have := (Finset.mem_Icc.mp hdmem).1
    omega
  rw [primeSieveQuotientFiber_eq_reciprocalInterval y x d hd]

/-- Singleton Li increments telescope on an ordinary integer interval. -/
theorem sum_primeSievePNTDensity_Ioc
    {a b : ℕ} (hab : a ≤ b) :
    (∑ q ∈ Finset.Ioc a b, primeSievePNTDensity q) =
      ((logarithmicIntegralFromTwo (b : ℝ) -
        logarithmicIntegralFromTwo (a : ℝ) : ℝ) : ℂ) := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hab
      subst a
      simp
  | succ b ih =>
      by_cases h : a ≤ b
      · rw [Finset.sum_Ioc_succ_top h]
        rw [ih h]
        simp [primeSievePNTDensity]
      · have ha : a = b + 1 := by omega
        subst a
        simp [primeSievePNTDensity]

/-- Telescoped Li mass of one reciprocal quotient interval.  Empty reversed
intervals are assigned mass zero, matching the finite interval itself. -/
def primeSieveReciprocalLiMass (y x d : ℕ) : ℂ :=
  if primeSieveReciprocalLower y x d ≤ primeSieveReciprocalUpper x d then
    ((logarithmicIntegralFromTwo (primeSieveReciprocalUpper x d : ℝ) -
      logarithmicIntegralFromTwo (primeSieveReciprocalLower y x d : ℝ) : ℝ) : ℂ)
  else 0

/-- The deterministic singleton density sums to the Li endpoint difference on
each reciprocal quotient interval. -/
theorem sum_primeSievePNTDensity_reciprocalInterval
    (y x d : ℕ) :
    (∑ q ∈ primeSieveReciprocalInterval y x d,
      primeSievePNTDensity q) =
      primeSieveReciprocalLiMass y x d := by
  by_cases h : primeSieveReciprocalLower y x d ≤
      primeSieveReciprocalUpper x d
  · unfold primeSieveReciprocalInterval
    rw [sum_primeSievePNTDensity_Ioc h]
    simp [primeSieveReciprocalLiMass, h]
  · have hle : primeSieveReciprocalUpper x d ≤
        primeSieveReciprocalLower y x d := by omega
    rw [primeSieveReciprocalInterval, Finset.Ioc_eq_empty_of_le hle]
    simp [primeSieveReciprocalLiMass, h]

/-- Exact prime count on one reciprocal interval, cast to `ℂ` through the prime
indicator. -/
def primeSieveReciprocalPrimeCount (y x d : ℕ) : ℂ :=
  ∑ q ∈ primeSieveReciprocalInterval y x d,
    primeSievePrimeIndicator q

/-- The prime-indicator sum is literally the cardinality of the prime subset. -/
theorem primeSieveReciprocalPrimeCount_eq_card
    (y x d : ℕ) :
    primeSieveReciprocalPrimeCount y x d =
      (((primeSieveReciprocalInterval y x d).filter Nat.Prime).card : ℕ) := by
  classical
  simp [primeSieveReciprocalPrimeCount, primeSievePrimeIndicator]

/-- Classical prime-count discrepancy on one reciprocal interval. -/
def primeSieveReciprocalPrimeDiscrepancy (y x d : ℕ) : ℂ :=
  primeSieveReciprocalPrimeCount y x d -
    primeSieveReciprocalLiMass y x d

/-- Summing indicator minus deterministic Li density on a quotient fibre gives
exactly its prime-count discrepancy. -/
theorem sum_primeIndicator_sub_density_reciprocalInterval
    (y x d : ℕ) :
    (∑ q ∈ primeSieveReciprocalInterval y x d,
      (primeSievePrimeIndicator q - primeSievePNTDensity q)) =
      primeSieveReciprocalPrimeDiscrepancy y x d := by
  unfold primeSieveReciprocalPrimeDiscrepancy
    primeSieveReciprocalPrimeCount
  rw [Finset.sum_sub_distrib,
    sum_primeSievePNTDensity_reciprocalInterval]

/-- Quotient-reindexed deterministic PNT bulk. -/
def primeSieveReciprocalPNTBulk (y x : ℕ) : ℂ :=
  ∑ d ∈ primeSieveQuotientSupport y x,
    primeSieveReciprocalLiMass y x d * mertensSummatory d

/-- Quotient-reindexed exact prime tail. -/
def primeSieveReciprocalPrimeTail (y x : ℕ) : ℂ :=
  ∑ d ∈ primeSieveQuotientSupport y x,
    primeSieveReciprocalPrimeCount y x d * mertensSummatory d

/-- Quotient-reindexed prime-count discrepancy, weighted by lower-scale Mertens. -/
def primeSieveReciprocalPNTError (y x : ℕ) : ℂ :=
  ∑ d ∈ primeSieveQuotientSupport y x,
    primeSieveReciprocalPrimeDiscrepancy y x d * mertensSummatory d

/-- The deterministic PNT bulk is exactly its quotient-fibre Li reindexing. -/
theorem primeSievePNTBulk_eq_reciprocalPNTBulk
    (y x : ℕ) :
    primeSievePNTBulk y x = primeSieveReciprocalPNTBulk y x := by
  unfold primeSievePNTBulk primeSieveReciprocalPNTBulk
  rw [sum_mertens_div_eq_reciprocalIntervals]
  apply Finset.sum_congr rfl
  intro d hd
  rw [sum_primeSievePNTDensity_reciprocalInterval]

/-- The exact prime tail is the same quotient sum with actual prime counts. -/
theorem primeSieveMertensPrimeTail_eq_reciprocalPrimeTail
    (y x : ℕ) :
    primeSieveMertensPrimeTail y x =
      primeSieveReciprocalPrimeTail y x := by
  calc
    primeSieveMertensPrimeTail y x =
        ∑ q ∈ Finset.Ioc y x,
          primeSievePrimeIndicator q * mertensSummatory (x / q) := by
      unfold primeSieveMertensPrimeTail primeSievePrimeIndicator
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hp : q.Prime <;> simp [hp]
    _ = ∑ d ∈ primeSieveQuotientSupport y x,
        (∑ q ∈ primeSieveReciprocalInterval y x d,
          primeSievePrimeIndicator q) * mertensSummatory d :=
      sum_mertens_div_eq_reciprocalIntervals y x primeSievePrimeIndicator
    _ = primeSieveReciprocalPrimeTail y x := by
      rfl

/-- **Quotient reindexing of the PNT error.**  The only fibre discrepancy left
is actual prime count minus the telescoped Li mass on the reciprocal interval. -/
theorem primeSievePNTError_eq_reciprocalPNTError
    (y x : ℕ) :
    primeSievePNTError y x = primeSieveReciprocalPNTError y x := by
  unfold primeSievePNTError primeSieveReciprocalPNTError
  rw [sum_mertens_div_eq_reciprocalIntervals]
  apply Finset.sum_congr rfl
  intro d hd
  rw [sum_primeIndicator_sub_density_reciprocalInterval]

/-- The quotient error is exactly prime-count tail minus deterministic Li bulk. -/
theorem primeSieveReciprocalPNTError_eq_primeTail_sub_bulk
    (y x : ℕ) :
    primeSieveReciprocalPNTError y x =
      primeSieveReciprocalPrimeTail y x -
        primeSieveReciprocalPNTBulk y x := by
  unfold primeSieveReciprocalPNTError primeSieveReciprocalPrimeTail
    primeSieveReciprocalPNTBulk
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  unfold primeSieveReciprocalPrimeDiscrepancy
  ring

/-- After quotient reindexing, the deterministic Li main term cancels exactly
between the corrected all-plus comb and the PNT error. -/
theorem primeSievePNTCorrected_sub_two_error_eq_allPlus_sub_two_primeTail
    (y x : ℕ) :
    primeSievePNTCorrectedAllPlusMass y x - 2 * primeSievePNTError y x =
      allPlusPrimeCombPrefixMass y x -
        2 * primeSieveReciprocalPrimeTail y x := by
  rw [primeSievePNTError_eq_reciprocalPNTError,
    primeSieveReciprocalPNTError_eq_primeTail_sub_bulk,
    ← primeSievePNTBulk_eq_reciprocalPNTBulk]
  unfold primeSievePNTCorrectedAllPlusMass
  ring

/-- The quotient-reindexed PNT error after the same square-wheel centering used
by the canonical nonzero response. -/
def primorialReciprocalPNTErrorCenteredResponse (k n : ℕ) : ℂ :=
  primorialSquareZeroModeCenter k n
    (fun x =>
      primeSieveReciprocalPNTError (primorialPNTPrimeSieveCutoff k) x)

/-- The old centered PNT-error object is definitionally replaced by the exact
weighted reciprocal-interval prime discrepancy. -/
theorem primorialPNTErrorCenteredResponse_eq_reciprocal
    (k n : ℕ) :
    primorialPNTErrorCenteredResponse k n =
      primorialReciprocalPNTErrorCenteredResponse k n := by
  unfold primorialPNTErrorCenteredResponse
    primorialReciprocalPNTErrorCenteredResponse
    primorialSquareZeroModeCenter
  simp only [primeSievePNTError_eq_reciprocalPNTError]

/-- **Reciprocal-interval form of `H_{k,n}`.**  The remaining prime-distribution
term is exactly the centered weighted family of classical prime-count-minus-Li
discrepancies on quotient intervals. -/
theorem primorialMinimalSquareWheelNonzeroResponse_eq_pntCorrected_sub_two_reciprocalError
    (k n : ℕ)
    (hlower : primorialBlockLower k < squarePrefixEndpoint n)
    (hupper : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n =
      primorialPNTCorrectedCombCenteredResponse k n -
        2 * primorialReciprocalPNTErrorCenteredResponse k n := by
  rw [primorialMinimalSquareWheelNonzeroResponse_eq_pntCorrected_sub_two_error
    k n hlower hupper,
    primorialPNTErrorCenteredResponse_eq_reciprocal]

/-- Exact norm transfer for the reciprocal-interval formulation. -/
theorem norm_primorialMinimalSquareWheelNonzeroResponse_le_reciprocalPNT
    (k n : ℕ)
    (hlower : primorialBlockLower k < squarePrefixEndpoint n)
    (hupper : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    ‖squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n‖ ≤
      ‖primorialPNTCorrectedCombCenteredResponse k n‖ +
        2 * ‖primorialReciprocalPNTErrorCenteredResponse k n‖ := by
  rw [primorialMinimalSquareWheelNonzeroResponse_eq_pntCorrected_sub_two_reciprocalError
    k n hlower hupper]
  simpa [norm_mul] using
    (norm_sub_le
      (primorialPNTCorrectedCombCenteredResponse k n)
      (2 * primorialReciprocalPNTErrorCenteredResponse k n))

end RHLean.Analysis
