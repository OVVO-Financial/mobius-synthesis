import Mathlib
import RHLean.Analysis.PrimeSieveQuotientPNTError

/-!
# Abel summation of the reciprocal prime-sieve PNT error

`RHLean.Analysis.PrimeSieveQuotientPNTError` proves that the prime-first PNT
error is exactly a Mertens-weighted sum of prime-count discrepancies on the
reciprocal quotient intervals

```text
primeSievePNTError y x
  = sum_{d = 1}^{K} (Pi_d - Li_d) * M(d),   K = x / (y + 1),
```

where the `d`-th interval is `(max y (x/(d+1)), x/d]`.  This module performs the
summation by parts that moves the Mertens weight off the *differences* and onto
the *values*.

Write `R(t) = pi(t) - Li(t)` for the classical prime-count discrepancy at the
integer cutoff `t` (`primeSievePrimeDiscrepancy`, with `pi` the honest prime
indicator sum over `Ioc 0 t` and `Li` the repository's
`logarithmicIntegralFromTwo`).  The identity proved here is

```text
primeSievePNTError y x
  = sum_{d = 1}^{K} mu(d) * R(floor (x/d))  -  M(K) * R(y),
```

with `K = x / (y + 1)` exactly as in `primeSieveQuotientSupport`.  It holds for
every pair of naturals `y x`, with no positivity or size hypothesis: when
`K = 0` both sides are `0` because `M 0 = 0`.

Two arithmetic facts make the telescoping exact and are proved here:

* for `1 <= d <= K` the reciprocal lower endpoint `max y (x/(d+1))` is *not*
  clipped by `y` at the *upper* end, i.e. `y < x/d`, so the `d`-th interval's
  upper endpoint is `x/d` on the nose;
* at the very last index the clip does happen: `x/(K+1) <= y`, so the boundary
  value of the telescope is `R(y)` and not `R(x/(K+1))`.

Consequently the boundary argument in the identity is exactly `y` — this
confirms the informal form derived outside Lean; see the deviation note in
`results/015`.

Everything here is finite algebra over already kernel-proved identities.  No
bound on `R`, on `M`, or on the Moebius-weighted sum is asserted anywhere; the
identity is a change of coordinates, not an estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## The prefix prime count and the classical discrepancy -/

/-- Exact prime count `pi(t)` through `t`, as the prime-indicator sum used
everywhere else in the prime-sieve development. -/
def primeSievePrefixPrimeCount (t : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc 0 t, primeSievePrimeIndicator q

/-- The prefix prime count is literally the cardinality of the set of primes
through `t`. -/
theorem primeSievePrefixPrimeCount_eq_card (t : ℕ) :
    primeSievePrefixPrimeCount t =
      (((Finset.Ioc 0 t).filter Nat.Prime).card : ℕ) := by
  classical
  simp [primeSievePrefixPrimeCount, primeSievePrimeIndicator]

/-- Classical prime-count discrepancy `R(t) = pi(t) - Li(t)` at an integer
cutoff, in the repository's `logarithmicIntegralFromTwo` normalization. -/
def primeSievePrimeDiscrepancy (t : ℕ) : ℂ :=
  primeSievePrefixPrimeCount t -
    ((logarithmicIntegralFromTwo (t : ℝ) : ℝ) : ℂ)

/-- On an ordinary integer interval the prefix prime counts subtract. -/
theorem primeSieveReciprocalPrimeCount_eq_sub
    (y x d : ℕ)
    (h : primeSieveReciprocalLower y x d ≤ primeSieveReciprocalUpper x d) :
    primeSieveReciprocalPrimeCount y x d =
      primeSievePrefixPrimeCount (primeSieveReciprocalUpper x d) -
        primeSievePrefixPrimeCount (primeSieveReciprocalLower y x d) := by
  have hsplit :=
    Finset.sum_Ioc_consecutive (f := primeSievePrimeIndicator)
      (Nat.zero_le (primeSieveReciprocalLower y x d)) h
  unfold primeSieveReciprocalPrimeCount primeSieveReciprocalInterval
  unfold primeSievePrefixPrimeCount
  linear_combination hsplit

/-- A nonempty reciprocal interval carries the difference of the two classical
discrepancies at its endpoints. -/
theorem primeSieveReciprocalPrimeDiscrepancy_eq_sub
    (y x d : ℕ)
    (h : primeSieveReciprocalLower y x d ≤ primeSieveReciprocalUpper x d) :
    primeSieveReciprocalPrimeDiscrepancy y x d =
      primeSievePrimeDiscrepancy (primeSieveReciprocalUpper x d) -
        primeSievePrimeDiscrepancy (primeSieveReciprocalLower y x d) := by
  unfold primeSieveReciprocalPrimeDiscrepancy primeSievePrimeDiscrepancy
  rw [primeSieveReciprocalPrimeCount_eq_sub y x d h]
  have hli : primeSieveReciprocalLiMass y x d =
      ((logarithmicIntegralFromTwo (primeSieveReciprocalUpper x d : ℝ) -
        logarithmicIntegralFromTwo (primeSieveReciprocalLower y x d : ℝ) :
          ℝ) : ℂ) := by
    simp [primeSieveReciprocalLiMass, h]
  rw [hli]
  push_cast
  ring

/-! ## The two endpoint facts for the quotient support -/

/-- On the quotient support the upper reciprocal endpoint is strictly above the
prime cutoff, so the `max` with `y` is inactive there. -/
theorem lt_div_of_mem_primeSieveQuotientSupport
    {y x d : ℕ} (hd : d ∈ primeSieveQuotientSupport y x) :
    y < x / d := by
  rcases Finset.mem_Icc.mp hd with ⟨hd1, hd2⟩
  have hdpos : 0 < d := hd1
  have h1 : d * (y + 1) ≤ x :=
    (Nat.le_div_iff_mul_le (Nat.succ_pos y)).1 hd2
  have h2 : (y + 1) * d ≤ x := by
    rw [Nat.mul_comm]; exact h1
  have h3 : y + 1 ≤ x / d := (Nat.le_div_iff_mul_le hdpos).2 h2
  omega

/-- Just past the quotient support the `max` with `y` becomes active: the next
reciprocal endpoint has already dropped to or below the prime cutoff. -/
theorem div_succ_quotientSupportTop_le (y x : ℕ) :
    x / (x / (y + 1) + 1) ≤ y := by
  by_contra hcon
  push_neg at hcon
  have h1 : (y + 1) * (x / (y + 1) + 1) ≤ x :=
    (Nat.le_div_iff_mul_le (Nat.succ_pos _)).1 hcon
  have h2 : (x / (y + 1) + 1) * (y + 1) ≤ x := by
    rw [Nat.mul_comm]; exact h1
  have h3 : x / (y + 1) + 1 ≤ x / (y + 1) :=
    (Nat.le_div_iff_mul_le (Nat.succ_pos y)).2 h2
  omega

/-- The clipped reciprocal endpoint function whose forward differences are the
reciprocal-interval discrepancies. -/
private def primeSieveClippedDiscrepancy (y x d : ℕ) : ℂ :=
  primeSievePrimeDiscrepancy (max y (x / d))

/-! ## Abel summation against the Mertens weight -/

/-- **Summation by parts for the Mertens weight.**  A Mertens-weighted sum of
forward differences is the Moebius-weighted sum of values minus one boundary
term.  This is the finite Abel identity, proved by induction from
`mertensSummatory_succ`; it holds for every `f` and every `n`. -/
theorem sum_mertensSummatory_mul_forwardDifference
    (f : ℕ → ℂ) (n : ℕ) :
    (∑ d ∈ Finset.Icc 1 n, mertensSummatory d * (f d - f (d + 1))) =
      (∑ d ∈ Finset.Icc 1 n, (((μ d : ℤ) : ℂ)) * f d) -
        mertensSummatory n * f (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih,
        mertensSummatory_succ]
      ring

/-- The Moebius-weighted sum of classical prime-count discrepancies at the
reciprocal cutoffs `floor (x/d)`, `1 <= d <= x/(y+1)`. -/
def primeSieveMoebiusDiscrepancySum (y x : ℕ) : ℂ :=
  ∑ d ∈ primeSieveQuotientSupport y x,
    (((μ d : ℤ) : ℂ)) * primeSievePrimeDiscrepancy (x / d)

/-- The Abel boundary term: the Mertens value at the top of the quotient support
times the classical discrepancy at the prime cutoff. -/
def primeSieveAbelBoundary (y x : ℕ) : ℂ :=
  mertensSummatory (x / (y + 1)) * primeSievePrimeDiscrepancy y

/-- **The Abel identity for the prime-sieve PNT error.**

```text
primeSievePNTError y x
  = sum_{d = 1}^{x/(y+1)} mu(d) * (pi(x/d) - Li(x/d))
      - M(x/(y+1)) * (pi(y) - Li(y)).
```

No hypothesis on `y` or `x` is needed. -/
theorem primeSievePNTError_eq_moebiusDiscrepancySum_sub_abelBoundary
    (y x : ℕ) :
    primeSievePNTError y x =
      primeSieveMoebiusDiscrepancySum y x - primeSieveAbelBoundary y x := by
  classical
  have hstep :
      primeSieveReciprocalPNTError y x =
        ∑ d ∈ Finset.Icc 1 (x / (y + 1)),
          mertensSummatory d *
            (primeSieveClippedDiscrepancy y x d -
              primeSieveClippedDiscrepancy y x (d + 1)) := by
    unfold primeSieveReciprocalPNTError primeSieveQuotientSupport
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hy : y < x / d :=
      lt_div_of_mem_primeSieveQuotientSupport
        (y := y) (x := x) (d := d) (by simpa [primeSieveQuotientSupport] using hd)
    have hmaxd : max y (x / d) = x / d := max_eq_right hy.le
    have hle : primeSieveReciprocalLower y x d ≤
        primeSieveReciprocalUpper x d := by
      have hmono : x / (d + 1) ≤ x / d :=
        Nat.div_le_div_left (by omega) (by
          rcases Finset.mem_Icc.mp hd with ⟨hd1, _⟩; omega)
      simp only [primeSieveReciprocalLower, primeSieveReciprocalUpper]
      exact max_le hy.le hmono
    rw [primeSieveReciprocalPrimeDiscrepancy_eq_sub y x d hle]
    simp only [primeSieveClippedDiscrepancy, primeSieveReciprocalLower,
      primeSieveReciprocalUpper, hmaxd]
    ring
  have hboundary :
      primeSieveClippedDiscrepancy y x (x / (y + 1) + 1) =
        primeSievePrimeDiscrepancy y := by
    have := div_succ_quotientSupportTop_le y x
    simp only [primeSieveClippedDiscrepancy, max_eq_left this]
  have hvalues :
      (∑ d ∈ Finset.Icc 1 (x / (y + 1)),
          (((μ d : ℤ) : ℂ)) * primeSieveClippedDiscrepancy y x d) =
        primeSieveMoebiusDiscrepancySum y x := by
    unfold primeSieveMoebiusDiscrepancySum primeSieveQuotientSupport
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hy : y < x / d :=
      lt_div_of_mem_primeSieveQuotientSupport
        (y := y) (x := x) (d := d) (by simpa [primeSieveQuotientSupport] using hd)
    simp only [primeSieveClippedDiscrepancy, max_eq_right hy.le]
  rw [primeSievePNTError_eq_reciprocalPNTError, hstep,
    sum_mertensSummatory_mul_forwardDifference, hboundary, hvalues,
    primeSieveAbelBoundary]

/-- Fully unfolded restatement of the Abel identity: no private abbreviation
appears, only the repository's `primeSievePNTError`, the Moebius function, the
prime-indicator prefix count, and `logarithmicIntegralFromTwo`. -/
theorem primeSievePNTError_eq_moebius_weighted_primeDiscrepancy
    (y x : ℕ) :
    primeSievePNTError y x =
      (∑ d ∈ Finset.Icc 1 (x / (y + 1)),
          (((μ d : ℤ) : ℂ)) *
            ((∑ q ∈ Finset.Ioc 0 (x / d), primeSievePrimeIndicator q) -
              ((logarithmicIntegralFromTwo ((x / d : ℕ) : ℝ) : ℝ) : ℂ))) -
        mertensSummatory (x / (y + 1)) *
          ((∑ q ∈ Finset.Ioc 0 y, primeSievePrimeIndicator q) -
            ((logarithmicIntegralFromTwo (y : ℝ) : ℝ) : ℂ)) := by
  rw [primeSievePNTError_eq_moebiusDiscrepancySum_sub_abelBoundary]
  rfl

/-- The reciprocal form and the Abel form of the error agree, so the change of
coordinates composes with the quotient reindexing already in the repository. -/
theorem primeSieveReciprocalPNTError_eq_moebiusDiscrepancySum_sub_abelBoundary
    (y x : ℕ) :
    primeSieveReciprocalPNTError y x =
      primeSieveMoebiusDiscrepancySum y x - primeSieveAbelBoundary y x := by
  rw [← primeSievePNTError_eq_reciprocalPNTError]
  exact primeSievePNTError_eq_moebiusDiscrepancySum_sub_abelBoundary y x

end RHLean.Analysis
