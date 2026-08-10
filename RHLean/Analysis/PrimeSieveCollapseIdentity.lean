import Mathlib
import RHLean.Analysis.PrimeSieveQuotientPNTError

/-!
# The prime-sieve collapse identity

This module records the exact finite rearrangement that turns the PNT-centered
prime-sieve decomposition into a signed sum over the reciprocal quotient family
plus one explicitly named smooth remainder.

Write

```text
C(y,x) = primeSievePNTCorrectedAllPlusMass y x
       = M_y^+(x) - 2 * (deterministic Li bulk),
E(y,x) = primeSievePNTError y x,
Pi_d(y,x) = primeSieveReciprocalPrimeCount y x d
       = # primes in (max y (x/(d+1)), x/d].
```

The collapse is

```text
C(y,x) - 2 * E(y,x)
  = - (sum_d M(d) * Pi_d(y,x)) + R(y,x),
R(y,x) = sum over y-smooth n <= x of mu(n).
```

The remainder is *defined*, not residual: `primeSieveSmoothMobiusMass y x` is
the Mobius mass of the `y`-smooth positive integers through `x`, characterized
elementarily in `mem_primeSieveSmoothSourceSet_iff` as
`1 <= n <= x` together with `p <= y` for every prime factor `p` of `n`.

Two exact facts drive the collapse, both already available in the repository:

* the deterministic Li bulk cancels identically between `C` and `-2E`
  (`primeSievePNTCorrected_sub_two_error_eq_allPlus_sub_two_primeTail`), which
  is where the "recombination with the PNT bulk" happens: the doubled bulk
  subtracted inside `C` is restored by `-2E`, leaving only actual prime counts;
* once `sqrt x < y`, the all-plus mass itself splits as
  `M_y^+(x) = R(y,x) + sum_d M(d) * Pi_d(y,x)`
  (`allPlusPrimeCombPrefixMass_eq_smoothMass_add_primeTail`), because an
  integer `n <= x` carries at most one prime factor above `y`, and its
  cofactor `n/q < q` is then automatically `y`-smooth.

Subtracting twice the signed sum from the first term of the split leaves the
signed sum with the opposite sign, which is the collapse.

A second exact form is also recorded, in which the reciprocal intervals are
weighted by the prime-count *discrepancies* `Pi_d - Li_d`; that moves one copy
of the deterministic bulk out of the signed sum and into the remainder, giving
the remainder `R - (Li bulk)`.  The two forms have the same left-hand side and
differ only in which object carries the Li model.

Everything here is finite algebra over already kernel-proved identities.  No
bound on either remainder is asserted anywhere: their sizes are open analytic
content.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## The smooth remainder -/

/-- The `y`-smooth positive integers through `x`, cut out by the canonical
largest-prime-factor coordinate. -/
def primeSieveSmoothSourceSet (y x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 x).filter fun n => canonicalLargestPrimeFactor n ≤ y

/-- Elementary characterization of the canonical smoothness cut. -/
theorem canonicalLargestPrimeFactor_le_iff_forall_primeFactors_le
    {y n : ℕ} (hy : 1 ≤ y) (hn : 0 < n) :
    canonicalLargestPrimeFactor n ≤ y ↔ ∀ p ∈ n.primeFactors, p ≤ y := by
  by_cases hn1 : 1 < n
  · constructor
    · intro hle p hp
      have hmax : p ≤ canonicalLargestPrimeFactor n := by
        unfold canonicalLargestPrimeFactor
        rw [dif_pos hn1]
        exact Finset.le_max' n.primeFactors p hp
      exact hmax.trans hle
    · intro hall
      exact hall _ (canonicalLargestPrimeFactor_mem_primeFactors hn1)
  · have hn0 : n = 1 := by omega
    subst hn0
    simp [canonicalLargestPrimeFactor, hy]

/-- Membership in the smooth source set, in elementary terms. -/
theorem mem_primeSieveSmoothSourceSet_iff
    {y x n : ℕ} (hy : 1 ≤ y) :
    n ∈ primeSieveSmoothSourceSet y x ↔
      1 ≤ n ∧ n ≤ x ∧ ∀ p ∈ n.primeFactors, p ≤ y := by
  classical
  unfold primeSieveSmoothSourceSet
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hle⟩
    exact ⟨h1, h2,
      (canonicalLargestPrimeFactor_le_iff_forall_primeFactors_le hy
        (by omega)).1 hle⟩
  · rintro ⟨h1, h2, hall⟩
    exact ⟨⟨h1, h2⟩,
      (canonicalLargestPrimeFactor_le_iff_forall_primeFactors_le hy
        (by omega)).2 hall⟩

/-- **The collapse remainder.**  The Mobius mass carried by the `y`-smooth
positive integers through `x`.  This is an explicitly defined arithmetic object,
never "whatever is left over". -/
def primeSieveSmoothMobiusMass (y x : ℕ) : ℂ :=
  ∑ n ∈ primeSieveSmoothSourceSet y x, canonicalMoebiusWeight n

/-! ## The signed sum -/

/-- **The signed sum.**  Lower-scale Mertens values weighted by the exact prime
counts of the reciprocal quotient intervals,
`sum_d M(d) * Pi_d(y,x)`. -/
def primeSieveReciprocalMertensSignedSum (y x : ℕ) : ℂ :=
  ∑ d ∈ primeSieveQuotientSupport y x,
    mertensSummatory d * primeSieveReciprocalPrimeCount y x d

/-- The signed sum is the repository's quotient-reindexed prime tail. -/
theorem primeSieveReciprocalMertensSignedSum_eq_reciprocalPrimeTail
    (y x : ℕ) :
    primeSieveReciprocalMertensSignedSum y x =
      primeSieveReciprocalPrimeTail y x := by
  unfold primeSieveReciprocalMertensSignedSum primeSieveReciprocalPrimeTail
  apply Finset.sum_congr rfl
  intro d _hd
  ring

/-- The signed sum is also the prime-first Mertens tail of the post-square-root
gap identity. -/
theorem primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail
    (y x : ℕ) :
    primeSieveReciprocalMertensSignedSum y x =
      primeSieveMertensPrimeTail y x := by
  rw [primeSieveReciprocalMertensSignedSum_eq_reciprocalPrimeTail,
    ← primeSieveMertensPrimeTail_eq_reciprocalPrimeTail]

/-! ## Splitting the positive prefix into smooth and rough parts -/

/-- The rough complement of the smooth source set is exactly the unresolved
high-source population of the post-square-root gap module. -/
theorem filter_not_smooth_eq_primeSieveHighSourceSet
    (y x : ℕ) :
    ((Finset.Icc 1 x).filter
        fun n => ¬ canonicalLargestPrimeFactor n ≤ y) =
      primeSieveHighSourceSet y x := by
  classical
  unfold primeSieveHighSourceSet
  ext n
  simp

/-- Mertens splits into its smooth part and its unresolved rough part.  This is
a partition of `[1,x]`; no hypothesis on `y` is needed. -/
theorem mertensSummatory_eq_smoothMass_add_highSourceMass
    (y x : ℕ) :
    mertensSummatory x =
      primeSieveSmoothMobiusMass y x +
        ∑ n ∈ primeSieveHighSourceSet y x, canonicalMoebiusWeight n := by
  classical
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory x]
  unfold cofactorMobiusPrefixMass primeSieveSmoothMobiusMass
    primeSieveSmoothSourceSet
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.Icc 1 x)
    (p := fun n => canonicalLargestPrimeFactor n ≤ y)
    (f := canonicalMoebiusWeight)]
  rw [filter_not_smooth_eq_primeSieveHighSourceSet y x]

/-- The unresolved rough mass is exactly minus the prime-first Mertens tail.
This is the post-square-root transport chain, read as a single equation. -/
theorem sum_primeSieveHighSourceSet_eq_neg_mertensPrimeTail
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    (∑ n ∈ primeSieveHighSourceSet y x, canonicalMoebiusWeight n) =
      -primeSieveMertensPrimeTail y x := by
  rw [sum_primeSieveHighSourceSet_eq_pairProducts y x hroot,
    sum_primeSieveTransportPairSet_eq_neg_cofactorMass y x hroot,
    primeSieveTransportCofactorMass_eq_mertensPrimeTail y x]

/-- Smooth mass in terms of Mertens and the signed sum. -/
theorem primeSieveSmoothMobiusMass_eq_mertens_add_signedSum
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    primeSieveSmoothMobiusMass y x =
      mertensSummatory x + primeSieveReciprocalMertensSignedSum y x := by
  have hsplit := mertensSummatory_eq_smoothMass_add_highSourceMass y x
  rw [sum_primeSieveHighSourceSet_eq_neg_mertensPrimeTail y x hroot] at hsplit
  rw [primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail]
  linear_combination -hsplit

/-- **All-plus collapse.**  Once the sieve cutoff is strictly above `sqrt x`,
the all-plus prime-comb mass is its smooth part plus exactly one copy of the
signed sum: `M_y^+(x) = R(y,x) + sum_d M(d) * Pi_d(y,x)`. -/
theorem allPlusPrimeCombPrefixMass_eq_smoothMass_add_signedSum
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    allPlusPrimeCombPrefixMass y x =
      primeSieveSmoothMobiusMass y x +
        primeSieveReciprocalMertensSignedSum y x := by
  have hgap :=
    allPlusPrimeCombPrefixMass_sub_mertens_eq_two_mertensPrimeTail y x hroot
  have hsmooth := primeSieveSmoothMobiusMass_eq_mertens_add_signedSum y x hroot
  have htail := primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail y x
  rw [← htail] at hgap
  linear_combination hgap - hsmooth

/-! ## The collapse identity -/

/-- **The collapse identity.**  With `C = primeSievePNTCorrectedAllPlusMass`,
`E = primeSievePNTError` and `Pi_d = primeSieveReciprocalPrimeCount`,

```text
C(y,x) - 2 E(y,x) = - (sum_d M(d) Pi_d(y,x)) + R(y,x)
```

for every `x` with `sqrt x < y`, where `R` is the smooth Mobius mass
`primeSieveSmoothMobiusMass y x`.

The deterministic Li bulk has cancelled exactly: it enters `C` doubled with a
minus sign and is restored by `-2E`, so no PNT model term survives in either
the signed sum or the remainder.  No estimate on `R` is claimed. -/
theorem primeSievePNTCorrected_sub_two_error_eq_neg_signedSum_add_smoothMass
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    primeSievePNTCorrectedAllPlusMass y x - 2 * primeSievePNTError y x =
      -primeSieveReciprocalMertensSignedSum y x +
        primeSieveSmoothMobiusMass y x := by
  have hbulk :=
    primeSievePNTCorrected_sub_two_error_eq_allPlus_sub_two_primeTail y x
  have hsplit :=
    allPlusPrimeCombPrefixMass_eq_smoothMass_add_signedSum y x hroot
  have htail :=
    primeSieveReciprocalMertensSignedSum_eq_reciprocalPrimeTail y x
  rw [hsplit, ← htail] at hbulk
  linear_combination hbulk

/-- Mertens itself in collapsed form: `M(x) = - signed sum + R`. -/
theorem mertensSummatory_eq_neg_signedSum_add_smoothMass
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    mertensSummatory x =
      -primeSieveReciprocalMertensSignedSum y x +
        primeSieveSmoothMobiusMass y x := by
  rw [mertensSummatory_eq_pntCorrectedAllPlus_sub_two_error y x hroot]
  exact primeSievePNTCorrected_sub_two_error_eq_neg_signedSum_add_smoothMass
    y x hroot

/-! ## The Li-subtracted variant

Replacing the prime counts `Pi_d` by the prime-count discrepancies
`Pi_d - Li_d` moves exactly one copy of the deterministic bulk from the signed
sum into the remainder.  Both identities are exact; they differ only in which
of the two objects carries the Li model.  This variant is recorded because it,
not the prime-count form above, is the one whose remainder was measured
numerically in record 006. -/

/-- Signed sum against the reciprocal-interval prime-count *discrepancies*
`Pi_d - Li_d` instead of the prime counts. -/
def primeSieveReciprocalMertensSignedDiscrepancySum (y x : ℕ) : ℂ :=
  ∑ d ∈ primeSieveQuotientSupport y x,
    mertensSummatory d * primeSieveReciprocalPrimeDiscrepancy y x d

/-- The discrepancy-weighted signed sum is exactly the PNT error `E`. -/
theorem primeSieveReciprocalMertensSignedDiscrepancySum_eq_pntError
    (y x : ℕ) :
    primeSieveReciprocalMertensSignedDiscrepancySum y x =
      primeSievePNTError y x := by
  rw [primeSievePNTError_eq_reciprocalPNTError]
  unfold primeSieveReciprocalMertensSignedDiscrepancySum
    primeSieveReciprocalPNTError
  apply Finset.sum_congr rfl
  intro d _hd
  ring

/-- The remainder belonging to the Li-subtracted signed sum: the smooth Mobius
mass with the deterministic Li bulk removed. -/
def primeSieveSmoothPNTCorrectedRemainder (y x : ℕ) : ℂ :=
  primeSieveSmoothMobiusMass y x - primeSievePNTBulk y x

/-- **Li-subtracted collapse identity.**  Weighting the reciprocal intervals by
`Pi_d - Li_d` instead of `Pi_d` gives the same left-hand side with the bulk
moved into the remainder. -/
theorem primeSievePNTCorrected_sub_two_error_eq_neg_signedDiscrepancySum_add_correctedRemainder
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    primeSievePNTCorrectedAllPlusMass y x - 2 * primeSievePNTError y x =
      -primeSieveReciprocalMertensSignedDiscrepancySum y x +
        primeSieveSmoothPNTCorrectedRemainder y x := by
  have hmain :=
    primeSievePNTCorrected_sub_two_error_eq_neg_signedSum_add_smoothMass
      y x hroot
  have hsplit :
      primeSievePNTError y x =
        primeSieveReciprocalMertensSignedSum y x -
          primeSievePNTBulk y x := by
    rw [primeSievePNTError_eq_reciprocalPNTError,
      primeSieveReciprocalPNTError_eq_primeTail_sub_bulk,
      primeSievePNTBulk_eq_reciprocalPNTBulk,
      primeSieveReciprocalMertensSignedSum_eq_reciprocalPrimeTail]
  rw [primeSieveReciprocalMertensSignedDiscrepancySum_eq_pntError]
  unfold primeSieveSmoothPNTCorrectedRemainder
  linear_combination hmain + hsplit

/-! ## The centered corollary -/

/-- The signed sum after the square-wheel zero-mode centering used by the
canonical nonzero response. -/
def primorialCollapseSignedSumCenteredResponse (k n : ℕ) : ℂ :=
  primorialSquareZeroModeCenter k n
    (fun x =>
      primeSieveReciprocalMertensSignedSum
        (primorialPNTPrimeSieveCutoff k) x)

/-- The smooth collapse remainder after the same centering. -/
def primorialCollapseSmoothCenteredResponse (k n : ℕ) : ℂ :=
  primorialSquareZeroModeCenter k n
    (fun x =>
      primeSieveSmoothMobiusMass (primorialPNTPrimeSieveCutoff k) x)

/-- **Centered collapse identity.**  On a synchronized primorial block the
canonical nonzero square-wheel response is exactly minus the centered signed
sum plus the centered smooth remainder. -/
theorem primorialMinimalSquareWheelNonzeroResponse_eq_neg_centeredSignedSum_add_centeredSmooth
    (k n : ℕ)
    (hlower : primorialBlockLower k < squarePrefixEndpoint n)
    (hupper : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n =
      -primorialCollapseSignedSumCenteredResponse k n +
        primorialCollapseSmoothCenteredResponse k n := by
  rw [primorialMinimalSquareWheelNonzeroResponse_eq_mertensCenter
    k n hlower hupper]
  set y := primorialPNTPrimeSieveCutoff k with hy
  have hblock : primorialBlockLower k ≤ primorialBlockUpper k :=
    (primorialEndpoint_strictMono (Nat.lt_succ_self k)).le
  have hxroot : Nat.sqrt (squarePrefixEndpoint n) < y :=
    sqrt_lt_primorialPNTPrimeSieveCutoff_of_le_upper hupper
  have hlroot : Nat.sqrt (primorialBlockLower k) < y :=
    sqrt_lt_primorialPNTPrimeSieveCutoff_of_le_upper hblock
  have huroot : Nat.sqrt (primorialBlockUpper k) < y :=
    sqrt_lt_primorialPNTPrimeSieveCutoff_of_le_upper (k := k) le_rfl
  have hxM :=
    mertensSummatory_eq_neg_signedSum_add_smoothMass y
      (squarePrefixEndpoint n) hxroot
  have hlM :=
    mertensSummatory_eq_neg_signedSum_add_smoothMass y
      (primorialBlockLower k) hlroot
  have huM :=
    mertensSummatory_eq_neg_signedSum_add_smoothMass y
      (primorialBlockUpper k) huroot
  unfold primorialCollapseSignedSumCenteredResponse
    primorialCollapseSmoothCenteredResponse
    primorialSquareZeroModeCenter
  rw [← hy]
  rw [hxM, hlM, huM]
  ring

/-- Exact norm transfer for the collapsed formulation.  This is a triangle
inequality only; it asserts nothing about the size of either piece. -/
theorem norm_primorialMinimalSquareWheelNonzeroResponse_le_collapse
    (k n : ℕ)
    (hlower : primorialBlockLower k < squarePrefixEndpoint n)
    (hupper : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    ‖squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n‖ ≤
      ‖primorialCollapseSignedSumCenteredResponse k n‖ +
        ‖primorialCollapseSmoothCenteredResponse k n‖ := by
  rw [primorialMinimalSquareWheelNonzeroResponse_eq_neg_centeredSignedSum_add_centeredSmooth
    k n hlower hupper]
  calc
    ‖-primorialCollapseSignedSumCenteredResponse k n +
        primorialCollapseSmoothCenteredResponse k n‖ ≤
        ‖-primorialCollapseSignedSumCenteredResponse k n‖ +
          ‖primorialCollapseSmoothCenteredResponse k n‖ :=
      norm_add_le _ _
    _ = ‖primorialCollapseSignedSumCenteredResponse k n‖ +
          ‖primorialCollapseSmoothCenteredResponse k n‖ := by
      rw [norm_neg]

end RHLean.Analysis
