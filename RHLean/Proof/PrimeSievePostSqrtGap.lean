import Mathlib
import RHLean.Arithmetic.PrimeWheelMobiusRecovery
import RHLean.Arithmetic.PrimesUpToFrontier
import RHLean.Analysis.CanonicalLowOccupancy
import RHLean.Analysis.DyadicTransportCanonicalForm

/-!
# The post-square-root prime-sieve gap

This module isolates the elementary prime-by-prime statement behind the later
square-root transport architecture.

Start every positive integer with sign `+1`.  Process every prime `p <= y`:
first-power hits reverse the sign, while multiples of `p^2` are killed.  The
existing prime-wheel field `seededPrimeComb` uses the opposite initial seed, so
the all-plus state is simply its negative.

If `sqrt x < y`, an integer `n <= x` cannot contain two unprocessed prime
factors.  Hence every unresolved squarefree source has a unique form `n = c*q`
with `q > y` prime and `c < q`.  Its current sign is `mu(c)`, whereas its final
Mobius sign is `-mu(c)`.  Summing the exact batch discrepancy gives

```text
M_y^+(x) - M(x)
  = 2 * sum_{y < q <= x, q prime} M(floor(x/q)).
```

No estimate, asymptotic input, or probabilistic statement occurs here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- The all-plus prime-comb site.  Negating the repository's seeded comb changes
the provisional seed from `-1` to `+1`.  The harmless zero site is fixed at
zero so prefix sums use the same convention as `mertensSummatory`. -/
def allPlusPrimeCombSite (S : Finset ℕ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else -seededPrimeComb S n

/-- Running all-plus mass after every prime at most `y` has acted, restricted to
positive integers through `x`. -/
def allPlusPrimeCombPrefixMass (y x : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x,
    (((allPlusPrimeCombSite (primesUpTo y) n : ℤ) : ℂ))

/-- Sources whose canonical largest prime has not yet acted. -/
noncomputable def primeSieveHighSourceSet (y x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 x).filter fun n =>
    y < canonicalLargestPrimeFactor n

/-- Canonical cofactor/large-prime pairs for the same unresolved population. -/
noncomputable def primeSieveTransportPairSet
    (y x : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    ((Finset.Icc 1 x).product (Finset.Ioc y x)).filter fun cq =>
      cq.2.Prime ∧ cq.1 * cq.2 ≤ x

/-- Cofactor-signed batch mass carried by the primes still above `y`. -/
def primeSieveTransportCofactorMass (y x : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 x,
    ∑ q ∈ Finset.Ioc y x,
      if q.Prime ∧ c * q ≤ x then canonicalMoebiusWeight c else 0

/-- Prime-first form of the same batch mass. -/
def primeSieveMertensPrimeTail (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x,
    if q.Prime then RHLean.Analysis.mertensSummatory (x / q) else 0

/-- `primesUpTo y` covers every prime coordinate through `sqrt upper` whenever
that square-root cutoff is at most `y`. -/
theorem primesUpTo_sqrtCoverage
    {y upper : ℕ} (hsqrt : Nat.sqrt upper ≤ y) :
    PrimeWheelSqrtCoverage (primesUpTo y) upper := by
  intro p hp hple
  exact mem_primesUpTo.mpr ⟨hp, hple.trans hsqrt⟩

/-- A smooth squarefree source has already acquired its final Mobius sign in the
all-plus process. -/
theorem allPlusPrimeCombSite_eq_moebius_of_smooth
    (S : Finset ℕ) {n : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hnpos : 0 < n)
    (hsmooth : IsPrimeWheelSmooth S n) :
    allPlusPrimeCombSite S n = μ n := by
  have hseed := seededPrimeComb_eq_neg_moebius_of_smooth S hprime hsmooth
  simp [allPlusPrimeCombSite, Nat.ne_of_gt hnpos, hseed]

/-- Under square-root coverage, an unresolved squarefree source has exactly one
unprocessed prime factor, so its all-plus sign is the opposite of its final
Mobius sign. -/
theorem allPlusPrimeCombSite_eq_neg_moebius_of_not_smooth
    (S : Finset ℕ) {upper n : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hsq : Squarefree n) (hnupper : n ≤ upper)
    (hnonsmooth : ¬ IsPrimeWheelSmooth S n) :
    allPlusPrimeCombSite S n = -μ n := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hsq.ne_zero
  have hseed := seededPrimeComb_eq_moebius_of_not_smooth
    S hprime hcover hsq hnupper hnonsmooth
  simp [allPlusPrimeCombSite, Nat.ne_of_gt hnpos, hseed]

/-- Under square-root coverage, a nonsquarefree source is killed in the all-plus
process, exactly as its Mobius weight vanishes. -/
theorem allPlusPrimeCombSite_eq_zero_of_not_squarefree
    (S : Finset ℕ) {upper n : ℕ}
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hnpos : 0 < n) (hnupper : n ≤ upper)
    (hnsq : ¬ Squarefree n) :
    allPlusPrimeCombSite S n = 0 := by
  have hseed := seededPrimeComb_eq_zero_of_not_squarefree
    S hcover hnpos hnupper hnsq
  simp [allPlusPrimeCombSite, Nat.ne_of_gt hnpos, hseed]

private theorem primeFactor_le_canonicalLargestPrimeFactor
    {n p : ℕ} (hn : 1 < n) (hp : p ∈ n.primeFactors) :
    p ≤ canonicalLargestPrimeFactor n := by
  unfold canonicalLargestPrimeFactor
  rw [dif_pos hn]
  exact Finset.le_max' n.primeFactors p hp

/-- On squarefree support, smoothness for the complete prime set through `y` is
exactly the largest-prime inequality `P+(n) <= y`. -/
theorem isPrimeWheelSmooth_primesUpTo_iff_largestPrime_le
    {y n : ℕ} (hy : 1 ≤ y) (hnpos : 0 < n) (hsq : Squarefree n) :
    IsPrimeWheelSmooth (primesUpTo y) n ↔
      canonicalLargestPrimeFactor n ≤ y := by
  by_cases hn1 : n = 1
  · subst n
    simp [IsPrimeWheelSmooth, canonicalLargestPrimeFactor, hy]
  · have hn : 1 < n := by omega
    constructor
    · intro hsmooth
      have hqmem := canonicalLargestPrimeFactor_mem_primeFactors hn
      exact (mem_primesUpTo.mp (hsmooth.2 _ hqmem)).2
    · intro hq
      refine ⟨hsq, ?_⟩
      intro p hp
      have hpPrime := (Nat.mem_primeFactors.mp hp).1
      have hpq := primeFactor_le_canonicalLargestPrimeFactor hn hp
      exact mem_primesUpTo.mpr ⟨hpPrime, hpq.trans hq⟩

/-- Exact pointwise discrepancy after `sqrt x < y`: a resolved source contributes
zero discrepancy; an unresolved source contributes `-2 mu(n)`. -/
theorem allPlusPrimeCombSite_sub_moebius_eq_high
    (y x n : ℕ) (hroot : Nat.sqrt x < y)
    (hn1 : 1 ≤ n) (hnx : n ≤ x) :
    (((allPlusPrimeCombSite (primesUpTo y) n : ℤ) : ℂ)) -
        canonicalMoebiusWeight n =
      if y < canonicalLargestPrimeFactor n then
        -2 * canonicalMoebiusWeight n
      else
        0 := by
  classical
  have hy : 1 ≤ y := by omega
  have hnpos : 0 < n := by omega
  have hcover : PrimeWheelSqrtCoverage (primesUpTo y) x :=
    primesUpTo_sqrtCoverage hroot.le
  have hprime : ∀ p ∈ primesUpTo y, Nat.Prime p := by
    intro p hp
    exact prime_of_mem_primesUpTo hp
  by_cases hsq : Squarefree n
  · have hsmoothIff :=
      isPrimeWheelSmooth_primesUpTo_iff_largestPrime_le hy hnpos hsq
    by_cases hq : canonicalLargestPrimeFactor n ≤ y
    · have hsmooth : IsPrimeWheelSmooth (primesUpTo y) n := hsmoothIff.mpr hq
      have hnotHigh : ¬ y < canonicalLargestPrimeFactor n := Nat.not_lt.mpr hq
      have hsite := allPlusPrimeCombSite_eq_moebius_of_smooth
        (primesUpTo y) hprime hnpos hsmooth
      rw [hsite]
      simp [hnotHigh, canonicalMoebiusWeight]
    · have hhigh : y < canonicalLargestPrimeFactor n := Nat.lt_of_not_ge hq
      have hsmooth : ¬ IsPrimeWheelSmooth (primesUpTo y) n := by
        intro hs
        exact hq (hsmoothIff.mp hs)
      have hsite := allPlusPrimeCombSite_eq_neg_moebius_of_not_smooth
        (primesUpTo y) hprime hcover hsq hnx hsmooth
      rw [hsite]
      simp [hhigh, canonicalMoebiusWeight]
      ring
  · have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    have hsite := allPlusPrimeCombSite_eq_zero_of_not_squarefree
      (primesUpTo y) hcover hnpos hnx hsq
    rw [hsite]
    simp [hmu, canonicalMoebiusWeight]

/-- Summing the pointwise discrepancy isolates exactly the unresolved canonical
largest-prime source mass. -/
theorem allPlusPrimeCombPrefixMass_sub_mertens_eq_neg_two_highSource
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    allPlusPrimeCombPrefixMass y x - RHLean.Analysis.mertensSummatory x =
      -2 *
        (∑ n ∈ primeSieveHighSourceSet y x, canonicalMoebiusWeight n) := by
  classical
  unfold allPlusPrimeCombPrefixMass
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory x]
  unfold cofactorMobiusPrefixMass
  calc
    (∑ n ∈ Finset.Icc 1 x,
        (((allPlusPrimeCombSite (primesUpTo y) n : ℤ) : ℂ))) -
        ∑ n ∈ Finset.Icc 1 x, canonicalMoebiusWeight n =
      ∑ n ∈ Finset.Icc 1 x,
        ((((allPlusPrimeCombSite (primesUpTo y) n : ℤ) : ℂ)) -
          canonicalMoebiusWeight n) := by
        rw [Finset.sum_sub_distrib]
    _ = ∑ n ∈ Finset.Icc 1 x,
        if y < canonicalLargestPrimeFactor n then
          -2 * canonicalMoebiusWeight n
        else
          0 := by
        apply Finset.sum_congr rfl
        intro n hn
        rcases Finset.mem_Icc.mp hn with ⟨hn1, hnx⟩
        exact allPlusPrimeCombSite_sub_moebius_eq_high y x n hroot hn1 hnx
    _ = ∑ n ∈ primeSieveHighSourceSet y x,
        -2 * canonicalMoebiusWeight n := by
        unfold primeSieveHighSourceSet
        rw [Finset.sum_filter]
    _ = -2 *
        (∑ n ∈ primeSieveHighSourceSet y x, canonicalMoebiusWeight n) := by
        rw [Finset.mul_sum]

private theorem cofactor_lt_largePrime_of_sqrt_lt
    {y x c q : ℕ}
    (hroot : Nat.sqrt x < y) (hyq : y < q)
    (hmul : c * q ≤ x) :
    c < q := by
  by_contra hnot
  have hqc : q ≤ c := Nat.le_of_not_gt hnot
  have hqq : q ^ 2 ≤ x := by
    calc
      q ^ 2 = q * q := by ring
      _ ≤ c * q := Nat.mul_le_mul_right q hqc
      _ ≤ x := hmul
  have hqSqrt : q ≤ Nat.sqrt x :=
    Nat.le_sqrt.mpr (by simpa [pow_two] using hqq)
  omega

private theorem primeSieveHighSource_to_pair_mem
    {y x m : ℕ} (hroot : Nat.sqrt x < y)
    (hm : m ∈ primeSieveHighSourceSet y x) :
    (canonicalCofactor m, canonicalLargestPrimeFactor m) ∈
      primeSieveTransportPairSet y x := by
  classical
  rcases Finset.mem_filter.mp hm with ⟨hmBase, hhigh⟩
  rcases Finset.mem_Icc.mp hmBase with ⟨hm1, hmx⟩
  have hy : 1 ≤ y := by omega
  have hmne : m ≠ 1 := by
    intro hmeq
    subst m
    simp [canonicalLargestPrimeFactor] at hhigh
    omega
  have hmgt : 1 < m := by omega
  have hqPrime := canonicalLargestPrimeFactor_prime hmgt
  have hprod := canonicalCofactor_mul_largestPrimeFactor hmgt
  have hcPos : 0 < canonicalCofactor m := by
    by_contra hnot
    have hc0 : canonicalCofactor m = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hc0, zero_mul] at hprod
    omega
  have hcLeM : canonicalCofactor m ≤ m := by
    calc
      canonicalCofactor m = canonicalCofactor m * 1 := by simp
      _ ≤ canonicalCofactor m * canonicalLargestPrimeFactor m :=
        Nat.mul_le_mul_left _ hqPrime.one_le
      _ = m := hprod
  have hqLeM : canonicalLargestPrimeFactor m ≤ m := by
    calc
      canonicalLargestPrimeFactor m = 1 * canonicalLargestPrimeFactor m := by simp
      _ ≤ canonicalCofactor m * canonicalLargestPrimeFactor m :=
        Nat.mul_le_mul_right _ hcPos
      _ = m := hprod
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hcPos, hcLeM.trans hmx⟩,
        Finset.mem_Ioc.mpr ⟨hhigh, hqLeM.trans hmx⟩⟩
  · exact ⟨hqPrime, by simpa [hprod] using hmx⟩

private theorem primeSieveHighSource_pair_injective
    {y x m n : ℕ} (hroot : Nat.sqrt x < y)
    (hm : m ∈ primeSieveHighSourceSet y x)
    (hn : n ∈ primeSieveHighSourceSet y x)
    (hpair :
      (canonicalCofactor m, canonicalLargestPrimeFactor m) =
        (canonicalCofactor n, canonicalLargestPrimeFactor n)) :
    m = n := by
  have hy : 1 ≤ y := by omega
  have hmBase := (Finset.mem_filter.mp hm).1
  have hnBase := (Finset.mem_filter.mp hn).1
  have hm1 := (Finset.mem_Icc.mp hmBase).1
  have hn1 := (Finset.mem_Icc.mp hnBase).1
  have hmHigh := (Finset.mem_filter.mp hm).2
  have hnHigh := (Finset.mem_filter.mp hn).2
  have hmgt : 1 < m := by
    by_contra hnot
    have hmeq : m = 1 := by omega
    subst m
    simp [canonicalLargestPrimeFactor] at hmHigh
    omega
  have hngt : 1 < n := by
    by_contra hnot
    have hneq : n = 1 := by omega
    subst n
    simp [canonicalLargestPrimeFactor] at hnHigh
    omega
  have hmprod := canonicalCofactor_mul_largestPrimeFactor hmgt
  have hnprod := canonicalCofactor_mul_largestPrimeFactor hngt
  have hc : canonicalCofactor m = canonicalCofactor n :=
    congrArg Prod.fst hpair
  have hq : canonicalLargestPrimeFactor m = canonicalLargestPrimeFactor n :=
    congrArg Prod.snd hpair
  calc
    m = canonicalCofactor m * canonicalLargestPrimeFactor m := hmprod.symm
    _ = canonicalCofactor n * canonicalLargestPrimeFactor n := by rw [hc, hq]
    _ = n := hnprod

private theorem primeSievePair_surjective
    {y x : ℕ} (hroot : Nat.sqrt x < y)
    (cq : ℕ × ℕ) (hcq : cq ∈ primeSieveTransportPairSet y x) :
    ∃ m ∈ primeSieveHighSourceSet y x,
      (canonicalCofactor m, canonicalLargestPrimeFactor m) = cq := by
  classical
  rcases Finset.mem_filter.mp hcq with ⟨hbase, hdata⟩
  rcases Finset.mem_product.mp hbase with ⟨hcMem, hqMem⟩
  rcases Finset.mem_Icc.mp hcMem with ⟨hc1, _hcx⟩
  rcases Finset.mem_Ioc.mp hqMem with ⟨hyq, _hqx⟩
  rcases hdata with ⟨hqPrime, hmul⟩
  have hcPos : 0 < cq.1 := by omega
  have hcqLt : cq.1 < cq.2 :=
    cofactor_lt_largePrime_of_sqrt_lt hroot hyq hmul
  have hlargest :
      canonicalLargestPrimeFactor (cq.1 * cq.2) = cq.2 :=
    canonicalLargestPrimeFactor_mul_prime_eq hcPos hcqLt hqPrime
  have hcofactor : canonicalCofactor (cq.1 * cq.2) = cq.1 :=
    canonicalCofactor_mul_prime_eq hcPos hcqLt hqPrime
  have hm1 : 1 ≤ cq.1 * cq.2 := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.ne_of_gt hcPos) hqPrime.ne_zero)
  have hmSource : cq.1 * cq.2 ∈ primeSieveHighSourceSet y x := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hm1, hmul⟩, by simpa [hlargest] using hyq⟩
  refine ⟨cq.1 * cq.2, hmSource, ?_⟩
  apply Prod.ext
  · exact hcofactor
  · exact hlargest

/-- Exact reindexing of all unresolved sources by their unique lower cofactor
and one remaining large prime. -/
theorem sum_primeSieveHighSourceSet_eq_pairProducts
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    (∑ m ∈ primeSieveHighSourceSet y x, canonicalMoebiusWeight m) =
      ∑ cq ∈ primeSieveTransportPairSet y x,
        canonicalMoebiusWeight (cq.1 * cq.2) := by
  classical
  refine Finset.sum_bij
    (fun m _hm => (canonicalCofactor m, canonicalLargestPrimeFactor m))
    (fun m hm => primeSieveHighSource_to_pair_mem hroot hm)
    (fun m hm n hn hmn => primeSieveHighSource_pair_injective hroot hm hn hmn)
    (fun cq hcq => by simpa using primeSievePair_surjective hroot cq hcq)
    ?_
  intro m hm
  have hmBase := (Finset.mem_filter.mp hm).1
  have hm1 := (Finset.mem_Icc.mp hmBase).1
  have hmHigh := (Finset.mem_filter.mp hm).2
  have hy : 1 ≤ y := by omega
  have hmgt : 1 < m := by
    by_contra hnot
    have hmeq : m = 1 := by omega
    subst m
    simp [canonicalLargestPrimeFactor] at hmHigh
    omega
  rw [canonicalCofactor_mul_largestPrimeFactor hmgt]

/-- On every unresolved pair the large prime is fresh relative to the lower
cofactor, so its final action reverses the source sign. -/
theorem sum_primeSieveTransportPairSet_eq_neg_cofactorMass
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    (∑ cq ∈ primeSieveTransportPairSet y x,
        canonicalMoebiusWeight (cq.1 * cq.2)) =
      -primeSieveTransportCofactorMass y x := by
  classical
  unfold primeSieveTransportPairSet primeSieveTransportCofactorMass
  rw [Finset.sum_filter]
  calc
    (∑ cq ∈ (Finset.Icc 1 x).product (Finset.Ioc y x),
        if cq.2.Prime ∧ cq.1 * cq.2 ≤ x then
          canonicalMoebiusWeight (cq.1 * cq.2)
        else
          0) =
      ∑ c ∈ Finset.Icc 1 x,
        ∑ q ∈ Finset.Ioc y x,
          if q.Prime ∧ c * q ≤ x then
            canonicalMoebiusWeight (c * q)
          else
            0 := by
        simpa only using
          (Finset.sum_product
            (s := Finset.Icc 1 x)
            (t := Finset.Ioc y x)
            (f := fun cq : ℕ × ℕ =>
              if cq.2.Prime ∧ cq.1 * cq.2 ≤ x then
                canonicalMoebiusWeight (cq.1 * cq.2)
              else
                0))
    _ = ∑ c ∈ Finset.Icc 1 x,
        ∑ q ∈ Finset.Ioc y x,
          if q.Prime ∧ c * q ≤ x then
            -canonicalMoebiusWeight c
          else
            0 := by
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hprime : q.Prime
        · by_cases hmul : c * q ≤ x
          · have hcPos : 0 < c := by
              exact Nat.zero_lt_of_lt (Finset.mem_Icc.mp hc).1
            have hyq : y < q := (Finset.mem_Ioc.mp hq).1
            have hcq : c < q :=
              cofactor_lt_largePrime_of_sqrt_lt hroot hyq hmul
            have hweight :=
              canonicalMoebiusWeight_mul_prime_eq_neg hcPos hcq hprime
            simp [hprime, hmul, hweight]
          · simp [hprime, hmul]
        · simp [hprime]
    _ = -∑ c ∈ Finset.Icc 1 x,
        ∑ q ∈ Finset.Ioc y x,
          if q.Prime ∧ c * q ≤ x then canonicalMoebiusWeight c else 0 := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro c _hc
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro q _hq
        by_cases h : q.Prime ∧ c * q ≤ x <;> simp [h]

/-- The cofactor-first batch mass is exactly the lower-scale Mertens transform
indexed by the unprocessed primes. -/
theorem primeSieveTransportCofactorMass_eq_mertensPrimeTail
    (y x : ℕ) :
    primeSieveTransportCofactorMass y x = primeSieveMertensPrimeTail y x := by
  classical
  unfold primeSieveTransportCofactorMass primeSieveMertensPrimeTail
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hprime : q.Prime
  · have hqPos : 0 < q := hprime.pos
    simp only [hprime, true_and, if_true]
    have hset :
        (Finset.Icc 1 x).filter (fun c => c * q ≤ x) =
          Finset.Icc 1 (x / q) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hc1, _hcx⟩, hmul⟩
        exact ⟨hc1, (Nat.le_div_iff_mul_le hqPos).2 hmul⟩
      · rintro ⟨hc1, hcdiv⟩
        exact ⟨⟨hc1, hcdiv.trans (Nat.div_le_self x q)⟩,
          (Nat.le_div_iff_mul_le hqPos).1 hcdiv⟩
    calc
      (∑ c ∈ Finset.Icc 1 x,
          if c * q ≤ x then canonicalMoebiusWeight c else 0) =
        ∑ c ∈ (Finset.Icc 1 x).filter (fun c => c * q ≤ x),
          canonicalMoebiusWeight c := by
            rw [Finset.sum_filter]
      _ = ∑ c ∈ Finset.Icc 1 (x / q), canonicalMoebiusWeight c := by
            rw [hset]
      _ = cofactorMobiusPrefixMass (x / q) := rfl
      _ = RHLean.Analysis.mertensSummatory (x / q) :=
            cofactorMobiusPrefixMass_eq_mertensSummatory (x / q)
  · simp [hprime]

/-- **Arbitrary post-square-root gap identity.**  Once all primes through a
cutoff strictly above `sqrt x` have acted, the remaining discrepancy from the
true Mertens value is exactly twice the transport batch carried by the still
unprocessed primes. -/
theorem allPlusPrimeCombPrefixMass_sub_mertens_eq_two_mertensPrimeTail
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    allPlusPrimeCombPrefixMass y x - RHLean.Analysis.mertensSummatory x =
      2 * primeSieveMertensPrimeTail y x := by
  calc
    allPlusPrimeCombPrefixMass y x - RHLean.Analysis.mertensSummatory x =
      -2 *
        (∑ n ∈ primeSieveHighSourceSet y x, canonicalMoebiusWeight n) :=
      allPlusPrimeCombPrefixMass_sub_mertens_eq_neg_two_highSource y x hroot
    _ = -2 *
        (∑ cq ∈ primeSieveTransportPairSet y x,
          canonicalMoebiusWeight (cq.1 * cq.2)) := by
      rw [sum_primeSieveHighSourceSet_eq_pairProducts y x hroot]
    _ = -2 * (-primeSieveTransportCofactorMass y x) := by
      rw [sum_primeSieveTransportPairSet_eq_neg_cofactorMass y x hroot]
    _ = 2 * primeSieveTransportCofactorMass y x := by ring
    _ = 2 * primeSieveMertensPrimeTail y x := by
      rw [primeSieveTransportCofactorMass_eq_mertensPrimeTail y x]

end RHLean.Proof
