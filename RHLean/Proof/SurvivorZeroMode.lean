import Mathlib
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.DeathProcessShellIdentity
import RHLean.Proof.DeathShellSubpolynomial

/-!
# Exact survivor zero-mode realization

PR #214 discharges the lifetime death process unconditionally. This module
puts the remaining lifetime-active component on an explicit canonical
cofactor/prime operator.

At stage `t`, write

`X_t = (t+1)^2 - 1`.

On the nonzero Mobius support every current moving-high integer has the unique
canonical factorization

`m = c*q`,

where `q` is prime, `c` is positive and squarefree, `q` is coprime to `c`, and
every prime divisor of `c` is strictly below `q`. The lifetime survivor is
therefore exactly the zero-mode cofactor sum

`sum_c K_{Lambda,t}(c) * (-mu(c))`,

where `K_{Lambda,t}(c)` counts admissible primes `q` satisfying

`c*q <= X_t`

and the current high-height condition

`2*Lambda*t < |q^2-c^2|`.

The module proves this finite identity and the translated-window equivalence to
the remaining lifetime endpoint premise. In the combined square-wheel route,
this survivor state is one arithmetic coordinate of the square-endpoint
oscillation, not an instruction to estimate each square block or each survivor
state independently. The companion square-wheel modules retain cancellation
across consecutive square blocks and expose the same residual through the
primorial wheel spectrum.

No power-saving estimate is assumed or proved here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open CanonicalGapAncestryBridge

/-- The exact admissibility predicate for one survivor cofactor/prime pair at
stage `t`. The represented integer is `c*q`. -/
def IsSurvivorZeroModePair (Λ : ℝ) (t c q : ℕ) : Prop :=
  CanonicalSourceData q c ∧
    c * q ≤ RHLean.Analysis.squarePrefixEndpoint t ∧
      2 * Λ * (t : ℝ) <
        |(q : ℝ) ^ 2 - (c : ℝ) ^ 2|

/-- Admissible survivor primes in the fixed cofactor fibre `c`. -/
noncomputable def survivorZeroModePrimeFiber
    (Λ : ℝ) (t c : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.Icc 2 (RHLean.Analysis.squarePrefixEndpoint t)).filter
      (fun q => IsSurvivorZeroModePair Λ t c q)

/-- The nonnegative integer kernel `K_{Lambda,t}(c)`: the number of admissible
alive primes in the cofactor fibre `c`. -/
def survivorZeroModeKernel (Λ : ℝ) (t c : ℕ) : ℕ :=
  (survivorZeroModePrimeFiber Λ t c).card

/-- The explicit signed zero-mode operator. Since an admissible fresh prime
reverses the Mobius sign, every prime in the `c` fibre contributes
`-mu(c)`. -/
def survivorZeroMode (Λ : ℝ) (t : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t),
    survivorZeroModeKernel Λ t c • (-canonicalMoebiusWeight c)

/-- Moving-high sources restricted to the support on which the Mobius weight
can be nonzero and the canonical prime/cofactor source data is exhaustive. -/
noncomputable def survivorSquarefreeSourceSet
    (Λ : ℝ) (t : ℕ) : Finset ℕ := by
  classical
  exact (movingCanonicalHighSet Λ t).filter fun m => 1 < m ∧ Squarefree m

/-- Ordinary cofactor/prime pair set underlying the zero-mode operator. -/
noncomputable def survivorZeroModePairSet
    (Λ : ℝ) (t : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    ((Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t)).product
      (Finset.Icc 2 (RHLean.Analysis.squarePrefixEndpoint t))).filter
        (fun cq => IsSurvivorZeroModePair Λ t cq.1 cq.2)

/-- Native source-signed mass of the same canonical survivor pairs. -/
def survivorZeroModePairSourceMass (Λ : ℝ) (t : ℕ) : ℂ :=
  ∑ cq ∈ survivorZeroModePairSet Λ t,
    canonicalMoebiusWeight (cq.1 * cq.2)

/-- In admissible canonical source data, the displayed prime is the canonical
largest prime factor even when the cofactor itself is numerically larger than
the prime. -/
private theorem canonicalLargestPrimeFactor_mul_eq_of_sourceData
    {c q : ℕ} (hdata : CanonicalSourceData q c) :
    canonicalLargestPrimeFactor (c * q) = q := by
  rcases hdata with ⟨hq, hc1, _hsq, _hcop, hdom⟩
  have hc : 0 < c := by omega
  have hm1 : 1 < c * q := by
    calc
      1 < q := hq.one_lt
      _ = 1 * q := by simp
      _ ≤ c * q := Nat.mul_le_mul_right q hc
  have hqmem : q ∈ (c * q).primeFactors := by
    exact Nat.mem_primeFactors.mpr
      ⟨hq, ⟨c, by simp [Nat.mul_comm]⟩,
        Nat.mul_ne_zero (Nat.ne_of_gt hc) hq.ne_zero⟩
  have hall : ∀ p ∈ (c * q).primeFactors, p ≤ q := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpDvd := Nat.dvd_of_mem_primeFactors hp
    rcases hpPrime.dvd_mul.mp hpDvd with hpc | hpq
    · exact (hdom p hpPrime hpc).le
    · exact ((Nat.prime_dvd_prime_iff_eq hpPrime hq).mp hpq).le
  unfold canonicalLargestPrimeFactor
  rw [dif_pos hm1]
  exact ((c * q).primeFactors.max'_eq_iff
    (Nat.nonempty_primeFactors.mpr hm1) q).2 ⟨hqmem, hall⟩

/-- The canonical cofactor of an admissible source product is its displayed
cofactor. -/
private theorem canonicalCofactor_mul_eq_of_sourceData
    {c q : ℕ} (hdata : CanonicalSourceData q c) :
    canonicalCofactor (c * q) = c := by
  rcases hdata with ⟨hq, hc1, hsq, hcop, hdom⟩
  unfold canonicalCofactor
  rw [canonicalLargestPrimeFactor_mul_eq_of_sourceData
    ⟨hq, hc1, hsq, hcop, hdom⟩]
  simpa [Nat.mul_comm] using Nat.mul_div_right c hq.pos

/-- An admissible fresh prime reverses the Mobius sign of its cofactor. -/
private theorem canonicalMoebiusWeight_mul_eq_neg_of_sourceData
    {c q : ℕ} (hdata : CanonicalSourceData q c) :
    canonicalMoebiusWeight (c * q) = -canonicalMoebiusWeight c := by
  rcases hdata with ⟨hq, _hc1, _hsq, hcop, _hdom⟩
  have hmu :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop.symm
  unfold canonicalMoebiusWeight
  rw [hmu, ArithmeticFunction.moebius_apply_prime hq]
  push_cast
  ring

/-- Filtering the current moving-high population to squarefree integers larger
than one does not change its Mobius mass. -/
theorem movingCanonicalHighSum_eq_survivorSquarefreeSourceMass
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (t : ℕ) :
    movingCanonicalHighSum Λ t =
      ∑ m ∈ survivorSquarefreeSourceSet Λ t, canonicalMoebiusWeight m := by
  classical
  unfold movingCanonicalHighSum canonicalMoebiusMass
    survivorSquarefreeSourceSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hmgt : 1 < m
  · by_cases hsq : Squarefree m
    · simp [hmgt, hsq]
    · have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      simp [hmgt, hsq, canonicalMoebiusWeight, hmu]
  · have hmle : m ≤ 1 := by omega
    have hmCases : m = 0 ∨ m = 1 := by omega
    rcases hmCases with rfl | rfl
    · simp [canonicalMoebiusWeight]
    · have hm' := hm
      unfold movingCanonicalHighSet at hm'
      have hhigh : IsMovingCanonicalHigh Λ t 1 :=
        (Finset.mem_filter.mp hm').2
      have hheight : canonicalHeightTwice 1 = 0 := by
        norm_num [canonicalHeightTwice, canonicalLargestPrimeFactor,
          canonicalCofactor]
      unfold IsMovingCanonicalHigh at hhigh
      rw [hheight, abs_zero] at hhigh
      have hnonneg : 0 ≤ 2 * Λ * (t : ℝ) := by positivity
      exfalso
      linarith

private theorem survivorSource_to_pair_mem
    {Λ : ℝ} {t m : ℕ}
    (hm : m ∈ survivorSquarefreeSourceSet Λ t) :
    (canonicalCofactor m, canonicalLargestPrimeFactor m) ∈
      survivorZeroModePairSet Λ t := by
  classical
  rcases Finset.mem_filter.mp hm with ⟨hmMoving, hsupport⟩
  rcases hsupport with ⟨hmgt, hsq⟩
  have hmMoving' := hmMoving
  unfold movingCanonicalHighSet at hmMoving'
  rcases Finset.mem_filter.mp hmMoving' with ⟨hmPrefix, hhigh⟩
  have hmLt : m < (t + 1) ^ 2 := by
    simpa [cumulativeSquarePrefixSet] using hmPrefix
  have hmX : m ≤ RHLean.Analysis.squarePrefixEndpoint t := by
    rw [← RHLean.Analysis.squarePrefixEndpoint_add_one t] at hmLt
    omega
  have hdata := canonicalSourceData_of_squarefree hsq hmgt
  have hcDvd : canonicalCofactor m ∣ m := canonicalCofactor_dvd hmgt
  have hqDvd : canonicalLargestPrimeFactor m ∣ m :=
    canonicalLargestPrimeFactor_dvd hmgt
  have hcLeM : canonicalCofactor m ≤ m :=
    Nat.le_of_dvd (by omega) hcDvd
  have hqLeM : canonicalLargestPrimeFactor m ≤ m :=
    Nat.le_of_dvd (by omega) hqDvd
  have hcX : canonicalCofactor m ≤ RHLean.Analysis.squarePrefixEndpoint t :=
    hcLeM.trans hmX
  have hqX : canonicalLargestPrimeFactor m ≤ RHLean.Analysis.squarePrefixEndpoint t :=
    hqLeM.trans hmX
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hdata.2.1, hcX⟩,
        Finset.mem_Icc.mpr ⟨hdata.1.two_le, hqX⟩⟩
  · refine ⟨hdata, ?_, ?_⟩
    · have hprod := canonicalCofactor_mul_largestPrimeFactor hmgt
      rw [hprod]
      exact hmX
    · simpa [canonicalHeightTwice] using hhigh

private theorem survivorSource_pair_injective
    {Λ : ℝ} {t m n : ℕ}
    (hm : m ∈ survivorSquarefreeSourceSet Λ t)
    (hn : n ∈ survivorSquarefreeSourceSet Λ t)
    (hpair :
      (canonicalCofactor m, canonicalLargestPrimeFactor m) =
        (canonicalCofactor n, canonicalLargestPrimeFactor n)) :
    m = n := by
  have hmgt : 1 < m := (Finset.mem_filter.mp hm).2.1
  have hngt : 1 < n := (Finset.mem_filter.mp hn).2.1
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

private theorem survivorPair_surjective
    {Λ : ℝ} {t : ℕ}
    (cq : ℕ × ℕ) (hcq : cq ∈ survivorZeroModePairSet Λ t) :
    ∃ m ∈ survivorSquarefreeSourceSet Λ t,
      (canonicalCofactor m, canonicalLargestPrimeFactor m) = cq := by
  classical
  rcases Finset.mem_filter.mp hcq with ⟨_hbase, hpair⟩
  rcases hpair with ⟨hdata, hmulX, hhigh⟩
  have hqPrime := hdata.1
  have hc1 := hdata.2.1
  have hcPos : 0 < cq.1 := by omega
  have hmgt : 1 < cq.1 * cq.2 := by
    calc
      1 < cq.2 := hqPrime.one_lt
      _ = 1 * cq.2 := by simp
      _ ≤ cq.1 * cq.2 := Nat.mul_le_mul_right cq.2 hcPos
  have hsq : Squarefree (cq.1 * cq.2) := by
    have hcop : Nat.Coprime cq.1 cq.2 := hdata.2.2.2.1.symm
    exact (Nat.squarefree_mul hcop).2 ⟨hdata.2.2.1, hqPrime.squarefree⟩
  have hlargest : canonicalLargestPrimeFactor (cq.1 * cq.2) = cq.2 :=
    canonicalLargestPrimeFactor_mul_eq_of_sourceData hdata
  have hcofactor : canonicalCofactor (cq.1 * cq.2) = cq.1 :=
    canonicalCofactor_mul_eq_of_sourceData hdata
  have hmLt :
      cq.1 * cq.2 < RHLean.Analysis.squarePrefixEndpoint t + 1 :=
    Nat.lt_succ_of_le hmulX
  rw [RHLean.Analysis.squarePrefixEndpoint_add_one t] at hmLt
  have hmPrefix : cq.1 * cq.2 ∈ cumulativeSquarePrefixSet t := by
    unfold cumulativeSquarePrefixSet
    exact Finset.mem_range.mpr hmLt
  have hmHigh : IsMovingCanonicalHigh Λ t (cq.1 * cq.2) := by
    unfold IsMovingCanonicalHigh canonicalHeightTwice
    rw [hlargest, hcofactor]
    exact hhigh
  have hmMoving : cq.1 * cq.2 ∈ movingCanonicalHighSet Λ t := by
    unfold movingCanonicalHighSet
    exact Finset.mem_filter.mpr ⟨hmPrefix, hmHigh⟩
  have hmSource : cq.1 * cq.2 ∈ survivorSquarefreeSourceSet Λ t := by
    exact Finset.mem_filter.mpr ⟨hmMoving, hmgt, hsq⟩
  refine ⟨cq.1 * cq.2, hmSource, ?_⟩
  apply Prod.ext
  · exact hcofactor
  · exact hlargest

/-- Exact reindexing of the nonzero moving-high source population by its
canonical cofactor and largest-prime coordinates. -/
theorem sum_survivorSquarefreeSourceSet_eq_pairProducts
    (Λ : ℝ) (t : ℕ) :
    (∑ m ∈ survivorSquarefreeSourceSet Λ t, canonicalMoebiusWeight m) =
      ∑ cq ∈ survivorZeroModePairSet Λ t,
        canonicalMoebiusWeight (cq.1 * cq.2) := by
  classical
  refine Finset.sum_bij
    (fun m _hm => (canonicalCofactor m, canonicalLargestPrimeFactor m))
    (fun m hm => survivorSource_to_pair_mem hm)
    (fun m hm n hn hmn => survivorSource_pair_injective hm hn hmn)
    (fun cq hcq => by simpa using (survivorPair_surjective cq hcq))
    ?_
  intro m hm
  have hmgt : 1 < m := (Finset.mem_filter.mp hm).2.1
  rw [canonicalCofactor_mul_largestPrimeFactor hmgt]

/-- The pair-source sum is exactly the explicit cofactor zero mode. -/
theorem survivorZeroModePairSourceMass_eq_zeroMode
    (Λ : ℝ) (t : ℕ) :
    survivorZeroModePairSourceMass Λ t = survivorZeroMode Λ t := by
  classical
  unfold survivorZeroModePairSourceMass survivorZeroModePairSet
    survivorZeroMode
  rw [Finset.sum_filter]
  calc
    (∑ cq ∈
        (Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t)).product
          (Finset.Icc 2 (RHLean.Analysis.squarePrefixEndpoint t)),
        if IsSurvivorZeroModePair Λ t cq.1 cq.2 then
          canonicalMoebiusWeight (cq.1 * cq.2)
        else 0) =
      ∑ c ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t),
        ∑ q ∈ Finset.Icc 2 (RHLean.Analysis.squarePrefixEndpoint t),
          if IsSurvivorZeroModePair Λ t c q then
            canonicalMoebiusWeight (c * q)
          else 0 := by
      simpa only using
        (Finset.sum_product
          (s := Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t))
          (t := Finset.Icc 2 (RHLean.Analysis.squarePrefixEndpoint t))
          (f := fun cq : ℕ × ℕ =>
            if IsSurvivorZeroModePair Λ t cq.1 cq.2 then
              canonicalMoebiusWeight (cq.1 * cq.2)
            else 0))
    _ = ∑ c ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t),
          ∑ q ∈ Finset.Icc 2 (RHLean.Analysis.squarePrefixEndpoint t),
            if IsSurvivorZeroModePair Λ t c q then
              -canonicalMoebiusWeight c
            else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hpair : IsSurvivorZeroModePair Λ t c q
      · have hweight :=
          canonicalMoebiusWeight_mul_eq_neg_of_sourceData hpair.1
        simp [hpair, hweight]
      · simp [hpair]
    _ = ∑ c ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t),
          survivorZeroModeKernel Λ t c • (-canonicalMoebiusWeight c) := by
      apply Finset.sum_congr rfl
      intro c hc
      unfold survivorZeroModeKernel survivorZeroModePrimeFiber
      rw [← Finset.sum_filter]
      simp

/-- **Exact survivor zero-mode identity.** The actual lifetime-active survivor
mass is the explicit signed cofactor kernel. -/
theorem lifetimeActiveAtomMass_eq_survivorZeroMode
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (t : ℕ) :
    lifetimeActiveAtomMass Λ t = survivorZeroMode Λ t := by
  calc
    lifetimeActiveAtomMass Λ t = movingCanonicalHighSum Λ t :=
      lifetimeActiveAtomMass_eq_movingCanonicalHighSum hΛ t
    _ = ∑ m ∈ survivorSquarefreeSourceSet Λ t,
          canonicalMoebiusWeight m :=
      movingCanonicalHighSum_eq_survivorSquarefreeSourceMass hΛ t
    _ = survivorZeroModePairSourceMass Λ t :=
      sum_survivorSquarefreeSourceSet_eq_pairProducts Λ t
    _ = survivorZeroMode Λ t :=
      survivorZeroModePairSourceMass_eq_zeroMode Λ t

/-- Pure-prime part of the zero mode, isolated by the cofactor value `c=1`. -/
def survivorPrimeZeroMode (Λ : ℝ) (t : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t),
    if c = 1 then
      survivorZeroModeKernel Λ t c • (-canonicalMoebiusWeight c)
    else 0

/-- Genuine composite-fibre part of the zero mode, containing all cofactors
`c>=2`. -/
def survivorCompositeZeroMode (Λ : ℝ) (t : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t),
    if 2 ≤ c then
      survivorZeroModeKernel Λ t c • (-canonicalMoebiusWeight c)
    else 0

/-- Exact prime/composite partition of the survivor zero mode. This is only a
structural split: the prime fibre is not claimed to satisfy the target power
bound separately. -/
theorem survivorZeroMode_eq_prime_add_composite
    (Λ : ℝ) (t : ℕ) :
    survivorZeroMode Λ t =
      survivorPrimeZeroMode Λ t + survivorCompositeZeroMode Λ t := by
  classical
  unfold survivorZeroMode survivorPrimeZeroMode survivorCompositeZeroMode
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
  by_cases hcone : c = 1
  · simp [hcone]
  · have hc2 : 2 ≤ c := by omega
    simp [hcone, hc2]

/-- General extreme-largest-prime observation. If `m<=x` and twice its
canonical largest prime is already above `x`, then its canonical cofactor is
one. -/
theorem canonicalCofactor_eq_one_of_endpoint_lt_two_mul_largestPrime
    {x m : ℕ} (hmgt : 1 < m) (hmx : m ≤ x)
    (hlarge : x < 2 * canonicalLargestPrimeFactor m) :
    canonicalCofactor m = 1 := by
  have hc1 : 1 ≤ canonicalCofactor m := canonicalCofactor_pos hmgt
  have hprod := canonicalCofactor_mul_largestPrimeFactor hmgt
  by_contra hne
  have hc2 : 2 ≤ canonicalCofactor m := by omega
  have htwo :
      2 * canonicalLargestPrimeFactor m ≤
        canonicalCofactor m * canonicalLargestPrimeFactor m :=
    Nat.mul_le_mul_right (canonicalLargestPrimeFactor m) hc2
  rw [hprod] at htwo
  omega

/-- Hence the extreme-largest-prime source is the prime itself. -/
theorem eq_largestPrimeFactor_of_endpoint_lt_two_mul_largestPrime
    {x m : ℕ} (hmgt : 1 < m) (hmx : m ≤ x)
    (hlarge : x < 2 * canonicalLargestPrimeFactor m) :
    m = canonicalLargestPrimeFactor m := by
  have hc :=
    canonicalCofactor_eq_one_of_endpoint_lt_two_mul_largestPrime
      hmgt hmx hlarge
  have hprod := canonicalCofactor_mul_largestPrimeFactor hmgt
  calc
    m = canonicalCofactor m * canonicalLargestPrimeFactor m := hprod.symm
    _ = canonicalLargestPrimeFactor m := by rw [hc]; simp

/-- In a survivor cofactor fibre, an extreme prime satisfying `2q>X_t` forces
`c=1`; there are no genuine composite sources in that extreme region. -/
theorem survivorZeroMode_core_eq_one_of_endpoint_lt_two_mul_prime
    {Λ : ℝ} {t c q : ℕ}
    (hq : q ∈ survivorZeroModePrimeFiber Λ t c)
    (hlarge : RHLean.Analysis.squarePrefixEndpoint t < 2 * q) :
    c = 1 := by
  classical
  rcases Finset.mem_filter.mp hq with ⟨_hqRange, hpair⟩
  have hc1 : 1 ≤ c := hpair.1.2.1
  have hprod : c * q ≤ RHLean.Analysis.squarePrefixEndpoint t := hpair.2.1
  by_contra hne
  have hc2 : 2 ≤ c := by omega
  have htwo : 2 * q ≤ c * q := Nat.mul_le_mul_right q hc2
  exact (not_le_of_gt hlarge) (htwo.trans hprod)

/-- The explicit zero mode has exactly the same translated-window energy as the
actual lifetime-active survivor sequence. -/
theorem survivorZeroMode_localEnergy_eq_lifetimeActive
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (N H : ℕ) :
    RHLean.Analysis.localSequenceEnergy (survivorZeroMode Λ) N H =
      RHLean.Analysis.localSequenceEnergy (lifetimeActiveAtomMass Λ) N H := by
  unfold RHLean.Analysis.localSequenceEnergy
  apply Finset.sum_congr rfl
  intro h hh
  rw [← lifetimeActiveAtomMass_eq_survivorZeroMode hΛ]

/-- The remaining lifetime-active RH-scale statement, written directly on the
explicit signed cofactor zero-mode operator. The companion square-wheel layer
shows how differences of complete square endpoints sit inside primorial-wheel
residual oscillation, so this is not intended to be estimated independently of
that oscillation. -/
def SurvivorZeroModePowerSavingStatement (Λ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        RHLean.Analysis.localSequenceEnergy (survivorZeroMode Λ) N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- The explicit zero-mode power-saving statement is exactly the current
lifetime-active survivor premise. -/
theorem survivorZeroModePowerSaving_iff_lifetimeActive
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    SurvivorZeroModePowerSavingStatement Λ ↔
      LifetimeActiveUniformLocalBoundedStatement Λ := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N H hH hHN
    rw [← survivorZeroMode_localEnergy_eq_lifetimeActive hΛ]
    exact hbound N H hH hHN
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N H hH hHN
    rw [survivorZeroMode_localEnergy_eq_lifetimeActive hΛ]
    exact hbound N H hH hHN

/-- After PR #214, the explicit zero-mode power saving is exactly the remaining
lifetime endpoint discrepancy premise. -/
theorem survivorZeroModePowerSaving_iff_endpointDiscrepancy
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    SurvivorZeroModePowerSavingStatement Λ ↔
      LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ := by
  rw [survivorZeroModePowerSaving_iff_lifetimeActive hΛ,
    lifetimeActiveUniformLocalBounded_iff_endpointDiscrepancy Λ]

/-- The protected square-prefix criterion follows from a power saving on the
explicit survivor zero mode. -/
theorem survivorZeroModePowerSaving_implies_squarePrefixUniformLocal
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hzero : SurvivorZeroModePowerSavingStatement Λ) :
    RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement := by
  apply lifetimeEndpointDiscrepancy_implies_squarePrefixUniformLocal hΛ
  exact (survivorZeroModePowerSaving_iff_endpointDiscrepancy hΛ.le).1 hzero

/-- Terminal protected consequence: a power saving on this exact zero-mode
operator implies RH through the existing classical Mertens-energy criterion. -/
theorem survivorZeroModePowerSaving_implies_riemannHypothesis
    {Λ : ℝ} (hΛ : 0 < Λ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion)
    (hzero : SurvivorZeroModePowerSavingStatement Λ) :
    RHLean.Analysis.RiemannHypothesisStatement := by
  apply lifetimeEndpointDiscrepancy_implies_riemannHypothesis hΛ criterion
  exact (survivorZeroModePowerSaving_iff_endpointDiscrepancy hΛ.le).1 hzero

end RHLean.Proof