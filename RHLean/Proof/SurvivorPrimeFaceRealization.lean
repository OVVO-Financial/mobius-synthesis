import Mathlib
import RHLean.Arithmetic.PrimeFaceMoebius
import RHLean.Arithmetic.SquarefreePrimeFaceSurjectivity
import RHLean.Proof.SurvivorPrimeFaceFrontier

/-!
# Actual survivor prime-face realization

This module identifies the abstract prime-face cancellation from
`SurvivorPrimeFaceFrontier` with the repository's actual fixed-`q` survivor
cofactor fibre.

For a prime `q`, every face of primes below `q` represents canonical source data,
and every active canonical cofactor is recovered uniquely from its squarefree
prime face. The Möbius weight of the represented cofactor is exactly the
Boolean-cube sign. Hence the actual fixed-prime survivor mass is the negative
complex cast of the alternating high prime-face mass, and therefore of the
three signed first-failure frontiers.

No cardinality estimate or analytic cancellation hypothesis is introduced.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open CanonicalGapAncestryBridge
open RHLean.Arithmetic

/-- Active cofactors in one actual fixed upper-prime survivor fibre. -/
noncomputable def survivorFixedPrimeActiveCofactors
    (Λ : ℝ) (t q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t)).filter
    (fun c => IsSurvivorZeroModePair Λ t c q)

/-- Prime faces selected by the same product and high-height conditions. -/
noncomputable def survivorPrimeFaceHighSet
    (Λ : ℝ) (t q : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (survivorPrimeFaceAmbient q).powerset.filter
    (survivorPrimeFaceHigh Λ t q)

private theorem prime_of_mem_survivorPrimeFaceAmbient
    {q p : ℕ} (hp : p ∈ survivorPrimeFaceAmbient q) : Nat.Prime p := by
  exact prime_of_mem_primesUpTo hp

private theorem primeFaceProduct_squarefree_of_subset_ambient
    {q : ℕ} {u : Finset ℕ}
    (hu : u ⊆ survivorPrimeFaceAmbient q) :
    Squarefree (primeFaceProduct u) := by
  have hprime : ∀ p ∈ u, Nat.Prime p := by
    intro p hp
    exact prime_of_mem_survivorPrimeFaceAmbient (hu hp)
  have hmu := moebius_primeFaceProduct_eq_booleanCubeSign u hprime
  by_contra hnsq
  have hz := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
  rw [hmu] at hz
  have hsign : booleanCubeSign u ≠ 0 := by
    simp [booleanCubeSign]
  exact hsign hz

/-- Every face of primes below a distinguished prime gives valid canonical
source data for that same distinguished prime. -/
theorem canonicalSourceData_primeFaceProduct
    {q : ℕ} (hq : q.Prime) {u : Finset ℕ}
    (hu : u ⊆ survivorPrimeFaceAmbient q) :
    CanonicalSourceData q (primeFaceProduct u) := by
  have hprime : ∀ p ∈ u, Nat.Prime p := by
    intro p hp
    exact prime_of_mem_survivorPrimeFaceAmbient (hu hp)
  have hsq : Squarefree (primeFaceProduct u) :=
    primeFaceProduct_squarefree_of_subset_ambient hu
  have hcpos : 1 ≤ primeFaceProduct u := by
    exact Nat.one_le_iff_ne_zero.mpr hsq.ne_zero
  have hnotdvd : ¬ q ∣ primeFaceProduct u := by
    intro hqd
    have hqd' : q ∣ u.prod id := by
      simpa [primeFaceProduct] using hqd
    rcases (Prime.dvd_finset_prod_iff hq.prime id).mp hqd' with
      ⟨p, hpu, hqp⟩
    have hpPrime := hprime p hpu
    rcases hpPrime.eq_one_or_self_of_dvd q hqp with hq1 | hqeq
    · exact hq.ne_one hq1
    · have hpBound := (mem_primesUpTo.mp (hu hpu)).2
      have hpLe : p ≤ p - 1 := by simpa only [hqeq] using hpBound
      have hp2 : 2 ≤ p := hpPrime.two_le
      omega
  refine ⟨hq, hcpos, hsq, hq.coprime_iff_not_dvd.mpr hnotdvd, ?_⟩
  intro p hp hpd
  have hpd' : p ∣ u.prod id := by
    simpa [primeFaceProduct] using hpd
  rcases (Prime.dvd_finset_prod_iff hp.prime id).mp hpd' with
    ⟨r, hru, hpr⟩
  have hrPrime := hprime r hru
  rcases hrPrime.eq_one_or_self_of_dvd p hpr with hp1 | hpeq
  · exact (hp.ne_one hp1).elim
  · have hrBound := (mem_primesUpTo.mp (hu hru)).2
    have hpBound : p ≤ q - 1 := by simpa only [hpeq] using hrBound
    have hq2 : 2 ≤ q := hq.two_le
    omega

/-- On a prime face below `q`, the abstract high predicate is exactly the actual
survivor-pair predicate of its represented cofactor. -/
theorem survivorPrimeFaceHigh_iff_isSurvivorZeroModePair
    (Λ : ℝ) (t : ℕ) {q : ℕ} (hq : q.Prime)
    {u : Finset ℕ} (hu : u ⊆ survivorPrimeFaceAmbient q) :
    survivorPrimeFaceHigh Λ t q u ↔
      IsSurvivorZeroModePair Λ t (primeFaceProduct u) q := by
  constructor
  · intro h
    exact ⟨canonicalSourceData_primeFaceProduct hq hu, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨hu, h.2.1⟩, h.2.2⟩

/-- The active cofactor set and the selected prime-face set are in exact
bijection under `u ↦ primeFaceProduct u`. -/
theorem survivorPrimeFaceHighSet_bij_activeCofactors
    (Λ : ℝ) (t : ℕ) {q : ℕ} (hq : q.Prime) :
    (∑ u ∈ survivorPrimeFaceHighSet Λ t q, μ (primeFaceProduct u)) =
      ∑ c ∈ survivorFixedPrimeActiveCofactors Λ t q, μ c := by
  classical
  refine Finset.sum_bij (fun u _ => primeFaceProduct u) ?_ ?_ ?_ ?_
  · intro u hu
    rw [survivorPrimeFaceHighSet, Finset.mem_filter] at hu
    obtain ⟨huPower, huHigh⟩ := hu
    have huSub : u ⊆ survivorPrimeFaceAmbient q :=
      Finset.mem_powerset.mp huPower
    have hpair : IsSurvivorZeroModePair Λ t (primeFaceProduct u) q :=
      (survivorPrimeFaceHigh_iff_isSurvivorZeroModePair Λ t hq huSub).mp huHigh
    have hcpos : 1 ≤ primeFaceProduct u := hpair.1.2.1
    have hqone : 1 ≤ q := hq.one_le
    have hcX : primeFaceProduct u ≤ RHLean.Analysis.squarePrefixEndpoint t := by
      calc
        primeFaceProduct u = primeFaceProduct u * 1 := by simp
        _ ≤ primeFaceProduct u * q := Nat.mul_le_mul_left _ hqone
        _ ≤ RHLean.Analysis.squarePrefixEndpoint t := hpair.2.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hcpos, hcX⟩, hpair⟩
  · intro u1 hu1 u2 hu2 hprod
    rw [survivorPrimeFaceHighSet, Finset.mem_filter] at hu1 hu2
    have hsub1 := Finset.mem_powerset.mp hu1.1
    have hsub2 := Finset.mem_powerset.mp hu2.1
    exact (primeFaceProduct_eq_iff
      (fun p hp => prime_of_mem_survivorPrimeFaceAmbient (hsub1 hp))
      (fun p hp => prime_of_mem_survivorPrimeFaceAmbient (hsub2 hp))).mp hprod
  · intro c hc
    rw [survivorFixedPrimeActiveCofactors, Finset.mem_filter] at hc
    obtain ⟨_hcRange, hpair⟩ := hc
    rcases hpair.1 with ⟨_hq', _hcpos, hsq, _hcop, hdom⟩
    let u := squarefreePrimeFace c
    have huSub : u ⊆ survivorPrimeFaceAmbient q := by
      intro p hpface
      have hpData := Nat.mem_primeFactors.mp hpface
      have hplt := hdom p hpData.1 hpData.2.1
      exact mem_primesUpTo.mpr ⟨hpData.1, by omega⟩
    have hprod : primeFaceProduct u = c :=
      primeFaceProduct_squarefreePrimeFace hsq
    have huHigh : survivorPrimeFaceHigh Λ t q u := by
      apply (survivorPrimeFaceHigh_iff_isSurvivorZeroModePair Λ t hq huSub).mpr
      simpa [hprod] using hpair
    refine ⟨u, ?_, hprod⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr huSub, huHigh⟩
  · intro u _hu
    rfl

/-- The integer Möbius mass of the actual active cofactor fibre is exactly the
alternating mass of its prime faces. -/
theorem survivorFixedPrimeActiveMobiusMass_eq_faceAlternating
    (Λ : ℝ) (t : ℕ) {q : ℕ} (hq : q.Prime) :
    (∑ c ∈ survivorFixedPrimeActiveCofactors Λ t q, μ c) =
      truncatedCubeAlternatingSum (survivorPrimeFaceAmbient q)
        (survivorPrimeFaceHigh Λ t q) := by
  classical
  rw [← survivorPrimeFaceHighSet_bij_activeCofactors Λ t hq]
  unfold survivorPrimeFaceHighSet truncatedCubeAlternatingSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hhigh : survivorPrimeFaceHigh Λ t q u
  · have huSub : u ⊆ survivorPrimeFaceAmbient q := Finset.mem_powerset.mp hu
    have hprime : ∀ p ∈ u, Nat.Prime p := by
      intro p hp
      exact prime_of_mem_survivorPrimeFaceAmbient (huSub hp)
    simp [hhigh, moebius_primeFaceProduct_eq_booleanCubeSign u hprime]
  · simp [hhigh]

/-- The actual fixed-prime survivor mass is the negative complex cast of the
prime-face alternating high mass. -/
theorem survivorFixedPrimeCofactorMass_eq_neg_faceAlternating
    (Λ : ℝ) (t : ℕ) {q : ℕ} (hq : q.Prime) :
    survivorFixedPrimeCofactorMass Λ t q =
      -((truncatedCubeAlternatingSum (survivorPrimeFaceAmbient q)
        (survivorPrimeFaceHigh Λ t q) : ℤ) : ℂ) := by
  classical
  unfold survivorFixedPrimeCofactorMass
  calc
    (∑ c ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t),
        survivorFixedPrimeCofactorTerm Λ t q c) =
      ∑ c ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t),
        if IsSurvivorZeroModePair Λ t c q then -canonicalMoebiusWeight c else 0 := by
      apply Finset.sum_congr rfl
      intro c _hc
      unfold survivorFixedPrimeCofactorTerm survivorFixedPrimeActivityIndicator
      by_cases h : IsSurvivorZeroModePair Λ t c q <;> simp [h]
    _ = ∑ c ∈ survivorFixedPrimeActiveCofactors Λ t q,
        -canonicalMoebiusWeight c := by
      unfold survivorFixedPrimeActiveCofactors
      rw [Finset.sum_filter]
    _ = -((∑ c ∈ survivorFixedPrimeActiveCofactors Λ t q, μ c : ℤ) : ℂ) := by
      unfold canonicalMoebiusWeight
      push_cast
      rw [Finset.sum_neg_distrib]
    _ = -((truncatedCubeAlternatingSum (survivorPrimeFaceAmbient q)
          (survivorPrimeFaceHigh Λ t q) : ℤ) : ℂ) := by
      rw [survivorFixedPrimeActiveMobiusMass_eq_faceAlternating Λ t hq]

/-- Actual three-frontier survivor cancellation. For every selected prime
coordinate below `q`, the complete fixed-`q` survivor fibre is exactly the
negative complex cast of three signed first-failure frontiers. Thus every
interior prime-face contribution has already cancelled before any magnitude is
taken. -/
theorem survivorFixedPrimeCofactorMass_eq_neg_threeFrontiers
    (Λ : ℝ) (t : ℕ) {q ell : ℕ} (hq : q.Prime) (hΛ : 0 ≤ Λ)
    (hell : ell ∈ survivorPrimeFaceAmbient q) :
    survivorFixedPrimeCofactorMass Λ t q =
      -((firstFailureBoundaryAlternatingSum (survivorPrimeFaceAmbient q) ell
            (survivorPrimeFaceTransportPrefix Λ t q) +
          firstFailureBoundaryAlternatingSum (survivorPrimeFaceAmbient q) ell
            (survivorPrimeFaceProductPrefix t q) -
          firstFailureBoundaryAlternatingSum (survivorPrimeFaceAmbient q) ell
            (survivorPrimeFaceBelowSmoothPrefix Λ t q) : ℤ) : ℂ) := by
  rw [survivorFixedPrimeCofactorMass_eq_neg_faceAlternating Λ t hq]
  rw [survivorPrimeFaceHigh_alternatingMass_eq_threeFrontiers Λ t q ell hΛ hell]

end RHLean.Proof
