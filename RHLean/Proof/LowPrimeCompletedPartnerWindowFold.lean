import Mathlib
import RHLean.Proof.LowPrimeParentChildWindowDifference
import RHLean.Proof.LowWheelSequentialRoughWindowFold

/-!
# Completed partner cube as an exact `window - p*window` fold

`LowPrimeParentChildWindowDifference` exposes the reciprocal prime-dilate
window in the post-root parent/child finite difference.  This module closes the
remaining representation gap for an arbitrary fresh prime `p <= R`.

The prime count in that window is not merely analogous to the low-wheel mixed
cell.  Complete the partner sieve through every low prime `<= R`, remove `p`
from that completed coordinate set, and split the full Boolean cube at `p`.
Then the prime-window count is exactly

`sum_t (-1)^|t| sum_k [1_W(P(t)k) - 1_W(p*P(t)k)]`.

The inner bracket is precisely `lowWheelMixedPrimeCell` by the already-checked
sequential window theorem.  Primes larger than `p` and at most `R` are spectator
coordinates needed to complete the partner sieve; when `p = R` is prime, those
spectators disappear and the completed partner cube is exactly the chronological
old cube `primesUpTo (p-1)`.

No absolute value, norm, PNT estimate, density statement, Mertens bound, or RH
input appears.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- All completed low-prime partner coordinates except the distinguished fresh
prime `p`. -/
def lowPrimeCompletedPartnerCoordinates (p R : ℕ) : Finset ℕ :=
  (primesUpTo R).erase p

/-- In one reciprocal `p`-window, the physical integers divisible by one
completed partner face, with the distinguished prime itself excluded. -/
def lowPrimeCompletedWindowFaceDivisorSet
    (p R X a : ℕ) (t : Finset ℕ) : Finset ℕ :=
  (primeDilateCofactorWindow p R X a).filter fun q =>
    ¬ p ∣ q ∧ primeFaceProduct t ∣ q

/-- The same reciprocal window, but now retaining exactly the integers which
survive the complete low wheel through `R`. -/
def lowPrimeCompletedWindowSurvivorSet
    (p R X a : ℕ) : Finset ℕ :=
  (primeDilateCofactorWindow p R X a).filter (lowWheelHighSurvivor R)

@[simp] theorem mem_lowPrimeCompletedWindowFaceDivisorSet
    {p R X a : ℕ} {t : Finset ℕ} {q : ℕ} :
    q ∈ lowPrimeCompletedWindowFaceDivisorSet p R X a t ↔
      q ∈ primeDilateCofactorWindow p R X a ∧
        ¬ p ∣ q ∧ primeFaceProduct t ∣ q := by
  simp [lowPrimeCompletedWindowFaceDivisorSet, and_assoc]

@[simp] theorem mem_lowPrimeCompletedWindowSurvivorSet
    {p R X a q : ℕ} :
    q ∈ lowPrimeCompletedWindowSurvivorSet p R X a ↔
      q ∈ primeDilateCofactorWindow p R X a ∧
        lowWheelHighSurvivor R q := by
  simp [lowPrimeCompletedWindowSurvivorSet]

/-- A completed partner face omitting `p` has product coprime to the fresh
prime. -/
theorem freshPrime_not_dvd_completedPartnerFaceProduct
    {p R : ℕ} (hp : p.Prime) (_hpR : p ≤ R) {t : Finset ℕ}
    (ht : t ∈ (lowPrimeCompletedPartnerCoordinates p R).powerset) :
    ¬ p ∣ primeFaceProduct t := by
  intro hdiv
  have hdiv' : p ∣ t.prod id := by
    simpa [primeFaceProduct] using hdiv
  rcases (Prime.dvd_finset_prod_iff hp.prime id).mp hdiv' with
    ⟨r, hrt, hpr⟩
  have htSub := Finset.mem_powerset.mp ht
  have hrCoord : r ∈ lowPrimeCompletedPartnerCoordinates p R := htSub hrt
  have hrData : r ≠ p ∧ r ∈ primesUpTo R := by
    simpa [lowPrimeCompletedPartnerCoordinates] using
      (Finset.mem_erase.mp hrCoord)
  have hrPrime : r.Prime := prime_of_mem_primesUpTo hrData.2
  have hprEq : p = r :=
    (Nat.prime_dvd_prime_iff_eq hp hrPrime).mp hpr
  exact hrData.1 hprEq.symm

/-- Completed partner faces are still ordinary low-prime faces of the full
wheel through `R`. -/
theorem completedPartnerFace_mem_primesUpTo_powerset
    {p R : ℕ} {t : Finset ℕ}
    (ht : t ∈ (lowPrimeCompletedPartnerCoordinates p R).powerset) :
    t ∈ (primesUpTo R).powerset := by
  apply Finset.mem_powerset.mpr
  intro r hr
  have hrCoord := (Finset.mem_powerset.mp ht) hr
  exact (Finset.mem_erase.mp hrCoord).2

/-- **Completed partner inclusion-exclusion with the `p` coordinate already
split off.**  The full survivor indicator through `R` is the alternating mass
of faces omitting `p`, with the single additional condition `p ∤ q`.

This is exactly the partner-side old-parent/fresh-child cancellation before any
window sum is taken. -/
theorem lowPrimeCompletedPartnerDivisorSum_eq_survivorIndicator
    {p R q : ℕ} (hp : p.Prime) (hpR : p ≤ R) :
    (∑ t ∈ (lowPrimeCompletedPartnerCoordinates p R).powerset,
        if ¬ p ∣ q ∧ primeFaceProduct t ∣ q then
          booleanCubeSign t
        else 0) =
      if lowWheelHighSurvivor R q then (1 : ℤ) else 0 := by
  classical
  have hpMem : p ∈ primesUpTo R :=
    mem_primesUpTo.mpr ⟨hp, hpR⟩
  have hpNotCoord : p ∉ lowPrimeCompletedPartnerCoordinates p R := by
    simp [lowPrimeCompletedPartnerCoordinates]
  have hdecomp :
      insert p (lowPrimeCompletedPartnerCoordinates p R) = primesUpTo R := by
    simpa [lowPrimeCompletedPartnerCoordinates] using
      (Finset.insert_erase hpMem)
  calc
    (∑ t ∈ (lowPrimeCompletedPartnerCoordinates p R).powerset,
        if ¬ p ∣ q ∧ primeFaceProduct t ∣ q then
          booleanCubeSign t
        else 0) = lowWheelDivisorFaceSum R q := by
      unfold lowWheelDivisorFaceSum
      rw [← hdecomp]
      rw [Finset.sum_powerset_insert hpNotCoord]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      have hpNot : p ∉ t :=
        Finset.notMem_of_mem_powerset_of_notMem ht hpNotCoord
      have hprod : primeFaceProduct (insert p t) =
          p * primeFaceProduct t := by
        simp [primeFaceProduct, hpNot]
      have hsign : booleanCubeSign (insert p t) = - booleanCubeSign t := by
        simp [booleanCubeSign, hpNot, Finset.card_insert_of_notMem, pow_succ]
      have hpNotProd : ¬ p ∣ primeFaceProduct t :=
        freshPrime_not_dvd_completedPartnerFaceProduct hp hpR ht
      by_cases hpq : p ∣ q
      · by_cases htq : primeFaceProduct t ∣ q
        · have hcop : Nat.Coprime p (primeFaceProduct t) :=
            (hp.coprime_iff_not_dvd).2 hpNotProd
          have hchild : p * primeFaceProduct t ∣ q :=
            hcop.mul_dvd_of_dvd_of_dvd hpq htq
          simp [hpq, htq, hprod, hchild, hsign]
        · have hchildNot : ¬ p * primeFaceProduct t ∣ q := by
            intro hchild
            exact htq ((dvd_mul_left (primeFaceProduct t) p).trans hchild)
          simp [hpq, htq, hprod, hchildNot]
      · have hchildNot : ¬ p * primeFaceProduct t ∣ q := by
          intro hchild
          exact hpq ((dvd_mul_right p (primeFaceProduct t)).trans hchild)
        by_cases htq : primeFaceProduct t ∣ q <;>
          simp [hpq, htq, hprod, hchildNot]
    _ = if lowWheelHighSurvivor R q then (1 : ℤ) else 0 :=
      lowWheelDivisorFaceSum_eq_survivorIndicator R q

/-- **Collapse the completed partner cube inside one reciprocal window.** -/
theorem sum_completedPartnerFaceDivisorCounts_eq_windowSurvivorCard
    (p R X a : ℕ) (hp : p.Prime) (hpR : p ≤ R) :
    (∑ t ∈ (lowPrimeCompletedPartnerCoordinates p R).powerset,
        booleanCubeSign t *
          ((lowPrimeCompletedWindowFaceDivisorSet p R X a t).card : ℤ)) =
      ((lowPrimeCompletedWindowSurvivorSet p R X a).card : ℤ) := by
  classical
  unfold lowPrimeCompletedWindowFaceDivisorSet
    lowPrimeCompletedWindowSurvivorSet
  calc
    (∑ t ∈ (lowPrimeCompletedPartnerCoordinates p R).powerset,
        booleanCubeSign t *
          (((primeDilateCofactorWindow p R X a).filter fun q =>
            ¬ p ∣ q ∧ primeFaceProduct t ∣ q).card : ℤ)) =
      ∑ t ∈ (lowPrimeCompletedPartnerCoordinates p R).powerset,
        ∑ q ∈ primeDilateCofactorWindow p R X a,
          if ¬ p ∣ q ∧ primeFaceProduct t ∣ q then
            booleanCubeSign t
          else 0 := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [← Finset.sum_filter]
      simp [mul_comm]
    _ = ∑ q ∈ primeDilateCofactorWindow p R X a,
        ∑ t ∈ (lowPrimeCompletedPartnerCoordinates p R).powerset,
          if ¬ p ∣ q ∧ primeFaceProduct t ∣ q then
            booleanCubeSign t
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ primeDilateCofactorWindow p R X a,
        if lowWheelHighSurvivor R q then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro q _hq
      exact lowPrimeCompletedPartnerDivisorSum_eq_survivorIndicator hp hpR
    _ = (((primeDilateCofactorWindow p R X a).filter
          (lowWheelHighSurvivor R)).card : ℤ) := by
      rw [← Finset.sum_filter]
      simp

/-- The multiplier realization remains valid for completed partner faces on
both sides of `p`; only omission of `p` itself is required. -/
theorem card_lowWheelPrimeWindowFreeMultiplier_eq_completedFaceDivisor
    {p R X a : ℕ} (hp : p.Prime) (hpR : p ≤ R) (ha : 0 < a)
    {t : Finset ℕ}
    (ht : t ∈ (lowPrimeCompletedPartnerCoordinates p R).powerset) :
    (lowWheelPrimeWindowFreeMultiplierSet
      p R X a (primeFaceProduct t)).card =
      (lowPrimeCompletedWindowFaceDivisorSet p R X a t).card := by
  classical
  have htFull := completedPartnerFace_mem_primesUpTo_powerset ht
  have htPos : 0 < primeFaceProduct t :=
    primeFaceProduct_pos_of_mem_powerset htFull
  have hpNot : ¬ p ∣ primeFaceProduct t :=
    freshPrime_not_dvd_completedPartnerFaceProduct hp hpR ht
  refine Finset.card_bij (fun k _hk => primeFaceProduct t * k) ?_ ?_ ?_
  · intro k hk
    rcases mem_lowWheelPrimeWindowFreeMultiplierSet.mp hk with
      ⟨hkWindow, hpk⟩
    rcases mem_lowWheelPrimeWindowMultiplierSet.mp hkWindow with
      ⟨_hk1, _hkX, hwindow⟩
    apply mem_lowPrimeCompletedWindowFaceDivisorSet.mpr
    refine ⟨hwindow, ?_, dvd_mul_right (primeFaceProduct t) k⟩
    intro hpq
    rcases hp.dvd_mul.mp hpq with hpface | hpk'
    · exact hpNot hpface
    · exact hpk hpk'
  · intro k1 _hk1 k2 _hk2 hmul
    exact Nat.eq_of_mul_eq_mul_left htPos hmul
  · intro q hq
    rcases mem_lowPrimeCompletedWindowFaceDivisorSet.mp hq with
      ⟨hwindow, hpq, hdiv⟩
    let k := q / primeFaceProduct t
    have hqRange := primeDilateCofactorWindow_subset_Ioc p R X a ha hwindow
    have hqpos : 0 < q := by
      have := (Finset.mem_Ioc.mp hqRange).1
      omega
    have hfaceLeQ : primeFaceProduct t ≤ q :=
      Nat.le_of_dvd hqpos hdiv
    have hk1 : 1 ≤ k := by
      unfold k
      exact (Nat.one_le_div_iff htPos).2 hfaceLeQ
    have hkX : k ≤ X := by
      unfold k
      exact (Nat.div_le_self q (primeFaceProduct t)).trans
        (Finset.mem_Ioc.mp hqRange).2
    have hcancel : primeFaceProduct t * k = q := by
      unfold k
      exact Nat.mul_div_cancel' hdiv
    have hpk : ¬ p ∣ k := by
      intro hpk'
      apply hpq
      rw [← hcancel]
      exact dvd_mul_of_dvd_right hpk' (primeFaceProduct t)
    refine ⟨k, mem_lowWheelPrimeWindowFreeMultiplierSet.mpr
      ⟨mem_lowWheelPrimeWindowMultiplierSet.mpr
        ⟨hk1, hkX, by simpa [hcancel] using hwindow⟩, hpk⟩, hcancel⟩

/-- Completed partner-side mixed-cell fold in one reciprocal window. -/
def lowPrimeCompletedPartnerMixedFold
    (p R X a : ℕ) : ℤ :=
  ∑ t ∈ (lowPrimeCompletedPartnerCoordinates p R).powerset,
    booleanCubeSign t *
      ∑ k ∈ Finset.Icc 1 X,
        lowWheelMixedPrimeCell p R X
          (primeFaceProduct t * k)
          (a * (primeFaceProduct t * k))

/-- **Completed `window - p*window` fold = complete low-wheel survivor count.**
Every inner sum is first the literal mixed window difference and then the
`p`-free multiplier count; the completed partner cube removes every remaining
low-prime divisor. -/
theorem lowPrimeCompletedPartnerMixedFold_eq_windowSurvivorCard
    (p R X a : ℕ) (hp : p.Prime) (hpR : p ≤ R) (ha : 0 < a) :
    lowPrimeCompletedPartnerMixedFold p R X a =
      ((lowPrimeCompletedWindowSurvivorSet p R X a).card : ℤ) := by
  unfold lowPrimeCompletedPartnerMixedFold
  calc
    (∑ t ∈ (lowPrimeCompletedPartnerCoordinates p R).powerset,
      booleanCubeSign t *
        ∑ k ∈ Finset.Icc 1 X,
          lowWheelMixedPrimeCell p R X
            (primeFaceProduct t * k)
            (a * (primeFaceProduct t * k))) =
      ∑ t ∈ (lowPrimeCompletedPartnerCoordinates p R).powerset,
        booleanCubeSign t *
          ((lowPrimeCompletedWindowFaceDivisorSet p R X a t).card : ℤ) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htFull := completedPartnerFace_mem_primesUpTo_powerset ht
      have htPos : 0 < primeFaceProduct t :=
        primeFaceProduct_pos_of_mem_powerset htFull
      have htel := sum_lowWheelMixedPrimeCell_mul_eq_freeWindowCard
        (p := p) (R := R) (X := X) (a := a)
        (b := primeFaceProduct t) hp ha htPos
      have hcard :=
        card_lowWheelPrimeWindowFreeMultiplier_eq_completedFaceDivisor
          (p := p) (R := R) (X := X) (a := a) hp hpR ha ht
      rw [htel, hcard]
    _ = ((lowPrimeCompletedWindowSurvivorSet p R X a).card : ℤ) :=
      sum_completedPartnerFaceDivisorCounts_eq_windowSurvivorCard
        p R X a hp hpR

/-- On a square-root reciprocal window the completed survivor set is literally
the prime set, because every window point lies strictly above `R` and below the
complete square endpoint. -/
theorem lowPrimeCompletedWindowSurvivorSet_eq_windowPrimeSet
    {p R a : ℕ} (hR : 2 ≤ R) (ha : 0 < a) :
    lowPrimeCompletedWindowSurvivorSet
        p R (squareRootEndpoint R) a =
      squareRootPrimeDilateWindowPrimeSet p R a := by
  classical
  ext q
  simp only [lowPrimeCompletedWindowSurvivorSet,
    squareRootPrimeDilateWindowPrimeSet, Finset.mem_filter]
  constructor
  · rintro ⟨hwindow, hsurv⟩
    have hqRange := primeDilateCofactorWindow_subset_Ioc
      p R (squareRootEndpoint R) a ha hwindow
    have hqI := Finset.mem_Ioc.mp hqRange
    exact ⟨hwindow,
      (lowWheelHighSurvivor_iff_prime hR hqI.1 hqI.2).mp hsurv⟩
  · rintro ⟨hwindow, hprime⟩
    have hqRange := primeDilateCofactorWindow_subset_Ioc
      p R (squareRootEndpoint R) a ha hwindow
    have hqI := Finset.mem_Ioc.mp hqRange
    exact ⟨hwindow,
      (lowWheelHighSurvivor_iff_prime hR hqI.1 hqI.2).mpr hprime⟩

/-- **Prime-window count = completed `window - p*window` mixed fold.**
This is the exact identification needed for the BornPostTail high-channel
finite difference at every fresh prime `p <= R`. -/
theorem primeDilateCofactorWindowPrimeCount_eq_completedPartnerMixedFold
    {p R a : ℕ} (hp : p.Prime) (hpR : p ≤ R)
    (hR : 2 ≤ R) (ha : 0 < a) :
    primeDilateCofactorWindowPrimeCount
        p R (squareRootEndpoint R) a =
      (lowPrimeCompletedPartnerMixedFold
        p R (squareRootEndpoint R) a : ℂ) := by
  have hfold := lowPrimeCompletedPartnerMixedFold_eq_windowSurvivorCard
    p R (squareRootEndpoint R) a hp hpR ha
  rw [lowPrimeCompletedWindowSurvivorSet_eq_windowPrimeSet hR ha] at hfold
  rw [primeDilateCofactorWindowPrimeCount_eq_windowPrimeSet_card]
  exact_mod_cast hfold.symm

/-- **High-response parent/child difference = completed low-wheel mixed fold.**
Beyond the shallow `K` transition, the exact BornPostTail high response has now
been identified all the way down to the existing `window - p*window` Boolean
operator. -/
theorem squareRootBornPostTailHighResponse_sub_child_eq_completedPartnerMixedFold
    {R K j p a : ℕ} (hp : p.Prime) (hpR : p ≤ R)
    (hR : 2 ≤ R) (ha : 0 < a) (hKa : K < a) :
    ((squareRootBornPostTailHighResponse R K j a : ℕ) : ℂ) -
        ((squareRootBornPostTailHighResponse R K j (p * a) : ℕ) : ℂ) =
      (lowPrimeCompletedPartnerMixedFold
        p R (squareRootEndpoint R) a : ℂ) := by
  rw [squareRootBornPostTailHighResponse_sub_child_eq_primeDilateWindow
    hp ha hKa]
  exact primeDilateCofactorWindowPrimeCount_eq_completedPartnerMixedFold
    hp hpR hR ha

/-- At the prime root itself the completed partner coordinates are exactly the
chronological old cube; there are no future spectator primes left. -/
theorem lowPrimeCompletedPartnerCoordinates_self_eq_pred
    {R : ℕ} (hR : R.Prime) :
    lowPrimeCompletedPartnerCoordinates R R = primesUpTo (R - 1) := by
  unfold lowPrimeCompletedPartnerCoordinates
  rw [primesUpTo_eq_insert_pred_of_prime hR]
  simp [freshPrime_not_mem_primesUpTo_pred hR]

/-- Root-prime specialization: the completed mixed fold is literally the old
chronological Boolean cube from the sequential low-wheel recurrence. -/
theorem lowPrimeCompletedPartnerMixedFold_self_eq_chronological
    {R X a : ℕ} (hR : R.Prime) :
    lowPrimeCompletedPartnerMixedFold R R X a =
      ∑ t ∈ (primesUpTo (R - 1)).powerset,
        booleanCubeSign t *
          ∑ k ∈ Finset.Icc 1 X,
            lowWheelMixedPrimeCell R R X
              (primeFaceProduct t * k)
              (a * (primeFaceProduct t * k)) := by
  unfold lowPrimeCompletedPartnerMixedFold
  rw [lowPrimeCompletedPartnerCoordinates_self_eq_pred hR]

end RHLean.Proof
