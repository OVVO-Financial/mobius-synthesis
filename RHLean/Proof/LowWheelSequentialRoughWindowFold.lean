import Mathlib
import RHLean.Proof.LowWheelDoubleCubeWindowFold

/-!
# Cumulative rough-window form of the sequential low-wheel fold

After a fresh prime `p` is added, `LowWheelDoubleCubeWindowFold` has already
summed the residual multiplier and removed its `p`-divisible part.  The second
old Boolean coordinate `t ⊆ primesUpTo (p-1)` is then exactly ordinary
inclusion-exclusion for divisibility by the previously processed primes.

Collapsing that cube leaves one signed old cofactor face `u` and a finite count
of integers in the reciprocal `p`-window which survive *every* prime coordinate
through `p`.

Thus the state after the `p` step is

`sum_u (-1)^|u| * #(p-rough integers in W_p(P(u)))`.

This is the cumulative sequential filtration: the effect of all earlier primes
has been retained in the survivor predicate, while the new prime simultaneously
creates the reciprocal window and removes its own divisible population.

No norm, density estimate, or asymptotic input appears.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- A fresh prime does not divide the product of a face formed only from primes
processed before it. -/
theorem freshPrime_not_dvd_pred_primeFaceProduct
    {p : ℕ} (hp : p.Prime) {t : Finset ℕ}
    (ht : t ∈ (primesUpTo (p - 1)).powerset) :
    ¬ p ∣ primeFaceProduct t := by
  intro hdiv
  have htSub := Finset.mem_powerset.mp ht
  have hdiv' : p ∣ t.prod id := by
    simpa [primeFaceProduct] using hdiv
  rcases (Prime.dvd_finset_prod_iff hp.prime id).mp hdiv' with
    ⟨r, hrt, hpr⟩
  have hrData := mem_primesUpTo.mp (htSub hrt)
  have hprEq : p = r :=
    (Nat.prime_dvd_prime_iff_eq hp hrData.1).mp hpr
  have hle : p ≤ p - 1 := by simpa [hprEq] using hrData.2
  have hlt : p - 1 < p := Nat.sub_lt hp.pos (by norm_num)
  exact (Nat.not_lt_of_ge hle) hlt

/-- Divisor realization of one old face inside a fresh-prime reciprocal window,
with the new prime excluded. -/
def lowWheelPrimeWindowFaceDivisorSet
    (p R X a : ℕ) (t : Finset ℕ) : Finset ℕ :=
  (primeDilateCofactorWindow p R X a).filter fun q =>
    ¬ p ∣ q ∧ primeFaceProduct t ∣ q

/-- The `p`-free multiplier realization and the divisor realization of one old
face have the same cardinality. -/
theorem card_lowWheelPrimeWindowFreeMultiplier_eq_faceDivisor
    {p R X a : ℕ} (hp : p.Prime) (ha : 0 < a)
    {t : Finset ℕ} (ht : t ∈ (primesUpTo (p - 1)).powerset) :
    (lowWheelPrimeWindowFreeMultiplierSet
      p R X a (primeFaceProduct t)).card =
      (lowWheelPrimeWindowFaceDivisorSet p R X a t).card := by
  classical
  have htPos : 0 < primeFaceProduct t :=
    primeFaceProduct_pos_of_mem_powerset ht
  have hpNot : ¬ p ∣ primeFaceProduct t :=
    freshPrime_not_dvd_pred_primeFaceProduct hp ht
  refine Finset.card_bij (fun k _hk => primeFaceProduct t * k) ?_ ?_ ?_
  · intro k hk
    rcases mem_lowWheelPrimeWindowFreeMultiplierSet.mp hk with
      ⟨hkWindow, hpk⟩
    rcases mem_lowWheelPrimeWindowMultiplierSet.mp hkWindow with
      ⟨_hk1, _hkX, hwindow⟩
    unfold lowWheelPrimeWindowFaceDivisorSet
    apply Finset.mem_filter.mpr
    refine ⟨hwindow, ?_, dvd_mul_right (primeFaceProduct t) k⟩
    intro hpq
    rcases hp.dvd_mul.mp hpq with hpface | hpk'
    · exact hpNot hpface
    · exact hpk hpk'
  · intro k1 _hk1 k2 _hk2 hmul
    exact Nat.eq_of_mul_eq_mul_left htPos hmul
  · intro q hq
    unfold lowWheelPrimeWindowFaceDivisorSet at hq
    rcases Finset.mem_filter.mp hq with ⟨hwindow, hpq, hdiv⟩
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

/-- Survivor population in one reciprocal window after all prime coordinates
through `p` have been processed. -/
def lowWheelPrimeWindowSurvivorSet
    (p R X a : ℕ) : Finset ℕ :=
  (primeDilateCofactorWindow p R X a).filter (lowWheelHighSurvivor p)

/-- Adding the prime coordinate `p` extends the survivor predicate from the old
prefix exactly by the new condition `p ∤ q`. -/
theorem lowWheelHighSurvivor_prime_iff_pred_and_not_dvd
    {p q : ℕ} (hp : p.Prime) :
    lowWheelHighSurvivor p q ↔
      lowWheelHighSurvivor (p - 1) q ∧ ¬ p ∣ q := by
  unfold lowWheelHighSurvivor
  rw [primesUpTo_eq_insert_pred_of_prime hp]
  constructor
  · intro h
    constructor
    · intro r hr
      exact h r (Finset.mem_insert_of_mem hr)
    · exact h p (Finset.mem_insert_self p (primesUpTo (p - 1)))
  · rintro ⟨hold, hpfree⟩ r hr
    rw [Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · exact hpfree
    · exact hold r hr

/-- Pointwise alternating mass of old face divisors, restricted to numbers free
of the newly added prime. -/
theorem lowWheelPredFaceDivisorSum_eq_survivorIndicator
    {p q : ℕ} (hp : p.Prime) :
    (∑ t ∈ (primesUpTo (p - 1)).powerset,
        if ¬ p ∣ q ∧ primeFaceProduct t ∣ q then
          booleanCubeSign t
        else 0) =
      if lowWheelHighSurvivor p q then (1 : ℤ) else 0 := by
  by_cases hpq : p ∣ q
  · have hsurv : ¬ lowWheelHighSurvivor p q := by
      intro h
      have hstep := (lowWheelHighSurvivor_prime_iff_pred_and_not_dvd hp).mp h
      exact hstep.2 hpq
    simp [hpq, hsurv]
  · have hstep := lowWheelHighSurvivor_prime_iff_pred_and_not_dvd
      (p := p) (q := q) hp
    have hiff : lowWheelHighSurvivor p q ↔ lowWheelHighSurvivor (p - 1) q := by
      simpa [hpq] using hstep
    calc
      (∑ t ∈ (primesUpTo (p - 1)).powerset,
          if ¬ p ∣ q ∧ primeFaceProduct t ∣ q then
            booleanCubeSign t
          else 0) = lowWheelDivisorFaceSum (p - 1) q := by
            unfold lowWheelDivisorFaceSum
            apply Finset.sum_congr rfl
            intro t _ht
            simp [hpq]
      _ = if lowWheelHighSurvivor (p - 1) q then 1 else 0 :=
        lowWheelDivisorFaceSum_eq_survivorIndicator (p - 1) q
      _ = if lowWheelHighSurvivor p q then 1 else 0 := by
        by_cases hold : lowWheelHighSurvivor (p - 1) q <;>
          simp [hold, hiff]

/-- **Collapse the old sieve cube.**  The signed sum of old-face divisor
populations in one reciprocal window is exactly the number of integers in that
window surviving every prime coordinate through `p`. -/
theorem sum_predFaceDivisorCounts_eq_windowSurvivorCard
    (p R X a : ℕ) (hp : p.Prime) :
    (∑ t ∈ (primesUpTo (p - 1)).powerset,
        booleanCubeSign t *
          ((lowWheelPrimeWindowFaceDivisorSet p R X a t).card : ℤ)) =
      ((lowWheelPrimeWindowSurvivorSet p R X a).card : ℤ) := by
  classical
  unfold lowWheelPrimeWindowFaceDivisorSet lowWheelPrimeWindowSurvivorSet
  calc
    (∑ t ∈ (primesUpTo (p - 1)).powerset,
        booleanCubeSign t *
          (((primeDilateCofactorWindow p R X a).filter fun q =>
            ¬ p ∣ q ∧ primeFaceProduct t ∣ q).card : ℤ)) =
      ∑ t ∈ (primesUpTo (p - 1)).powerset,
        ∑ q ∈ primeDilateCofactorWindow p R X a,
          if ¬ p ∣ q ∧ primeFaceProduct t ∣ q then
            booleanCubeSign t
          else 0 := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [← Finset.sum_filter]
      simp [mul_comm]
    _ = ∑ q ∈ primeDilateCofactorWindow p R X a,
        ∑ t ∈ (primesUpTo (p - 1)).powerset,
          if ¬ p ∣ q ∧ primeFaceProduct t ∣ q then
            booleanCubeSign t
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ primeDilateCofactorWindow p R X a,
        if lowWheelHighSurvivor p q then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro q _hq
      exact lowWheelPredFaceDivisorSum_eq_survivorIndicator hp
    _ = (((primeDilateCofactorWindow p R X a).filter
          (lowWheelHighSurvivor p)).card : ℤ) := by
      rw [← Finset.sum_filter]
      simp

/-- The signed old `t`-cube of `p`-free multiplier cardinalities is therefore
exactly one cumulative `p`-survivor window count. -/
theorem sum_predFaceFreeWindowCards_eq_windowSurvivorCard
    (p R X a : ℕ) (hp : p.Prime) (ha : 0 < a) :
    (∑ t ∈ (primesUpTo (p - 1)).powerset,
        booleanCubeSign t *
          ((lowWheelPrimeWindowFreeMultiplierSet
            p R X a (primeFaceProduct t)).card : ℤ)) =
      ((lowWheelPrimeWindowSurvivorSet p R X a).card : ℤ) := by
  calc
    (∑ t ∈ (primesUpTo (p - 1)).powerset,
        booleanCubeSign t *
          ((lowWheelPrimeWindowFreeMultiplierSet
            p R X a (primeFaceProduct t)).card : ℤ)) =
      ∑ t ∈ (primesUpTo (p - 1)).powerset,
        booleanCubeSign t *
          ((lowWheelPrimeWindowFaceDivisorSet p R X a t).card : ℤ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [card_lowWheelPrimeWindowFreeMultiplier_eq_faceDivisor hp ha ht]
    _ = ((lowWheelPrimeWindowSurvivorSet p R X a).card : ℤ) :=
      sum_predFaceDivisorCounts_eq_windowSurvivorCard p R X a hp

/-- **Cumulative sequential rough-window fold.**  After prime `p` is processed,
the full double-cube state has collapsed to one old signed cofactor cube.  Its
coefficient is exactly the count of integers in the geometric reciprocal window
which survive every prime coordinate through `p`. -/
theorem lowWheelDoubleCubePrimePrefix_step_eq_survivorWindowCards
    (R p : ℕ) (hp : p.Prime) :
    lowWheelDoubleCubeSetTransportLedger R (primesUpTo p) =
      ∑ u ∈ (primesUpTo (p - 1)).powerset,
        (booleanCubeSign u : ℂ) *
          ((lowWheelPrimeWindowSurvivorSet
            p R (squareRootEndpoint R) (primeFaceProduct u)).card : ℂ) := by
  rw [lowWheelDoubleCubePrimePrefix_step_eq_freeWindowCards R p hp]
  apply Finset.sum_congr rfl
  intro u hu
  have huPos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset hu
  have hcollapse := sum_predFaceFreeWindowCards_eq_windowSurvivorCard
    p R (squareRootEndpoint R) (primeFaceProduct u) hp huPos
  have hcollapseC :
      (∑ t ∈ (primesUpTo (p - 1)).powerset,
          (booleanCubeSign t : ℂ) *
            ((lowWheelPrimeWindowFreeMultiplierSet
              p R (squareRootEndpoint R) (primeFaceProduct u)
              (primeFaceProduct t)).card : ℂ)) =
        ((lowWheelPrimeWindowSurvivorSet
          p R (squareRootEndpoint R) (primeFaceProduct u)).card : ℂ) := by
    exact_mod_cast hcollapse
  rw [← hcollapseC, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  ring

end RHLean.Proof
