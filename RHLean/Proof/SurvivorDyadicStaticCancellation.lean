import Mathlib
import RHLean.Analysis.DyadicTransportCompression
import RHLean.Proof.SurvivorZeroMode

/-!
# Static survivor dyadic cancellation

This module isolates an exact Möbius cancellation already present inside each
fixed upper-prime survivor fibre.

For one fixed `q`, write the active cofactor term as

```text
T(c,q) = -mu(c) * 1_{(c,q) survives}.
```

Every positive cofactor is either odd or twice a positive integer.  On an odd
parent `d`, Möbius doubling gives `mu(2d) = -mu(d)`.  Therefore the parent and
child contributions cancel identically whenever `(d,q)` and `(2d,q)` have the
same survivor activity.

The complete finite cofactor sum is proved to equal

```text
sum_{d odd, d <= X/2} (T(d,q) + T(2d,q))
  + sum_{d odd, X/2 < d <= X} T(d,q).
```

The first sum is supported only on parent/child activity mismatches; the second
is the explicit top dyadic product boundary.  No magnitude estimate is taken
before this signed cancellation and no analytic smallness statement is made.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

/-- Complex-valued activity indicator for one survivor source. -/
def survivorFixedPrimeActivityIndicator
    (Λ : ℝ) (t q c : ℕ) : ℂ := by
  classical
  exact if IsSurvivorZeroModePair Λ t c q then 1 else 0

/-- One signed cofactor contribution in a fixed upper-prime survivor fibre. -/
def survivorFixedPrimeCofactorTerm
    (Λ : ℝ) (t q c : ℕ) : ℂ :=
  -canonicalMoebiusWeight c * survivorFixedPrimeActivityIndicator Λ t q c

/-- Complete signed survivor mass in one fixed upper-prime fibre. -/
def survivorFixedPrimeCofactorMass
    (Λ : ℝ) (t q : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t),
    survivorFixedPrimeCofactorTerm Λ t q c

/-- Parent plus doubled-child contribution before any absolute value is taken. -/
def survivorDyadicPairContribution
    (Λ : ℝ) (t q d : ℕ) : ℂ :=
  survivorFixedPrimeCofactorTerm Λ t q d +
    survivorFixedPrimeCofactorTerm Λ t q (2 * d)

/-- On an odd parent, the doubled-child term has the opposite cofactor weight. -/
theorem survivorFixedPrimeCofactorTerm_two_mul_of_odd
    (Λ : ℝ) (t q d : ℕ) (hd : Odd d) :
    survivorFixedPrimeCofactorTerm Λ t q (2 * d) =
      canonicalMoebiusWeight d *
        survivorFixedPrimeActivityIndicator Λ t q (2 * d) := by
  unfold survivorFixedPrimeCofactorTerm
  rw [canonicalMoebiusWeight_two_mul d, if_pos hd]
  ring

/-- The parent/child signed contribution is the exact activity-indicator
difference multiplied by the parent Möbius weight.  This keeps the cancellation
visible before any norm. -/
theorem survivorDyadicPairContribution_eq_activityDifference
    (Λ : ℝ) (t q d : ℕ) (hd : Odd d) :
    survivorDyadicPairContribution Λ t q d =
      canonicalMoebiusWeight d *
        (survivorFixedPrimeActivityIndicator Λ t q (2 * d) -
          survivorFixedPrimeActivityIndicator Λ t q d) := by
  unfold survivorDyadicPairContribution survivorFixedPrimeCofactorTerm
  rw [canonicalMoebiusWeight_two_mul d, if_pos hd]
  ring

/-- Equal survivor activity gives equal complex activity indicators. -/
theorem survivorFixedPrimeActivityIndicator_eq_of_activity_iff
    (Λ : ℝ) (t q c c' : ℕ)
    (hactivity :
      IsSurvivorZeroModePair Λ t c q ↔
        IsSurvivorZeroModePair Λ t c' q) :
    survivorFixedPrimeActivityIndicator Λ t q c =
      survivorFixedPrimeActivityIndicator Λ t q c' := by
  classical
  unfold survivorFixedPrimeActivityIndicator
  by_cases hc : IsSurvivorZeroModePair Λ t c q
  · have hc' : IsSurvivorZeroModePair Λ t c' q := hactivity.mp hc
    simp [hc, hc']
  · have hc' : ¬ IsSurvivorZeroModePair Λ t c' q := by
      intro h
      exact hc (hactivity.mpr h)
    simp [hc, hc']

/-- If an odd parent and its doubled child have the same survivor activity,
their signed contribution vanishes exactly. -/
theorem survivorDyadicPairContribution_eq_zero_of_activity_iff
    (Λ : ℝ) (t q d : ℕ) (hd : Odd d)
    (hactivity :
      IsSurvivorZeroModePair Λ t d q ↔
        IsSurvivorZeroModePair Λ t (2 * d) q) :
    survivorDyadicPairContribution Λ t q d = 0 := by
  rw [survivorDyadicPairContribution_eq_activityDifference Λ t q d hd]
  rw [survivorFixedPrimeActivityIndicator_eq_of_activity_iff
    Λ t q d (2 * d) hactivity]
  ring

/-- A nonzero odd parent/child contribution certifies an actual activity
mismatch.  Thus the paired sum is supported on the defect set before norms. -/
theorem survivorDyadic_activity_ne_of_pairContribution_ne_zero
    (Λ : ℝ) (t q d : ℕ) (hd : Odd d)
    (hne : survivorDyadicPairContribution Λ t q d ≠ 0) :
    ¬ (IsSurvivorZeroModePair Λ t d q ↔
      IsSurvivorZeroModePair Λ t (2 * d) q) := by
  intro hactivity
  exact hne
    (survivorDyadicPairContribution_eq_zero_of_activity_iff
      Λ t q d hd hactivity)

/-- A doubled even parent has zero Möbius weight, hence contributes nothing. -/
theorem survivorFixedPrimeCofactorTerm_two_mul_of_even
    (Λ : ℝ) (t q d : ℕ) (hd : Even d) :
    survivorFixedPrimeCofactorTerm Λ t q (2 * d) = 0 := by
  unfold survivorFixedPrimeCofactorTerm
  have hnotOdd : ¬ Odd d := Nat.not_odd_iff_even.mpr hd
  rw [canonicalMoebiusWeight_two_mul d, if_neg hnotOdd]
  ring

private theorem survivor_sum_Icc_eq_odd_add_even
    (B : ℕ) (f : ℕ → ℂ) :
    (∑ c ∈ Finset.Icc 1 B, f c) =
      (∑ c ∈ oddCofactorPrefix B, f c) +
        ∑ c ∈ evenCofactorPrefix B, f c := by
  calc
    (∑ c ∈ Finset.Icc 1 B, f c) =
        ∑ c ∈ Finset.Icc 1 B,
          ((if Odd c then f c else 0) +
            (if Even c then f c else 0)) := by
      apply Finset.sum_congr rfl
      intro c _hc
      by_cases hodd : Odd c
      · have hnotEven : ¬ Even c := Nat.not_even_iff_odd.mpr hodd
        simp [hodd, hnotEven]
      · have heven : Even c := Nat.not_odd_iff_even.mp hodd
        simp [hodd, heven]
    _ =
        (∑ c ∈ oddCofactorPrefix B, f c) +
          ∑ c ∈ evenCofactorPrefix B, f c := by
      rw [Finset.sum_add_distrib]
      unfold oddCofactorPrefix evenCofactorPrefix
      rw [Finset.sum_filter, Finset.sum_filter]

private theorem survivor_sum_evenCofactorPrefix_eq_sum_double
    (B : ℕ) (f : ℕ → ℂ) :
    (∑ c ∈ evenCofactorPrefix B, f c) =
      ∑ d ∈ Finset.Icc 1 (B / 2), f (2 * d) := by
  classical
  symm
  refine Finset.sum_bij (fun d _ => 2 * d) ?_ ?_ ?_ ?_
  · intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hd1, hdB⟩
    have h2dB : 2 * d ≤ B := by
      have hmul := (Nat.le_div_iff_mul_le (by omega : 0 < 2)).1 hdB
      simpa [Nat.mul_comm] using hmul
    have hpos : 1 ≤ 2 * d := by omega
    exact mem_evenCofactorPrefix.mpr
      ⟨hpos, h2dB, even_two_mul d⟩
  · intro d1 _hd1 d2 _hd2 h
    change 2 * d1 = 2 * d2 at h
    omega
  · intro c hc
    rcases mem_evenCofactorPrefix.mp hc with ⟨hc1, hcB, hceven⟩
    have hdouble : 2 * (c / 2) = c := Nat.two_mul_div_two_of_even hceven
    refine ⟨c / 2, ?_, hdouble⟩
    apply Finset.mem_Icc.mpr
    constructor
    · have hcne : c ≠ 0 := by omega
      have hcgt : 1 < c := Nat.one_lt_of_ne_zero_of_even hcne hceven
      omega
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
      have hmul : c / 2 * 2 = c := by
        simpa [Nat.mul_comm] using hdouble
      rw [hmul]
      exact hcB
  · intro d _hd
    rfl

private theorem survivor_sum_double_eq_odd_half
    (Λ : ℝ) (t q B : ℕ) :
    (∑ d ∈ Finset.Icc 1 (B / 2),
      survivorFixedPrimeCofactorTerm Λ t q (2 * d)) =
      ∑ d ∈ oddCofactorPrefix (B / 2),
        survivorFixedPrimeCofactorTerm Λ t q (2 * d) := by
  calc
    (∑ d ∈ Finset.Icc 1 (B / 2),
        survivorFixedPrimeCofactorTerm Λ t q (2 * d)) =
      ∑ d ∈ Finset.Icc 1 (B / 2),
        if Odd d then survivorFixedPrimeCofactorTerm Λ t q (2 * d) else 0 := by
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hodd : Odd d
      · simp [hodd]
      · have heven : Even d := Nat.not_odd_iff_even.mp hodd
        simp [hodd, survivorFixedPrimeCofactorTerm_two_mul_of_even Λ t q d heven]
    _ = ∑ d ∈ oddCofactorPrefix (B / 2),
        survivorFixedPrimeCofactorTerm Λ t q (2 * d) := by
      unfold oddCofactorPrefix
      rw [Finset.sum_filter]

/-- Exact static dyadic compression in every fixed upper-prime fibre.

All parent/child pairs at half scale remain inside one signed sum.  The only
unpaired odd parents are the explicit top dyadic boundary `B/2 < d <= B`. -/
theorem survivorFixedPrimeCofactorMass_eq_dyadicPairs_add_boundary
    (Λ : ℝ) (t q : ℕ) :
    survivorFixedPrimeCofactorMass Λ t q =
      (∑ d ∈ oddCofactorPrefix
          (RHLean.Analysis.squarePrefixEndpoint t / 2),
        survivorDyadicPairContribution Λ t q d) +
      ∑ d ∈ dyadicCofactorBoundary
          (RHLean.Analysis.squarePrefixEndpoint t),
        survivorFixedPrimeCofactorTerm Λ t q d := by
  let B := RHLean.Analysis.squarePrefixEndpoint t
  have hsubset := oddCofactorPrefix_half_subset B
  have hoddSplit :
      (∑ d ∈ oddCofactorPrefix B, survivorFixedPrimeCofactorTerm Λ t q d) =
        (∑ d ∈ dyadicCofactorBoundary B,
          survivorFixedPrimeCofactorTerm Λ t q d) +
        ∑ d ∈ oddCofactorPrefix (B / 2),
          survivorFixedPrimeCofactorTerm Λ t q d := by
    unfold dyadicCofactorBoundary
    exact (Finset.sum_sdiff hsubset).symm
  unfold survivorFixedPrimeCofactorMass
  change
    (∑ c ∈ Finset.Icc 1 B, survivorFixedPrimeCofactorTerm Λ t q c) = _
  rw [survivor_sum_Icc_eq_odd_add_even B
    (fun c => survivorFixedPrimeCofactorTerm Λ t q c)]
  rw [survivor_sum_evenCofactorPrefix_eq_sum_double B
    (fun c => survivorFixedPrimeCofactorTerm Λ t q c)]
  rw [survivor_sum_double_eq_odd_half Λ t q B]
  rw [hoddSplit]
  unfold survivorDyadicPairContribution
  rw [Finset.sum_add_distrib]
  ring

end RHLean.Proof
