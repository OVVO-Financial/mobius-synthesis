import Mathlib
import RHLean.Proof.SurvivorDyadicStaticCancellation

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

open CanonicalGapAncestryBridge

/-!
# Exact dyadic activity-mismatch shells

The static dyadic cancellation reduces a fixed upper-prime survivor fibre to
odd parent/child activity mismatches plus an explicit top boundary.  This file
shows that, for an odd parent and an upper prime above `2`, the mismatch cannot
come from canonical factorization data.

Indeed, adjoining the prime `2` to an odd squarefree canonical cofactor preserves
canonical source admissibility exactly.  Therefore the pair `(d,q)`, `(2*d,q)`
can disagree only because one of the two geometric survivor inequalities changes
truth value:

* the product cutoff `c*q <= X_t`;
* the high-height cutoff `2*Lambda*t < |q^2-c^2|`.

The only upper-prime fibre not covered by this dyadic source invariance is
`q = 2`.  Canonical source data then forces the cofactor to be exactly `1`, so
the global exceptional sector is a single canonical source rather than an
uncontrolled residue family.

This is an exact support classification, not an estimate.
-/

/-- For an odd cofactor and `q > 2`, canonical source admissibility is unchanged
by adjoining the prime coordinate `2`. -/
theorem canonicalSourceData_two_mul_iff_of_odd
    {q d : ℕ} (hd : Odd d) (hqgt : 2 < q) :
    CanonicalSourceData q (2 * d) ↔ CanonicalSourceData q d := by
  constructor
  · rintro ⟨hqPrime, h2d1, hsq2, hcop2d, hdom2⟩
    have hd1 : 1 ≤ d := by
      by_contra h
      have hd0 : d = 0 := by omega
      simp [hd0] at h2d1
    have hdDvd : d ∣ 2 * d := ⟨2, by simp [Nat.mul_comm]⟩
    refine ⟨hqPrime, hd1, hsq2.squarefree_of_dvd hdDvd,
      hcop2d.coprime_dvd_right hdDvd, ?_⟩
    intro p hp hpd
    exact hdom2 p hp (hpd.trans hdDvd)
  · rintro hdata
    rcases hdata with ⟨hqPrime, hd1, hsq, hcop, hdom⟩
    have h2copd : Nat.Coprime 2 d := hd.coprime_two_left
    have hsq2 : Squarefree (2 * d) :=
      (Nat.squarefree_mul h2copd).2 ⟨Nat.squarefree_two, hsq⟩
    have hqne2 : q ≠ 2 := by omega
    have hqcop2 : Nat.Coprime q 2 :=
      (Nat.coprime_primes hqPrime Nat.prime_two).2 hqne2
    have hqcop2d : Nat.Coprime q (2 * d) :=
      Nat.Coprime.mul_right hqcop2 hcop
    refine ⟨hqPrime, by omega, hsq2, hqcop2d, ?_⟩
    intro p hp hpd
    rcases hp.dvd_mul.mp hpd with hp2 | hpd
    · have hpEq : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
      omega
    · exact hdom p hp hpd

/-- The exceptional distinguished-prime fibre `q = 2` has only the unit
cofactor.  No nontrivial canonical cofactor can have every prime divisor below
`2`. -/
theorem canonicalSourceData_two_iff_one (c : ℕ) :
    CanonicalSourceData 2 c ↔ c = 1 := by
  constructor
  · rintro ⟨_hprime, hc1, _hsq, _hcop, hdom⟩
    by_contra hcne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcne
    have hplt : p < 2 := hdom p hp hpd
    exact (not_lt_of_ge hp.two_le) hplt
  · rintro rfl
    refine ⟨Nat.prime_two, by norm_num, by simp, by simp, ?_⟩
    intro p hp hpd
    have hp1 : p = 1 := Nat.dvd_one.mp hpd
    subst p
    norm_num at hp

/-- Consequently any actual survivor source with distinguished prime `2` has
cofactor exactly `1`. -/
theorem cofactor_eq_one_of_survivorPair_prime_two
    {Λ : ℝ} {t c : ℕ}
    (hpair : IsSurvivorZeroModePair Λ t c 2) :
    c = 1 :=
  (canonicalSourceData_two_iff_one c).mp hpair.1

/-- The geometric part of the survivor predicate for a cofactor `c`. -/
def SurvivorDyadicGeometry (Λ : ℝ) (t q c : ℕ) : Prop :=
  c * q ≤ RHLean.Analysis.squarePrefixEndpoint t ∧
    2 * Λ * (t : ℝ) < |(q : ℝ) ^ 2 - (c : ℝ) ^ 2|

/-- Once canonical source data is fixed, survivor activity is exactly the two
geometric cutoffs. -/
theorem isSurvivorZeroModePair_iff_dyadicGeometry
    {Λ : ℝ} {t q c : ℕ} (hdata : CanonicalSourceData q c) :
    IsSurvivorZeroModePair Λ t c q ↔ SurvivorDyadicGeometry Λ t q c := by
  unfold IsSurvivorZeroModePair SurvivorDyadicGeometry
  simp [hdata]

/-- For an odd parent and `q > 2`, the parent and doubled child have equal
survivor activity exactly when their two geometric predicates agree. -/
theorem survivorDyadic_activity_iff_geometry_iff
    {Λ : ℝ} {t q d : ℕ}
    (hd : Odd d) (hqgt : 2 < q)
    (hdata : CanonicalSourceData q d) :
    (IsSurvivorZeroModePair Λ t d q ↔
      IsSurvivorZeroModePair Λ t (2 * d) q) ↔
      (SurvivorDyadicGeometry Λ t q d ↔
        SurvivorDyadicGeometry Λ t q (2 * d)) := by
  have hdata2 : CanonicalSourceData q (2 * d) :=
    (canonicalSourceData_two_mul_iff_of_odd hd hqgt).2 hdata
  rw [isSurvivorZeroModePair_iff_dyadicGeometry hdata,
    isSurvivorZeroModePair_iff_dyadicGeometry hdata2]

/-- **Exact mismatch-shell classification.**  Under canonical source data, a
dyadic activity mismatch is precisely an exclusive geometric crossing: either
the parent satisfies the product-and-height conditions and the child does not,
or conversely. -/
theorem survivorDyadic_activity_mismatch_iff_geometry_crossing
    {Λ : ℝ} {t q d : ℕ}
    (hd : Odd d) (hqgt : 2 < q)
    (hdata : CanonicalSourceData q d) :
    ¬ (IsSurvivorZeroModePair Λ t d q ↔
      IsSurvivorZeroModePair Λ t (2 * d) q) ↔
      ((SurvivorDyadicGeometry Λ t q d ∧
          ¬ SurvivorDyadicGeometry Λ t q (2 * d)) ∨
        (SurvivorDyadicGeometry Λ t q (2 * d) ∧
          ¬ SurvivorDyadicGeometry Λ t q d)) := by
  rw [survivorDyadic_activity_iff_geometry_iff hd hqgt hdata]
  tauto

/-- The doubled child's product condition always implies the parent's product
condition. -/
theorem survivorDyadic_child_product_implies_parent
    {t q d : ℕ}
    (hchild : (2 * d) * q ≤ RHLean.Analysis.squarePrefixEndpoint t) :
    d * q ≤ RHLean.Analysis.squarePrefixEndpoint t := by
  have hdle : d ≤ 2 * d := by omega
  exact (Nat.mul_le_mul_right q hdle).trans hchild

/-- **Three geometric shells.**  Because the child product cutoff is stronger,
all dyadic activity mismatch is carried by exactly three types of boundary:

1. the parent is active but doubling crosses the product cutoff;
2. both products fit, the parent is high, but doubling crosses into the height band;
3. the child is active, while the parent lies inside the height band.

No fourth shell is possible: child product admissibility already forces parent
product admissibility. -/
theorem survivorDyadic_activity_mismatch_iff_three_geometric_shells
    {Λ : ℝ} {t q d : ℕ}
    (hd : Odd d) (hqgt : 2 < q)
    (hdata : CanonicalSourceData q d) :
    ¬ (IsSurvivorZeroModePair Λ t d q ↔
      IsSurvivorZeroModePair Λ t (2 * d) q) ↔
      ((SurvivorDyadicGeometry Λ t q d ∧
          ¬ ((2 * d) * q ≤ RHLean.Analysis.squarePrefixEndpoint t)) ∨
        (SurvivorDyadicGeometry Λ t q d ∧
          (2 * d) * q ≤ RHLean.Analysis.squarePrefixEndpoint t ∧
          ¬ (2 * Λ * (t : ℝ) <
            |(q : ℝ) ^ 2 - ((2 * d : ℕ) : ℝ) ^ 2|)) ∨
        (SurvivorDyadicGeometry Λ t q (2 * d) ∧
          ¬ (2 * Λ * (t : ℝ) <
            |(q : ℝ) ^ 2 - (d : ℝ) ^ 2|))) := by
  rw [survivorDyadic_activity_mismatch_iff_geometry_crossing
    hd hqgt hdata]
  have hprod :
      (2 * d) * q ≤ RHLean.Analysis.squarePrefixEndpoint t →
        d * q ≤ RHLean.Analysis.squarePrefixEndpoint t :=
    survivorDyadic_child_product_implies_parent
  unfold SurvivorDyadicGeometry
  tauto

/-- Hence every nonzero odd dyadic pair contribution is supported on one of the
two explicit geometric crossing shells. -/
theorem survivorDyadic_geometry_crossing_of_pairContribution_ne_zero
    {Λ : ℝ} {t q d : ℕ}
    (hd : Odd d) (hqgt : 2 < q)
    (hdata : CanonicalSourceData q d)
    (hne : survivorDyadicPairContribution Λ t q d ≠ 0) :
    (SurvivorDyadicGeometry Λ t q d ∧
        ¬ SurvivorDyadicGeometry Λ t q (2 * d)) ∨
      (SurvivorDyadicGeometry Λ t q (2 * d) ∧
        ¬ SurvivorDyadicGeometry Λ t q d) := by
  have hmismatch :=
    survivorDyadic_activity_ne_of_pairContribution_ne_zero Λ t q d hd hne
  exact (survivorDyadic_activity_mismatch_iff_geometry_crossing
    hd hqgt hdata).1 hmismatch

/-- Nonzero dyadic pair mass therefore lies in one of the three explicit
geometric shells above. -/
theorem survivorDyadic_three_geometric_shells_of_pairContribution_ne_zero
    {Λ : ℝ} {t q d : ℕ}
    (hd : Odd d) (hqgt : 2 < q)
    (hdata : CanonicalSourceData q d)
    (hne : survivorDyadicPairContribution Λ t q d ≠ 0) :
    (SurvivorDyadicGeometry Λ t q d ∧
        ¬ ((2 * d) * q ≤ RHLean.Analysis.squarePrefixEndpoint t)) ∨
      (SurvivorDyadicGeometry Λ t q d ∧
        (2 * d) * q ≤ RHLean.Analysis.squarePrefixEndpoint t ∧
        ¬ (2 * Λ * (t : ℝ) <
          |(q : ℝ) ^ 2 - ((2 * d : ℕ) : ℝ) ^ 2|)) ∨
      (SurvivorDyadicGeometry Λ t q (2 * d) ∧
        ¬ (2 * Λ * (t : ℝ) <
          |(q : ℝ) ^ 2 - (d : ℝ) ^ 2|)) := by
  have hmismatch :=
    survivorDyadic_activity_ne_of_pairContribution_ne_zero Λ t q d hd hne
  exact (survivorDyadic_activity_mismatch_iff_three_geometric_shells
    hd hqgt hdata).1 hmismatch

end RHLean.Proof
