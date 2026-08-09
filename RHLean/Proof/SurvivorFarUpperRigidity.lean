import Mathlib
import RHLean.Analysis.DyadicTransportCanonicalForm
import RHLean.Proof.SurvivorLargePrimeRootBoundary
import RHLean.Proof.SurvivorPrimeFaceRealization

/-!
# Far-upper survivor rigidity

This module isolates the exact obstruction left after prime-face cancellation in
the large-prime survivor sector for the repository's concrete cutoff
`Lambda = 16`.

Write `R = t + 1` and `X_t = R^2 - 1`.  The existing root-boundary theorem
shows that for `t >= 55` and `q >= t + 9 = R + 8`, the survivor height condition
is automatic whenever `c*q <= X_t`.  In this range the complete fixed-`q`
survivor fibre is therefore exactly the negative lower-scale Mertens prefix

```text
-M(floor(X_t / q)).
```

The dyadic parent/child toggle consequently rewrites this same value as the odd
first-failure boundary; it does not make the fixed-`q` fibre smaller.  Summing
over the far-upper primes gives an exact reciprocal Mertens transform.  No
magnitude estimate or RH-scale cancellation hypothesis is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open CanonicalGapAncestryBridge

/-- A positive squarefree cofactor strictly below a prime gives admissible
canonical source data with that prime as the distinguished coordinate. -/
private theorem canonicalSourceData_of_squarefree_lt_prime
    {c q : ℕ} (hq : q.Prime) (hc1 : 1 ≤ c)
    (hsq : Squarefree c) (hcq : c < q) :
    CanonicalSourceData q c := by
  have hcpos : 0 < c := by omega
  have hcop : Nat.Coprime q c :=
    Nat.coprime_of_lt_prime (Nat.ne_of_gt hcpos) hcq hq
  refine ⟨hq, hc1, hsq, hcop, ?_⟩
  intro p hp hpc
  have hp_le_c : p ≤ c := Nat.le_of_dvd hcpos hpc
  exact lt_of_le_of_lt hp_le_c hcq

/-- Inside the square-root cofactor range, a far-upper prime survivor term is
exactly the raw product-cutoff term.  Nonsquarefree cofactors cause no mismatch:
the survivor predicate rejects them while their Möbius weight is already zero. -/
theorem survivorFixedPrimeCofactorTerm_sixteen_eq_productTerm_of_far_largePrime
    (t c q : ℕ) (ht : 55 ≤ t) (hqFar : t + 9 ≤ q)
    (hqPrime : q.Prime) (hc : c ∈ Finset.Ico 1 (t + 1)) :
    survivorFixedPrimeCofactorTerm 16 t q c =
      if c * q ≤ RHLean.Analysis.squarePrefixEndpoint t then
        -canonicalMoebiusWeight c
      else 0 := by
  rcases Finset.mem_Ico.mp hc with ⟨hc1, hcR⟩
  by_cases hprod : c * q ≤ RHLean.Analysis.squarePrefixEndpoint t
  · by_cases hmu : μ c = 0
    · simp [survivorFixedPrimeCofactorTerm,
        survivorFixedPrimeActivityIndicator, canonicalMoebiusWeight,
        hmu, hprod]
    · have hsq : Squarefree c :=
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
      have hRq : t + 1 < q := by omega
      have hcq : c < q := lt_trans hcR hRq
      have hsource : CanonicalSourceData q c :=
        canonicalSourceData_of_squarefree_lt_prime hqPrime hc1 hsq hcq
      have hpair : IsSurvivorZeroModePair 16 t c q :=
        (isSurvivorZeroModePair_sixteen_iff_source_and_product_of_far_largePrime
          t c q ht hqFar).2 ⟨hsource, hprod⟩
      simp [survivorFixedPrimeCofactorTerm,
        survivorFixedPrimeActivityIndicator, hpair, hprod]
  · have hnotPair : ¬ IsSurvivorZeroModePair 16 t c q := by
      intro hpair
      exact hprod hpair.2.1
    simp [survivorFixedPrimeCofactorTerm,
      survivorFixedPrimeActivityIndicator, hnotPair, hprod]

/-- Cofactors at or above the square root cannot survive in a far-upper prime
fibre.  This is the support reduction needed to compare the survivor sum with
the existing prime-dilation fibre. -/
private theorem survivorFixedPrimeCofactorTerm_sixteen_eq_zero_of_root_le
    (t c q : ℕ) (ht : 55 ≤ t) (hqFar : t + 9 ≤ q)
    (hcRoot : t + 1 ≤ c) :
    survivorFixedPrimeCofactorTerm 16 t q c = 0 := by
  have hnotPair : ¬ IsSurvivorZeroModePair 16 t c q := by
    intro hpair
    have hcle : c ≤ t - 7 :=
      survivor_largePrime_cofactor_le_t_sub_seven
        t c q ht hqFar hpair.2.1
    omega
  simp [survivorFixedPrimeCofactorTerm,
    survivorFixedPrimeActivityIndicator, hnotPair]

/-- **Fixed-prime far-upper rigidity.**  Away from the bounded root strip, the
complete `Lambda = 16` survivor fibre is exactly the negative raw lower-cofactor
prime-dilation fibre. -/
theorem survivorFixedPrimeCofactorMass_sixteen_eq_neg_primeDilatedLowCofactorMass
    (t q : ℕ) (ht : 55 ≤ t) (hqPrime : q.Prime)
    (hqFar : t + 9 ≤ q) :
    survivorFixedPrimeCofactorMass 16 t q =
      -primeDilatedLowCofactorMass (t + 1) q := by
  classical
  unfold survivorFixedPrimeCofactorMass
  have hXt : t ≤ RHLean.Analysis.squarePrefixEndpoint t := by
    have hsq : t + 1 ≤ (t + 1) ^ 2 := by
      nlinarith [Nat.zero_le t]
    have hend := RHLean.Analysis.squarePrefixEndpoint_add_one t
    omega
  have hsubset :
      Finset.Ico 1 (t + 1) ⊆
        Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t) := by
    intro c hc
    rcases Finset.mem_Ico.mp hc with ⟨hc1, hcR⟩
    have hct : c ≤ t := by omega
    exact Finset.mem_Icc.mpr ⟨hc1, hct.trans hXt⟩
  have hrestrict :
      (∑ c ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t),
          survivorFixedPrimeCofactorTerm 16 t q c) =
        ∑ c ∈ Finset.Ico 1 (t + 1),
          survivorFixedPrimeCofactorTerm 16 t q c := by
    symm
    apply Finset.sum_subset hsubset
    intro c hcBig hcNotSmall
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcBig).1
    have hcRoot : t + 1 ≤ c := by
      by_contra hnot
      have hcLt : c < t + 1 := Nat.lt_of_not_ge hnot
      exact hcNotSmall (Finset.mem_Ico.mpr ⟨hc1, hcLt⟩)
    exact survivorFixedPrimeCofactorTerm_sixteen_eq_zero_of_root_le
      t c q ht hqFar hcRoot
  rw [hrestrict]
  unfold primeDilatedLowCofactorMass
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rw [survivorFixedPrimeCofactorTerm_sixteen_eq_productTerm_of_far_largePrime
    t c q ht hqFar hqPrime hc]
  change
    (if c * q ≤ RHLean.Analysis.squarePrefixEndpoint t then
        -canonicalMoebiusWeight c
      else 0) =
      -(if c * q ≤ RHLean.Analysis.squarePrefixEndpoint t then
          canonicalMoebiusWeight c
        else 0)
  by_cases hprod : c * q ≤ RHLean.Analysis.squarePrefixEndpoint t <;>
    simp [hprod]

/-- The same rigidity statement in its canonical lower-scale Mertens form. -/
theorem survivorFixedPrimeCofactorMass_sixteen_eq_neg_mertensSummatory
    (t q : ℕ) (ht : 55 ≤ t) (hqPrime : q.Prime)
    (hqFar : t + 9 ≤ q) :
    survivorFixedPrimeCofactorMass 16 t q =
      -RHLean.Analysis.mertensSummatory
        (RHLean.Analysis.squarePrefixEndpoint t / q) := by
  have hR : 0 < t + 1 := by omega
  have hRq : t + 1 < q := by omega
  calc
    survivorFixedPrimeCofactorMass 16 t q =
        -primeDilatedLowCofactorMass (t + 1) q :=
      survivorFixedPrimeCofactorMass_sixteen_eq_neg_primeDilatedLowCofactorMass
        t q ht hqPrime hqFar
    _ = -cofactorMobiusPrefixMass (squareRootEndpoint (t + 1) / q) := by
      rw [primeDilatedLowCofactorMass_eq_cofactorMobiusPrefixMass
        (t + 1) q hR hRq hqPrime.pos]
    _ = -RHLean.Analysis.mertensSummatory
        (squareRootEndpoint (t + 1) / q) := by
      rw [cofactorMobiusPrefixMass_eq_mertensSummatory]
    _ = -RHLean.Analysis.mertensSummatory
        (RHLean.Analysis.squarePrefixEndpoint t / q) := by
      rfl

/-- Prime-face doubling changes only the representation of a far-upper fixed
prime fibre: the same survivor mass is the negative odd dyadic first-failure
boundary. -/
theorem survivorFixedPrimeCofactorMass_sixteen_eq_neg_dyadicPrimeFiberBoundaryMass
    (t q : ℕ) (ht : 55 ≤ t) (hqPrime : q.Prime)
    (hqFar : t + 9 ≤ q) :
    survivorFixedPrimeCofactorMass 16 t q =
      -dyadicPrimeFiberBoundaryMass (t + 1) q := by
  have hR : 0 < t + 1 := by omega
  have hRq : t + 1 < q := by omega
  calc
    survivorFixedPrimeCofactorMass 16 t q =
        -primeDilatedLowCofactorMass (t + 1) q :=
      survivorFixedPrimeCofactorMass_sixteen_eq_neg_primeDilatedLowCofactorMass
        t q ht hqPrime hqFar
    _ = -dyadicPrimeFiberBoundaryMass (t + 1) q := by
      rw [primeDilatedLowCofactorMass_eq_dyadicPrimeFiberBoundaryMass
        (t + 1) q hR hRq hqPrime.pos]

/-- The complete far-upper prime portion of the `Lambda = 16` survivor. -/
def survivorSixteenFarUpperPrimeMass (t : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc (t + 9) (RHLean.Analysis.squarePrefixEndpoint t),
    if q.Prime then survivorFixedPrimeCofactorMass 16 t q else 0

/-- **Global far-upper rigidity.**  The entire sector beyond the first seven
integer offsets above the square root is exactly a signed reciprocal Mertens
transform.  Thus fixed-`q` prime-face cancellation cannot by itself remove the
lower-scale Mertens obstruction. -/
theorem survivorSixteenFarUpperPrimeMass_eq_neg_mertensTransform
    (t : ℕ) (ht : 55 ≤ t) :
    survivorSixteenFarUpperPrimeMass t =
      -∑ q ∈ Finset.Icc (t + 9) (RHLean.Analysis.squarePrefixEndpoint t),
        if q.Prime then
          RHLean.Analysis.mertensSummatory
            (RHLean.Analysis.squarePrefixEndpoint t / q)
        else 0 := by
  classical
  unfold survivorSixteenFarUpperPrimeMass
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q hqmem
  have hqFar : t + 9 ≤ q := (Finset.mem_Icc.mp hqmem).1
  by_cases hqPrime : q.Prime
  · simp only [hqPrime, if_true]
    rw [survivorFixedPrimeCofactorMass_sixteen_eq_neg_mertensSummatory
      t q ht hqPrime hqFar]
  · simp [hqPrime]

end RHLean.Proof
