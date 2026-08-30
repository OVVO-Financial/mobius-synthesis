import Mathlib
import RHLean.Proof.SquareRootLowPrimeBornSquareBoundary
import RHLean.Proof.SquareRootLowPrimeHighSupportDichotomy

/-!
# Born-channel support dichotomy

The born partner condition has one boundary absent from the high channel:
`q <= c`.  Decreasing the cofactor preserves the endpoint inequality and the
roughness condition, but can cross this order boundary.  This file proves that
this is the only interior obstruction.

Thus a missing born displacement corner is supported by one of the already
visible boundaries:

* the lower owner cutoff;
* the root crossing `d < q`;
* the square endpoint crossing `R^2-1 < d*q`;
* or, before arithmetic freshness is discharged, a roughness failure
  `q <= P+(d)`.

For divisor parents of an existing born atom, roughness and the endpoint bound
are automatic.  Their absence therefore means owner cutoff or root crossing.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Any positive squarefree owned cofactor satisfying the four literal born
partner inequalities produces a born response atom. -/
theorem squareRootLowPrimeBornAtom_of_squarefreeCofactor
    {R K U c d q : ℕ}
    (hz : (c, q) ∈ squareRootLowPrimeBornResponseAtoms R K U)
    (hd : 0 < d) (hdSq : Squarefree d)
    (hdOwner : canonicalLargestPrimeFactor d ∈
      squareRootLowPrimeFreshPrimeSet K U)
    (hrough : canonicalLargestPrimeFactor d < q)
    (horder : q ≤ d) (hdq : d * q ≤ squareRootEndpoint R) :
    (d, q) ∈ squareRootLowPrimeBornResponseAtoms R K U := by
  have hzBorn := (mem_squareRootLowPrimeBornResponseAtoms.mp hz).2
  have hqData := Finset.mem_filter.mp hzBorn
  have hdUpper : d ≤ squareRootEndpoint R := by
    have hdLeProd : d ≤ d * q := Nat.le_mul_of_pos_right d hqData.2.1.pos
    exact hdLeProd.trans hdq
  have hdOwned :=
    squareRootLowPrimeSquarefreeCofactor_mem_ownedResponseCofactors
      hd hdSq hdUpper hdOwner
  have hdBorn : q ∈ squareRootBornPartnerSet R d := by
    unfold squareRootBornPartnerSet
    exact Finset.mem_filter.mpr
      ⟨hqData.1, hqData.2.1, hrough, horder, hdq⟩
  exact mem_squareRootLowPrimeBornResponseAtoms.mpr
    ⟨squareRootLowPrimeOwnedResponseAtom_of_ownedCofactor
      hdOwned (Finset.mem_union.mpr (Or.inl hdBorn)),
      hdBorn⟩

/-- **Complete born support dichotomy.** -/
theorem squareRootLowPrimeBorn_missing_support
    {R K U c d q : ℕ}
    (hz : (c, q) ∈ squareRootLowPrimeBornResponseAtoms R K U)
    (hd : 0 < d) (hdSq : Squarefree d)
    (hmissing : (d, q) ∉ squareRootLowPrimeBornResponseAtoms R K U) :
    canonicalLargestPrimeFactor d ∉ squareRootLowPrimeFreshPrimeSet K U ∨
      q ≤ canonicalLargestPrimeFactor d ∨
        d < q ∨ squareRootEndpoint R < d * q := by
  by_cases hdOwner : canonicalLargestPrimeFactor d ∈
      squareRootLowPrimeFreshPrimeSet K U
  · by_cases hrough : canonicalLargestPrimeFactor d < q
    · by_cases horder : q ≤ d
      · by_cases hdq : d * q ≤ squareRootEndpoint R
        · exact (hmissing
            (squareRootLowPrimeBornAtom_of_squarefreeCofactor
              hz hd hdSq hdOwner hrough horder hdq)).elim
        · exact Or.inr (Or.inr (Or.inr (Nat.lt_of_not_ge hdq)))
      · exact Or.inr (Or.inr (Or.inl (Nat.lt_of_not_ge horder)))
    · exact Or.inr (Or.inl (Nat.le_of_not_gt hrough))
  · exact Or.inl hdOwner

/-- A positive divisor of a squarefree cofactor is squarefree. -/
theorem squarefree_of_dvd_ownedResponseCofactor
    {R K U c d : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedResponseCofactors R K U)
    (hdc : d ∣ c) : Squarefree d := by
  have hcSign :=
    squareRootLowPrimeOwnedResponseCofactor_moebius_eq_one_or_neg_one hc
  have hcMuNe : μ c ≠ 0 := by
    rcases hcSign with h | h <;> omega
  have hcSq : Squarefree c :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hcMuNe
  exact hcSq.squarefree_of_dvd hdc

/-- **Born divisor-parent closure above the order boundary.** -/
theorem squareRootLowPrimeBornDivisorAtom_mem
    {R K U c d q : ℕ}
    (hz : (c, q) ∈ squareRootLowPrimeBornResponseAtoms R K U)
    (hd : 0 < d) (hdc : d ∣ c)
    (hdOwner : canonicalLargestPrimeFactor d ∈
      squareRootLowPrimeFreshPrimeSet K U)
    (horder : q ≤ d) :
    (d, q) ∈ squareRootLowPrimeBornResponseAtoms R K U := by
  rcases mem_squareRootLowPrimeBornResponseAtoms.mp hz with
    ⟨hzResponse, hzBorn⟩
  have hcOwned :=
    squareRootLowPrimeOwnedResponseAtom_fst_mem_ownedResponseCofactors
      hzResponse
  have hcPos : 0 < c := by
    rcases mem_squareRootLowPrimeOwnedResponseCofactors.mp hcOwned with hbad | hdelete
    · exact (squareRootLowPrimeOwnedBadCofactor_data hbad).1
    · exact (squareRootLowPrimeOwnedDeletionCofactor_data hdelete).1
  have hqData := Finset.mem_filter.mp hzBorn
  have hdGt : 1 < d := lt_of_lt_of_le hqData.2.1.one_lt horder
  have hcGt : 1 < c := lt_of_lt_of_le hdGt (Nat.le_of_dvd hcPos hdc)
  have hdSq := squarefree_of_dvd_ownedResponseCofactor hcOwned hdc
  have hrough : canonicalLargestPrimeFactor d < q :=
    (canonicalLargestPrimeFactor_le_of_dvd hd hcGt hdc).trans_lt
      hqData.2.2.1
  have hdq : d * q ≤ squareRootEndpoint R :=
    (Nat.mul_le_mul_right q (Nat.le_of_dvd hcPos hdc)).trans
      hqData.2.2.2.2
  exact squareRootLowPrimeBornAtom_of_squarefreeCofactor
    hz hd hdSq hdOwner hrough horder hdq

/-- **Born missing divisor-parent = owner cutoff or root crossing.** -/
theorem squareRootLowPrimeBorn_missingDivisor_owner_or_rootCrossing
    {R K U c d q : ℕ}
    (hz : (c, q) ∈ squareRootLowPrimeBornResponseAtoms R K U)
    (hd : 0 < d) (hdc : d ∣ c)
    (hmissing : (d, q) ∉ squareRootLowPrimeBornResponseAtoms R K U) :
    canonicalLargestPrimeFactor d ∉ squareRootLowPrimeFreshPrimeSet K U ∨
      d < q := by
  by_cases hdOwner : canonicalLargestPrimeFactor d ∈
      squareRootLowPrimeFreshPrimeSet K U
  · by_cases horder : q ≤ d
    · exact (hmissing
        (squareRootLowPrimeBornDivisorAtom_mem
          hz hd hdc hdOwner horder)).elim
    · exact Or.inr (Nat.lt_of_not_ge horder)
  · exact Or.inl hdOwner

end RHLean.Proof
