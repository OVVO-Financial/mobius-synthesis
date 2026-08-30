import Mathlib
import RHLean.Proof.SquareRootLowPrimeSequentialDissipationOwnership
import RHLean.Proof.LowPrimeParentChildWindowDifference

/-!
# Deep low-prime response weights as uniquely owned prime-extension atoms

The exact sequential decomposition

`Delta_p = -D_p + F_p`

uses the complete natural response

`BornPartnerCount(c) + HighResponse(c)`

at each fresh cofactor.  A support count alone does not control this weight.
Beyond the shallow crossing depth, however, every unit of that weight is an
actual prime-extension atom `(c,q)`:

* `q <= R` is a born-smooth partner of `c`, or
* `R < q` is a still-unprocessed post-root partner of `c`.

These two partner sets are disjoint.  Their union has cardinality exactly the
complete combined response, including the honest high cutoff at `c = R`.

Over a fresh-prime interval `(K,U]`, the already-owned bad cofactors all satisfy
`K < P+(c) <= c`, so this atomization applies to the complete bad mass.  When
`U < R`, every partner prime lies strictly above `P+(c)`.  Therefore

`(c,q) |-> c*q`

is injective: the child recovers `q` as its canonical largest prime and recovers
`c` as its canonical cofactor.  Thus the complete weighted bad mass is the
cardinality of one literal child-state set below `R^2-1`.

This removes the response-weight opacity without asserting that the resulting
`O(R^2)` raw bad-mass bound is the desired dissipation estimate.  The remaining
quantitative task is signed cancellation between the bad and deletion child
states, or equivalently control of their excess.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- All literal prime partners contributing to the complete deep response of a
cofactor.  The born and post-root ranges are kept separate in the definition
and proved disjoint below. -/
def squareRootLowPrimeDeepPartnerSet (R c : ℕ) : Finset ℕ :=
  squareRootBornPartnerSet R c ∪ squareRootPostRootPrimePartnerSet R c

/-- Born partners lie at or below `R`, whereas post-root partners lie strictly
above `R`. -/
theorem squareRootLowPrimeBornPartnerSet_disjoint_postRootPartnerSet
    (R c : ℕ) :
    Disjoint (squareRootBornPartnerSet R c)
      (squareRootPostRootPrimePartnerSet R c) := by
  classical
  rw [Finset.disjoint_left]
  intro q hborn hpost
  have hb := Finset.mem_filter.mp hborn
  have hp := Finset.mem_filter.mp hpost
  have hqR : q ≤ R := (Finset.mem_Icc.mp hb.1).2
  have hRq : R < q := (Finset.mem_Ioc.mp hp.1).1
  omega

/-- The deep partner set has the expected born-plus-post-root cardinality. -/
theorem card_squareRootLowPrimeDeepPartnerSet
    {R c : ℕ} (hc : 0 < c) :
    (squareRootLowPrimeDeepPartnerSet R c).card =
      squareRootBornPartnerCount R c +
        squareRootPostRootPrimePrefixCard R c := by
  unfold squareRootLowPrimeDeepPartnerSet squareRootBornPartnerCount
  rw [Finset.card_union_of_disjoint
      (squareRootLowPrimeBornPartnerSet_disjoint_postRootPartnerSet R c),
    card_squareRootPostRootPrimePartnerSet_eq_prefixCard hc]

/-- At or beyond the root there cannot be a post-root prime partner while the
product remains below `R^2-1`. -/
theorem squareRootPostRootPrimePartnerSet_eq_empty_of_root_le
    {R c : ℕ} (hR : 1 ≤ R) (hcR : R ≤ c) :
    squareRootPostRootPrimePartnerSet R c = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqIoc, _hqPrime, hcqX⟩
  have hRq : R < q := (Finset.mem_Ioc.mp hqIoc).1
  have hqLower : R + 1 ≤ q := by omega
  have hprodLower : R * (R + 1) ≤ c * q :=
    Nat.mul_le_mul hcR hqLower
  have hXltSquare : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hsqpos : 0 < R ^ 2 := by positivity
    omega
  have hSquareLt : R ^ 2 < R * (R + 1) := by
    nlinarith
  have hXlt : squareRootEndpoint R < c * q :=
    hXltSquare.trans (hSquareLt.trans_le hprodLower)
  omega

/-- Beyond the shallow cutoff, the complete combined response is exactly the
cardinality of the literal deep partner set.  This includes the honest high
cutoff: for `c >= R`, the post-root partner set is empty. -/
theorem card_squareRootLowPrimeDeepPartnerSet_eq_combinedFreshResponse
    {R K j c : ℕ} (hR : 1 ≤ R) (hc : 0 < c) (hKc : K < c) :
    (squareRootLowPrimeDeepPartnerSet R c).card =
      squareRootLowPrimeCombinedFreshResponse R K j c := by
  rw [card_squareRootLowPrimeDeepPartnerSet hc]
  by_cases hcR : c ≤ R - 1
  · simp [squareRootLowPrimeCombinedFreshResponse,
      squareRootBornPostTailHighResponse, hcR, Nat.not_le.mpr hKc]
  · have hroot : R ≤ c := by omega
    have hpostEmpty :=
      squareRootPostRootPrimePartnerSet_eq_empty_of_root_le hR hroot
    have hprefixZero : squareRootPostRootPrimePrefixCard R c = 0 := by
      rw [← card_squareRootPostRootPrimePartnerSet_eq_prefixCard hc,
        hpostEmpty]
      simp
    simp [squareRootLowPrimeCombinedFreshResponse, hcR, hprefixZero]

/-- One cofactor fibre of prime-extension atoms. -/
def squareRootLowPrimeBadAtomFiber (R c : ℕ) : Finset (ℕ × ℕ) :=
  ({c} : Finset ℕ).product (squareRootLowPrimeDeepPartnerSet R c)

@[simp] theorem mem_squareRootLowPrimeBadAtomFiber
    {R c : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeBadAtomFiber R c ↔
      z.1 = c ∧ z.2 ∈ squareRootLowPrimeDeepPartnerSet R c := by
  unfold squareRootLowPrimeBadAtomFiber
  constructor
  · intro hz
    rcases Finset.mem_product.mp hz with ⟨hz1, hz2⟩
    exact ⟨Finset.mem_singleton.mp hz1, hz2⟩
  · rintro ⟨hz1, hz2⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hz1, hz2⟩

/-- The complete atom carrier over the globally owned positive-orientation
cofactors in `(K,U]`. -/
def squareRootLowPrimeOwnedBadAtoms
    (R K U : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeOwnedBadCofactors R K U).biUnion
    (squareRootLowPrimeBadAtomFiber R)

/-- Arithmetic data forced by membership in the globally owned bad-cofactor
carrier. -/
theorem squareRootLowPrimeOwnedBadCofactor_data
    {R K U c : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedBadCofactors R K U) :
    0 < c ∧ K < c ∧
      canonicalLargestPrimeFactor c ≤ U ∧ μ c = 1 := by
  unfold squareRootLowPrimeOwnedBadCofactors at hc
  rcases Finset.mem_biUnion.mp hc with ⟨p, hpSet, hcp⟩
  rcases Finset.mem_filter.mp hpSet with ⟨hpIoc, hpPrime⟩
  rcases Finset.mem_Ioc.mp hpIoc with ⟨hKp, hpU⟩
  unfold squareRootLowPrimeBadCofactors at hcp
  rcases Finset.mem_filter.mp hcp with ⟨hcFresh, hmu⟩
  unfold squareRootLowPrimeBornFreshCofactors at hcFresh
  rcases Finset.mem_filter.mp hcFresh with ⟨hcIcc, hlpf⟩
  rcases Finset.mem_Icc.mp hcIcc with ⟨hc1, _hcX⟩
  have hcne : c ≠ 1 := by
    intro hcEq
    subst c
    have hlpfOne : canonicalLargestPrimeFactor 1 = 1 := by
      simp [canonicalLargestPrimeFactor]
    rw [hlpfOne] at hlpf
    exact hpPrime.ne_one hlpf.symm
  have hcgt : 1 < c := by omega
  have hpDvd : p ∣ c := by
    rw [← hlpf]
    exact canonicalLargestPrimeFactor_dvd hcgt
  have hpLeC : p ≤ c := Nat.le_of_dvd (by omega) hpDvd
  refine ⟨by omega, hKp.trans_le hpLeC, ?_, hmu⟩
  rw [hlpf]
  exact hpU

/-- Distinct cofactor fibres of atoms are disjoint. -/
theorem squareRootLowPrimeBadAtomFiber_pairwiseDisjoint
    (R K U : ℕ) :
    Set.PairwiseDisjoint
      (↑(squareRootLowPrimeOwnedBadCofactors R K U))
      (squareRootLowPrimeBadAtomFiber R) := by
  intro c _hc d _hd hcd
  change Disjoint (squareRootLowPrimeBadAtomFiber R c)
    (squareRootLowPrimeBadAtomFiber R d)
  rw [Finset.disjoint_left]
  intro z hzc hzd
  have hzcData := mem_squareRootLowPrimeBadAtomFiber.mp hzc
  have hzdData := mem_squareRootLowPrimeBadAtomFiber.mp hzd
  exact hcd (hzcData.1.symm.trans hzdData.1)

/-- **Complete response atomization.**  The raw globally owned bad mass on the
deep interval `(K,U]` is exactly the cardinality of one literal atom set.  No
uniform response-weight estimate is used. -/
theorem squareRootLowPrimeGlobalBadMass_eq_ownedBadAtoms_card
    {R K j U : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeGlobalBadMass R K j K U =
      (squareRootLowPrimeOwnedBadAtoms R K U).card := by
  rw [squareRootLowPrimeGlobalBadMass_eq_ownedCofactorSum]
  symm
  calc
    (squareRootLowPrimeOwnedBadAtoms R K U).card =
        ∑ z ∈ squareRootLowPrimeOwnedBadAtoms R K U, 1 := by simp
    _ = ∑ c ∈ squareRootLowPrimeOwnedBadCofactors R K U,
          ∑ z ∈ squareRootLowPrimeBadAtomFiber R c, 1 := by
      unfold squareRootLowPrimeOwnedBadAtoms
      exact Finset.sum_biUnion
        (squareRootLowPrimeBadAtomFiber_pairwiseDisjoint R K U)
    _ = ∑ c ∈ squareRootLowPrimeOwnedBadCofactors R K U,
          (squareRootLowPrimeDeepPartnerSet R c).card := by
      apply Finset.sum_congr rfl
      intro c _hc
      simp [squareRootLowPrimeBadAtomFiber]
    _ = ∑ c ∈ squareRootLowPrimeOwnedBadCofactors R K U,
          squareRootLowPrimeCombinedFreshResponse R K j c := by
      apply Finset.sum_congr rfl
      intro c hc
      have hcData := squareRootLowPrimeOwnedBadCofactor_data hc
      exact card_squareRootLowPrimeDeepPartnerSet_eq_combinedFreshResponse
        (by omega) hcData.1 hcData.2.1

/-- Every prime in the deep partner set is genuinely prime. -/
theorem prime_of_mem_squareRootLowPrimeDeepPartnerSet
    {R c q : ℕ} (hq : q ∈ squareRootLowPrimeDeepPartnerSet R c) :
    q.Prime := by
  rcases Finset.mem_union.mp hq with hborn | hpost
  · exact (Finset.mem_filter.mp hborn).2.1
  · exact (Finset.mem_filter.mp hpost).2.1

/-- Every atom product lies below the square endpoint. -/
theorem mul_le_squareRootEndpoint_of_mem_deepPartnerSet
    {R c q : ℕ} (hq : q ∈ squareRootLowPrimeDeepPartnerSet R c) :
    c * q ≤ squareRootEndpoint R := by
  rcases Finset.mem_union.mp hq with hborn | hpost
  · exact (Finset.mem_filter.mp hborn).2.2.2.2
  · exact (Finset.mem_filter.mp hpost).2.2

/-- On an interval ending below the root, every atom partner lies above every
prime factor of its owned cofactor. -/
theorem canonicalLargestPrimeFactor_lt_partner_of_ownedBadAtom
    {R K U c q : ℕ} (hUR : U < R)
    (hc : c ∈ squareRootLowPrimeOwnedBadCofactors R K U)
    (hq : q ∈ squareRootLowPrimeDeepPartnerSet R c) :
    canonicalLargestPrimeFactor c < q := by
  rcases Finset.mem_union.mp hq with hborn | hpost
  · exact (Finset.mem_filter.mp hborn).2.2.1
  · have hcData := squareRootLowPrimeOwnedBadCofactor_data hc
    have hRq : R < q :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpost).1).1
    exact lt_of_le_of_lt hcData.2.2.1 (hUR.trans hRq)

/-- The product map from deep bad atoms to arithmetic children. -/
def squareRootLowPrimeBadAtomChild (z : ℕ × ℕ) : ℕ := z.1 * z.2

/-- The atom product map is injective on the complete owned carrier below the
root.  The child recovers the partner as its largest prime and the cofactor as
its canonical cofactor. -/
theorem squareRootLowPrimeBadAtomChild_injOn
    {R K U : ℕ} (hUR : U < R) :
    Set.InjOn squareRootLowPrimeBadAtomChild
      (squareRootLowPrimeOwnedBadAtoms R K U) := by
  intro z hz w hw hchild
  unfold squareRootLowPrimeOwnedBadAtoms at hz hw
  rcases Finset.mem_biUnion.mp hz with ⟨c, hc, hzc⟩
  rcases Finset.mem_biUnion.mp hw with ⟨d, hd, hwd⟩
  have hzcData := mem_squareRootLowPrimeBadAtomFiber.mp hzc
  have hwdData := mem_squareRootLowPrimeBadAtomFiber.mp hwd
  have hz1 : z.1 = c := hzcData.1
  have hw1 : w.1 = d := hwdData.1
  have hcpos := (squareRootLowPrimeOwnedBadCofactor_data hc).1
  have hdpos := (squareRootLowPrimeOwnedBadCofactor_data hd).1
  have hzPrime := prime_of_mem_squareRootLowPrimeDeepPartnerSet hzcData.2
  have hwPrime := prime_of_mem_squareRootLowPrimeDeepPartnerSet hwdData.2
  have hzRough := canonicalLargestPrimeFactor_lt_partner_of_ownedBadAtom
    hUR hc hzcData.2
  have hwRough := canonicalLargestPrimeFactor_lt_partner_of_ownedBadAtom
    hUR hd hwdData.2
  have hzLargest :
      canonicalLargestPrimeFactor (z.1 * z.2) = z.2 := by
    rw [hz1]
    exact canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hcpos hzPrime hzRough
  have hwLargest :
      canonicalLargestPrimeFactor (w.1 * w.2) = w.2 := by
    rw [hw1]
    exact canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hdpos hwPrime hwRough
  have hq : z.2 = w.2 := by
    rw [← hzLargest, ← hwLargest]
    exact congrArg canonicalLargestPrimeFactor hchild
  have hzCofactor : canonicalCofactor (z.1 * z.2) = z.1 := by
    rw [hz1]
    exact canonicalCofactor_mul_prime_eq_of_rough hcpos hzPrime hzRough
  have hwCofactor : canonicalCofactor (w.1 * w.2) = w.1 := by
    rw [hw1]
    exact canonicalCofactor_mul_prime_eq_of_rough hdpos hwPrime hwRough
  have hcEq : z.1 = w.1 := by
    rw [← hzCofactor, ← hwCofactor]
    exact congrArg canonicalCofactor hchild
  exact Prod.ext hcEq hq

/-- Literal arithmetic child states generated by the complete bad atom carrier. -/
def squareRootLowPrimeOwnedBadChildren
    (R K U : ℕ) : Finset ℕ :=
  (squareRootLowPrimeOwnedBadAtoms R K U).image
    squareRootLowPrimeBadAtomChild

/-- Atomization loses no cardinality below the root. -/
theorem card_squareRootLowPrimeOwnedBadChildren
    {R K U : ℕ} (hUR : U < R) :
    (squareRootLowPrimeOwnedBadChildren R K U).card =
      (squareRootLowPrimeOwnedBadAtoms R K U).card := by
  unfold squareRootLowPrimeOwnedBadChildren
  exact Finset.card_image_iff.mpr
    (squareRootLowPrimeBadAtomChild_injOn hUR)

/-- Every owned bad child is positive and below the square endpoint. -/
theorem squareRootLowPrimeOwnedBadChildren_subset_Icc
    {R K U : ℕ} :
    squareRootLowPrimeOwnedBadChildren R K U ⊆
      Finset.Icc 1 (squareRootEndpoint R) := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
  unfold squareRootLowPrimeOwnedBadAtoms at hz
  rcases Finset.mem_biUnion.mp hz with ⟨c, hc, hzc⟩
  have hzData := mem_squareRootLowPrimeBadAtomFiber.mp hzc
  have hcpos := (squareRootLowPrimeOwnedBadCofactor_data hc).1
  have hz1pos : 0 < z.1 := by
    simpa [hzData.1] using hcpos
  have hqPrime := prime_of_mem_squareRootLowPrimeDeepPartnerSet hzData.2
  have hprod := mul_le_squareRootEndpoint_of_mem_deepPartnerSet hzData.2
  have hprod' : z.1 * z.2 ≤ squareRootEndpoint R := by
    simpa [hzData.1] using hprod
  exact Finset.mem_Icc.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.ne_of_gt hz1pos) hqPrime.ne_zero),
      hprod'⟩

/-- **Global complete-response support bound.**  After the actual response
weights are expanded into uniquely owned child states, the entire raw bad mass
on `(K,U]`, `U<R`, is at most the number of integers below `R^2`.

This is intentionally recorded as the exact combinatorial baseline.  It does
not claim the stronger signed-excess or energy bound. -/
theorem squareRootLowPrimeGlobalBadMass_le_squareRootEndpoint
    {R K j U : ℕ} (hR : 2 ≤ R) (hUR : U < R) :
    squareRootLowPrimeGlobalBadMass R K j K U ≤ squareRootEndpoint R := by
  rw [squareRootLowPrimeGlobalBadMass_eq_ownedBadAtoms_card hR,
    ← card_squareRootLowPrimeOwnedBadChildren hUR]
  calc
    (squareRootLowPrimeOwnedBadChildren R K U).card ≤
        (Finset.Icc 1 (squareRootEndpoint R)).card :=
      Finset.card_le_card squareRootLowPrimeOwnedBadChildren_subset_Icc
    _ = squareRootEndpoint R := by
      simp

end RHLean.Proof
