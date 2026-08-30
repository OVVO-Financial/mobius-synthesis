import Mathlib
import RHLean.Proof.SquareRootLowPrimeResponseForest

/-!
# Post-root response as a lower-scale reciprocal cofactor transform

The internal born response forest closes on later owned cofactors.  Its only
unbounded exit population is therefore the post-root partner range `q > R`.
This module applies the repository's concrete `c -> floor((R^2-1)/q)` map to
that population before taking any norm.

For fixed `q`, the admitted parent cofactors are exactly the owned response
cofactors in the lower prefix

`c <= floor((R^2-1)/q)`.

Consequently the complete signed post-root child mass is the negative of the
lower-triangular transform

`sum_{R < q <= R^2-1, q prime}
   H_{K,U}(floor((R^2-1)/q))`,

where `H_{K,U}(B)` is the signed Möbius mass of owned cofactors in `[1,B]`.
Grouping by the reciprocal quotient gives

`sum_{K < B < R} N_R(B) H_{K,U}(B)`.

The lower shells `B <= K` vanish identically because every owned cofactor has
canonical owner in `(K,U]`, hence is itself strictly larger than `K`.

This is an exact quantitative reduction of the post-root obstruction to a
finite lower-scale transform.  No norm, PNT estimate, Mertens estimate, or
energy decrement is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- All post-root prime coordinates that can occur below the square endpoint. -/
def squareRootLowPrimePostRootPrimeSet (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter Nat.Prime

@[simp] theorem mem_squareRootLowPrimePostRootPrimeSet
    {R q : ℕ} :
    q ∈ squareRootLowPrimePostRootPrimeSet R ↔
      R < q ∧ q ≤ squareRootEndpoint R ∧ q.Prime := by
  simp [squareRootLowPrimePostRootPrimeSet, and_assoc]

/-- Signed owned-cofactor prefix at lower reciprocal scale `B`. -/
def squareRootLowPrimeRestrictedOwnedCofactorPrefixMass
    (R K U B : ℕ) : ℂ :=
  ∑ c ∈ squareRootLowPrimeOwnedResponseCofactors R K U,
    if c ≤ B then canonicalMoebiusWeight c else 0

/-- Parent-side signed mass of the post-root response atoms. -/
def squareRootLowPrimePostRootParentMass
    (R K U : ℕ) : ℂ :=
  ∑ z ∈ squareRootLowPrimePostRootResponseAtoms R K U,
    canonicalMoebiusWeight z.1

/-- The direct reciprocal lower-scale transform. -/
def squareRootLowPrimePostRootCofactorTransform
    (R K U : ℕ) : ℂ :=
  ∑ q ∈ squareRootLowPrimePostRootPrimeSet R,
    squareRootLowPrimeRestrictedOwnedCofactorPrefixMass
      R K U (squareRootEndpoint R / q)

/-- The post-root atom carrier is exactly one product carrier cut by the
hyperbola `c*q <= R^2-1`. -/
theorem squareRootLowPrimePostRootResponseAtoms_eq_product_filter
    (R K U : ℕ) :
    squareRootLowPrimePostRootResponseAtoms R K U =
      ((squareRootLowPrimeOwnedResponseCofactors R K U).product
        (squareRootLowPrimePostRootPrimeSet R)).filter fun z =>
          z.1 * z.2 ≤ squareRootEndpoint R := by
  classical
  ext z
  constructor
  · intro hz
    rcases mem_squareRootLowPrimePostRootResponseAtoms.mp hz with
      ⟨hzResponse, hzPost⟩
    have hcCarrier :=
      squareRootLowPrimeOwnedResponseAtom_fst_mem_ownedResponseCofactors
        hzResponse
    unfold squareRootPostRootPrimePartnerSet at hzPost
    rcases Finset.mem_filter.mp hzPost with
      ⟨hqIoc, hqPrime, hproduct⟩
    have hqSet : z.2 ∈ squareRootLowPrimePostRootPrimeSet R := by
      unfold squareRootLowPrimePostRootPrimeSet
      exact Finset.mem_filter.mpr ⟨hqIoc, hqPrime⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hcCarrier, hqSet⟩, hproduct⟩
  · intro hz
    rcases Finset.mem_filter.mp hz with ⟨hzProduct, hproduct⟩
    rcases Finset.mem_product.mp hzProduct with ⟨hcCarrier, hqSet⟩
    unfold squareRootLowPrimePostRootPrimeSet at hqSet
    rcases Finset.mem_filter.mp hqSet with ⟨hqIoc, hqPrime⟩
    have hqPost :
        z.2 ∈ squareRootPostRootPrimePartnerSet R z.1 := by
      unfold squareRootPostRootPrimePartnerSet
      exact Finset.mem_filter.mpr
        ⟨hqIoc, ⟨hqPrime, hproduct⟩⟩
    have hqDeep : z.2 ∈ squareRootLowPrimeDeepPartnerSet R z.1 :=
      Finset.mem_union.mpr (Or.inr hqPost)
    have hzResponse :
        z ∈ squareRootLowPrimeOwnedResponseAtoms R K U := by
      rcases mem_squareRootLowPrimeOwnedResponseCofactors.mp hcCarrier with
        hcBad | hcDeletion
      · apply Finset.mem_union.mpr
        left
        unfold squareRootLowPrimeOwnedBadAtoms
        exact Finset.mem_biUnion.mpr
          ⟨z.1, hcBad,
            mem_squareRootLowPrimeBadAtomFiber.mpr ⟨rfl, hqDeep⟩⟩
      · apply Finset.mem_union.mpr
        right
        unfold squareRootLowPrimeOwnedDeletionAtoms
        exact Finset.mem_biUnion.mpr
          ⟨z.1, hcDeletion,
            mem_squareRootLowPrimeBadAtomFiber.mpr ⟨rfl, hqDeep⟩⟩
    exact mem_squareRootLowPrimePostRootResponseAtoms.mpr
      ⟨hzResponse, hqPost⟩

/-- **Pointwise reciprocal reindexing.**  For one post-root prime `q`, the
hyperbolic parent condition is exactly the lower cutoff
`c <= floor((R^2-1)/q)`. -/
theorem squareRootLowPrimePostRootParentMass_eq_cofactorTransform
    (R K U : ℕ) :
    squareRootLowPrimePostRootParentMass R K U =
      squareRootLowPrimePostRootCofactorTransform R K U := by
  classical
  unfold squareRootLowPrimePostRootParentMass
    squareRootLowPrimePostRootCofactorTransform
  rw [squareRootLowPrimePostRootResponseAtoms_eq_product_filter,
    Finset.sum_filter]
  calc
    (∑ z ∈ (squareRootLowPrimeOwnedResponseCofactors R K U).product
          (squareRootLowPrimePostRootPrimeSet R),
        if z.1 * z.2 ≤ squareRootEndpoint R then
          canonicalMoebiusWeight z.1
        else 0) =
      ∑ c ∈ squareRootLowPrimeOwnedResponseCofactors R K U,
        ∑ q ∈ squareRootLowPrimePostRootPrimeSet R,
          if c * q ≤ squareRootEndpoint R then
            canonicalMoebiusWeight c
          else 0 := by
            simpa only using
              (Finset.sum_product
                (s := squareRootLowPrimeOwnedResponseCofactors R K U)
                (t := squareRootLowPrimePostRootPrimeSet R)
                (f := fun z : ℕ × ℕ =>
                  if z.1 * z.2 ≤ squareRootEndpoint R then
                    canonicalMoebiusWeight z.1
                  else 0))
    _ = ∑ q ∈ squareRootLowPrimePostRootPrimeSet R,
        ∑ c ∈ squareRootLowPrimeOwnedResponseCofactors R K U,
          if c * q ≤ squareRootEndpoint R then
            canonicalMoebiusWeight c
          else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ q ∈ squareRootLowPrimePostRootPrimeSet R,
        squareRootLowPrimeRestrictedOwnedCofactorPrefixMass
          R K U (squareRootEndpoint R / q) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqPrime : q.Prime :=
        (mem_squareRootLowPrimePostRootPrimeSet.mp hq).2.2
      unfold squareRootLowPrimeRestrictedOwnedCofactorPrefixMass
      apply Finset.sum_congr rfl
      intro c _hc
      by_cases hproduct : c * q ≤ squareRootEndpoint R
      · have hdiv : c ≤ squareRootEndpoint R / q :=
          (Nat.le_div_iff_mul_le hqPrime.pos).2 hproduct
        simp [hproduct, hdiv]
      · have hdiv : ¬ c ≤ squareRootEndpoint R / q := by
          intro hc
          exact hproduct ((Nat.le_div_iff_mul_le hqPrime.pos).1 hc)
        simp [hproduct, hdiv]

/-- Adjoining the post-root partner flips the parent Möbius sign, so the child
mass is the negative reciprocal cofactor transform. -/
theorem squareRootLowPrimePostRootChildMass_eq_neg_cofactorTransform
    {R K U : ℕ} (hUR : U < R) :
    squareRootLowPrimePostRootChildMass R K U =
      -squareRootLowPrimePostRootCofactorTransform R K U := by
  rw [← squareRootLowPrimePostRootParentMass_eq_cofactorTransform]
  unfold squareRootLowPrimePostRootChildMass
    squareRootLowPrimePostRootParentMass
  calc
    (∑ z ∈ squareRootLowPrimePostRootResponseAtoms R K U,
        canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z)) =
      ∑ z ∈ squareRootLowPrimePostRootResponseAtoms R K U,
        -canonicalMoebiusWeight z.1 := by
          apply Finset.sum_congr rfl
          intro z hz
          exact squareRootLowPrimeOwnedResponseAtomChild_moebiusWeight
            hUR (mem_squareRootLowPrimePostRootResponseAtoms.mp hz).1
    _ = -(∑ z ∈ squareRootLowPrimePostRootResponseAtoms R K U,
        canonicalMoebiusWeight z.1) := by
          rw [Finset.sum_neg_distrib]

/-- Every owned cofactor is strictly above the lower owner cutoff `K`. -/
theorem squareRootLowPrimeOwnedResponseCofactor_gt_cutoff
    {R K U c : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedResponseCofactors R K U) :
    K < c := by
  rcases mem_squareRootLowPrimeOwnedResponseCofactors.mp hc with hc | hc
  · exact (squareRootLowPrimeOwnedBadCofactor_data hc).2.1
  · exact (squareRootLowPrimeOwnedDeletionCofactor_data hc).2.1

/-- Therefore every lower reciprocal shell at or below `K` is identically
empty in the signed transform. -/
theorem squareRootLowPrimeRestrictedOwnedCofactorPrefixMass_eq_zero_of_le_cutoff
    {R K U B : ℕ} (hBK : B ≤ K) :
    squareRootLowPrimeRestrictedOwnedCofactorPrefixMass R K U B = 0 := by
  unfold squareRootLowPrimeRestrictedOwnedCofactorPrefixMass
  apply Finset.sum_eq_zero
  intro c hc
  have hKc := squareRootLowPrimeOwnedResponseCofactor_gt_cutoff hc
  have hnot : ¬ c ≤ B := by omega
  simp [hnot]

/-- Number of post-root primes with one fixed reciprocal quotient `B`. -/
def squareRootLowPrimePostRootReciprocalCount
    (R B : ℕ) : ℕ :=
  ((squareRootLowPrimePostRootPrimeSet R).filter fun q =>
    squareRootEndpoint R / q = B).card

/-- Post-root reciprocal quotients lie in the strict lower range `[1,R-1]`. -/
theorem squareRootLowPrimePostRoot_quotient_mem_Icc
    {R q : ℕ} (hR : 2 ≤ R)
    (hq : q ∈ squareRootLowPrimePostRootPrimeSet R) :
    squareRootEndpoint R / q ∈ Finset.Icc 1 (R - 1) := by
  rcases mem_squareRootLowPrimePostRootPrimeSet.mp hq with
    ⟨hRq, hqX, hqPrime⟩
  have hlow : 1 ≤ squareRootEndpoint R / q :=
    (Nat.le_div_iff_mul_le hqPrime.pos).2 (by simpa using hqX)
  have hRpos : 0 < R := by omega
  have hXltSquare : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hsqpos : 0 < R ^ 2 := by positivity
    exact Nat.sub_lt hsqpos (by norm_num)
  have hSquareLt : R ^ 2 < R * q := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hRq hRpos
  have hXlt : squareRootEndpoint R < R * q :=
    hXltSquare.trans hSquareLt
  have hdivlt : squareRootEndpoint R / q < R :=
    (Nat.div_lt_iff_lt_mul hqPrime.pos).2 hXlt
  exact Finset.mem_Icc.mpr ⟨hlow, by omega⟩

/-- **Reciprocal quotient-shell compression.**  The post-root transform is one
lower-triangular sum over reciprocal scales. -/
theorem squareRootLowPrimePostRootCofactorTransform_eq_quotientShellSum
    (R K U : ℕ) (hR : 2 ≤ R) :
    squareRootLowPrimePostRootCofactorTransform R K U =
      ∑ B ∈ Finset.Icc 1 (R - 1),
        (squareRootLowPrimePostRootReciprocalCount R B : ℂ) *
          squareRootLowPrimeRestrictedOwnedCofactorPrefixMass R K U B := by
  classical
  have hmaps :
      ∀ q ∈ squareRootLowPrimePostRootPrimeSet R,
        squareRootEndpoint R / q ∈ Finset.Icc 1 (R - 1) := by
    intro q hq
    exact squareRootLowPrimePostRoot_quotient_mem_Icc hR hq
  unfold squareRootLowPrimePostRootCofactorTransform
    squareRootLowPrimePostRootReciprocalCount
  calc
    (∑ q ∈ squareRootLowPrimePostRootPrimeSet R,
        squareRootLowPrimeRestrictedOwnedCofactorPrefixMass
          R K U (squareRootEndpoint R / q)) =
      ∑ B ∈ Finset.Icc 1 (R - 1),
        ∑ _q ∈ squareRootLowPrimePostRootPrimeSet R with
            squareRootEndpoint R / _q = B,
          squareRootLowPrimeRestrictedOwnedCofactorPrefixMass R K U B := by
            symm
            simpa using
              (Finset.sum_fiberwise_of_maps_to'
                (s := squareRootLowPrimePostRootPrimeSet R)
                (t := Finset.Icc 1 (R - 1))
                (g := fun q => squareRootEndpoint R / q)
                hmaps
                (fun B : ℕ =>
                  squareRootLowPrimeRestrictedOwnedCofactorPrefixMass
                    R K U B))
    _ = ∑ B ∈ Finset.Icc 1 (R - 1),
        (((squareRootLowPrimePostRootPrimeSet R).filter fun q =>
            squareRootEndpoint R / q = B).card : ℂ) *
          squareRootLowPrimeRestrictedOwnedCofactorPrefixMass R K U B := by
            apply Finset.sum_congr rfl
            intro B _hB
            simp

/-- Active reciprocal scales after deleting the identically zero shells
`B <= K`. -/
def squareRootLowPrimePostRootActiveCofactorTransform
    (R K U : ℕ) : ℂ :=
  ∑ B ∈ Finset.Ioc K (R - 1),
    (squareRootLowPrimePostRootReciprocalCount R B : ℂ) *
      squareRootLowPrimeRestrictedOwnedCofactorPrefixMass R K U B

/-- The full quotient-shell transform is supported only on `K < B < R`. -/
theorem squareRootLowPrimePostRootCofactorTransform_eq_active
    (R K U : ℕ) (hR : 2 ≤ R) (hKR : K < R) :
    squareRootLowPrimePostRootCofactorTransform R K U =
      squareRootLowPrimePostRootActiveCofactorTransform R K U := by
  rw [squareRootLowPrimePostRootCofactorTransform_eq_quotientShellSum
    R K U hR]
  unfold squareRootLowPrimePostRootActiveCofactorTransform
  have hset :
      Finset.Icc 1 (R - 1) =
        Finset.Icc 1 K ∪ Finset.Ioc K (R - 1) := by
    ext B
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj :
      Disjoint (Finset.Icc 1 K) (Finset.Ioc K (R - 1)) := by
    rw [Finset.disjoint_left]
    intro B hlow hhigh
    rcases Finset.mem_Icc.mp hlow with ⟨_hB1, hBK⟩
    rcases Finset.mem_Ioc.mp hhigh with ⟨hKB, _hBR⟩
    omega
  rw [hset, Finset.sum_union hdisj]
  have hzero :
      (∑ B ∈ Finset.Icc 1 K,
        (squareRootLowPrimePostRootReciprocalCount R B : ℂ) *
          squareRootLowPrimeRestrictedOwnedCofactorPrefixMass R K U B) = 0 := by
    apply Finset.sum_eq_zero
    intro B hB
    have hBK := (Finset.mem_Icc.mp hB).2
    rw [squareRootLowPrimeRestrictedOwnedCofactorPrefixMass_eq_zero_of_le_cutoff
      hBK]
    ring
  rw [hzero, zero_add]

/-- **Post-root C-to-R reduction.**  The complete post-root signed child mass is
the negative active lower-scale transform on the exact range `K < B < R`. -/
theorem squareRootLowPrimePostRootChildMass_eq_neg_activeCofactorTransform
    {R K U : ℕ} (hR : 2 ≤ R) (hKR : K < R) (hUR : U < R) :
    squareRootLowPrimePostRootChildMass R K U =
      -squareRootLowPrimePostRootActiveCofactorTransform R K U := by
  rw [squareRootLowPrimePostRootChildMass_eq_neg_cofactorTransform hUR,
    squareRootLowPrimePostRootCofactorTransform_eq_active R K U hR hKR]

end RHLean.Proof
