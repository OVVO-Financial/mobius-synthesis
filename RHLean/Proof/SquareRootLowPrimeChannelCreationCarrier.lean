import Mathlib
import RHLean.Proof.CreationResponseFrontierCancellationReal
import RHLean.Proof.SquareRootLowPrimeSignedResponseChildren
import RHLean.Proof.SquareRootLowPrimeQuantitativeEnergyReduction

/-!
# Channel-faithful shallow creation carrier

The shallow state `T(K)` is expanded into literal unit states without combining
its two response channels prematurely:

* one distinguished head state of weight `+1`;
* one born seat for every unit of `BornPartnerCount(c)`;
* one high seat for every unit of `HighResponse(c)` on the honest `c<R`
  cutoff.

Only cofactors with nonzero Möbius weight are retained.  Every non-head state
has weight `-mu(c)`, so all weights have absolute value at most one.

The signed mass of this finite carrier is exactly the real running imbalance
at the shallow cutoff.  The deep response carrier is the previously defined
set of literal response atoms, weighted by the Möbius sign of their arithmetic
children.  Its mass is exactly the negative deep increment sum.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- A creation state is either the distinguished head, a born seat, or a high
seat. -/
abbrev SquareRootLowPrimeCreationState :=
  Option (Sum (ℕ × ℕ) (ℕ × ℕ))

/-- Shallow cofactors in the born channel. -/
def squareRootLowPrimeShallowBornCofactors
    (R K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (squareRootEndpoint R)).filter fun c =>
    canonicalLargestPrimeFactor c ≤ K ∧ μ c ≠ 0

/-- Shallow cofactors in the honest high channel. -/
def squareRootLowPrimeShallowHighCofactors
    (R K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (R - 1)).filter fun c =>
    canonicalLargestPrimeFactor c ≤ K ∧ μ c ≠ 0

/-- Born seats belonging to one cofactor. -/
def squareRootLowPrimeShallowBornSeatFiber
    (R c : ℕ) : Finset (ℕ × ℕ) :=
  ({c} : Finset ℕ).product
    (Finset.range (squareRootBornPartnerCount R c))

/-- High seats belonging to one cofactor. -/
def squareRootLowPrimeShallowHighSeatFiber
    (R K j c : ℕ) : Finset (ℕ × ℕ) :=
  ({c} : Finset ℕ).product
    (Finset.range (squareRootBornPostTailHighResponse R K j c))

/-- Complete born-seat population at the shallow cutoff. -/
def squareRootLowPrimeShallowBornSeatAtoms
    (R K : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeShallowBornCofactors R K).biUnion
    (squareRootLowPrimeShallowBornSeatFiber R)

/-- Complete high-seat population at the shallow cutoff. -/
def squareRootLowPrimeShallowHighSeatAtoms
    (R K j : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeShallowHighCofactors R K).biUnion
    (squareRootLowPrimeShallowHighSeatFiber R K j)

/-- Born seats tagged as creation states. -/
def squareRootLowPrimeShallowBornCreationStates
    (R K : ℕ) : Finset SquareRootLowPrimeCreationState :=
  (squareRootLowPrimeShallowBornSeatAtoms R K).image fun z =>
    some (Sum.inl z)

/-- High seats tagged as creation states. -/
def squareRootLowPrimeShallowHighCreationStates
    (R K j : ℕ) : Finset SquareRootLowPrimeCreationState :=
  (squareRootLowPrimeShallowHighSeatAtoms R K j).image fun z =>
    some (Sum.inr z)

/-- Complete literal shallow creation carrier. -/
def squareRootLowPrimeCreationCarrierExact
    (R K j : ℕ) : Finset SquareRootLowPrimeCreationState :=
  insert none
    (squareRootLowPrimeShallowBornCreationStates R K ∪
      squareRootLowPrimeShallowHighCreationStates R K j)

/-- Complex signed weight of one shallow creation state. -/
def squareRootLowPrimeCreationWeightComplex :
    SquareRootLowPrimeCreationState → ℂ
  | none => 1
  | some (Sum.inl z) => -canonicalMoebiusWeight z.1
  | some (Sum.inr z) => -canonicalMoebiusWeight z.1

/-- Ordered real weight of one shallow creation state. -/
def squareRootLowPrimeCreationWeightReal
    (x : SquareRootLowPrimeCreationState) : ℝ :=
  (squareRootLowPrimeCreationWeightComplex x).re

/-- Real signed weight of one deep response atom. -/
def squareRootLowPrimeResponseAtomWeightReal
    (z : ℕ × ℕ) : ℝ :=
  (canonicalMoebiusWeight (squareRootLowPrimeBadAtomChild z)).re

@[simp] theorem mem_squareRootLowPrimeShallowBornSeatFiber
    {R c : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeShallowBornSeatFiber R c ↔
      z.1 = c ∧ z.2 < squareRootBornPartnerCount R c := by
  rcases z with ⟨z1, z2⟩
  simp [squareRootLowPrimeShallowBornSeatFiber, eq_comm, and_comm]

@[simp] theorem mem_squareRootLowPrimeShallowHighSeatFiber
    {R K j c : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeShallowHighSeatFiber R K j c ↔
      z.1 = c ∧ z.2 < squareRootBornPostTailHighResponse R K j c := by
  rcases z with ⟨z1, z2⟩
  simp [squareRootLowPrimeShallowHighSeatFiber, eq_comm, and_comm]

/-- Born seat fibres over different cofactors are disjoint. -/
theorem squareRootLowPrimeShallowBornSeatFiber_pairwiseDisjoint
    (R K : ℕ) :
    Set.PairwiseDisjoint
      (↑(squareRootLowPrimeShallowBornCofactors R K))
      (squareRootLowPrimeShallowBornSeatFiber R) := by
  intro c _hc d _hd hcd
  change Disjoint
    (squareRootLowPrimeShallowBornSeatFiber R c)
    (squareRootLowPrimeShallowBornSeatFiber R d)
  rw [Finset.disjoint_left]
  intro z hzc hzd
  exact hcd
    ((mem_squareRootLowPrimeShallowBornSeatFiber.mp hzc).1.symm.trans
      (mem_squareRootLowPrimeShallowBornSeatFiber.mp hzd).1)

/-- High seat fibres over different cofactors are disjoint. -/
theorem squareRootLowPrimeShallowHighSeatFiber_pairwiseDisjoint
    (R K j : ℕ) :
    Set.PairwiseDisjoint
      (↑(squareRootLowPrimeShallowHighCofactors R K))
      (squareRootLowPrimeShallowHighSeatFiber R K j) := by
  intro c _hc d _hd hcd
  change Disjoint
    (squareRootLowPrimeShallowHighSeatFiber R K j c)
    (squareRootLowPrimeShallowHighSeatFiber R K j d)
  rw [Finset.disjoint_left]
  intro z hzc hzd
  exact hcd
    ((mem_squareRootLowPrimeShallowHighSeatFiber.mp hzc).1.symm.trans
      (mem_squareRootLowPrimeShallowHighSeatFiber.mp hzd).1)

/-- Signed mass of one born-seat fibre. -/
theorem squareRootLowPrimeShallowBornSeatFiber_weight_sum
    (R c : ℕ) :
    (∑ z ∈ squareRootLowPrimeShallowBornSeatFiber R c,
      -canonicalMoebiusWeight z.1) =
      -canonicalMoebiusWeight c *
        (squareRootBornPartnerCount R c : ℂ) := by
  unfold squareRootLowPrimeShallowBornSeatFiber
  simp
  ring

/-- Signed mass of one high-seat fibre. -/
theorem squareRootLowPrimeShallowHighSeatFiber_weight_sum
    (R K j c : ℕ) :
    (∑ z ∈ squareRootLowPrimeShallowHighSeatFiber R K j c,
      -canonicalMoebiusWeight z.1) =
      -canonicalMoebiusWeight c *
        (squareRootBornPostTailHighResponse R K j c : ℂ) := by
  unfold squareRootLowPrimeShallowHighSeatFiber
  simp
  ring

/-- Signed mass of all shallow born seats. -/
theorem squareRootLowPrimeShallowBornSeatAtoms_weight_sum
    (R K : ℕ) :
    (∑ z ∈ squareRootLowPrimeShallowBornSeatAtoms R K,
      -canonicalMoebiusWeight z.1) =
      ∑ c ∈ squareRootLowPrimeShallowBornCofactors R K,
        -canonicalMoebiusWeight c *
          (squareRootBornPartnerCount R c : ℂ) := by
  unfold squareRootLowPrimeShallowBornSeatAtoms
  rw [Finset.sum_biUnion
    (squareRootLowPrimeShallowBornSeatFiber_pairwiseDisjoint R K)]
  apply Finset.sum_congr rfl
  intro c _hc
  exact squareRootLowPrimeShallowBornSeatFiber_weight_sum R c

/-- Signed mass of all shallow high seats. -/
theorem squareRootLowPrimeShallowHighSeatAtoms_weight_sum
    (R K j : ℕ) :
    (∑ z ∈ squareRootLowPrimeShallowHighSeatAtoms R K j,
      -canonicalMoebiusWeight z.1) =
      ∑ c ∈ squareRootLowPrimeShallowHighCofactors R K,
        -canonicalMoebiusWeight c *
          (squareRootBornPostTailHighResponse R K j c : ℂ) := by
  unfold squareRootLowPrimeShallowHighSeatAtoms
  rw [Finset.sum_biUnion
    (squareRootLowPrimeShallowHighSeatFiber_pairwiseDisjoint R K j)]
  apply Finset.sum_congr rfl
  intro c _hc
  exact squareRootLowPrimeShallowHighSeatFiber_weight_sum R K j c

/-- The born and high tagged creation populations are disjoint. -/
theorem squareRootLowPrimeShallowBornCreationStates_disjoint_high
    (R K j : ℕ) :
    Disjoint (squareRootLowPrimeShallowBornCreationStates R K)
      (squareRootLowPrimeShallowHighCreationStates R K j) := by
  rw [Finset.disjoint_left]
  intro x hxBorn hxHigh
  rcases Finset.mem_image.mp hxBorn with ⟨z, _hz, rfl⟩
  rcases Finset.mem_image.mp hxHigh with ⟨w, _hw, hEq⟩
  cases hEq

/-- The distinguished head is not a tagged seat. -/
theorem none_not_mem_squareRootLowPrimeCreationSeats
    (R K j : ℕ) :
    none ∉ squareRootLowPrimeShallowBornCreationStates R K ∪
      squareRootLowPrimeShallowHighCreationStates R K j := by
  simp [squareRootLowPrimeShallowBornCreationStates,
    squareRootLowPrimeShallowHighCreationStates]

/-- Reindexing the born tagged states loses no signed mass. -/
theorem squareRootLowPrimeShallowBornCreationStates_weight_sum
    (R K : ℕ) :
    (∑ x ∈ squareRootLowPrimeShallowBornCreationStates R K,
      squareRootLowPrimeCreationWeightComplex x) =
      ∑ z ∈ squareRootLowPrimeShallowBornSeatAtoms R K,
        -canonicalMoebiusWeight z.1 := by
  unfold squareRootLowPrimeShallowBornCreationStates
  apply Finset.sum_image
  intro a _ha b _hb hab
  simpa using hab

/-- Reindexing the high tagged states loses no signed mass. -/
theorem squareRootLowPrimeShallowHighCreationStates_weight_sum
    (R K j : ℕ) :
    (∑ x ∈ squareRootLowPrimeShallowHighCreationStates R K j,
      squareRootLowPrimeCreationWeightComplex x) =
      ∑ z ∈ squareRootLowPrimeShallowHighSeatAtoms R K j,
        -canonicalMoebiusWeight z.1 := by
  unfold squareRootLowPrimeShallowHighCreationStates
  apply Finset.sum_image
  intro a _ha b _hb hab
  simpa using hab

private theorem shallowBornSeatMass_eq_neg_runningBorn
    (R K : ℕ) :
    (∑ c ∈ squareRootLowPrimeShallowBornCofactors R K,
      -canonicalMoebiusWeight c *
        (squareRootBornPartnerCount R c : ℂ)) =
      -(∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        if canonicalLargestPrimeFactor c ≤ K then
          canonicalMoebiusWeight c *
            (squareRootBornPartnerCount R c : ℂ)
        else 0) := by
  unfold squareRootLowPrimeShallowBornCofactors
  rw [Finset.sum_filter, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases hle : canonicalLargestPrimeFactor c ≤ K
  · by_cases hmu : μ c = 0
    · simp [hle, hmu, canonicalMoebiusWeight]
    · simp [hle, hmu]
  · simp [hle]

private theorem shallowHighSeatMass_eq_neg_runningHigh
    (R K j : ℕ) :
    (∑ c ∈ squareRootLowPrimeShallowHighCofactors R K,
      -canonicalMoebiusWeight c *
        (squareRootBornPostTailHighResponse R K j c : ℂ)) =
      -(∑ c ∈ Finset.Icc 1 (R - 1),
        if canonicalLargestPrimeFactor c ≤ K then
          canonicalMoebiusWeight c *
            (squareRootBornPostTailHighResponse R K j c : ℂ)
        else 0) := by
  unfold squareRootLowPrimeShallowHighCofactors
  rw [Finset.sum_filter, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases hle : canonicalLargestPrimeFactor c ≤ K
  · by_cases hmu : μ c = 0
    · simp [hle, hmu, canonicalMoebiusWeight]
    · simp [hle, hmu]
  · simp [hle]

/-- **The literal channel-faithful creation carrier has mass exactly `T(K)`.** -/
theorem squareRootLowPrimeCreationCarrierExact_weight_sum
    (R K j : ℕ) :
    (∑ x ∈ squareRootLowPrimeCreationCarrierExact R K j,
      squareRootLowPrimeCreationWeightComplex x) =
      squareRootLowPrimeRunningImbalance R K j K := by
  unfold squareRootLowPrimeCreationCarrierExact
  rw [Finset.sum_insert
      (none_not_mem_squareRootLowPrimeCreationSeats R K j),
    Finset.sum_union
      (squareRootLowPrimeShallowBornCreationStates_disjoint_high R K j),
    squareRootLowPrimeShallowBornCreationStates_weight_sum,
    squareRootLowPrimeShallowHighCreationStates_weight_sum,
    squareRootLowPrimeShallowBornSeatAtoms_weight_sum,
    squareRootLowPrimeShallowHighSeatAtoms_weight_sum,
    shallowBornSeatMass_eq_neg_runningBorn,
    shallowHighSeatMass_eq_neg_runningHigh]
  unfold squareRootLowPrimeCreationWeightComplex
    squareRootLowPrimeRunningImbalance
    squareRootBornPostTailRunningLowPrimeResponse
  ring

/-- Real form of the exact shallow creation representation. -/
theorem squareRootLowPrimeCreationCarrierExact_realWeight_sum
    (R K j : ℕ) :
    (∑ x ∈ squareRootLowPrimeCreationCarrierExact R K j,
      squareRootLowPrimeCreationWeightReal x) =
      squareRootLowPrimeRunningImbalanceReal R K j K := by
  have h := congrArg Complex.re
    (squareRootLowPrimeCreationCarrierExact_weight_sum R K j)
  simpa [squareRootLowPrimeCreationWeightReal,
    squareRootLowPrimeRunningImbalanceReal] using h

/-- Every shallow creation state has real weight of absolute value at most one. -/
theorem abs_squareRootLowPrimeCreationWeightReal_le_one
    (x : SquareRootLowPrimeCreationState) :
    |squareRootLowPrimeCreationWeightReal x| ≤ 1 := by
  rcases x with _ | x
  · simp [squareRootLowPrimeCreationWeightReal,
      squareRootLowPrimeCreationWeightComplex]
  · rcases x with z | z
    · simp [squareRootLowPrimeCreationWeightReal,
        squareRootLowPrimeCreationWeightComplex, canonicalMoebiusWeight]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := z.1)
    · simp [squareRootLowPrimeCreationWeightReal,
        squareRootLowPrimeCreationWeightComplex, canonicalMoebiusWeight]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := z.1)

/-- The literal response-atom carrier has mass exactly the negative deep
increment sum. -/
theorem squareRootLowPrimeOwnedResponseAtoms_realWeight_sum
    {R K j U : ℕ} (hR : 2 ≤ R) (hUR : U < R) :
    (∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
      squareRootLowPrimeResponseAtomWeightReal z) =
      -(∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p) := by
  have h := congrArg Complex.re
    (squareRootLowPrimeFreshIncrement_sum_eq_neg_ownedResponseAtomChildMass
      (R := R) (K := K) (j := j) (U := U) hR hUR)
  have hre :
      (∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p) =
        -(∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
          squareRootLowPrimeResponseAtomWeightReal z) := by
    simpa [squareRootLowPrimeResponseAtomWeightReal,
      squareRootLowPrimeFreshIncrementReal] using h
  linarith

/-- Every deep response atom has real weight of absolute value at most one. -/
theorem abs_squareRootLowPrimeResponseAtomWeightReal_le_one
    (z : ℕ × ℕ) :
    |squareRootLowPrimeResponseAtomWeightReal z| ≤ 1 := by
  simp [squareRootLowPrimeResponseAtomWeightReal,
    canonicalMoebiusWeight]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

end RHLean.Proof
