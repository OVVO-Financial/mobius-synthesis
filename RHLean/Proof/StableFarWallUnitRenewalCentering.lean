import RHLean.Proof.StableFarWallCrossingRenewal

/-!
# Center the complete stable-far renewal on its physical homes

The nonunit strict-crossing renewal has already been reduced to one generation:
a return with cofactor `d>1` lands in the existing descended child carrier at
`P+(d)` and carries the opposite child sign.  The only crossing returns not in
that recurrence have `d=1`.  They return to the literal far-prime unit state
`(1,p)`.

This file centers that terminal sector as well.  Every unit crossing occurrence
is regrouped by its far prime `p`; the existing unit-face terminal carrier
supplies exactly one baseline copy of the same prime.  Hence

  unitRenewal + unitTerminal = sum_p (multiplicity(p) - 1).

Combining this with the nonunit result gives a two-level centered incidence
normal form for the complete child-far / crossing-renewal / far-unit packet,
with all owner multiplicities retained and no norm taken.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Strict crossings whose returned cofactor is already terminal. -/
def lowWheelFarPrimeQ2UnitCrossingTriples (R : ℕ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (lowWheelFarPrimeQ2CrossingTriples R).filter fun t => t.2.1 = 1

/-- The strict crossing carrier is exactly the disjoint union of unit returns
and nonunit one-generation returns. -/
theorem lowWheelFarPrimeQ2CrossingTriples_eq_unit_union_nonUnit (R : ℕ) :
    lowWheelFarPrimeQ2CrossingTriples R =
      lowWheelFarPrimeQ2UnitCrossingTriples R ∪
        lowWheelFarPrimeQ2NonUnitCrossingTriples R := by
  ext t
  constructor
  · intro ht
    have hbase : t ∈ lowWheelFarPrimeLowCofactorTriples R :=
      (Finset.mem_filter.mp ht).1
    rcases lowWheelFarPrimeLowCofactorTriple_data hbase with
      ⟨_hq, _hqR, hd1, _hp, _hpR, _hsq, _hrough, _hcut⟩
    by_cases hdone : t.2.1 = 1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht, hdone⟩)
    · have hdgt : 1 < t.2.1 := lt_of_le_of_ne hd1 (Ne.symm hdone)
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht, hdgt⟩)
  · intro ht
    rcases Finset.mem_union.mp ht with hu | hn
    · exact (Finset.mem_filter.mp hu).1
    · exact (Finset.mem_filter.mp hn).1

/-- Unit and nonunit returns are genuinely disjoint. -/
theorem lowWheelFarPrimeQ2UnitCrossing_disjoint_nonUnit (R : ℕ) :
    Disjoint (lowWheelFarPrimeQ2UnitCrossingTriples R)
      (lowWheelFarPrimeQ2NonUnitCrossingTriples R) := by
  rw [Finset.disjoint_left]
  intro t hu hn
  have h1 := (Finset.mem_filter.mp hu).2
  have hgt := (Finset.mem_filter.mp hn).2
  omega

/-- Complete crossing-renewal mass indexed by the original crossing triples. -/
def lowWheelFarPrimeQ2ReturnedRenewalMass (R : ℕ) : ℂ :=
  ∑ t ∈ lowWheelFarPrimeQ2CrossingTriples R,
    lowWheelFullTaggedPhysicalWeight ((∅ : Finset ℕ), (t.2.1, t.2.2))

/-- Unit-return part of the crossing renewal. -/
def lowWheelFarPrimeQ2UnitReturnedRenewalMass (R : ℕ) : ℂ :=
  ∑ t ∈ lowWheelFarPrimeQ2UnitCrossingTriples R,
    lowWheelFullTaggedPhysicalWeight ((∅ : Finset ℕ), (t.2.1, t.2.2))

/-- The product-carrier renewal used by the final parent reduction is exactly
the original triple-indexed renewal mass. -/
theorem lowWheelFarPrimeCrossingStableMass_eq_returnedRenewalMass (R : ℕ) :
    (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        lowWheelFullTaggedPhysicalWeight
          (lowWheelFarPrimeCrossingStableState x)) =
      lowWheelFarPrimeQ2ReturnedRenewalMass R := by
  unfold lowWheelFarPrimeCrossingProductCarrier
    lowWheelFarPrimeQ2ReturnedRenewalMass
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    have hbase : t ∈ lowWheelFarPrimeLowCofactorTriples R :=
      (Finset.mem_filter.mp ht).1
    have hcoords := lowWheelFarPrimeProduct_coordinates hbase
    have hlpf :
        canonicalLargestPrimeFactor (t.2.1 * t.2.2) = t.2.2 := by
      simpa [lowWheelFarPrimeProductKey] using hcoords.1
    have hcof : canonicalCofactor (t.2.1 * t.2.2) = t.2.1 := by
      simpa [lowWheelFarPrimeProductKey] using hcoords.2
    unfold lowWheelFarPrimeCrossingStableState lowWheelFarPrimeProductKey
    rw [hlpf, hcof]
  · intro a ha b hb hab
    exact lowWheelFarPrimeProductKey_injOn R
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab

/-- Exact unit/nonunit split of the complete renewal mass. -/
theorem lowWheelFarPrimeQ2ReturnedRenewalMass_eq_unit_add_nonUnit (R : ℕ) :
    lowWheelFarPrimeQ2ReturnedRenewalMass R =
      lowWheelFarPrimeQ2UnitReturnedRenewalMass R +
        lowWheelFarPrimeQ2NonUnitReturnedRenewalMass R := by
  unfold lowWheelFarPrimeQ2ReturnedRenewalMass
    lowWheelFarPrimeQ2UnitReturnedRenewalMass
    lowWheelFarPrimeQ2NonUnitReturnedRenewalMass
  rw [lowWheelFarPrimeQ2CrossingTriples_eq_unit_union_nonUnit R,
    Finset.sum_union (lowWheelFarPrimeQ2UnitCrossing_disjoint_nonUnit R)]

/-- A unit crossing returns with literal weight `+1`. -/
theorem lowWheelFarPrimeQ2UnitCrossing_returnedWeight_eq_one
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeQ2UnitCrossingTriples R) :
    lowWheelFullTaggedPhysicalWeight
        ((∅ : Finset ℕ), (t.2.1, t.2.2)) = 1 := by
  have h1 := (Finset.mem_filter.mp ht).2
  rw [h1]
  simp [lowWheelFullTaggedPhysicalWeight, canonicalMoebiusWeight,
    booleanCubeSign]

/-- The far prime of every unit crossing is already one of the literal far unit
terminal products. -/
theorem lowWheelFarPrimeQ2UnitCrossing_prime_mem_unitProducts
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeQ2UnitCrossingTriples R) :
    t.2.2 ∈ lowWheelFarPrimeUnitProducts R := by
  have hcross := (Finset.mem_filter.mp ht).1
  have h1 := (Finset.mem_filter.mp ht).2
  have hbase : t ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hcross).1
  rcases lowWheelFarPrimeLowCofactorTriple_data hbase with
    ⟨hq, hqR, _hd1, hp, hpR, _hsq, _hrough, hcut⟩
  have hR1 : 1 < R := by omega
  have hpX : t.2.2 ≤ squareRootEndpoint R := by
    have hq1 : 1 ≤ t.1 := hq.one_le
    have hle : t.2.2 ≤ t.1 * t.2.2 := by
      simpa using Nat.mul_le_mul_right t.2.2 hq1
    have hqp : t.1 * t.2.2 ≤ squareRootEndpoint R := by
      simpa [h1] using hcut
    exact hle.trans hqp
  have hpair : (1, t.2.2) ∈ lowWheelFarPrimePairSet R := by
    apply mem_lowWheelFarPrimePairSet.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨by norm_num, hR1⟩,
      Finset.mem_Icc.mpr ⟨hpR, hpX⟩, hp, ?_⟩
    simpa using hpX
  have hsqPair : (1, t.2.2) ∈ lowWheelFarPrimeSquarefreePairSet R :=
    mem_lowWheelFarPrimeSquarefreePairSet.mpr ⟨hpair, by simp⟩
  have hunit : (1, t.2.2) ∈ lowWheelFarPrimeUnitPairSet R :=
    Finset.mem_filter.mpr ⟨hsqPair, rfl⟩
  exact Finset.mem_image.mpr ⟨(1, t.2.2), hunit, rfl⟩

/-- Number of unit crossing owners returning to one far prime. -/
def lowWheelFarPrimeQ2UnitCrossingMultiplicity (R p : ℕ) : ℕ :=
  ((lowWheelFarPrimeQ2UnitCrossingTriples R).filter fun t => t.2.2 = p).card

/-- Finite Fubini of unit returns onto their far-prime homes. -/
theorem lowWheelFarPrimeQ2UnitReturnedRenewalMass_eq_multiplicity (R : ℕ) :
    lowWheelFarPrimeQ2UnitReturnedRenewalMass R =
      ∑ p ∈ lowWheelFarPrimeUnitProducts R,
        (lowWheelFarPrimeQ2UnitCrossingMultiplicity R p : ℂ) := by
  have hmaps : ∀ t ∈ lowWheelFarPrimeQ2UnitCrossingTriples R,
      t.2.2 ∈ lowWheelFarPrimeUnitProducts R := by
    intro t ht
    exact lowWheelFarPrimeQ2UnitCrossing_prime_mem_unitProducts ht
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := lowWheelFarPrimeQ2UnitCrossingTriples R)
    (t := lowWheelFarPrimeUnitProducts R)
    (g := fun t : ℕ × (ℕ × ℕ) => t.2.2) hmaps
    (fun t => lowWheelFullTaggedPhysicalWeight
      ((∅ : Finset ℕ), (t.2.1, t.2.2)))
  unfold lowWheelFarPrimeQ2UnitReturnedRenewalMass
  rw [hfiber.symm]
  apply Finset.sum_congr rfl
  intro p hp
  calc
    (∑ t ∈ lowWheelFarPrimeQ2UnitCrossingTriples R with t.2.2 = p,
        lowWheelFullTaggedPhysicalWeight
          ((∅ : Finset ℕ), (t.2.1, t.2.2))) =
      ∑ _t ∈ (lowWheelFarPrimeQ2UnitCrossingTriples R).filter
          (fun t => t.2.2 = p), (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact lowWheelFarPrimeQ2UnitCrossing_returnedWeight_eq_one
          (Finset.mem_filter.mp ht).1
    _ = (lowWheelFarPrimeQ2UnitCrossingMultiplicity R p : ℂ) := by
      simp [lowWheelFarPrimeQ2UnitCrossingMultiplicity]

/-- The far unit terminal product itself has weight `-1`. -/
theorem lowWheelFarPrimeUnitProduct_weight_eq_neg_one
    {R p : ℕ} (hp : p ∈ lowWheelFarPrimeUnitProducts R) :
    canonicalMoebiusWeight p = -1 := by
  have hpPrime := (lowWheelFarPrimeUnitProduct_prime_far hp).1
  unfold canonicalMoebiusWeight
  rw [ArithmeticFunction.moebius_apply_prime hpPrime]
  norm_num

/-- **Centered unit incidence.**  The unit renewal occurrences and the one
existing terminal copy leave exactly `multiplicity - 1` at each far prime. -/
theorem lowWheelFarPrimeQ2UnitRenewal_add_unitTerminal_eq_centeredMultiplicity
    (R : ℕ) :
    lowWheelFarPrimeQ2UnitReturnedRenewalMass R +
        (∑ p ∈ lowWheelFarPrimeUnitProducts R, canonicalMoebiusWeight p) =
      ∑ p ∈ lowWheelFarPrimeUnitProducts R,
        ((lowWheelFarPrimeQ2UnitCrossingMultiplicity R p : ℂ) - 1) := by
  rw [lowWheelFarPrimeQ2UnitReturnedRenewalMass_eq_multiplicity]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [lowWheelFarPrimeUnitProduct_weight_eq_neg_one hp]
  ring

/-- **Two-level centered incidence normal form.**  The whole child-far packet,
all strict crossing returns, and the far-prime unit terminal baseline reduce to
one centered multiplicity field on descended children plus one centered
multiplicity field on unit far primes. -/
theorem lowWheelFarPrimeChildFar_add_crossingRenewal_add_unitTerminal_eq_centered
    (R : ℕ) :
    (∑ q ∈ primesUpTo (R - 1),
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1) +
      (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        lowWheelFullTaggedPhysicalWeight
          (lowWheelFarPrimeCrossingStableState x)) +
      (∑ p ∈ lowWheelFarPrimeUnitProducts R, canonicalMoebiusWeight p) =
    (∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
      (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ)) *
        canonicalMoebiusWeight y.2.1) +
      ∑ p ∈ lowWheelFarPrimeUnitProducts R,
        ((lowWheelFarPrimeQ2UnitCrossingMultiplicity R p : ℂ) - 1) := by
  rw [lowWheelFarPrimeCrossingStableMass_eq_returnedRenewalMass,
    lowWheelFarPrimeQ2ReturnedRenewalMass_eq_unit_add_nonUnit]
  have hnon :=
    lowWheelFarPrimeChildFarSlices_add_nonUnitRenewal_eq_centeredMultiplicity R
  have hunit :=
    lowWheelFarPrimeQ2UnitRenewal_add_unitTerminal_eq_centeredMultiplicity R
  linear_combination hnon + hunit

end RHLean.Proof
