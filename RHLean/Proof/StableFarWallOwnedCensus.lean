import RHLean.Proof.StableFarWallSignedReassembly

/-!
# The unit face and both owned images on one arithmetic carrier

The internal terminal mate and frozen top image have the true Möbius weight
of their original ordered Euler-cut child.  Those children are injective
across both populations, not merely within either image.  All their primes
are at most the root, so they are disjoint from the far unit primes.

Thus `UnitFace - InternalMate - TopImage` is the negative Möbius mass of one
literal disjoint integer carrier.  Combining it with the true crossing
products gives the joint signed boundary census before any norm.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open FrozenCofactorTopBottom LowWheelCanonicalDowncrossOwnership

attribute [local instance] Classical.propDecidable

/-- The ordered-cut bridge also includes frozen terminal sources. -/
theorem lowWheelCanonicalRepeatedFrozen_mem_orderedEulerCutCarrier
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenPart R) :
    y ∈ orderedEulerCutCarrier R := by
  have hrepeated := (Finset.mem_filter.mp hy).1
  have hshape := (Finset.mem_filter.mp hy).2
  have htagged := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged with ⟨ht, hx⟩
  have hp := (lowWheelCanonicalDowncrossPart_adjacent_shell hx).1
  have hquot : y.2.2 / lowWheelCanonicalDowncrossPivot y.2 = 1 := by
    change y.2.2 / lowWheelTaggedDowncrossPivot y = 1
    rw [hshape.1]
    exact Nat.div_self hp.pos
  have hparent :
      LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossParent y.1 y.2 =
        primeFaceProduct y.1 := by
    unfold LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossParent
    rw [hquot, Nat.mul_one]
  apply mem_orderedEulerCutCarrier.mpr
  refine ⟨ht, mem_lowWheelCanonicalDowncrossOrientedPart.mpr ⟨hx, ?_⟩⟩
  intro r hr
  rw [hparent] at hr
  have hrData := Nat.mem_primeFactors.mp hr
  have hrDvd : r ∣ y.1.prod id := by simpa [primeFaceProduct] using hrData.2.1
  rcases (Prime.dvd_finset_prod_iff hrData.1.prime id).mp hrDvd with ⟨s, hs, hrs⟩
  have hsPrime := prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hs)
  have heq : r = s := (Nat.prime_dvd_prime_iff_eq hrData.1 hsPrime).mp hrs
  subst r
  exact hshape.2 s hs

/-- Original sources of the two owned physical images. -/
def lowWheelFrozenTopFarOwnedSources (R : ℕ) : Finset LowWheelTaggedDowncrossState :=
  lowWheelCanonicalRepeatedTerminalInternalPart R ∪
    lowWheelCanonicalRepeatedFrozenCofactorPart R

theorem lowWheelFrozenTopFarOwnedSources_disjoint (R : ℕ) :
    Disjoint (lowWheelCanonicalRepeatedTerminalInternalPart R)
      (lowWheelCanonicalRepeatedFrozenCofactorPart R) := by
  rw [Finset.disjoint_left]
  intro y hi hc
  have hone := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  have hgt := (Finset.mem_filter.mp hc).2
  omega

theorem lowWheelFrozenTopFarOwnedSource_mem_orderedEulerCutCarrier
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelFrozenTopFarOwnedSources R) :
    y ∈ orderedEulerCutCarrier R := by
  apply lowWheelCanonicalRepeatedFrozen_mem_orderedEulerCutCarrier
  rcases Finset.mem_union.mp hy with hi | hc
  · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  · exact (Finset.mem_filter.mp hc).1

/-- The two images share one multiplicity-free child-integer carrier. -/
def lowWheelFrozenTopFarOwnedProducts (R : ℕ) : Finset ℕ :=
  (lowWheelFrozenTopFarOwnedSources R).image orderedEulerCutChildInteger

theorem lowWheelFrozenTopFarOwnedProducts_sum
    {M : Type*} [AddCommMonoid M] (R : ℕ) (f : ℕ → M) :
    (∑ n ∈ lowWheelFrozenTopFarOwnedProducts R, f n) =
      ∑ y ∈ lowWheelFrozenTopFarOwnedSources R, f (orderedEulerCutChildInteger y) := by
  unfold lowWheelFrozenTopFarOwnedProducts
  apply Finset.sum_image
  intro a ha b hb hab
  exact orderedEulerCutChildInteger_injective_on_carrier
    (lowWheelFrozenTopFarOwnedSource_mem_orderedEulerCutCarrier ha)
    (lowWheelFrozenTopFarOwnedSource_mem_orderedEulerCutCarrier hb) hab

theorem lowWheelFrozenTopFarOwnedSources_mass_eq_neg_products (R : ℕ) :
    (∑ y ∈ lowWheelFrozenTopFarOwnedSources R, lowWheelTaggedDowncrossWeight y) =
      -∑ n ∈ lowWheelFrozenTopFarOwnedProducts R, canonicalMoebiusWeight n := by
  rw [lowWheelFrozenTopFarOwnedProducts_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  have h := orderedEulerCutChildWeight_eq_neg
    (orderedEulerCutShape_of_mem_carrier
      (lowWheelFrozenTopFarOwnedSource_mem_orderedEulerCutCarrier hy))
  change orderedEulerCutWeight y = -canonicalMoebiusWeight (orderedEulerCutChildInteger y)
  rw [h, neg_neg]

/-- Exact joint parity and no-multiplicity completion of both owned images. -/
theorem lowWheelInternalMate_add_topImage_eq_ownedProductMass (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalMateLedger R +
        lowWheelFrozenCofactorTopImageLedger R =
      ∑ n ∈ lowWheelFrozenTopFarOwnedProducts R, canonicalMoebiusWeight n := by
  have hi := sum_lowWheelCanonicalRepeatedTerminalInternal_add_mate_eq_zero R
  have ht := lowWheelFrozenCofactorTopImageLedger_eq_neg R
  unfold lowWheelCanonicalFrozenCofactorLedger at ht
  have hs := lowWheelFrozenTopFarOwnedSources_mass_eq_neg_products R
  unfold lowWheelFrozenTopFarOwnedSources at hs
  rw [Finset.sum_union (lowWheelFrozenTopFarOwnedSources_disjoint R)] at hs
  linear_combination hi + ht - hs

/-- Every owned product is smooth through the original inclusive root. -/
theorem lowWheelFrozenTopFarOwnedProduct_largestPrime_le_root
    {R n : ℕ} (hn : n ∈ lowWheelFrozenTopFarOwnedProducts R) :
    canonicalLargestPrimeFactor n ≤ R := by
  rcases Finset.mem_image.mp hn with ⟨y, hy, rfl⟩
  rcases Finset.mem_union.mp hy with hi | hc
  · have hterminal := (Finset.mem_filter.mp hi).1
    have hg := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
    have hs := orderedEulerCutShape_of_mem_carrier
      (lowWheelFrozenTopFarOwnedSource_mem_orderedEulerCutCarrier
        (Finset.mem_union_left _ hi))
    have hpred : y.1 ∈ (primesUpTo (y.2.2 - 1)).powerset := by
      apply Finset.mem_powerset.mpr
      intro r hr
      have hd := hs.2.2.2.2.1 r hr
      exact mem_primesUpTo.mpr ⟨hd.1, by omega⟩
    have hnot : y.2.2 ∉ y.1 := by
      intro h
      exact (Nat.lt_irrefl _) (hs.2.2.2.2.1 _ h).2
    have hchild : orderedEulerCutChildInteger y =
        primeFaceProduct (insert y.2.2 y.1) := by
      simp [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
        orderedEulerCutPivot, orderedEulerCutLowProduct, hg.1,
        primeFaceProduct, hnot]
    rw [hchild, canonicalLargestPrimeFactor_insert_freshPrime hs.1 hpred]
    have hle := (Finset.mem_filter.mp hi).2
    exact hg.2.1.trans_le hle
  · rw [← lowWheelFrozenCofactorTopPrime_eq_childLargest hc]
    exact (lowWheelFrozenCofactorTopPrime_lt_root hc).le

/-- Far unit primes, without their redundant cofactor-one tag. -/
def lowWheelFarPrimeUnitProducts (R : ℕ) : Finset ℕ :=
  (lowWheelFarPrimeUnitPairSet R).image Prod.snd

theorem lowWheelFarPrimeUnitProduct_prime_far
    {R p : ℕ} (hp : p ∈ lowWheelFarPrimeUnitProducts R) :
    p.Prime ∧ R + 8 ≤ p := by
  rcases Finset.mem_image.mp hp with ⟨⟨c,p⟩, hcp, rfl⟩
  have hd := mem_lowWheelFarPrimePairSet.mp
    (mem_lowWheelFarPrimeSquarefreePairSet.mp (Finset.mem_filter.mp hcp).1).1
  exact ⟨hd.2.2.1, (Finset.mem_Icc.mp hd.2.1).1⟩

theorem lowWheelFarPrimeUnitFaceMass_eq_neg_productMass (R : ℕ) :
    lowWheelFarPrimeUnitFaceMass R =
      -∑ p ∈ lowWheelFarPrimeUnitProducts R, canonicalMoebiusWeight p := by
  unfold lowWheelFarPrimeUnitFaceMass lowWheelFarPrimeUnitProducts
  rw [Finset.sum_image]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro cp hcp
    have hc1 := (Finset.mem_filter.mp hcp).2
    have hp := (mem_lowWheelFarPrimePairSet.mp
      (mem_lowWheelFarPrimeSquarefreePairSet.mp (Finset.mem_filter.mp hcp).1).1).2.2.1
    simp [canonicalMoebiusWeight, hc1, ArithmeticFunction.moebius_apply_prime hp]
  · intro a ha b hb hab
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab

theorem lowWheelFarPrimeUnitProducts_disjoint_owned (R : ℕ) :
    Disjoint (lowWheelFarPrimeUnitProducts R) (lowWheelFrozenTopFarOwnedProducts R) := by
  rw [Finset.disjoint_left]
  intro p hp ho
  have hd := lowWheelFarPrimeUnitProduct_prime_far hp
  have hl := lowWheelFrozenTopFarOwnedProduct_largestPrime_le_root ho
  have hfac : canonicalLargestPrimeFactor p = p := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      (by norm_num : 0 < (1 : ℕ)) hd.1 (by
        simpa [canonicalLargestPrimeFactor] using hd.1.one_lt)
    simpa using h
  rw [hfac] at hl
  omega

/-- The disjoint arithmetic census of the unit face and both owned images. -/
def lowWheelFarWallTerminalProducts (R : ℕ) : Finset ℕ :=
  lowWheelFarPrimeUnitProducts R ∪ lowWheelFrozenTopFarOwnedProducts R

/-- Three physical terms reassemble into one true Möbius carrier. -/
theorem lowWheelFarPrimeUnit_sub_internalMate_sub_top_eq_neg_terminalMass (R : ℕ) :
    lowWheelFarPrimeUnitFaceMass R -
        lowWheelCanonicalRepeatedTerminalInternalMateLedger R -
        lowWheelFrozenCofactorTopImageLedger R =
      -∑ n ∈ lowWheelFarWallTerminalProducts R, canonicalMoebiusWeight n := by
  rw [sub_sub, lowWheelInternalMate_add_topImage_eq_ownedProductMass,
    lowWheelFarPrimeUnitFaceMass_eq_neg_productMass]
  unfold lowWheelFarWallTerminalProducts
  rw [Finset.sum_union (lowWheelFarPrimeUnitProducts_disjoint_owned R)]
  ring

/-- **Joint boundary reassembly.** All four previously separate nonrecursive
terms are now the signed difference of crossing products and terminal products.
The square-owner tag on crossing products is still present. -/
theorem lowWheelFarWall_remainingBoundary_eq_signed_products (R : ℕ) :
    lowWheelFarPrimeUnitFaceMass R - lowWheelFarPrimeQ2CrossingMass R -
        lowWheelCanonicalRepeatedTerminalInternalMateLedger R -
        lowWheelFrozenCofactorTopImageLedger R =
      (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R, canonicalMoebiusWeight x.2) -
        ∑ n ∈ lowWheelFarWallTerminalProducts R, canonicalMoebiusWeight n := by
  have h := lowWheelFarPrimeUnit_sub_internalMate_sub_top_eq_neg_terminalMass R
  rw [lowWheelFarPrimeQ2CrossingMass_eq_neg_productMass]
  linear_combination h

/-- The complete hard residual with the descended packet still attached. -/
theorem lowWheelFrozenTopFarResidual_eq_descended_add_crossing_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      (∑ x ∈ lowWheelFarPrimeDescendedProductCarrier R, canonicalMoebiusWeight x.2) +
      (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R, canonicalMoebiusWeight x.2) -
        ∑ n ∈ lowWheelFarWallTerminalProducts R, canonicalMoebiusWeight n := by
  have h := lowWheelFarWall_remainingBoundary_eq_signed_products R
  rw [lowWheelFrozenTopFarResidual_eq_unit_sub_descended_sub_crossing_sub_owned R hR,
    lowWheelFarPrimeQ2DescendedMass_eq_neg_productMass]
  linear_combination h

/-- The integer homes on which the remaining four populations can interact. -/
def lowWheelFarWallBoundaryProductHomes (R : ℕ) : Finset ℕ :=
  (lowWheelFarPrimeCrossingProductCarrier R).image Prod.snd ∪
    lowWheelFarWallTerminalProducts R

/-- All crossing owners at a fixed integer, with their exact multiplicity. -/
def lowWheelFarWallCrossingMultiplicity (R n : ℕ) : ℕ :=
  ((lowWheelFarPrimeCrossingProductCarrier R).filter fun x => x.2 = n).card

/-- Signed incidence after reassembling the crossing and terminal occurrences.
This is an integer difference, not truncated natural subtraction. -/
def lowWheelFarWallBoundaryCoefficient (R n : ℕ) : ℤ :=
  (lowWheelFarWallCrossingMultiplicity R n : ℤ) -
    if n ∈ lowWheelFarWallTerminalProducts R then 1 else 0

/-- Finite Fubini at the integer homes retains every crossing owner. -/
theorem lowWheelFarPrimeCrossingProduct_sum_eq_multiplicity (R : ℕ) :
    (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R, canonicalMoebiusWeight x.2) =
      ∑ n ∈ lowWheelFarWallBoundaryProductHomes R,
        (lowWheelFarWallCrossingMultiplicity R n : ℂ) * canonicalMoebiusWeight n := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := lowWheelFarPrimeCrossingProductCarrier R)
    (t := lowWheelFarWallBoundaryProductHomes R) (g := Prod.snd)
    (fun x hx => Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    (fun x => canonicalMoebiusWeight x.2)
  rw [← hf]
  apply Finset.sum_congr rfl
  intro n _hn
  calc
    (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R with x.2 = n,
        canonicalMoebiusWeight x.2) =
      ∑ _x ∈ (lowWheelFarPrimeCrossingProductCarrier R).filter (fun x => x.2 = n),
        canonicalMoebiusWeight n := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by simp [lowWheelFarWallCrossingMultiplicity]

private theorem terminalProducts_sum_eq_indicator (R : ℕ) :
    (∑ n ∈ lowWheelFarWallTerminalProducts R, canonicalMoebiusWeight n) =
      ∑ n ∈ lowWheelFarWallBoundaryProductHomes R,
        if n ∈ lowWheelFarWallTerminalProducts R then canonicalMoebiusWeight n else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    constructor
    · intro hn
      refine Finset.mem_filter.mpr ⟨?_, hn⟩
      exact Finset.mem_union_right _ hn
    · intro hn
      exact (Finset.mem_filter.mp hn).2
  · intro n _hn
    rfl

/-- **Signed reassembly before energy.**  The four-term boundary is one
Möbius sum whose integer coefficient has already subtracted every terminal
occurrence from its full crossing-owner fibre.  No norm, sign assumption,
unproved multiplicity-one substitution, or boundary estimate is used. -/
theorem lowWheelFarWall_remainingBoundary_eq_coefficient_sum (R : ℕ) :
    lowWheelFarPrimeUnitFaceMass R - lowWheelFarPrimeQ2CrossingMass R -
        lowWheelCanonicalRepeatedTerminalInternalMateLedger R -
        lowWheelFrozenCofactorTopImageLedger R =
      ∑ n ∈ lowWheelFarWallBoundaryProductHomes R,
        (lowWheelFarWallBoundaryCoefficient R n : ℂ) * canonicalMoebiusWeight n := by
  rw [lowWheelFarWall_remainingBoundary_eq_signed_products,
    lowWheelFarPrimeCrossingProduct_sum_eq_multiplicity, terminalProducts_sum_eq_indicator,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hn : n ∈ lowWheelFarWallTerminalProducts R
  · simp [lowWheelFarWallBoundaryCoefficient, hn, sub_mul]
  · simp [lowWheelFarWallBoundaryCoefficient, hn]

/-- Crossing products cannot also be either old owned image: they retain a
prime strictly beyond the inclusive root wheel. -/
theorem lowWheelFarPrimeCrossingProduct_not_owned
    {R : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    x.2 ∉ lowWheelFrozenTopFarOwnedProducts R := by
  rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
  intro ho
  have hfar := (lowWheelFarPrimeProduct_geometry (Finset.mem_filter.mp ht).1).2.2.2
  have hlow := lowWheelFrozenTopFarOwnedProduct_largestPrime_le_root ho
  omega

/-- The exact complement census: on a crossing fibre the subtracted terminal
occurrence is a unit far prime, and never an internal or top-image occurrence. -/
theorem lowWheelFarPrimeCrossingProduct_mem_terminal_iff_unit
    {R : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    x.2 ∈ lowWheelFarWallTerminalProducts R ↔ x.2 ∈ lowWheelFarPrimeUnitProducts R := by
  change x.2 ∈ lowWheelFarPrimeUnitProducts R ∪ lowWheelFrozenTopFarOwnedProducts R ↔ _
  simp only [Finset.mem_union, lowWheelFarPrimeCrossingProduct_not_owned hx, or_false]

/-- A unit far prime retains its full endpoint range after its redundant
cofactor-one coordinate is forgotten. -/
theorem lowWheelFarPrimeUnitProduct_data
    {R p : ℕ} (hp : p ∈ lowWheelFarPrimeUnitProducts R) :
    p.Prime ∧ R + 8 ≤ p ∧ p ≤ squareRootEndpoint R := by
  rcases Finset.mem_image.mp hp with ⟨⟨c,p⟩, hcp, rfl⟩
  have hpair := mem_lowWheelFarPrimePairSet.mp
    (mem_lowWheelFarPrimeSquarefreePairSet.mp (Finset.mem_filter.mp hcp).1).1
  have hpRange := Finset.mem_Icc.mp hpair.2.1
  exact ⟨hpair.2.2.1, hpRange.1, hpRange.2⟩

/-- **Every non-top unit prime has a genuine strict crossing owner.**
If `2*p ≤ X_R`, Bertrand applied to `floor(X_R/p)/2` supplies a prime `q`
with `q*p ≤ X_R < q^2*p`.  The resulting `(q,1,p)` is therefore an actual
member of the strict crossing carrier, not an auxiliary prime substitution. -/
theorem lowWheelFarPrimeUnitProduct_has_crossingOwner
    {R p : ℕ} (hp : p ∈ lowWheelFarPrimeUnitProducts R)
    (h2p : 2 * p ≤ squareRootEndpoint R) :
    ∃ q : ℕ, (q,p) ∈ lowWheelFarPrimeCrossingProductCarrier R := by
  rcases lowWheelFarPrimeUnitProduct_data hp with ⟨hpPrime, hpFar, _hpX⟩
  let n := squareRootEndpoint R / p
  let m := n / 2
  have hn2 : 2 ≤ n := by
    dsimp [n]
    exact (Nat.le_div_iff_mul_le hpPrime.pos).2 h2p
  have hm0 : m ≠ 0 := by
    dsimp [m]
    omega
  rcases Nat.bertrand m hm0 with ⟨q, hqPrime, hmq, hq2m⟩
  have hqN : q ≤ n := by
    dsimp [m] at hmq hq2m
    omega
  have hqXp : q * p ≤ squareRootEndpoint R := by
    apply (Nat.le_div_iff_mul_le hpPrime.pos).1
    simpa [n] using hqN
  have hRpos : 0 < R := by
    by_contra hnot
    have hR0 : R = 0 := by omega
    subst R
    simp [squareRootEndpoint] at h2p
    omega
  have hXltR2 : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hne : R ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.ne_of_gt hRpos)
    simpa [pow_two] using Nat.pred_lt hne
  have hRp : R ≤ p := by omega
  have hXltRp : squareRootEndpoint R < R * p :=
    hXltR2.trans_le (Nat.mul_le_mul_left R hRp)
  have hnR : n < R := by
    dsimp [n]
    exact (Nat.div_lt_iff_lt_mul hpPrime.pos).2 hXltRp
  have hqR : q < R := hqN.trans_lt hnR
  have hnlt2q : n < 2 * q := by
    dsimp [m] at hmq
    omega
  have h2qleqq : 2 * q ≤ q * q :=
    Nat.mul_le_mul_right q hqPrime.two_le
  have hnltqq : n < q * q := hnlt2q.trans_le h2qleqq
  have hcross : squareRootEndpoint R < (q * q) * p := by
    apply (Nat.div_lt_iff_lt_mul hpPrime.pos).1
    simpa [n] using hnltqq
  have htriple : (q,(1,p)) ∈ lowWheelFarPrimeLowCofactorTriples R := by
    apply lowWheelFarPrimeLowCofactorTriple_mem_of_data
    · exact hqPrime
    · exact hqR
    · norm_num
    · exact hpPrime
    · exact hpFar
    · norm_num
    · simpa [canonicalLargestPrimeFactor] using hqPrime.one_lt
    · simpa using hqXp
  have hcrossTriple : (q,(1,p)) ∈ lowWheelFarPrimeQ2CrossingTriples R := by
    apply Finset.mem_filter.mpr
    refine ⟨htriple, ?_⟩
    simpa [Nat.mul_assoc] using hcross
  refine ⟨q, Finset.mem_image.mpr ⟨(q,(1,p)), hcrossTriple, ?_⟩⟩
  simp [lowWheelFarPrimeProductKey]

/-- Hence deleting one crossing occurrence for every unit prime below the top
half is multiplicity-safe: the crossing fibre is provably nonempty. -/
theorem lowWheelFarWallCrossingMultiplicity_pos_of_unit_two_mul_le
    {R p : ℕ} (hp : p ∈ lowWheelFarPrimeUnitProducts R)
    (h2p : 2 * p ≤ squareRootEndpoint R) :
    0 < lowWheelFarWallCrossingMultiplicity R p := by
  rcases lowWheelFarPrimeUnitProduct_has_crossingOwner hp h2p with ⟨q, hq⟩
  unfold lowWheelFarWallCrossingMultiplicity
  apply Finset.card_pos.mpr
  exact ⟨(q,p), Finset.mem_filter.mpr ⟨hq, rfl⟩⟩

/-- Unit primes that have at least the dyadic room required for one crossing. -/
def lowWheelFarPrimePairedUnitProducts (R : ℕ) : Finset ℕ :=
  (lowWheelFarPrimeUnitProducts R).filter fun p =>
    2 * p ≤ squareRootEndpoint R

/-- The complementary unmatched unit face: primes strictly above half the endpoint. -/
def lowWheelFarPrimeTopUnitProducts (R : ℕ) : Finset ℕ :=
  (lowWheelFarPrimeUnitProducts R).filter fun p =>
    squareRootEndpoint R < 2 * p

/-- The unit face splits exactly into cancellable and top-half populations. -/
theorem lowWheelFarPrimeUnitProducts_eq_paired_union_top (R : ℕ) :
    lowWheelFarPrimeUnitProducts R =
      lowWheelFarPrimePairedUnitProducts R ∪ lowWheelFarPrimeTopUnitProducts R := by
  ext p
  constructor
  · intro hp
    by_cases hlow : 2 * p ≤ squareRootEndpoint R
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hp, hlow⟩)
    · have htop : squareRootEndpoint R < 2 * p := Nat.lt_of_not_ge hlow
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hp, htop⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hpaired | htop
    · exact (Finset.mem_filter.mp hpaired).1
    · exact (Finset.mem_filter.mp htop).1

/-- There is no crossing occurrence at a top-half unit prime: every crossing
owner is a prime at least two, so its base product would already exceed `X_R`. -/
theorem lowWheelFarWallCrossingMultiplicity_eq_zero_of_topUnit
    {R p : ℕ} (hp : p ∈ lowWheelFarPrimeTopUnitProducts R) :
    lowWheelFarWallCrossingMultiplicity R p = 0 := by
  have htop := (Finset.mem_filter.mp hp).2
  unfold lowWheelFarWallCrossingMultiplicity
  apply Finset.card_eq_zero.mpr
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxCross, hxp⟩
  rcases Finset.mem_image.mp hxCross with ⟨t, ht, htx⟩
  have hbase := (Finset.mem_filter.mp ht).1
  have hcut := (lowWheelFarPrimeProduct_geometry hbase).2.2.1
  have hq2 := (lowWheelFarPrimeLowCofactorTriple_data hbase).1.two_le
  have hprodEq : (lowWheelFarPrimeProductKey t).2 = p := by
    exact (congrArg Prod.snd htx).trans hxp
  rw [hprodEq] at hcut
  have h2ple : 2 * p ≤ t.1 * p := Nat.mul_le_mul_right p hq2
  omega

/-- Likewise an old owned product can carry no crossing occurrence. -/
theorem lowWheelFarWallCrossingMultiplicity_eq_zero_of_owned
    {R n : ℕ} (hn : n ∈ lowWheelFrozenTopFarOwnedProducts R) :
    lowWheelFarWallCrossingMultiplicity R n = 0 := by
  unfold lowWheelFarWallCrossingMultiplicity
  apply Finset.card_eq_zero.mpr
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxCross, hxn⟩
  have hnot := lowWheelFarPrimeCrossingProduct_not_owned hxCross
  apply hnot
  simpa [hxn] using hn

/-- Integer multiplicity left after deleting one genuine crossing occurrence
for every cancellable unit prime.  The preceding existence theorem guarantees
that this formal subtraction never asks for an occurrence that is absent. -/
def lowWheelFarWallExtraCrossingCoefficient (R n : ℕ) : ℤ :=
  (lowWheelFarWallCrossingMultiplicity R n : ℤ) -
    if n ∈ lowWheelFarPrimePairedUnitProducts R then 1 else 0

theorem lowWheelFarWallExtraCrossingCoefficient_nonneg (R n : ℕ) :
    0 ≤ lowWheelFarWallExtraCrossingCoefficient R n := by
  unfold lowWheelFarWallExtraCrossingCoefficient
  by_cases hn : n ∈ lowWheelFarPrimePairedUnitProducts R
  · rcases Finset.mem_filter.mp hn with ⟨hunit, h2n⟩
    have hpos := lowWheelFarWallCrossingMultiplicity_pos_of_unit_two_mul_le hunit h2n
    simp [hn]
    omega
  · simp [hn]

/-- The exact signed complement after unit/crossing cancellation: extra
crossing owners, unmatched top-half unit primes, and the two old owned images. -/
def lowWheelFarWallCancelledBoundaryCoefficient (R n : ℕ) : ℤ :=
  lowWheelFarWallExtraCrossingCoefficient R n -
    (if n ∈ lowWheelFarPrimeTopUnitProducts R then 1 else 0) -
    (if n ∈ lowWheelFrozenTopFarOwnedProducts R then 1 else 0)

/-- Pointwise exact cancellation census.  This is the formal version of
choosing one crossing occurrence for every `2*p ≤ X_R` unit prime and deleting
the equal signed pair before any norm is taken. -/
theorem lowWheelFarWallBoundaryCoefficient_eq_cancelled (R n : ℕ) :
    lowWheelFarWallBoundaryCoefficient R n =
      lowWheelFarWallCancelledBoundaryCoefficient R n := by
  unfold lowWheelFarWallBoundaryCoefficient lowWheelFarWallCancelledBoundaryCoefficient
    lowWheelFarWallExtraCrossingCoefficient
  by_cases hu : n ∈ lowWheelFarPrimeUnitProducts R
  · have hno : n ∉ lowWheelFrozenTopFarOwnedProducts R := by
      intro ho
      exact (Finset.disjoint_left.mp (lowWheelFarPrimeUnitProducts_disjoint_owned R)) hu ho
    by_cases hlow : 2 * n ≤ squareRootEndpoint R
    · have hnotTop : ¬ squareRootEndpoint R < 2 * n := by omega
      simp [lowWheelFarWallTerminalProducts, lowWheelFarPrimePairedUnitProducts,
        lowWheelFarPrimeTopUnitProducts, hu, hno, hlow, hnotTop]
    · have htop : squareRootEndpoint R < 2 * n := by omega
      simp [lowWheelFarWallTerminalProducts, lowWheelFarPrimePairedUnitProducts,
        lowWheelFarPrimeTopUnitProducts, hu, hno, hlow, htop]
  · by_cases ho : n ∈ lowWheelFrozenTopFarOwnedProducts R
    · simp [lowWheelFarWallTerminalProducts, lowWheelFarPrimePairedUnitProducts,
        lowWheelFarPrimeTopUnitProducts, hu, ho]
    · simp [lowWheelFarWallTerminalProducts, lowWheelFarPrimePairedUnitProducts,
        lowWheelFarPrimeTopUnitProducts, hu, ho]

/-- **Final signed boundary reassembly.**  After one legitimate crossing/unit
pair has been removed on every eligible unit fibre, the remaining four-term
boundary is literally one Möbius carrier with the exact complement coefficient.
No absolute value or energy estimate has yet been taken. -/
theorem lowWheelFarWall_remainingBoundary_eq_cancelledCoefficient_sum (R : ℕ) :
    lowWheelFarPrimeUnitFaceMass R - lowWheelFarPrimeQ2CrossingMass R -
        lowWheelCanonicalRepeatedTerminalInternalMateLedger R -
        lowWheelFrozenCofactorTopImageLedger R =
      ∑ n ∈ lowWheelFarWallBoundaryProductHomes R,
        (lowWheelFarWallCancelledBoundaryCoefficient R n : ℂ) *
          canonicalMoebiusWeight n := by
  rw [lowWheelFarWall_remainingBoundary_eq_coefficient_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [lowWheelFarWallBoundaryCoefficient_eq_cancelled]

/-- The complete hard physical residual is now the literal q²-descended child
packet plus the fully reassembled signed complement.  This is the desired
signed-reassembly-first interface for the subsequent energy step. -/
theorem lowWheelFrozenTopFarResidual_eq_descended_add_cancelledBoundary
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      (∑ x ∈ lowWheelFarPrimeDescendedProductCarrier R,
        canonicalMoebiusWeight x.2) +
      ∑ n ∈ lowWheelFarWallBoundaryProductHomes R,
        (lowWheelFarWallCancelledBoundaryCoefficient R n : ℂ) *
          canonicalMoebiusWeight n := by
  have hb := lowWheelFarWall_remainingBoundary_eq_cancelledCoefficient_sum R
  rw [lowWheelFrozenTopFarResidual_eq_unit_sub_descended_sub_crossing_sub_owned R hR,
    lowWheelFarPrimeQ2DescendedMass_eq_neg_productMass]
  linear_combination hb

/-- A concrete regression against silently replacing a crossing-owner fibre
by one occurrence: owners 3 and 5 both represent the same far prime 23. -/
theorem lowWheelFarWallCrossingMultiplicity_twelve_twentyThree_ge_two :
    2 ≤ lowWheelFarWallCrossingMultiplicity 12 23 := by
  have hmem (q : ℕ) (hq : q = 3 ∨ q = 5) :
      (q,23) ∈ lowWheelFarPrimeCrossingProductCarrier 12 := by
    have htr : (q,(1,23)) ∈ lowWheelFarPrimeLowCofactorTriples 12 := by
      apply lowWheelFarPrimeLowCofactorTriple_mem_of_data
      all_goals rcases hq with rfl | rfl <;>
        norm_num [canonicalLargestPrimeFactor, squareRootEndpoint]
    apply Finset.mem_image.mpr
    refine ⟨(q,(1,23)), Finset.mem_filter.mpr ⟨htr, ?_⟩, rfl⟩
    rcases hq with rfl | rfl <;> norm_num [squareRootEndpoint]
  have hsub : ({(3,23),(5,23)} : Finset (ℕ × ℕ)) ⊆
      (lowWheelFarPrimeCrossingProductCarrier 12).filter (fun x => x.2 = 23) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hmem 3 (Or.inl rfl), rfl⟩
    · exact Finset.mem_filter.mpr ⟨hmem 5 (Or.inr rfl), rfl⟩
  have hcard := Finset.card_le_card hsub
  norm_num only [Finset.card_insert_of_notMem (by decide : (3,23) ∉ ({(5,23)} : Finset (ℕ × ℕ))),
    Finset.card_singleton] at hcard
  exact hcard

end RHLean.Proof