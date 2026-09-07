import Mathlib
import RHLean.Proof.SquareRootLowPrimeStructuralKey
import RHLean.Proof.SquareRootLowPrimeCanonicalCreationResponseMap

/-!
# Shallow processed seats are exactly tagged creation seats

At a cofactor whose canonical largest prime is at most `K`, the processed-seat
fibre has

`CombinedFreshResponse = BornPartnerCount + HighResponse`

literal absolute seats.  The creation carrier stores the same fibre with the
born prefix and high suffix tagged separately.  Therefore the non-head shallow
processed carrier is canonically equivalent to the non-head creation carrier:

* `s < BornPartnerCount(c)` is the born tag with local seat `s`;
* otherwise the state is the high tag with local seat
  `s - BornPartnerCount(c)`.

The inverse simply restores the high offset.  No finite-cardinality choice is
used.  This is the coordinate bridge on which the compressed Partial branch is
ranked.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Shallow non-head processed seats. -/
def squareRootLowPrimeProcessedShallowSeatAtoms
    (R K j U : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeProcessedSeatAtoms R K j U).filter fun z =>
    canonicalLargestPrimeFactor z.1 ≤ K

@[simp] theorem mem_squareRootLowPrimeProcessedShallowSeatAtoms
    {R K j U : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeProcessedShallowSeatAtoms R K j U ↔
      z ∈ squareRootLowPrimeProcessedSeatAtoms R K j U ∧
        canonicalLargestPrimeFactor z.1 ≤ K := by
  simp [squareRootLowPrimeProcessedShallowSeatAtoms]

/-- Read one absolute shallow processed seat as a born/high creation seat. -/
def squareRootLowPrimeProcessedShallowSeatToCreation
    (R : ℕ) (z : ℕ × ℕ) : SquareRootLowPrimeCreationState :=
  if z.2 < squareRootBornPartnerCount R z.1 then
    some (Sum.inl z)
  else
    some (Sum.inr (z.1, z.2 - squareRootBornPartnerCount R z.1))

/-- Forget the born/high tag while retaining the absolute seat.  The value on
`none` is irrelevant because the equivalence below uses the erased carrier. -/
def squareRootLowPrimeCreationToProcessedShallowSeat
    (R : ℕ) : SquareRootLowPrimeCreationState → ℕ × ℕ
  | none => (1, 0)
  | some (Sum.inl z) => z
  | some (Sum.inr z) =>
      (z.1, squareRootBornPartnerCount R z.1 + z.2)

/-- A shallow processed seat lands in the literal non-head creation carrier. -/
theorem squareRootLowPrimeProcessedShallowSeatToCreation_mem
    {R K j U : ℕ} (_hR : 1 ≤ R) (_hKU : K ≤ U)
    {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimeProcessedShallowSeatAtoms R K j U) :
    squareRootLowPrimeProcessedShallowSeatToCreation R z ∈
      (squareRootLowPrimeCreationCarrierExact R K j).erase none := by
  rcases mem_squareRootLowPrimeProcessedShallowSeatAtoms.mp hz with
    ⟨hzProcessed, hshallow⟩
  rcases mem_squareRootLowPrimeProcessedSeatAtoms.mp hzProcessed with
    ⟨hcProcessed, hsCombined⟩
  rcases Finset.mem_filter.mp hcProcessed with
    ⟨hcRange, _hlpfU, hmu⟩
  have hcBorn : z.1 ∈ squareRootLowPrimeShallowBornCofactors R K := by
    exact Finset.mem_filter.mpr ⟨hcRange, hshallow, hmu⟩
  by_cases hsBorn : z.2 < squareRootBornPartnerCount R z.1
  · have hzBorn : z ∈ squareRootLowPrimeShallowBornSeatAtoms R K := by
      unfold squareRootLowPrimeShallowBornSeatAtoms
      apply Finset.mem_biUnion.mpr
      exact ⟨z.1, hcBorn,
        mem_squareRootLowPrimeShallowBornSeatFiber.mpr ⟨rfl, hsBorn⟩⟩
    apply Finset.mem_erase.mpr
    refine ⟨by simp [squareRootLowPrimeProcessedShallowSeatToCreation, hsBorn], ?_⟩
    unfold squareRootLowPrimeCreationCarrierExact
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union.mpr
    left
    unfold squareRootLowPrimeShallowBornCreationStates
    exact Finset.mem_image.mpr ⟨z, hzBorn, by
      simp [squareRootLowPrimeProcessedShallowSeatToCreation, hsBorn]⟩
  · have hcR : z.1 ≤ R - 1 := by
      by_contra hcNot
      have hcNot' : ¬ z.1 ≤ R - 1 := hcNot
      have hsOnlyBorn :
          z.2 < squareRootBornPartnerCount R z.1 := by
        simpa [squareRootLowPrimeCombinedFreshResponse, hcNot'] using hsCombined
      exact hsBorn hsOnlyBorn
    have hsHigh :
        z.2 - squareRootBornPartnerCount R z.1 <
          squareRootBornPostTailHighResponse R K j z.1 := by
      have hsCombined' :
          z.2 < squareRootBornPartnerCount R z.1 +
            squareRootBornPostTailHighResponse R K j z.1 := by
        simpa [squareRootLowPrimeCombinedFreshResponse, hcR] using hsCombined
      omega
    have hcHigh : z.1 ∈ squareRootLowPrimeShallowHighCofactors R K := by
      have hcOne := (Finset.mem_Icc.mp hcRange).1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hcOne, hcR⟩, hshallow, hmu⟩
    let w : ℕ × ℕ :=
      (z.1, z.2 - squareRootBornPartnerCount R z.1)
    have hwHigh : w ∈ squareRootLowPrimeShallowHighSeatAtoms R K j := by
      unfold squareRootLowPrimeShallowHighSeatAtoms
      apply Finset.mem_biUnion.mpr
      refine ⟨z.1, hcHigh, ?_⟩
      exact mem_squareRootLowPrimeShallowHighSeatFiber.mpr
        ⟨by rfl, by simpa [w] using hsHigh⟩
    apply Finset.mem_erase.mpr
    refine ⟨by simp [squareRootLowPrimeProcessedShallowSeatToCreation, hsBorn], ?_⟩
    unfold squareRootLowPrimeCreationCarrierExact
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union.mpr
    right
    unfold squareRootLowPrimeShallowHighCreationStates
    exact Finset.mem_image.mpr ⟨w, hwHigh, by
      simp [squareRootLowPrimeProcessedShallowSeatToCreation, hsBorn, w]⟩

/-- Every non-head creation seat restores to a shallow processed seat. -/
theorem squareRootLowPrimeCreationToProcessedShallowSeat_mem
    {R K j U : ℕ} (hR : 1 ≤ R) (hKU : K ≤ U)
    {x : SquareRootLowPrimeCreationState}
    (hx : x ∈ (squareRootLowPrimeCreationCarrierExact R K j).erase none) :
    squareRootLowPrimeCreationToProcessedShallowSeat R x ∈
      squareRootLowPrimeProcessedShallowSeatAtoms R K j U := by
  have hxCarrier := (Finset.mem_erase.mp hx).2
  have hxNone := (Finset.mem_erase.mp hx).1
  rcases squareRootLowPrimeCreationCarrierExact_nonhead_cases hxCarrier hxNone with
    ⟨z, hzBorn, rfl⟩ | ⟨z, hzHigh, rfl⟩
  · have hzData := squareRootLowPrimeShallowBornSeatAtom_data hzBorn
    have hcData := Finset.mem_filter.mp hzData.1
    have hcRange := hcData.1
    have hshallow := hcData.2.1
    have hmu := hcData.2.2
    have hcProcessed :
        z.1 ∈ squareRootLowPrimeProcessedSignedCofactors R U := by
      exact Finset.mem_filter.mpr
        ⟨hcRange, hshallow.trans hKU, hmu⟩
    have hsCombined :
        z.2 < squareRootLowPrimeCombinedFreshResponse R K j z.1 := by
      unfold squareRootLowPrimeCombinedFreshResponse
      omega
    exact mem_squareRootLowPrimeProcessedShallowSeatAtoms.mpr
      ⟨mem_squareRootLowPrimeProcessedSeatAtoms.mpr
        ⟨hcProcessed, hsCombined⟩, hshallow⟩
  · have hzData := squareRootLowPrimeShallowHighSeatAtom_data hzHigh
    have hcData := Finset.mem_filter.mp hzData.1
    have hcHighRange := hcData.1
    have hshallow := hcData.2.1
    have hmu := hcData.2.2
    have hcOne := (Finset.mem_Icc.mp hcHighRange).1
    have hcR := (Finset.mem_Icc.mp hcHighRange).2
    have hRR : R ≤ R ^ 2 := by
      calc
        R = R * 1 := by simp
        _ ≤ R * R := Nat.mul_le_mul_left R hR
        _ = R ^ 2 := by ring
    have hRX : R - 1 ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      exact Nat.sub_le_sub_right hRR 1
    have hcProcessed :
        z.1 ∈ squareRootLowPrimeProcessedSignedCofactors R U := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hcOne, hcR.trans hRX⟩,
          hshallow.trans hKU, hmu⟩
    have hsCombined :
        squareRootBornPartnerCount R z.1 + z.2 <
          squareRootLowPrimeCombinedFreshResponse R K j z.1 := by
      simpa [squareRootLowPrimeCombinedFreshResponse, hcR] using
        Nat.add_lt_add_left hzData.2 (squareRootBornPartnerCount R z.1)
    exact mem_squareRootLowPrimeProcessedShallowSeatAtoms.mpr
      ⟨mem_squareRootLowPrimeProcessedSeatAtoms.mpr
        ⟨hcProcessed, hsCombined⟩, hshallow⟩

/-- Restoring the absolute seat after tagging born/high is the identity. -/
theorem squareRootLowPrimeCreationToProcessedShallowSeat_toCreation
    {R K j U : ℕ} (_hR : 1 ≤ R) (_hKU : K ≤ U)
    {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimeProcessedShallowSeatAtoms R K j U) :
    squareRootLowPrimeCreationToProcessedShallowSeat R
        (squareRootLowPrimeProcessedShallowSeatToCreation R z) = z := by
  rcases mem_squareRootLowPrimeProcessedShallowSeatAtoms.mp hz with
    ⟨hzProcessed, _hshallow⟩
  have hsCombined := (mem_squareRootLowPrimeProcessedSeatAtoms.mp hzProcessed).2
  by_cases hsBorn : z.2 < squareRootBornPartnerCount R z.1
  · simp [squareRootLowPrimeProcessedShallowSeatToCreation,
      squareRootLowPrimeCreationToProcessedShallowSeat, hsBorn]
  · simp only [squareRootLowPrimeProcessedShallowSeatToCreation, hsBorn,
      if_false, squareRootLowPrimeCreationToProcessedShallowSeat]
    apply Prod.ext
    · rfl
    · omega

/-- Tagging a non-head creation state after forgetting the tag recovers it. -/
theorem squareRootLowPrimeProcessedShallowSeatToCreation_fromCreation
    {R K j U : ℕ} (_hR : 1 ≤ R) (_hKU : K ≤ U)
    {x : SquareRootLowPrimeCreationState}
    (hx : x ∈ (squareRootLowPrimeCreationCarrierExact R K j).erase none) :
    squareRootLowPrimeProcessedShallowSeatToCreation R
        (squareRootLowPrimeCreationToProcessedShallowSeat R x) = x := by
  have hxCarrier := (Finset.mem_erase.mp hx).2
  have hxNone := (Finset.mem_erase.mp hx).1
  rcases squareRootLowPrimeCreationCarrierExact_nonhead_cases hxCarrier hxNone with
    ⟨z, hzBorn, rfl⟩ | ⟨z, hzHigh, rfl⟩
  · have hzData := squareRootLowPrimeShallowBornSeatAtom_data hzBorn
    simp [squareRootLowPrimeCreationToProcessedShallowSeat,
      squareRootLowPrimeProcessedShallowSeatToCreation, hzData.2]
  · have hzData := squareRootLowPrimeShallowHighSeatAtom_data hzHigh
    have hnotBorn :
        ¬ squareRootBornPartnerCount R z.1 + z.2 <
          squareRootBornPartnerCount R z.1 := by omega
    simp [squareRootLowPrimeCreationToProcessedShallowSeat,
      squareRootLowPrimeProcessedShallowSeatToCreation, hnotBorn]

/-- **Canonical shallow processed/creation equivalence.** -/
noncomputable def squareRootLowPrimeProcessedShallowSeatCreationEquiv
    (R K j U : ℕ) (hR : 1 ≤ R) (hKU : K ≤ U) :
    ↥(squareRootLowPrimeProcessedShallowSeatAtoms R K j U) ≃
      ↥((squareRootLowPrimeCreationCarrierExact R K j).erase none) where
  toFun z :=
    ⟨squareRootLowPrimeProcessedShallowSeatToCreation R z.1,
      squareRootLowPrimeProcessedShallowSeatToCreation_mem hR hKU z.2⟩
  invFun x :=
    ⟨squareRootLowPrimeCreationToProcessedShallowSeat R x.1,
      squareRootLowPrimeCreationToProcessedShallowSeat_mem hR hKU x.2⟩
  left_inv z := by
    apply Subtype.ext
    exact squareRootLowPrimeCreationToProcessedShallowSeat_toCreation
      hR hKU z.2
  right_inv x := by
    apply Subtype.ext
    exact squareRootLowPrimeProcessedShallowSeatToCreation_fromCreation
      hR hKU x.2

/-- The equivalence preserves the cofactor and hence the native unit weight. -/
theorem squareRootLowPrimeProcessedShallowSeatCreationEquiv_weight_eq
    {R K j U : ℕ} (hR : 1 ≤ R) (hKU : K ≤ U)
    (z : ↥(squareRootLowPrimeProcessedShallowSeatAtoms R K j U)) :
    squareRootLowPrimeCreationWeightReal
        (squareRootLowPrimeProcessedShallowSeatCreationEquiv
          R K j U hR hKU z : SquareRootLowPrimeCreationState) =
      squareRootLowPrimeProcessedSeatWeightReal (some z.1) := by
  rcases z with ⟨⟨c, s⟩, hz⟩
  by_cases hsBorn : s < squareRootBornPartnerCount R c
  · simp [squareRootLowPrimeProcessedShallowSeatCreationEquiv,
      squareRootLowPrimeProcessedShallowSeatToCreation, hsBorn,
      squareRootLowPrimeCreationWeightReal,
      squareRootLowPrimeCreationWeightComplex, canonicalMoebiusWeight,
      squareRootLowPrimeProcessedSeatWeightReal]
  · simp [squareRootLowPrimeProcessedShallowSeatCreationEquiv,
      squareRootLowPrimeProcessedShallowSeatToCreation, hsBorn,
      squareRootLowPrimeCreationWeightReal,
      squareRootLowPrimeCreationWeightComplex, canonicalMoebiusWeight,
      squareRootLowPrimeProcessedSeatWeightReal]

end RHLean.Proof
