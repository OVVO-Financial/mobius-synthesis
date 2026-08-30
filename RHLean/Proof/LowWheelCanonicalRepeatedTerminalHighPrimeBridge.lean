import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedParentClassification
import RHLean.Proof.LowWheelHighPrimeSurvivor

/-!
# Repeated terminal downcrosses as the existing high-prime transport geometry

The repeated-parent classification leaves a terminal shape `y = (t,(1,p))`
with `P(t) <= R < p * P(t)`.  This module isolates the genuinely external part
`R < p` and records that it is literally the repository's pre-existing
high-prime transport fibre with low cofactor `P(t)`.

No norm, PNT estimate, asymptotic input, or further Euler descent appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The genuinely external part of the repeated terminal boundary. -/
def lowWheelCanonicalRepeatedExternalTerminalPart (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalRepeatedTerminalBoundary R).filter fun y =>
    R < lowWheelTaggedDowncrossPivot y

@[simp] theorem mem_lowWheelCanonicalRepeatedExternalTerminalPart
    {R : ℕ} {y : LowWheelTaggedDowncrossState} :
    y ∈ lowWheelCanonicalRepeatedExternalTerminalPart R ↔
      y ∈ lowWheelCanonicalRepeatedTerminalBoundary R ∧
        R < lowWheelTaggedDowncrossPivot y := by
  simp [lowWheelCanonicalRepeatedExternalTerminalPart]

/-- Every repeated external terminal occurrence is still in the complete
canonical tagged downcross carrier. -/
theorem lowWheelCanonicalRepeatedExternalTerminal_mem_taggedCarrier
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedExternalTerminalPart R) :
    y ∈ lowWheelCanonicalTaggedDowncrossCarrier R := by
  have hterminal := (Finset.mem_filter.mp hy).1
  have hfrozen := (Finset.mem_filter.mp hterminal).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  exact (Finset.mem_filter.mp hrepeated).1

/-- **External-terminal/high-prime bridge.**  A repeated terminal state with
`R < p` is literally an existing high-prime transport pair when its Boolean
face product is read as the low cofactor.  The same product has canonical
coordinates `(P(t),p)`, and the Boolean face sign is the Möbius sign of `P(t)`.
-/
theorem lowWheelCanonicalRepeatedExternalTerminal_highPrime_data
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedExternalTerminalPart R) :
    primeFaceProduct y.1 ∈ Finset.Ico 1 R ∧
      lowWheelTaggedDowncrossPivot y ∈
        squareRootHighPrimeCofactorSet R (primeFaceProduct y.1) ∧
      (primeFaceProduct y.1, lowWheelTaggedDowncrossPivot y) ∈
        squareRootTransportPairSet R ∧
      canonicalCofactor
          (primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y) =
        primeFaceProduct y.1 ∧
      canonicalLargestPrimeFactor
          (primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y) =
        lowWheelTaggedDowncrossPivot y ∧
      canonicalMoebiusWeight (primeFaceProduct y.1) =
        (booleanCubeSign y.1 : ℂ) := by
  have hterminal := (Finset.mem_filter.mp hy).1
  have hpR := (Finset.mem_filter.mp hy).2
  rcases lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal with
    ⟨hc, hk, hp, _hface, hdown, _hup⟩
  have htagged :=
    lowWheelCanonicalRepeatedExternalTerminal_mem_taggedCarrier hy
  have htagData := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hdownMem := htagData.2
  have hphysical := (mem_lowWheelCanonicalDowncrossPart.mp hdownMem).1
  have hphysicalData := mem_lowWheelCanonicalPhysicalStateSet.mp hphysical
  have hpairCarrier := hphysicalData.2.2.2
  have hPpos : 0 < primeFaceProduct y.1 :=
    primeFaceProduct_pos_of_mem_powerset htagData.1
  have htop0 := hpairCarrier.2.2.2
  rw [hc, hk] at htop0
  have htop :
      primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y ≤
        squareRootEndpoint R := by
    simpa using htop0
  have hcRange := hphysicalData.1
  rw [hc] at hcRange
  have hRpos : 0 < R := by
    have h1R := (Finset.mem_Ico.mp hcRange).2
    omega
  have hXltSquare : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hsqpos : 0 < R ^ 2 := by positivity
    omega
  have hPltR : primeFaceProduct y.1 < R := by
    by_contra hnot
    have hRleP : R ≤ primeFaceProduct y.1 := Nat.le_of_not_gt hnot
    have hPeq : primeFaceProduct y.1 = R :=
      Nat.le_antisymm hdown hRleP
    have hSquareLt :
        R ^ 2 < R * lowWheelTaggedDowncrossPivot y := by
      simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hpR hRpos
    have hbad :
        squareRootEndpoint R < R * lowWheelTaggedDowncrossPivot y :=
      hXltSquare.trans hSquareLt
    rw [hPeq] at htop
    exact (Nat.not_lt_of_ge htop) hbad
  have hPone : 1 ≤ primeFaceProduct y.1 := Nat.succ_le_iff.mpr hPpos
  have hpLeProduct :
      lowWheelTaggedDowncrossPivot y ≤
        primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y := by
    calc
      lowWheelTaggedDowncrossPivot y =
          1 * lowWheelTaggedDowncrossPivot y := by simp
      _ ≤ primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y :=
        Nat.mul_le_mul_right _ hPone
  have hpX : lowWheelTaggedDowncrossPivot y ≤ squareRootEndpoint R :=
    hpLeProduct.trans htop
  have hhigh :
      lowWheelTaggedDowncrossPivot y ∈
        squareRootHighPrimeCofactorSet R (primeFaceProduct y.1) := by
    unfold squareRootHighPrimeCofactorSet
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hpR, hpX⟩, hp, htop⟩
  have htransport :
      (primeFaceProduct y.1, lowWheelTaggedDowncrossPivot y) ∈
        squareRootTransportPairSet R := by
    unfold squareRootTransportPairSet
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hp, htop⟩
    · exact Finset.mem_Ico.mpr ⟨hPone, hPltR⟩
    · exact Finset.mem_Ioc.mpr ⟨hpR, hpX⟩
  have hPp : primeFaceProduct y.1 < lowWheelTaggedDowncrossPivot y :=
    hPltR.trans hpR
  have hcofactor := canonicalCofactor_mul_prime_eq hPpos hPp hp
  have hlargest := canonicalLargestPrimeFactor_mul_prime_eq hPpos hPp hp
  have hfaceSub := Finset.mem_powerset.mp htagData.1
  have hprimeFace : ∀ q ∈ y.1, q.Prime := by
    intro q hq
    exact prime_of_mem_primesUpTo (hfaceSub hq)
  have hmu := moebius_primeFaceProduct_eq_booleanCubeSign y.1 hprimeFace
  have hweight :
      canonicalMoebiusWeight (primeFaceProduct y.1) =
        (booleanCubeSign y.1 : ℂ) := by
    unfold canonicalMoebiusWeight
    rw [hmu]
  exact ⟨Finset.mem_Ico.mpr ⟨hPone, hPltR⟩,
    hhigh, htransport, hcofactor, hlargest, hweight⟩

/-- External terminal shape before imposing the unique/repeated parent split. -/
def lowWheelCanonicalExternalTerminalPart (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalTaggedDowncrossCarrier R).filter fun y =>
    y.2.1 = 1 ∧
      y.2.2 = lowWheelTaggedDowncrossPivot y ∧
      (∀ q ∈ y.1, q < lowWheelTaggedDowncrossPivot y) ∧
      R < lowWheelTaggedDowncrossPivot y

/-- Unique-parent external terminal occurrences. -/
def lowWheelCanonicalExternalTerminalUniquePart (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalExternalTerminalPart R).filter fun y =>
    y ∈ lowWheelCanonicalDowncrossUniqueParentPart R

/-- Repeated-parent external terminal occurrences. -/
def lowWheelCanonicalExternalTerminalRepeatedPart (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalExternalTerminalPart R).filter fun y =>
    y ∈ lowWheelCanonicalDowncrossRepeatedParentPart R

/-- The complete external-terminal carrier splits exactly according to the
already-proved global parent partition. -/
theorem lowWheelCanonicalExternalTerminal_eq_unique_union_repeated
    (R : ℕ) :
    lowWheelCanonicalExternalTerminalPart R =
      lowWheelCanonicalExternalTerminalUniquePart R ∪
        lowWheelCanonicalExternalTerminalRepeatedPart R := by
  classical
  ext y
  constructor
  · intro hy
    have hcarrier := (Finset.mem_filter.mp hy).1
    have hsplit :
        y ∈ lowWheelCanonicalDowncrossUniqueParentPart R ∨
          y ∈ lowWheelCanonicalDowncrossRepeatedParentPart R := by
      have hu :
          y ∈ lowWheelCanonicalDowncrossUniqueParentPart R ∪
            lowWheelCanonicalDowncrossRepeatedParentPart R := by
        rw [← lowWheelCanonicalTaggedDowncrossCarrier_eq_unique_union_repeated R]
        exact hcarrier
      exact Finset.mem_union.mp hu
    rcases hsplit with hu | hr
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hy, hu⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hy, hr⟩
  · intro hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (Finset.mem_filter.mp hy).1
    · exact (Finset.mem_filter.mp hy).1

/-- The repeated part of the complete external-terminal carrier is exactly the
external subpart of the repeated terminal boundary. -/
theorem lowWheelCanonicalExternalTerminalRepeated_eq_repeatedExternalTerminal
    (R : ℕ) :
    lowWheelCanonicalExternalTerminalRepeatedPart R =
      lowWheelCanonicalRepeatedExternalTerminalPart R := by
  classical
  ext y
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hext, hrepeated⟩
    rcases Finset.mem_filter.mp hext with
      ⟨_hcarrier, hc, hk, hface, hpR⟩
    have hfrozen : y ∈ lowWheelCanonicalRepeatedFrozenPart R :=
      Finset.mem_filter.mpr ⟨hrepeated, ⟨hk, hface⟩⟩
    have hterminal : y ∈ lowWheelCanonicalRepeatedTerminalBoundary R :=
      Finset.mem_filter.mpr ⟨hfrozen, hc⟩
    exact Finset.mem_filter.mpr ⟨hterminal, hpR⟩
  · intro hy
    have hterminal := (Finset.mem_filter.mp hy).1
    have hpR := (Finset.mem_filter.mp hy).2
    rcases lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal with
      ⟨hc, hk, _hp, hface, _hdown, _hup⟩
    have hfrozen := (Finset.mem_filter.mp hterminal).1
    have hrepeated := (Finset.mem_filter.mp hfrozen).1
    have hcarrier := (Finset.mem_filter.mp hrepeated).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hcarrier, ?_⟩, hrepeated⟩
    exact ⟨hc, hk, hface, hpR⟩

/-- The unique external-terminal population costs at most the already-owned
root budget `R`. -/
theorem lowWheelCanonicalExternalTerminalUniquePart_card_le_root
    (R : ℕ) :
    (lowWheelCanonicalExternalTerminalUniquePart R).card ≤ R := by
  have hsub :
      lowWheelCanonicalExternalTerminalUniquePart R ⊆
        lowWheelCanonicalDowncrossUniqueParentPart R := by
    intro y hy
    exact (Finset.mem_filter.mp hy).2
  exact (Finset.card_le_card hsub).trans
    (lowWheelCanonicalDowncrossUniqueParentPart_card_le_root R)

end RHLean.Proof
