import Mathlib
import RHLean.Proof.LowWheelExternalTerminalFaceLedger
import RHLean.Proof.LowWheelCanonicalDowncrossParentFibers

/-!
# Split the external high-prime grid by the canonical downcross parent

The high-prime transport already has the exact Boolean-face coordinate system
`(t,p)`, with `P(t) < R < p` and `P(t)*p <= X_R`.  This file sends such a pair
to the literal terminal downcross occurrence

`(t,(1,p))`.

The map is injective and every image is a genuine canonical root-downcross.  We
can therefore partition the existing high-prime transport grid by the
unique/repeated parent partition without inventing any new population.  The
unique side has cardinality at most `R` immediately, because its terminal tag
injects into the already-owned unique-parent downcross carrier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

abbrev LowWheelExternalTerminalFacePrime := Finset ℕ × ℕ

/-- Flattened version of the face/high-prime grid underlying
`squareRootExternalTerminalFaceLedger`. -/
def squareRootExternalTerminalFaceCarrier (R : ℕ) :
    Finset LowWheelExternalTerminalFacePrime :=
  ((admissiblePrimeFaces (R - 1)).product
      (Finset.Ioc R (squareRootEndpoint R))).filter fun z =>
    z.2.Prime ∧ primeFaceProduct z.1 * z.2 ≤ squareRootEndpoint R

@[simp] theorem mem_squareRootExternalTerminalFaceCarrier
    {R p : ℕ} {t : Finset ℕ} :
    (t, p) ∈ squareRootExternalTerminalFaceCarrier R ↔
      t ∈ admissiblePrimeFaces (R - 1) ∧
      p ∈ Finset.Ioc R (squareRootEndpoint R) ∧
      p.Prime ∧ primeFaceProduct t * p ≤ squareRootEndpoint R := by
  simp [squareRootExternalTerminalFaceCarrier, and_assoc]

/-- Read one existing face/high-prime transport coordinate as the corresponding
terminal canonical downcross occurrence. -/
def squareRootExternalTerminalTag
    (z : LowWheelExternalTerminalFacePrime) : LowWheelTaggedDowncrossState :=
  (z.1, (1, z.2))

/-- The terminal tagging loses no multiplicity. -/
theorem squareRootExternalTerminalTag_injective :
    Function.Injective squareRootExternalTerminalTag := by
  intro a b hab
  rcases a with ⟨t, p⟩
  rcases b with ⟨u, q⟩
  have hface : t = u := congrArg Prod.fst hab
  have hstate : (1, p) = (1, q) := congrArg Prod.snd hab
  have hpq : p = q := congrArg Prod.snd hstate
  subst u
  subst q
  rfl

/-- Every existing external face/high-prime coordinate is literally a
canonical tagged downcross state. -/
theorem squareRootExternalTerminalTag_mem_downcross
    {R : ℕ} (hR : 2 ≤ R)
    {z : LowWheelExternalTerminalFacePrime}
    (hz : z ∈ squareRootExternalTerminalFaceCarrier R) :
    squareRootExternalTerminalTag z ∈
      lowWheelCanonicalTaggedDowncrossCarrier R := by
  rcases z with ⟨t, p⟩
  rcases mem_squareRootExternalTerminalFaceCarrier.mp hz with
    ⟨htAdm, hpRange, hp, htop⟩
  have htFiltered :
      t ∈ (primesUpTo R).powerset.filter
        (fun u => primeFaceProduct u < R) := by
    rw [← admissiblePrimeFaces_pred_eq_lowCube_filter_product_lt R (by omega)]
    exact htAdm
  rcases Finset.mem_filter.mp htFiltered with ⟨ht, hPltR⟩
  have hPpos : 0 < primeFaceProduct t :=
    primeFaceProduct_pos_of_mem_powerset ht
  have hpR : R < p := (Finset.mem_Ioc.mp hpRange).1
  have hpX : p ≤ squareRootEndpoint R := (Finset.mem_Ioc.mp hpRange).2
  have hpivot : lowWheelCanonicalCofactorQuotientPivot (1, p) = p := by
    simp [lowWheelCanonicalCofactorQuotientPivot, hp.minFac_eq]
  have hphysical :
      (1, p) ∈ lowWheelCanonicalPhysicalStateSet R t := by
    apply mem_lowWheelCanonicalPhysicalStateSet.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨by norm_num, by omega⟩,
      Finset.mem_Icc.mpr ⟨hp.one_le, hpX⟩, by simp, ?_⟩
    refine ⟨by norm_num, by omega, ?_, by simpa using htop⟩
    have hpLe : p ≤ primeFaceProduct t * p := by
      calc
        p = 1 * p := by simp
        _ ≤ primeFaceProduct t * p := Nat.mul_le_mul_right p (by omega)
    exact hpR.trans_le hpLe
  have hnot : ¬ lowWheelCanonicalCofactorQuotientPivot (1, p) ∣ 1 := by
    rw [hpivot]
    exact hp.not_dvd_one
  have hdown :
      primeFaceProduct t *
          (p / lowWheelCanonicalCofactorQuotientPivot (1, p)) ≤ R := by
    rw [hpivot, Nat.div_self hp.pos]
    simpa using Nat.le_of_lt hPltR
  apply mem_lowWheelCanonicalTaggedDowncrossCarrier.mpr
  exact ⟨ht, mem_lowWheelCanonicalDowncrossPart.mpr
    ⟨hphysical, hnot, hdown⟩⟩

/-- External face/high-prime coordinates whose terminal occurrence has a unique
canonical root parent. -/
def squareRootExternalTerminalUniqueFaceCarrier (R : ℕ) :
    Finset LowWheelExternalTerminalFacePrime :=
  (squareRootExternalTerminalFaceCarrier R).filter fun z =>
    squareRootExternalTerminalTag z ∈
      lowWheelCanonicalDowncrossUniqueParentPart R

/-- Complementary repeated-parent part of the same pre-existing high-prime
transport grid. -/
def squareRootExternalTerminalRepeatedFaceCarrier (R : ℕ) :
    Finset LowWheelExternalTerminalFacePrime :=
  (squareRootExternalTerminalFaceCarrier R).filter fun z =>
    squareRootExternalTerminalTag z ∈
      lowWheelCanonicalDowncrossRepeatedParentPart R

/-- The unique external face/high-prime population inherits the global root
budget without any prime-count factor. -/
theorem squareRootExternalTerminalUniqueFaceCarrier_card_le_root
    (R : ℕ) :
    (squareRootExternalTerminalUniqueFaceCarrier R).card ≤ R := by
  have htagInj : Set.InjOn squareRootExternalTerminalTag
      (squareRootExternalTerminalUniqueFaceCarrier R) :=
    squareRootExternalTerminalTag_injective.injOn
  have hcard :
      ((squareRootExternalTerminalUniqueFaceCarrier R).image
        squareRootExternalTerminalTag).card =
        (squareRootExternalTerminalUniqueFaceCarrier R).card :=
    Finset.card_image_iff.mpr htagInj
  have hsub :
      (squareRootExternalTerminalUniqueFaceCarrier R).image
          squareRootExternalTerminalTag ⊆
        lowWheelCanonicalDowncrossUniqueParentPart R := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    exact (Finset.mem_filter.mp hz).2
  rw [← hcard]
  exact (Finset.card_le_card hsub).trans
    (lowWheelCanonicalDowncrossUniqueParentPart_card_le_root R)

/-- For `R >= 2`, the high-prime grid is exhausted by the unique and repeated
canonical parent classes. -/
theorem squareRootExternalTerminalFaceCarrier_eq_unique_union_repeated
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootExternalTerminalFaceCarrier R =
      squareRootExternalTerminalUniqueFaceCarrier R ∪
        squareRootExternalTerminalRepeatedFaceCarrier R := by
  ext z
  constructor
  · intro hz
    have htag := squareRootExternalTerminalTag_mem_downcross hR hz
    have hsplit :
        squareRootExternalTerminalTag z ∈
            lowWheelCanonicalDowncrossUniqueParentPart R ∨
          squareRootExternalTerminalTag z ∈
            lowWheelCanonicalDowncrossRepeatedParentPart R := by
      have hu :
          squareRootExternalTerminalTag z ∈
              lowWheelCanonicalDowncrossUniqueParentPart R ∪
            lowWheelCanonicalDowncrossRepeatedParentPart R := by
        rw [← lowWheelCanonicalTaggedDowncrossCarrier_eq_unique_union_repeated R]
        exact htag
      exact Finset.mem_union.mp hu
    rcases hsplit with hu | hr
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hz, hu⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hz, hr⟩
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (Finset.mem_filter.mp hz).1
    · exact (Finset.mem_filter.mp hz).1

/-- The two external parent classes are disjoint. -/
theorem squareRootExternalTerminalUnique_disjoint_repeated
    (R : ℕ) :
    Disjoint
      (squareRootExternalTerminalUniqueFaceCarrier R)
      (squareRootExternalTerminalRepeatedFaceCarrier R) := by
  rw [Finset.disjoint_left]
  intro z hzU hzR
  have hU := (Finset.mem_filter.mp hzU).2
  have hC := (Finset.mem_filter.mp hzR).2
  exact (Finset.disjoint_left.mp
    (lowWheelCanonicalDowncrossUnique_disjoint_repeated R)) hU hC

end RHLean.Proof
