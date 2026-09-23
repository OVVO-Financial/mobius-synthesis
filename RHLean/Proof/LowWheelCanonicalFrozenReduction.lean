import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedParentClassification
import RHLean.Proof.LowWheelCanonicalRepeatedFrozenFactorGeometry
import RHLean.Proof.LowWheelFrozenCofactorTopBottomCancellation
import RHLean.Proof.LowWheelCanonicalRepeatedTerminalCutoff
import RHLean.Proof.LowWheelCanonicalRepeatedTerminalHighPrimeBridge
import RHLean.Proof.LowWheelExternalTerminalEightRootBound

/-!
# Frozen canonical downcross carrier and external reassembly

The durable historical object in this module is the frozen canonical downcross
carrier.  The current continuation also records the exact reassembly exposed by
the global top/bottom cancellation.

After the movable repeated population cancels, the canonical defect is

`D_R = U_R + Terminal_R - TopImage_R`.

The terminal boundary splits at the inclusive low-wheel cutoff.  Its external
part is literally the repeated-parent part of the existing external high-prime
grid, so it can be recombined with the already-proved

`ERrep_R + FarSurvivor_{R-1} = Near_R - ERuniq_R`.

The resulting hard object is one signed residual

`InternalTerminal_R - TopImage_R - FarSurvivor_{R-1}`.

No norm is taken inside that residual, and no PNT, Mertens estimate, or
RH-critical hypothesis is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open FrozenCofactorTopBottom

attribute [local instance] Classical.propDecidable

/-- Historical frozen first-crossing carrier retained for downstream geometry. -/
def lowWheelCanonicalFrozenDowncrossPart (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalTaggedDowncrossCarrier R).filter
    LowWheelDowncrossFrozenShape

/-- Signed internal part of the repeated terminal boundary. -/
def lowWheelCanonicalRepeatedTerminalInternalLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R,
    lowWheelTaggedDowncrossWeight y

/-- Signed external part of the repeated terminal boundary. -/
def lowWheelCanonicalRepeatedTerminalExternalLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalRepeatedTerminalExternalPart R,
    lowWheelTaggedDowncrossWeight y

/-- The repeated terminal ledger splits exactly at the inclusive low-wheel
cutoff. -/
theorem lowWheelCanonicalTerminalBoundaryLedger_eq_internal_add_external
    (R : ℕ) :
    lowWheelCanonicalTerminalBoundaryLedger R =
      lowWheelCanonicalRepeatedTerminalInternalLedger R +
        lowWheelCanonicalRepeatedTerminalExternalLedger R := by
  unfold lowWheelCanonicalTerminalBoundaryLedger
    lowWheelCanonicalRepeatedTerminalInternalLedger
    lowWheelCanonicalRepeatedTerminalExternalLedger
  rw [lowWheelCanonicalRepeatedTerminal_eq_internal_union_external R,
    Finset.sum_union
      (lowWheelCanonicalRepeatedTerminalInternal_disjoint_external R)]

/-- Every frozen-cofactor top image still carries the original sub-root pivot. -/
theorem lowWheelFrozenCofactorTopImage_pivot_lt_root
    {R : ℕ} {z : LowWheelTaggedDowncrossState}
    (hz : z ∈ lowWheelFrozenCofactorTopImage R) :
    lowWheelTaggedDowncrossPivot z < R := by
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  change lowWheelCanonicalCofactorQuotientPivot
      (lowWheelFrozenCofactorTopToggle y).2 < R
  rw [lowWheelFrozenCofactorTopToggle_pivot y]
  exact lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_root hy

/-- Hence the top image and the genuinely external terminal carrier are
literally disjoint.  Their cancellation cannot be a one-step carrier inclusion. -/
theorem lowWheelFrozenCofactorTopImage_disjoint_externalTerminal
    (R : ℕ) :
    Disjoint (lowWheelFrozenCofactorTopImage R)
      (lowWheelCanonicalRepeatedTerminalExternalPart R) := by
  rw [Finset.disjoint_left]
  intro z hzTop hzExt
  have hlt := lowWheelFrozenCofactorTopImage_pivot_lt_root hzTop
  have hgt := (Finset.mem_filter.mp hzExt).2
  omega

private theorem externalTerminalTag_mem_repeatedExternal
    {R : ℕ} (hR : 2 ≤ R)
    {z : LowWheelExternalTerminalFacePrime}
    (hz : z ∈ squareRootExternalTerminalRepeatedFaceCarrier R) :
    squareRootExternalTerminalTag z ∈
      lowWheelCanonicalRepeatedTerminalExternalPart R := by
  have hzBase := (Finset.mem_filter.mp hz).1
  have hzRepeated := (Finset.mem_filter.mp hz).2
  rcases mem_squareRootExternalTerminalFaceCarrier.mp hzBase with
    ⟨htAdm, hpRange, hpPrime, _htop⟩
  have _hdown := squareRootExternalTerminalTag_mem_downcross hR hzBase
  have htFiltered :
      z.1 ∈ (primesUpTo R).powerset.filter
        (fun t => primeFaceProduct t < R) := by
    rw [← admissiblePrimeFaces_pred_eq_lowCube_filter_product_lt R (by omega)]
    exact htAdm
  have htSub := Finset.mem_powerset.mp (Finset.mem_filter.mp htFiltered).1
  have hpivot :
      lowWheelTaggedDowncrossPivot (squareRootExternalTerminalTag z) = z.2 := by
    simp [squareRootExternalTerminalTag, lowWheelTaggedDowncrossPivot,
      lowWheelCanonicalCofactorQuotientPivot, hpPrime.minFac_eq]
  have hface :
      ∀ q ∈ (squareRootExternalTerminalTag z).1,
        q < lowWheelTaggedDowncrossPivot (squareRootExternalTerminalTag z) := by
    intro q hq
    have hqR := (mem_primesUpTo.mp (htSub hq)).2
    have hRp := (Finset.mem_Ioc.mp hpRange).1
    rw [hpivot]
    omega
  have hfrozen : squareRootExternalTerminalTag z ∈
      lowWheelCanonicalRepeatedFrozenPart R := by
    apply Finset.mem_filter.mpr
    refine ⟨hzRepeated, ?_⟩
    constructor
    · simpa [squareRootExternalTerminalTag] using hpivot.symm
    · exact hface
  have hterminal : squareRootExternalTerminalTag z ∈
      lowWheelCanonicalRepeatedTerminalBoundary R := by
    apply Finset.mem_filter.mpr
    exact ⟨hfrozen, by simp [squareRootExternalTerminalTag]⟩
  apply Finset.mem_filter.mpr
  refine ⟨hterminal, ?_⟩
  rw [hpivot]
  exact (Finset.mem_Ioc.mp hpRange).1

private theorem repeatedExternal_to_faceCarrier
    {R : ℕ} (hR : 2 ≤ R)
    {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalExternalPart R) :
    (y.1, lowWheelTaggedDowncrossPivot y) ∈
      squareRootExternalTerminalRepeatedFaceCarrier R := by
  have hterminal := (Finset.mem_filter.mp hy).1
  have _hgt := (Finset.mem_filter.mp hy).2
  have hgeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
  have htagged : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R := by
    have hfrozen := (Finset.mem_filter.mp hterminal).1
    have hrepeated := (Finset.mem_filter.mp hfrozen).1
    exact (Finset.mem_filter.mp hrepeated).1
  have htagData := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hhigh := lowWheelCanonicalRepeatedExternalTerminal_highPrime_data
    (show y ∈ lowWheelCanonicalRepeatedTerminalExternalPart R from hy)
  have htFiltered :
      y.1 ∈ (primesUpTo R).powerset.filter
        (fun t => primeFaceProduct t < R) := by
    apply Finset.mem_filter.mpr
    exact ⟨htagData.1, (Finset.mem_Ico.mp hhigh.1).2⟩
  have htAdm : y.1 ∈ admissiblePrimeFaces (R - 1) := by
    rw [admissiblePrimeFaces_pred_eq_lowCube_filter_product_lt R (by omega)]
    exact htFiltered
  have hpData :
      lowWheelTaggedDowncrossPivot y ∈
        Finset.Ioc R (squareRootEndpoint R) ∧
      (lowWheelTaggedDowncrossPivot y).Prime ∧
      primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y ≤
        squareRootEndpoint R := by
    unfold squareRootHighPrimeCofactorSet at hhigh
    exact Finset.mem_filter.mp hhigh.2.1
  have hzBase :
      (y.1, lowWheelTaggedDowncrossPivot y) ∈
        squareRootExternalTerminalFaceCarrier R := by
    apply mem_squareRootExternalTerminalFaceCarrier.mpr
    exact ⟨htAdm, hpData.1, hpData.2.1, hpData.2.2⟩
  apply Finset.mem_filter.mpr
  refine ⟨hzBase, ?_⟩
  have hrepeated := (Finset.mem_filter.mp (Finset.mem_filter.mp hterminal).1).1
  have htagEq :
      squareRootExternalTerminalTag
          (y.1, lowWheelTaggedDowncrossPivot y) = y := by
    exact Prod.ext rfl (Prod.ext hgeom.1.symm hgeom.2.1.symm)
  rw [htagEq]
  exact hrepeated

/-- The repeated external terminal signed mass is literally `ERrep` on the
pre-existing face/high-prime grid. -/
theorem lowWheelCanonicalRepeatedTerminalExternalLedger_eq_ERrep
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelCanonicalRepeatedTerminalExternalLedger R = squareRootERrep R := by
  unfold lowWheelCanonicalRepeatedTerminalExternalLedger squareRootERrep
  symm
  refine Finset.sum_bij
    (fun z _hz => squareRootExternalTerminalTag z)
    (fun z hz => externalTerminalTag_mem_repeatedExternal hR hz)
    (fun a _ha b _hb hab => squareRootExternalTerminalTag_injective hab)
    (fun y hy => by
      refine ⟨(y.1, lowWheelTaggedDowncrossPivot y),
        repeatedExternal_to_faceCarrier hR hy, ?_⟩
      have hterminal := (Finset.mem_filter.mp hy).1
      have hgeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
      exact Prod.ext rfl (Prod.ext hgeom.1.symm hgeom.2.1.symm))
    (fun z _hz => by
      simp [lowWheelTaggedDowncrossWeight, squareRootExternalTerminalTag,
        canonicalMoebiusWeight])

/-- Exact frozen-top/external normal form. -/
theorem lowWheelCanonicalDefectLedger_eq_unique_add_internal_add_ERrep_sub_topImage
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelCanonicalDefectLedger R =
      lowWheelCanonicalDowncrossUniqueParentLedger R +
        lowWheelCanonicalRepeatedTerminalInternalLedger R +
        squareRootERrep R - lowWheelFrozenCofactorTopImageLedger R := by
  rw [lowWheelCanonicalDefectLedger_eq_downcrossLedger,
    lowWheelCanonicalDowncrossLedger_eq_unique_add_terminal_sub_topImage,
    lowWheelCanonicalTerminalBoundaryLedger_eq_internal_add_external,
    lowWheelCanonicalRepeatedTerminalExternalLedger_eq_ERrep R hR]
  ring

/-- The single signed residual left after combining the frozen top image with
the external high-prime closure. -/
def lowWheelFrozenTopFarResidual (R : ℕ) : ℂ :=
  lowWheelCanonicalRepeatedTerminalInternalLedger R -
    lowWheelFrozenCofactorTopImageLedger R -
    survivorSixteenFarUpperPrimeMass (R - 1)

/-- For `R >= 56`, the complete canonical defect is the single frozen/top/far
residual plus only three already-root-scale ledgers. -/
theorem lowWheelCanonicalDefectLedger_eq_frozenTopFarResidual_add_rootTerms
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelCanonicalDefectLedger R =
      lowWheelFrozenTopFarResidual R +
        lowWheelCanonicalDowncrossUniqueParentLedger R +
        squareRootNearPrimeTransport R - squareRootERuniq R := by
  have hD :=
    lowWheelCanonicalDefectLedger_eq_unique_add_internal_add_ERrep_sub_topImage
      R (by omega)
  have hE := squareRootERrep_add_farSurvivor_eq_near_sub_ERuniq R hR
  unfold lowWheelFrozenTopFarResidual
  linear_combination hD + hE

/-- Quantitatively, every term outside `lowWheelFrozenTopFarResidual` is already
root scale.  No norm is taken inside that residual. -/
theorem norm_lowWheelCanonicalDefectLedger_le_frozenTopFarResidual_add_nine_root
    (R : ℕ) (hR : 56 ≤ R) :
    ‖lowWheelCanonicalDefectLedger R‖ ≤
      ‖lowWheelFrozenTopFarResidual R‖ + 9 * (R : ℝ) := by
  rw [lowWheelCanonicalDefectLedger_eq_frozenTopFarResidual_add_rootTerms R hR]
  have hU := norm_lowWheelCanonicalDowncrossUniqueParentLedger_le_root R
  have hN := norm_squareRootNearPrimeTransport_le R hR
  have hE := norm_squareRootERuniq_le_root R
  calc
    ‖lowWheelFrozenTopFarResidual R +
        lowWheelCanonicalDowncrossUniqueParentLedger R +
        squareRootNearPrimeTransport R - squareRootERuniq R‖ ≤
      ‖lowWheelFrozenTopFarResidual R +
          lowWheelCanonicalDowncrossUniqueParentLedger R +
          squareRootNearPrimeTransport R‖ + ‖squareRootERuniq R‖ :=
        norm_sub_le _ _
    _ ≤ (‖lowWheelFrozenTopFarResidual R +
            lowWheelCanonicalDowncrossUniqueParentLedger R‖ +
          ‖squareRootNearPrimeTransport R‖) + ‖squareRootERuniq R‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ((‖lowWheelFrozenTopFarResidual R‖ +
            ‖lowWheelCanonicalDowncrossUniqueParentLedger R‖) +
          ‖squareRootNearPrimeTransport R‖) + ‖squareRootERuniq R‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ((‖lowWheelFrozenTopFarResidual R‖ + (R : ℝ)) +
          7 * (R : ℝ)) + (R : ℝ) := by
        gcongr
    _ = ‖lowWheelFrozenTopFarResidual R‖ + 9 * (R : ℝ) := by ring

end RHLean.Proof
