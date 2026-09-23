import Mathlib
import RHLean.Proof.SquareRootLowPrimeCombinedTaggedElevenPushforward
import RHLean.Proof.CanonicalGapAncestryEnergyBridge

/-!
# The full-face Go defect is the first canonical ancestry generation

This module is purely an exact coordinate bridge.  For a live full-face defect
incidence `((r,q),d)`, the existing Go ancestry theorems already say that

`(q,d) -> (q,r*d)`

is one canonical parent edge: `d < q < r*d`, the parent is transport-oriented,
the child is smooth-oriented, and stripping the largest prime `r` from the
child core recovers `d`.

Packaging both endpoints in the bounded source universe at
`B = squareRootEndpoint R` shows more: the unsigned ancestry generation-one
field at the child is exactly the root-parent weight.  The physical full-face
source carries that same weight.  Thus the Go defect is literally a
restriction of `sourceGeneration B 1`, with no norm and no new observable.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge
open CanonicalGapAncestryEnergyBridge

attribute [local instance] Classical.propDecidable

/-- **Typed depth-one ancestry realization.**  Every full-face Go defect
incidence packages into a transport root and its immediate smooth child in the
bounded canonical ancestry flow at the physical square endpoint. -/
theorem squareRootLowPrimeGoFullFaceDefect_depthOneAncestry
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    ∃ parent child : SourceIndex (squareRootEndpoint R),
      sourcePrime parent = q ∧
      sourceCore parent = d ∧
      sourcePrime child = q ∧
      sourceCore child = r * d ∧
      TransportOriented parent ∧
      SmoothOriented child ∧
      sourceParent child = some parent ∧
      lowWheelFullTaggedPhysicalWeight
          (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) =
        ((sourceGeneration (squareRootEndpoint R) 1 child : ℤ) : ℂ) := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, hcube, hd⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hparentData :=
    squareRootLowPrimeGoFullBirthBoundary_parent_canonicalRoot
      hq hr hrq hfull
  have hchildData :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth
      hq hr hrq hfull
  have hfirst :=
    squareRootLowPrimeGoFullBirthBoundary_firstContact_le
      hq hrq hcube hfull
  have hqX : q ≤ squareRootEndpoint R := by
    have hq3 : q ≤ q ^ 3 := by
      calc
        q = q * 1 := by simp
        _ ≤ q * q := Nat.mul_le_mul_left q hq.one_le
        _ ≤ q * (q * q) := by
          exact Nat.mul_le_mul_left q (Nat.le_mul_of_pos_right q hq.pos)
        _ = q ^ 3 := by ring
    exact hq3.trans hcube
  have hdX : d ≤ squareRootEndpoint R :=
    (Nat.le_of_lt hparentData.2).trans hqX
  have hrdX : r * d ≤ squareRootEndpoint R := by
    have hqOne : 1 ≤ q := hq.one_le
    have hle : r * d ≤ q * (r * d) := by
      simpa using Nat.mul_le_mul_right (r * d) hqOne
    exact hle.trans (by
      simpa [Nat.mul_assoc] using hfirst)
  let parent : SourceIndex (squareRootEndpoint R) :=
    (⟨q, Nat.lt_succ_of_le hqX⟩, ⟨d, Nat.lt_succ_of_le hdX⟩)
  let child : SourceIndex (squareRootEndpoint R) :=
    (⟨q, Nat.lt_succ_of_le hqX⟩, ⟨r * d, Nat.lt_succ_of_le hrdX⟩)
  have hparentAdm : SourceAdmissible parent := by
    change CanonicalSourceData q d
    exact hparentData.1
  have hchildAdm : SourceAdmissible child := by
    change CanonicalSourceData q (r * d)
    exact hchildData.1
  have hparentTransport : TransportOriented parent := by
    refine ⟨hparentAdm, ?_⟩
    change d ≤ q
    exact hparentData.2.le
  have hchildSmooth : SmoothOriented child := by
    refine ⟨hchildAdm, ?_⟩
    change q < r * d
    exact hchildData.2
  have hcofactor :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalCofactor hr hfull
  have hparentIndex : parentIndex child hchildSmooth = parent := by
    apply Prod.ext
    · apply Fin.ext
      rfl
    · apply Fin.ext
      change canonicalCofactor (r * d) = d
      exact hcofactor
  have hchildParent : sourceParent child = some parent := by
    rw [smoothSource_has_parent child hchildSmooth, hparentIndex]
  have hparentNone : sourceParent parent = none :=
    (sourceParent_eq_none_iff_transport parent hparentAdm).2 hparentTransport
  have hgen :
      sourceGeneration (squareRootEndpoint R) 1 child = sourceWeight parent := by
    rw [show 1 = 0 + 1 by norm_num,
      sourceGeneration_succ, sourceGeneration_zero]
    simp [boundedSourceFlow, ParentFlow.successorOperator, hchildParent,
      ParentFlow.rootField, hparentNone]
  have hparentWeight : sourceWeight parent = (μ (q * d) : ℤ) := by
    rw [sourceWeight_of_admissible parent hparentAdm]
    rfl
  have hsource :=
    squareRootLowPrimeGoSecondBoundaryFullFaceSource_weight_eq
      hq hr hrq hfull
  refine ⟨parent, child, rfl, rfl, rfl, rfl,
    hparentTransport, hchildSmooth, hchildParent, ?_⟩
  rw [hgen, hparentWeight]
  simpa [squareRootLowPrimeGoFullFaceDefectSourceTag,
    canonicalMoebiusWeight] using hsource

/-- The same statement with the sign reversal exposed.  Generation one is the
root-parent weight; the actual smooth child source has the opposite weight. -/
theorem squareRootLowPrimeGoFullFaceDefect_generationOne_eq_neg_childWeight
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    ∃ child : SourceIndex (squareRootEndpoint R),
      sourcePrime child = q ∧ sourceCore child = r * d ∧
      SmoothOriented child ∧
      sourceGeneration (squareRootEndpoint R) 1 child = -sourceWeight child := by
  rcases squareRootLowPrimeGoFullFaceDefect_depthOneAncestry hz with
    ⟨parent, child, _hp, _hc, hcq, hcc, htrans, hsmooth, hparent, _hweight⟩
  have hparentNone : sourceParent parent = none :=
    (sourceParent_eq_none_iff_transport parent htrans.1).2 htrans
  have hgen :
      sourceGeneration (squareRootEndpoint R) 1 child = sourceWeight parent := by
    rw [show 1 = 0 + 1 by norm_num,
      sourceGeneration_succ, sourceGeneration_zero]
    simp [boundedSourceFlow, ParentFlow.successorOperator, hparent,
      ParentFlow.rootField, hparentNone]
  have hsign := sourceWeight_signReversal child parent hparent
  refine ⟨child, hcq, hcc, hsmooth, ?_⟩
  rw [hgen]
  linarith

end RHLean.Proof