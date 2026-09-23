import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoDefectCanonicalSeed
import RHLean.Proof.LowWheelFrozenSecondContactWindowDescent

/-!
# Canonical saturated seeds are the frozen second-contact source carrier

This module compares the canonical `SourceIndex` window introduced in
`LowWheelFrozenSecondContactScaleFlux` with the original physical frozen source.
It is an exact finite dictionary; no norm or estimate appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Every canonical saturated seed has one and only one physical frozen
second-contact source whose owner/parent-face coordinates recover the seed. -/
theorem lowWheelFrozenSecondContactCanonicalSeed_existsUnique_source
    {R : ℕ} {s : SourceIndex (squareRootEndpoint R)}
    (hs : s ∈ lowWheelFrozenSecondContactCanonicalSeeds R) :
    ∃! y : LowWheelTaggedDowncrossState,
      y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R ∧
      lowWheelFrozenSecondContactParentMap y =
        (sourcePrime s, squarefreePrimeFace (sourceCore s)) := by
  have hseed := mem_lowWheelFrozenSecondContactCanonicalSeeds_iff.mp hs
  have hadm := hseed.1
  change CanonicalSourceData (sourcePrime s) (sourceCore s) at hadm
  rcases hadm with ⟨hq, hc1, hsq, _hcop, hdom⟩
  let V := squarefreePrimeFace (sourceCore s)
  have hprod : primeFaceProduct V = sourceCore s := by
    simpa [V] using primeFaceProduct_squarefreePrimeFace hsq
  have hpred : V ∈ (primesUpTo (sourcePrime s - 1)).powerset := by
    apply Finset.mem_powerset.mpr
    intro p hp
    have hpFactors : p ∈ (sourceCore s).primeFactors := by
      simpa [V, squarefreePrimeFace] using hp
    have hpData := Nat.mem_primeFactors.mp hpFactors
    have hpLt : p < sourcePrime s := hdom p hpData.1 hpData.2.1
    exact mem_primesUpTo.mpr ⟨hpData.1, by omega⟩
  have hV : V ∈ lowWheelFrozenSecondContactHighOwnerWindow R (sourcePrime s) := by
    unfold lowWheelFrozenSecondContactHighOwnerWindow
    apply mem_frozenPrimeUniverseWindowFaces.mpr
    refine ⟨hpred, ?_, ?_⟩
    · rw [hprod]
      exact hseed.2.2.1
    · rw [hprod]
      exact hseed.2.2.2
  rcases lowWheelFrozenSecondContactParentMap_surjOn_highOwnerWindow
      hq hseed.2.1 hV with ⟨y, hy, hmap⟩
  have hmap' : lowWheelFrozenSecondContactParentMap y =
      (sourcePrime s, squarefreePrimeFace (sourceCore s)) := by
    simpa [V] using hmap
  refine ⟨y, ⟨hy, hmap'⟩, ?_⟩
  intro z hz
  exact (lowWheelFrozenSecondContactParentMap_injOn R)
    hz.1 hy (hz.2.trans hmap'.symm)

/-- Consequently every deep full-face Go defect seed already has a unique
physical frozen second-contact source on the same saturated owner/parent-face
coordinates. -/
theorem squareRootLowPrimeGoFullFaceDefectSaturated_existsUnique_frozenSource
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R) :
    ∃! y : LowWheelTaggedDowncrossState,
      y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R ∧
      lowWheelFrozenSecondContactParentMap y =
        (q, squarefreePrimeFace (r * d)) := by
  rcases squareRootLowPrimeGoFullFaceDefectSaturated_exists_canonicalSeed hz with
    ⟨child, hseed, hcq, hcc, _hgen⟩
  have h := lowWheelFrozenSecondContactCanonicalSeed_existsUnique_source hseed
  simpa [hcq, hcc] using h

/-- The overlap is same-sign, not a cancellation.  The unique frozen source
attached to a deep Go defect carries exactly the full-face Go source weight. -/
theorem squareRootLowPrimeGoFullFaceDefectSaturated_frozenSource_weight_eq
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R) :
    ∃! y : LowWheelTaggedDowncrossState,
      y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R ∧
      lowWheelFrozenSecondContactParentMap y =
        (q, squarefreePrimeFace (r * d)) ∧
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) =
        lowWheelFullTaggedPhysicalWeight
          (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) := by
  rcases squareRootLowPrimeGoFullFaceDefectSaturated_existsUnique_frozenSource hz with
    ⟨y, hy, hyUnique⟩
  have hyFrozen := (Finset.mem_filter.mp hy.1).1
  have hweight := lowWheelFrozenSecondContactParentMap_weight_eq_source hyFrozen
  have hparentWeight :
      lowWheelFrozenSecondContactParentWeight
          (lowWheelFrozenSecondContactParentMap y) =
        (booleanCubeSign (squarefreePrimeFace (r * d)) : ℂ) := by
    rw [hy.2]
    rfl
  have hgoWeight :
      lowWheelFullTaggedPhysicalWeight
          (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) =
        (booleanCubeSign (squarefreePrimeFace (r * d)) : ℂ) := by
    simp [squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoSecondBoundaryFullFaceSource,
      lowWheelFullTaggedPhysicalWeight, canonicalMoebiusWeight]
  have heq :
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) =
        lowWheelFullTaggedPhysicalWeight
          (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) := by
    calc
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) =
          lowWheelFrozenSecondContactParentWeight
            (lowWheelFrozenSecondContactParentMap y) := hweight.symm
      _ = (booleanCubeSign (squarefreePrimeFace (r * d)) : ℂ) := hparentWeight
      _ = lowWheelFullTaggedPhysicalWeight
          (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) := hgoWeight.symm
  refine ⟨y, ⟨hy.1, hy.2, heq⟩, ?_⟩
  intro z hz'
  apply hyUnique
  exact ⟨hz'.1, hz'.2.1⟩

end RHLean.Proof