import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoDefectAncestryGeneration
import RHLean.Proof.LowWheelFrozenSecondContactScaleFlux

/-!
# Full-face defect on the saturated canonical seed carrier

The deep part of the full-face Go defect is not merely an arithmetic child
of the saturated second-contact population.  Its canonical ancestry child is a
literal member of the existing saturated seed window
`lowWheelFrozenSecondContactCanonicalSeeds R`.

The complementary root-floor incidence fails that same seed predicate at one
named condition only: its core lies at or below `R`.

No norm or estimate appears here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge
open CanonicalGapAncestryEnergyBridge

attribute [local instance] Classical.propDecidable

/-- **Deep defect = saturated canonical seed.**  For `R < r*d`, the ancestry
child `(q,r*d)` lies in the exact `max R (X_R/q^2)` saturated seed window. -/
theorem squareRootLowPrimeGoFullFaceDefectSaturated_exists_canonicalSeed
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R) :
    ∃ child : SourceIndex (squareRootEndpoint R),
      child ∈ lowWheelFrozenSecondContactCanonicalSeeds R ∧
      sourcePrime child = q ∧ sourceCore child = r * d ∧
      sourceGeneration (squareRootEndpoint R) 1 child = -sourceWeight child := by
  have hzFull :=
    (mem_squareRootLowPrimeGoFullFaceDefectSaturatedIncidences.mp hz).1
  have hroot :=
    (mem_squareRootLowPrimeGoFullFaceDefectSaturatedIncidences.mp hz).2
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hzFull with
    ⟨_hrR, hqR, _hdR, hr, hq, hrq, hcube, hd⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hphysical :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).2
  have hfirst :=
    squareRootLowPrimeGoFullBirthBoundary_firstContact_le hq hrq hcube hfull
  rcases squareRootLowPrimeGoFullFaceDefect_generationOne_eq_neg_childWeight hzFull with
    ⟨child, hcq, hcc, hsmooth, hgen⟩
  have hdeep : squareRootEndpoint R / (q * q) < r * d := by
    have h := (Nat.div_lt_iff_lt_mul hr.pos).1 hphysical
    simpa [Nat.div_div_eq_div_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using h
  have hupper : r * d ≤ squareRootEndpoint R / q := by
    apply (Nat.le_div_iff_mul_le hq.pos).2
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hfirst
  have hseed : child ∈ lowWheelFrozenSecondContactCanonicalSeeds R := by
    rw [mem_lowWheelFrozenSecondContactCanonicalSeeds_iff]
    refine ⟨hsmooth.1, ?_, ?_, ?_⟩
    · simpa [hcq] using hqR
    · rw [hcq, hcc]
      exact max_lt hroot hdeep
    · rw [hcq, hcc]
      exact hupper
  exact ⟨child, hseed, hcq, hcc, hgen⟩

/-- The root-floor complement cannot be a saturated canonical seed with the
same `(q,r*d)` coordinates: it fails the strict `R < sourceCore` part of the
`max R ...` lower wall. -/
theorem squareRootLowPrimeGoFullFaceDefectRootFloor_no_matching_canonicalSeed
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R) :
    ¬ ∃ child : SourceIndex (squareRootEndpoint R),
      child ∈ lowWheelFrozenSecondContactCanonicalSeeds R ∧
      sourcePrime child = q ∧ sourceCore child = r * d := by
  intro hex
  rcases hex with ⟨child, hseed, _hcq, hcc⟩
  have hroot :=
    (mem_squareRootLowPrimeGoFullFaceDefectRootFloorIncidences.mp hz).2
  have hdata := mem_lowWheelFrozenSecondContactCanonicalSeeds_iff.mp hseed
  have hgt : R < sourceCore child :=
    lt_of_le_of_lt (le_max_left R
      (squareRootEndpoint R /
        (sourcePrime child * sourcePrime child))) hdata.2.2.1
  rw [hcc] at hgt
  omega

end RHLean.Proof