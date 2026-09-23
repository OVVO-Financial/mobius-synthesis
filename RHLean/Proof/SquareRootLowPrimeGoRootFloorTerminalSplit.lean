import Mathlib
import RHLean.Proof.SquareRootLowPrimeCanonicalSeedSourceBridge
import RHLean.Proof.LowWheelCanonicalRepeatedTerminalCutoff

/-!
# Root-floor full-face defects are unique or internal terminal downcrosses

The root-floor half of the full-face Go source has state

`(squarefreePrimeFace (r*d), (1,q))`

with `r*d <= R < q*(r*d)`, every face prime below `q`, and `q < R`.
Thus it is a literal canonical root-downcross with frozen `c=1` terminal shape.
The already-compiled unique/repeated parent partition then gives an exact
classification: either the occurrence is in the root-cardinality unique-parent
carrier, or it is a repeated internal terminal state.  No estimate or prime-gap
input is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A root-floor full-face source is literally on the canonical downcross
carrier. -/
theorem squareRootLowPrimeGoFullFaceDefectRootFloorSource_mem_downcross
    {R r q d : ℕ}
    (hR : 2 ≤ R)
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R) :
    squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d) ∈
      lowWheelCanonicalTaggedDowncrossCarrier R := by
  have hzFull :=
    (mem_squareRootLowPrimeGoFullFaceDefectRootFloorIncidences.mp hz).1
  have hroot :=
    (mem_squareRootLowPrimeGoFullFaceDefectRootFloorIncidences.mp hz).2
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hzFull with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, hcube, hd⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hphysicalFull :=
    squareRootLowPrimeGoSecondBoundaryFullFaceSource_mem_transport
      hR hq hr hrq hcube hd
  have hphysicalData := mem_lowWheelFullTaggedPhysicalCarrier.mp hphysicalFull
  have hfaceProd :
      primeFaceProduct
          (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)).1 =
        r * d := by
    simpa [squareRootLowPrimeGoFullFaceDefectSourceTag] using
      squareRootLowPrimeGoSecondBoundaryFullFaceSource_faceProduct
        hq hr hrq hfull
  have hpivot :
      lowWheelCanonicalCofactorQuotientPivot
          (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)).2 = q := by
    simp [squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoSecondBoundaryFullFaceSource,
      lowWheelCanonicalCofactorQuotientPivot, hq.minFac_eq]
  apply mem_lowWheelCanonicalTaggedDowncrossCarrier.mpr
  refine ⟨hphysicalData.1, mem_lowWheelCanonicalDowncrossPart.mpr ?_⟩
  refine ⟨hphysicalData.2, ?_, ?_⟩
  · rw [hpivot]
    exact hq.not_dvd_one
  · change primeFaceProduct
        (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)).1 *
        ((squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)).2.2 /
          lowWheelCanonicalCofactorQuotientPivot
            (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)).2) ≤ R
    rw [hpivot]
    change primeFaceProduct
        (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)).1 *
        (q / q) ≤ R
    rw [Nat.div_self hq.pos, Nat.mul_one, hfaceProd]
    exact hroot

/-- The same occurrence has the literal frozen terminal shape: quotient equals
its prime pivot and every Boolean-face prime is smaller than that pivot. -/
theorem squareRootLowPrimeGoFullFaceDefectRootFloorSource_frozenShape
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R) :
    LowWheelDowncrossFrozenShape
      (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) := by
  have hzFull :=
    (mem_squareRootLowPrimeGoFullFaceDefectRootFloorIncidences.mp hz).1
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hzFull with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, hd⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth hq hr hrq hfull
  have hpivot :
      lowWheelCanonicalCofactorQuotientPivot
          (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)).2 = q := by
    simp [squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoSecondBoundaryFullFaceSource,
      lowWheelCanonicalCofactorQuotientPivot, hq.minFac_eq]
  constructor
  · change q = _
    exact hpivot.symm
  · intro p hp
    change p < lowWheelCanonicalCofactorQuotientPivot
      (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)).2
    rw [hpivot]
    have hpFactors : p ∈ (r * d).primeFactors := by
      simpa [squareRootLowPrimeGoFullFaceDefectSourceTag,
        squareRootLowPrimeGoSecondBoundaryFullFaceSource,
        squarefreePrimeFace] using hp
    have hpData := Nat.mem_primeFactors.mp hpFactors
    exact hchild.1.2.2.2.2 p hpData.1 hpData.2.1

/-- **Exact root-floor classification.**  No third boundary type occurs: the
full-face source is either in the existing unique-parent root carrier, or in the
existing repeated internal-terminal carrier. -/
theorem squareRootLowPrimeGoFullFaceDefectRootFloorSource_unique_or_internalTerminal
    {R r q d : ℕ}
    (hR : 2 ≤ R)
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R) :
    squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d) ∈
        lowWheelCanonicalDowncrossUniqueParentPart R ∨
      squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d) ∈
        lowWheelCanonicalRepeatedTerminalInternalPart R := by
  let y := squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)
  have hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R := by
    simpa [y] using
      squareRootLowPrimeGoFullFaceDefectRootFloorSource_mem_downcross hR hz
  have hfrozen : LowWheelDowncrossFrozenShape y := by
    simpa [y] using
      squareRootLowPrimeGoFullFaceDefectRootFloorSource_frozenShape hz
  have hsplit :
      y ∈ lowWheelCanonicalDowncrossUniqueParentPart R ∨
        y ∈ lowWheelCanonicalDowncrossRepeatedParentPart R := by
    have hu : y ∈
        lowWheelCanonicalDowncrossUniqueParentPart R ∪
          lowWheelCanonicalDowncrossRepeatedParentPart R := by
      rw [← lowWheelCanonicalTaggedDowncrossCarrier_eq_unique_union_repeated R]
      exact hy
    exact Finset.mem_union.mp hu
  rcases hsplit with hu | hrp
  · exact Or.inl hu
  · right
    have hfc : y ∈ lowWheelCanonicalRepeatedFrozenPart R :=
      Finset.mem_filter.mpr ⟨hrp, hfrozen⟩
    have hterminal : y ∈ lowWheelCanonicalRepeatedTerminalBoundary R := by
      apply Finset.mem_filter.mpr
      refine ⟨hfc, ?_⟩
      rfl
    apply Finset.mem_filter.mpr
    refine ⟨hterminal, ?_⟩
    have hzFull :=
      (mem_squareRootLowPrimeGoFullFaceDefectRootFloorIncidences.mp hz).1
    have hqR :=
      (mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hzFull).2.1
    have hq :=
      (mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hzFull).2.2.2.2.1
    have hpivot : lowWheelTaggedDowncrossPivot y = q := by
      simp [y, squareRootLowPrimeGoFullFaceDefectSourceTag,
        squareRootLowPrimeGoSecondBoundaryFullFaceSource,
        lowWheelTaggedDowncrossPivot,
        lowWheelCanonicalCofactorQuotientPivot, hq.minFac_eq]
    rw [hpivot]
    omega

end RHLean.Proof