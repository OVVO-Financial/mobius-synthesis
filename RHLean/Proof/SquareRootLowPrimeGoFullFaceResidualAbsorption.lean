import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoFullFacePartner
import RHLean.Proof.LowWheelFrozenFirstFailureBridge

/-!
# Absorb the full-face Go defect mate into the existing physical residual

An earlier layer embeds every unfinished two-boundary Go defect into the literal full
physical carrier and pairs it with the existing full-face/quotient Othello
mate.  The remaining bookkeeping question is where those mate occurrences sit
inside the earlier frozen/top/far normal form.

This file proves that the far part of the complete Go-defect mate image is
already a subcarrier of the literal hard physical residual.  The key geometric
fact is that a defect mate has a face prime strictly *above* its canonical
pivot.  A frozen top image has every face prime strictly below its unchanged
pivot, so the populations are disjoint.  The defect mate quotient is also at
least two, making it disjoint from the internal-terminal mate image, whose
cofactor/quotient state is exactly `(1,1)`.

Thus the far Go-defect correction is not an additional scalar error term.  It is
already present, with opposite sign, inside the old physical residual and can be
cancelled there before any norm is taken.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open FrozenCofactorTopBottom
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Every face prime of a frozen-top image lies strictly below its unchanged
canonical pivot. -/
theorem lowWheelFrozenCofactorTopImage_facePrime_lt_pivot
    {R : ℕ} {z : LowWheelTaggedDowncrossState}
    (hz : z ∈ lowWheelFrozenCofactorTopImage R)
    {a : ℕ} (ha : a ∈ z.1) :
    a < lowWheelCanonicalCofactorQuotientPivot z.2 := by
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  change a ∈ y.1 at ha
  rw [lowWheelFrozenCofactorTopToggle_pivot]
  exact lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy ha

/-- On a live Go defect source, the least active full-face prime is strictly
below the interior owner `r` and lies on the Boolean face rather than in the
outer quotient. -/
theorem squareRootLowPrimeGoFullFaceDefect_oppositePrime_lt_interior
    {R r q d : ℕ} (_hR : 2 ≤ R)
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    let s := squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)
    let p := lowWheelFullOppositePrime R s
    (lowWheelFullActivePrimeSet R s).Nonempty ∧
      p.Prime ∧ p < r ∧ p ∈ s.1 := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, hqR, _hdR, hr, hq, hrq, hcube, hd⟩
  let s := squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)
  let p := lowWheelFullOppositePrime R s
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hdgt : 1 < d :=
    squareRootLowPrimeGoFullBirthBoundary_parent_one_lt hr hrq hfull
  obtain ⟨a, haPrime, haDvd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hrough :=
    (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull).2.2.2.1
  have haLe : a ≤ canonicalLargestPrimeFactor d :=
    prime_dvd_le_canonicalLargestPrimeFactor hdgt haPrime haDvd
  have har : a < r := haLe.trans_lt hrough
  have hdPos : 0 < d := by omega
  have hrdNe : r * d ≠ 0 :=
    Nat.mul_ne_zero hr.ne_zero (Nat.ne_of_gt hdPos)
  have haFace : a ∈ s.1 := by
    have haProd : a ∣ r * d := dvd_mul_of_dvd_right haDvd r
    have haFactors : a ∈ (r * d).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨haPrime, haProd, hrdNe⟩
    simpa [s, squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoSecondBoundaryFullFaceSource,
      squarefreePrimeFace] using haFactors
  have haGlobal : a ∈ primesUpTo R :=
    mem_primesUpTo.mpr ⟨haPrime, by omega⟩
  have haActive : a ∈ lowWheelFullActivePrimeSet R s :=
    mem_lowWheelFullActivePrimeSet.mpr ⟨haGlobal, Or.inl haFace⟩
  have hnonempty : (lowWheelFullActivePrimeSet R s).Nonempty := ⟨a, haActive⟩
  have hpLeA : p ≤ a := by
    dsimp only [p]
    unfold lowWheelFullOppositePrime
    rw [dif_pos hnonempty]
    exact Finset.min'_le _ _ haActive
  have hpr : p < r := hpLeA.trans_lt har
  have hpData := lowWheelFullOppositePrime_data hnonempty
  have hpPrime : p.Prime := prime_of_mem_primesUpTo hpData.1
  have hpNotDvdQ : ¬ p ∣ q := by
    intro hpq
    have hpEqQ := (Nat.prime_dvd_prime_iff_eq hpPrime hq).mp hpq
    omega
  have hpFace : p ∈ s.1 := by
    have hactive : p ∈ s.1 ∨ p ∣ s.2.2 := hpData.2
    have hsQuot : s.2.2 = q := by
      rfl
    rw [hsQuot] at hactive
    exact hactive.resolve_right hpNotDvdQ
  exact ⟨hnonempty, hpPrime, hpr, hpFace⟩

/-- A complete Go-defect mate retains the interior owner `r` on its face while
its canonical pivot is strictly smaller.  This is the orientation opposite to
a frozen-top image. -/
theorem squareRootLowPrimeGoFullFaceDefectMateTag_exists_facePrime_gt_pivot
    {R r q d : ℕ} (hR : 2 ≤ R)
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    ∃ a ∈ (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).1,
      lowWheelCanonicalCofactorQuotientPivot
          (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2 < a := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, hd⟩
  let s := squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)
  let p := lowWheelFullOppositePrime R s
  have hpData :=
    squareRootLowPrimeGoFullFaceDefect_oppositePrime_lt_interior hR hz
  dsimp only at hpData
  rcases hpData with ⟨hnonempty, hpPrime, hpr, hpFace⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hd1 := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull).1
  have hdPos : 0 < d := by omega
  have hrDvd : r ∣ r * d := dvd_mul_right r d
  have hrdNe : r * d ≠ 0 :=
    Nat.mul_ne_zero hr.ne_zero (Nat.ne_of_gt hdPos)
  have hrFace : r ∈ s.1 := by
    have hrFactors : r ∈ (r * d).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hr, hrDvd, hrdNe⟩
    simpa [s, squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoSecondBoundaryFullFaceSource,
      squarefreePrimeFace] using hrFactors
  have hprNe : p ≠ r := ne_of_lt hpr
  have hrMate :
      r ∈ (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).1 := by
    change r ∈ (lowWheelFullFaceQuotientMate R s).1
    unfold lowWheelFullFaceQuotientMate
    rw [dif_pos hnonempty]
    change r ∈ (lowWheelFullFaceQuotientToggleAt p s).1
    unfold lowWheelFullFaceQuotientToggleAt
    dsimp only
    unfold lowWheelFaceTailToggleAt
    rw [if_pos hpFace]
    exact Finset.mem_erase.mpr ⟨hprNe.symm, hrFace⟩
  have hpDvdMate :
      p ∣ (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2.1 *
        (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2.2 := by
    change p ∣ (lowWheelFullFaceQuotientMate R s).2.1 *
      (lowWheelFullFaceQuotientMate R s).2.2
    unfold lowWheelFullFaceQuotientMate
    rw [dif_pos hnonempty]
    change p ∣ (lowWheelFullFaceQuotientToggleAt p s).2.1 *
      (lowWheelFullFaceQuotientToggleAt p s).2.2
    unfold lowWheelFullFaceQuotientToggleAt
    dsimp only
    unfold lowWheelFaceTailToggleAt
    rw [if_pos hpFace]
    exact ⟨s.2.1 * s.2.2, by ring⟩
  have hpivotLe :
      lowWheelCanonicalCofactorQuotientPivot
          (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2 ≤ p := by
    unfold lowWheelCanonicalCofactorQuotientPivot
    exact Nat.minFac_le_of_dvd hpPrime.two_le hpDvdMate
  exact ⟨r, hrMate, hpivotLe.trans_lt hpr⟩

/-- A Go-defect mate has nontrivial quotient.  Hence it cannot coincide with an
internal-terminal mate image, whose complete state is `(1,1)`. -/
theorem squareRootLowPrimeGoFullFaceDefectMateTag_quotient_two_le
    {R r q d : ℕ} (hR : 2 ≤ R)
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    2 ≤ (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2.2 := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, _hr, hq, _hrq, _hcube, _hd⟩
  let s := squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)
  let p := lowWheelFullOppositePrime R s
  have hpData :=
    squareRootLowPrimeGoFullFaceDefect_oppositePrime_lt_interior hR hz
  dsimp only at hpData
  rcases hpData with ⟨hnonempty, hpPrime, _hpr, hpFace⟩
  have hquot :
      (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2.2 = p * q := by
    change (lowWheelFullFaceQuotientMate R s).2.2 = p * q
    unfold lowWheelFullFaceQuotientMate
    rw [dif_pos hnonempty]
    change (lowWheelFullFaceQuotientToggleAt p s).2.2 = p * q
    unfold lowWheelFullFaceQuotientToggleAt
    dsimp only
    unfold lowWheelFaceTailToggleAt
    rw [if_pos hpFace]
    rfl
  rw [hquot]
  exact hpPrime.two_le.trans (Nat.le_mul_of_pos_right p hq.pos)

/-- The complete Go-defect mate image is disjoint from the old frozen-top image.
The former has a face prime above its pivot; the latter has all face primes
below its pivot. -/
theorem squareRootLowPrimeGoFullFaceDefectMateImage_disjoint_topImage
    {R : ℕ} (hR : 2 ≤ R) :
    Disjoint (squareRootLowPrimeGoFullFaceDefectMateImage R)
      (lowWheelFrozenCofactorTopImage R) := by
  rw [Finset.disjoint_left]
  intro z hzMate hzTop
  rcases Finset.mem_image.mp hzMate with ⟨i, hi, rfl⟩
  rcases i with ⟨⟨r, q⟩, d⟩
  obtain ⟨a, haFace, hpivotLt⟩ :=
    squareRootLowPrimeGoFullFaceDefectMateTag_exists_facePrime_gt_pivot hR hi
  have haTop := lowWheelFrozenCofactorTopImage_facePrime_lt_pivot hzTop haFace
  omega

/-- The complete Go-defect mate image is also disjoint from the internal-terminal
mate image. -/
theorem squareRootLowPrimeGoFullFaceDefectMateImage_disjoint_internalMate
    {R : ℕ} (hR : 2 ≤ R) :
    Disjoint (squareRootLowPrimeGoFullFaceDefectMateImage R)
      (lowWheelCanonicalRepeatedTerminalInternalMateImage R) := by
  rw [Finset.disjoint_left]
  intro z hzMate hzInternal
  rcases Finset.mem_image.mp hzMate with ⟨i, hi, rfl⟩
  rcases i with ⟨⟨r, q⟩, d⟩
  have htwo := squareRootLowPrimeGoFullFaceDefectMateTag_quotient_two_le hR hi
  have hone := lowWheelCanonicalRepeatedTerminalInternalMateImage_state_eq_one hzInternal
  have hquot :
      (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)).2.2 = 1 :=
    congrArg Prod.snd hone
  omega

/-- Far part of the Go-defect mate image. -/
def squareRootLowPrimeGoFullFaceDefectMateFarImage (R : ℕ) :
    Finset LowWheelFullTaggedPhysicalState :=
  (squareRootLowPrimeGoFullFaceDefectMateImage R).filter fun z =>
    R + 8 ≤ lowWheelTaggedHighProduct z

/-- Every far Go-defect mate is a literal far physical occurrence. -/
theorem squareRootLowPrimeGoFullFaceDefectMateFarImage_subset_farPhysical
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeGoFullFaceDefectMateFarImage R ⊆
      lowWheelFarTaggedPhysicalCarrier R := by
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hzImage, hfar⟩
  exact mem_lowWheelFarTaggedPhysicalCarrier.mpr
    ⟨squareRootLowPrimeGoFullFaceDefectMateImage_subset_transport hR hzImage,
      hfar⟩

/-- The far defect-mate image is disjoint from both image populations that were
already removed when the old hard physical residual was formed. -/
theorem squareRootLowPrimeGoFullFaceDefectMateFarImage_disjoint_owned
    {R : ℕ} (hR : 2 ≤ R) :
    Disjoint (squareRootLowPrimeGoFullFaceDefectMateFarImage R)
      (lowWheelFrozenTopFarOwnedImage R) := by
  rw [Finset.disjoint_left]
  intro z hzFar hzOwned
  have hzImage := (Finset.mem_filter.mp hzFar).1
  rcases Finset.mem_union.mp hzOwned with hzInternal | hzTop
  · have hdisj :=
      Finset.disjoint_left.mp
        (squareRootLowPrimeGoFullFaceDefectMateImage_disjoint_internalMate hR)
    exact hdisj hzImage (Finset.mem_filter.mp hzInternal).1
  · have hdisj :=
      Finset.disjoint_left.mp
        (squareRootLowPrimeGoFullFaceDefectMateImage_disjoint_topImage hR)
    exact hdisj hzImage hzTop

/-- **Residual absorption.**  Every far unfinished Go second-boundary defect mate
already lies in the literal hard physical residual carrier.  Hence its signed
cancellation partner must be removed there before any norm/frame estimate is
applied. -/
theorem squareRootLowPrimeGoFullFaceDefectMateFarImage_subset_physicalResidual
    {R : ℕ} (hR : 6 ≤ R) :
    squareRootLowPrimeGoFullFaceDefectMateFarImage R ⊆
      lowWheelFrozenTopFarPhysicalResidualCarrier R := by
  intro z hz
  apply Finset.mem_sdiff.mpr
  refine ⟨squareRootLowPrimeGoFullFaceDefectMateFarImage_subset_farPhysical
      (by omega) hz, ?_⟩
  intro hzOwned
  exact (Finset.disjoint_left.mp
    (squareRootLowPrimeGoFullFaceDefectMateFarImage_disjoint_owned
      (R := R) (by omega))) hz hzOwned

/-- The second-contact defect is automatically far: its square contact lies
above `R²-1`, whereas its outer prime is at most half the root. -/
theorem squareRootLowPrimeGoFullFaceDefectMateTag_far
    {R r q d : ℕ} (hR : 6 ≤ R)
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    R + 8 ≤ lowWheelTaggedHighProduct
      (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)) := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, hcube, hd⟩
  have hp := squareRootLowPrimeGoFullFaceDefect_oppositePrime_lt_interior
    (by omega : 2 ≤ R) hz
  dsimp only at hp
  have hr3 : 3 ≤ r := by have := hp.2.1.two_le; omega
  have hq5 : 5 ≤ q := by
    have hq4 : q ≠ 4 := by intro h; subst q; norm_num at hq
    omega
  have h125 : 125 ≤ q ^ 3 := by
    have := Nat.pow_le_pow_left hq5 3
    norm_num at this
    exact this
  have hR12 : 12 ≤ R := by
    unfold squareRootEndpoint at hcube
    have hsq : 125 ≤ R ^ 2 := le_trans h125 (hcube.trans (Nat.sub_le _ _))
    nlinarith
  have hfour : 4 * (q * q) ≤ q * (q * q) :=
    Nat.mul_le_mul_right (q * q) (by omega : 4 ≤ q)
  have hhalf : 2 * q ≤ R := by
    have hsq := hcube.trans (Nat.sub_le (R ^ 2) 1)
    nlinarith
  have hsecond :=
    squareRootLowPrimeGoSecondBoundaryDefect_secondContact_gt hq hr hd
  have hfull := (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hprod : lowWheelTaggedHighProduct
      (squareRootLowPrimeGoFullFaceDefectMateTag R ((r, q), d)) = (r * d) * q := by
    unfold squareRootLowPrimeGoFullFaceDefectMateTag lowWheelFullFaceQuotientMate
    rw [dif_pos hp.1]
    unfold lowWheelTaggedHighProduct
    rw [lowWheelFullFaceQuotientToggleAt_highProduct]
    change primeFaceProduct
      (squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d).1 * q = _
    rw [squareRootLowPrimeGoSecondBoundaryFullFaceSource_faceProduct hq hr hrq hfull]
  rw [hprod]
  by_contra hnot
  have hsmall : (r * d) * q ≤ R + 7 := by omega
  have hmul := Nat.mul_le_mul hhalf hsmall
  unfold squareRootEndpoint at hsecond
  have hlarge : R ^ 2 ≤ q * q * (r * d) := by omega
  nlinarith

/-- There is no near Go mate remainder: every live defect mate is far. -/
theorem squareRootLowPrimeGoFullFaceDefectMateFarImage_eq_image
    {R : ℕ} (hR : 6 ≤ R) :
    squareRootLowPrimeGoFullFaceDefectMateFarImage R =
      squareRootLowPrimeGoFullFaceDefectMateImage R := by
  apply Finset.filter_eq_self.mpr
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨⟨⟨r, q⟩, d⟩, hd, rfl⟩
  exact squareRootLowPrimeGoFullFaceDefectMateTag_far hR hd

/-- The actual physical residual after deleting the far defect mates. -/
def squareRootLowPrimeGoReducedPhysicalResidualCarrier (R : ℕ) :
    Finset LowWheelFullTaggedPhysicalState :=
  lowWheelFrozenTopFarPhysicalResidualCarrier R \
    squareRootLowPrimeGoFullFaceDefectMateFarImage R

/-- Signed mass is taken only after the mate subcarrier has been deleted. -/
def squareRootLowPrimeGoReducedPhysicalResidualLedger (R : ℕ) : ℂ :=
  ∑ z ∈ squareRootLowPrimeGoReducedPhysicalResidualCarrier R,
    lowWheelFullTaggedPhysicalWeight z

/-- The remaining mate occurrences, below the far cutoff. -/
def squareRootLowPrimeGoFullFaceDefectMateNearLedger (R : ℕ) : ℂ :=
  ∑ z ∈ squareRootLowPrimeGoFullFaceDefectMateImage R \
      squareRootLowPrimeGoFullFaceDefectMateFarImage R,
    lowWheelFullTaggedPhysicalWeight z

/-- Exact deletion identity on the physical carrier.  No norm is taken. -/
theorem squareRootLowPrimeGo_physicalResidual_add_defect_eq_reduced_sub_near
    {R : ℕ} (hR : 6 ≤ R) :
    lowWheelFrozenTopFarPhysicalResidualLedger R +
        ((squareRootLowPrimeGoFullFaceDefectSourceMass R : ℤ) : ℂ) =
      squareRootLowPrimeGoReducedPhysicalResidualLedger R -
        squareRootLowPrimeGoFullFaceDefectMateNearLedger R := by
  have hphysical := Finset.sum_sdiff
    (squareRootLowPrimeGoFullFaceDefectMateFarImage_subset_physicalResidual hR)
    (f := lowWheelFullTaggedPhysicalWeight)
  have hfar : squareRootLowPrimeGoFullFaceDefectMateFarImage R ⊆
      squareRootLowPrimeGoFullFaceDefectMateImage R := Finset.filter_subset _ _
  have hmates := Finset.sum_sdiff hfar (f := lowWheelFullTaggedPhysicalWeight)
  have hcancel := squareRootLowPrimeGoFullFaceDefectMass_add_existingMate_eq_zero
    (R := R) (by omega : 2 ≤ R)
  rw [squareRootLowPrimeGoFullFaceDefectMateLedger_eq_imageSum (by omega)] at hcancel
  change squareRootLowPrimeGoReducedPhysicalResidualLedger R +
      (∑ z ∈ squareRootLowPrimeGoFullFaceDefectMateFarImage R,
        lowWheelFullTaggedPhysicalWeight z) =
      lowWheelFrozenTopFarPhysicalResidualLedger R at hphysical
  change squareRootLowPrimeGoFullFaceDefectMateNearLedger R +
      (∑ z ∈ squareRootLowPrimeGoFullFaceDefectMateFarImage R,
        lowWheelFullTaggedPhysicalWeight z) = _ at hmates
  linear_combination -hphysical + hmates + hcancel

/-- The apparent near correction vanishes on the physical defect schedule. -/
theorem squareRootLowPrimeGoFullFaceDefectMateNearLedger_eq_zero
    {R : ℕ} (hR : 6 ≤ R) :
    squareRootLowPrimeGoFullFaceDefectMateNearLedger R = 0 := by
  unfold squareRootLowPrimeGoFullFaceDefectMateNearLedger
  rw [squareRootLowPrimeGoFullFaceDefectMateFarImage_eq_image hR]
  simp

/-- The complete Go defect is absorbed, with no new near boundary charge. -/
theorem squareRootLowPrimeGo_physicalResidual_add_defect_eq_reduced
    {R : ℕ} (hR : 6 ≤ R) :
    lowWheelFrozenTopFarPhysicalResidualLedger R +
        ((squareRootLowPrimeGoFullFaceDefectSourceMass R : ℤ) : ℂ) =
      squareRootLowPrimeGoReducedPhysicalResidualLedger R := by
  rw [squareRootLowPrimeGo_physicalResidual_add_defect_eq_reduced_sub_near hR,
    squareRootLowPrimeGoFullFaceDefectMateNearLedger_eq_zero hR, sub_zero]

/-- Retain both near corrections in the compensated signed reconstruction. -/
theorem squareRootLowPrimeGo_frozenResidual_add_defect_eq_reduced_compensated
    {R : ℕ} (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R +
        ((squareRootLowPrimeGoFullFaceDefectSourceMass R : ℤ) : ℂ) =
      squareRootLowPrimeGoReducedPhysicalResidualLedger R -
        squareRootLowPrimeGoFullFaceDefectMateNearLedger R -
        lowWheelCanonicalRepeatedTerminalInternalMateNearLedger R := by
  rw [lowWheelFrozenTopFarResidual_eq_physicalResidual_sub_near R hR]
  have h := squareRootLowPrimeGo_physicalResidual_add_defect_eq_reduced_sub_near
    (R := R) (by omega : 6 ≤ R)
  linear_combination h

/-- Energy of this compensated residual component.  This definition does not
assert a frame estimate or identify it with the recovered Mertens energy. -/
def squareRootLowPrimeGoReducedCompensatedResidualEnergy (R : ℕ) : ℝ :=
  ‖squareRootLowPrimeGoReducedPhysicalResidualLedger R -
    squareRootLowPrimeGoFullFaceDefectMateNearLedger R -
    lowWheelCanonicalRepeatedTerminalInternalMateNearLedger R‖ ^ 2

/-- Compensation and deletion preserve the exact residual energy. -/
theorem squareRootLowPrimeGoReducedCompensatedResidualEnergy_eq
    {R : ℕ} (hR : 56 ≤ R) :
    squareRootLowPrimeGoReducedCompensatedResidualEnergy R =
      ‖lowWheelFrozenTopFarResidual R +
        ((squareRootLowPrimeGoFullFaceDefectSourceMass R : ℤ) : ℂ)‖ ^ 2 := by
  unfold squareRootLowPrimeGoReducedCompensatedResidualEnergy
  rw [squareRootLowPrimeGo_frozenResidual_add_defect_eq_reduced_compensated hR]

end RHLean.Proof
