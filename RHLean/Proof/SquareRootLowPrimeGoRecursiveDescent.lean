import Mathlib
import RHLean.Proof.SquareRootLowPrimeFirstOwnerWallRecurrence
import RHLean.Proof.SquareRootLowPrimeGoFourthPowerCutoff
import RHLean.Proof.SquareRootLowPrimeGoWallStripTelescope

/-!
# Recursive Go descent through the unique smaller prime owner

The square-dilated Go residual is a frozen predecessor cube.  When its cutoff
has not yet fallen below the owner prime `q`, split at the completed lower
prefix `q - 1`.  The remaining rough/smooth window is exactly the difference
of two fresh-prime upper-column telescopes.

Algebraically this gives

`F_{q^-}(y) = M(q-1) - sum_{r<q prime} (F_{r^-}(y/r) - F_{r^-}((q-1)/r))`.

The prime coordinate in every summand is strictly smaller than `q`; the
underlying recurrence is the same fresh-prime Euler recurrence already used by
the wall telescope.

After the weighted-liberty flattening, the apparently prime-count weighted
second-boundary defect admits the same treatment.  For one fixed liberty prime
`r < q`, the surviving parents are exactly one interval in the frozen
predecessor cube through `r-1`.  Thus one whole `r`-slice is a difference of
two frozen predecessor states; the prime-count weight disappears before any
norm or estimate is taken.

No norm, PNT input, or asymptotic estimate is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- At its own predecessor cutoff, the frozen prime universe is already the
complete ordinary Mertens prefix. -/
theorem frozenPrimeUniverseMass_pred_eq_mertensSummatoryInt
    {q : ℕ} (_hq : q.Prime) :
    frozenPrimeUniverseMass (primesUpTo (q - 1)) (q - 1) =
      mertensSummatoryInt (q - 1) := by
  unfold frozenPrimeUniverseMass mertensSummatoryInt
  exact truncatedPrimeCube_eq_moebiusPrefix (q - 1)

/-- **Recursive Go law.**  An unfinished frozen predecessor state at owner `q`
is the completed lower-scale Mertens state through `q-1` minus disjoint
smaller-prime boundary strips. -/
theorem frozenPrimeUniverseMass_eq_mertensPred_sub_smallerOwnerStrips
    {q y : ℕ} (hq : q.Prime) (hqy : q ≤ y) :
    frozenPrimeUniverseMass (primesUpTo (q - 1)) y =
      mertensSummatoryInt (q - 1) -
        ∑ r ∈ primesUpTo (q - 1),
          (frozenPrimeUniverseMass (primesUpTo (r - 1)) (y / r) -
            frozenPrimeUniverseMass (primesUpTo (r - 1)) ((q - 1) / r)) := by
  have hqTwo : 2 ≤ q := hq.two_le
  have hyOne : 1 ≤ y := by omega
  have hpredOne : 1 ≤ q - 1 := by omega
  have hy := frozenPrimeUniverse_upperColumn_telescope y (q - 1) hyOne
  have hpred :=
    frozenPrimeUniverse_upperColumn_telescope (q - 1) (q - 1) hpredOne
  rw [frozenPrimeUniverseMass_pred_eq_mertensSummatoryInt hq] at hpred
  rw [Finset.sum_sub_distrib, hy, hpred]
  ring

/-- Every recursive Go owner in the preceding law is strictly smaller than the
current owner. -/
theorem mem_primesUpTo_pred_lt_owner
    {q r : ℕ} (hr : r ∈ primesUpTo (q - 1)) :
    r < q := by
  have hrData := mem_primesUpTo.mp hr
  have hrTwo : 2 ≤ r := hrData.1.two_le
  have hrq := hrData.2
  omega

/-- Square-residual specialization of the recursive Go law. -/
theorem squareRootLowPrimeGoWallSquareResidual_eq_mertensPred_sub_smallerOwnerStrips
    {q X : ℕ} (hq : q.Prime)
    (hunfinished : q ≤ X / (q * q)) :
    squareRootLowPrimeGoWallSquareResidual q X =
      mertensSummatoryInt (q - 1) -
        ∑ r ∈ primesUpTo (q - 1),
          (frozenPrimeUniverseMass (primesUpTo (r - 1))
              ((X / (q * q)) / r) -
            frozenPrimeUniverseMass (primesUpTo (r - 1)) ((q - 1) / r)) := by
  rw [squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff]
  exact frozenPrimeUniverseMass_eq_mertensPred_sub_smallerOwnerStrips
    hq hunfinished

/-! ## Weighted liberty slices are frozen predecessor strips -/

/-- Generic arithmetic form of a frozen predecessor cube. -/
theorem frozenPrimeUniverseMass_eq_goSmoothCofactorSum
    {r Y : ℕ} (hr : r.Prime) :
    frozenPrimeUniverseMass (primesUpTo (r - 1)) Y =
      ∑ d ∈ squareRootLowPrimeGoSmoothCofactors r Y, μ d := by
  have h :=
    squareRootLowPrimeGoWallSquareResidual_eq_smoothCofactorSum
      (q := r) (X := (r * r) * Y) hr
  rw [squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff] at h
  have hrrPos : 0 < r * r := Nat.mul_pos hr.pos hr.pos
  have hcut : r * r * Y / (r * r) = Y :=
    Nat.mul_div_cancel_left Y hrrPos
  rw [hcut] at h
  exact h

/-- Total lower cutoff for one `r`-liberty slice. -/
def squareRootLowPrimeGoDefectSliceLowerCutoff
    (q X r : ℕ) : ℕ :=
  min (q - 1) (X / (q * q) / r)

/-- Exact support flattening at fixed `r`. -/
theorem squareRootLowPrimeGoSecondBoundaryDefectParents_eq_smooth_sdiff
    {q X r : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X) :
    squareRootLowPrimeGoSecondBoundaryDefectParents q X r =
      squareRootLowPrimeGoSmoothCofactors r (q - 1) \
        squareRootLowPrimeGoSmoothCofactors r
          (squareRootLowPrimeGoDefectSliceLowerCutoff q X r) := by
  classical
  have hq2Pos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hqleCut : q ≤ X / (q * q) := by
    apply (Nat.le_div_iff_mul_le hq2Pos).2
    calc
      q * (q * q) = q ^ 3 := by ring
      _ ≤ X := hcube
  ext d
  constructor
  · intro hd
    rcases mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd with
      ⟨hfull, hphysical⟩
    rcases mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull with
      ⟨hd1, hdq, hsq, hrough, _hbirth⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_squareRootLowPrimeGoSmoothCofactors.mpr
      ⟨hd1, hdq, hsq, hrough⟩, ?_⟩
    intro hlower
    have hdLower :=
      (mem_squareRootLowPrimeGoSmoothCofactors.mp hlower).2.1
    have hLowerLe :
        squareRootLowPrimeGoDefectSliceLowerCutoff q X r ≤
          X / (q * q) / r := by
      unfold squareRootLowPrimeGoDefectSliceLowerCutoff
      exact min_le_right _ _
    exact (Nat.not_lt_of_ge (hdLower.trans hLowerLe)) hphysical
  · intro hd
    rcases Finset.mem_sdiff.mp hd with ⟨hupper, hnotLower⟩
    rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hupper with
      ⟨hd1, hdq, hsq, hrough⟩
    have hphysical : X / (q * q) / r < d := by
      by_contra hnot
      have hdPhys : d ≤ X / (q * q) / r := Nat.le_of_not_gt hnot
      have hdLower :
          d ≤ squareRootLowPrimeGoDefectSliceLowerCutoff q X r := by
        unfold squareRootLowPrimeGoDefectSliceLowerCutoff
        exact le_min hdq hdPhys
      exact hnotLower
        (mem_squareRootLowPrimeGoSmoothCofactors.mpr
          ⟨hd1, hdLower, hsq, hrough⟩)
    have hbirthMul : q - 1 < d * r := by
      have hcutMul : X / (q * q) < d * r :=
        (Nat.div_lt_iff_lt_mul hr.pos).1 hphysical
      omega
    have hbirth : (q - 1) / r < d :=
      (Nat.div_lt_iff_lt_mul hr.pos).2 hbirthMul
    apply mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mpr
    exact ⟨mem_squareRootLowPrimeGoFullBirthBoundaryParents.mpr
      ⟨hd1, hdq, hsq, hrough, hbirth⟩, hphysical⟩

/-- The lower smooth prefix is contained in the full fixed-owner parent prefix. -/
theorem squareRootLowPrimeGoDefectSliceLower_subset_upper
    (q X r : ℕ) :
    squareRootLowPrimeGoSmoothCofactors r
        (squareRootLowPrimeGoDefectSliceLowerCutoff q X r) ⊆
      squareRootLowPrimeGoSmoothCofactors r (q - 1) := by
  intro d hd
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hd with
    ⟨hd1, hdLower, hsq, hrough⟩
  apply mem_squareRootLowPrimeGoSmoothCofactors.mpr
  refine ⟨hd1, ?_, hsq, hrough⟩
  exact hdLower.trans (by
    unfold squareRootLowPrimeGoDefectSliceLowerCutoff
    exact min_le_left _ _)

/-- The Möbius mass of one fixed `r` defect slice is exactly one difference of
frozen predecessor states. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_moebiusSum_eq_frozenStrip
    {q X r : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X) :
    (∑ d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r, μ d) =
      frozenPrimeUniverseMass (primesUpTo (r - 1)) (q - 1) -
        frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootLowPrimeGoDefectSliceLowerCutoff q X r) := by
  rw [squareRootLowPrimeGoSecondBoundaryDefectParents_eq_smooth_sdiff
    hq hr hrq hcube]
  have hsub := squareRootLowPrimeGoDefectSliceLower_subset_upper q X r
  have hUpper :=
    frozenPrimeUniverseMass_eq_goSmoothCofactorSum
      (r := r) (Y := q - 1) hr
  have hLower :=
    frozenPrimeUniverseMass_eq_goSmoothCofactorSum
      (r := r) (Y := squareRootLowPrimeGoDefectSliceLowerCutoff q X r) hr
  calc
    (∑ d ∈ squareRootLowPrimeGoSmoothCofactors r (q - 1) \
        squareRootLowPrimeGoSmoothCofactors r
          (squareRootLowPrimeGoDefectSliceLowerCutoff q X r), μ d) =
      (∑ d ∈ squareRootLowPrimeGoSmoothCofactors r (q - 1), μ d) -
        ∑ d ∈ squareRootLowPrimeGoSmoothCofactors r
          (squareRootLowPrimeGoDefectSliceLowerCutoff q X r), μ d :=
      (eq_sub_iff_add_eq).2 (Finset.sum_sdiff hsub)
    _ = frozenPrimeUniverseMass (primesUpTo (r - 1)) (q - 1) -
        frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootLowPrimeGoDefectSliceLowerCutoff q X r) := by
      rw [← hUpper, ← hLower]

/-- Source-signed mass of one fixed interior-prime liberty slice. -/
def squareRootLowPrimeGoDefectPrimeSliceSourceMass
    (q X r : ℕ) : ℤ :=
  ∑ d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r, μ (q * d)

/-- One liberty prime is one signed frozen strip. -/
theorem squareRootLowPrimeGoDefectPrimeSliceSourceMass_eq_neg_frozenStrip
    {q X r : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X) :
    squareRootLowPrimeGoDefectPrimeSliceSourceMass q X r =
      -(frozenPrimeUniverseMass (primesUpTo (r - 1)) (q - 1) -
        frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootLowPrimeGoDefectSliceLowerCutoff q X r)) := by
  unfold squareRootLowPrimeGoDefectPrimeSliceSourceMass
  calc
    (∑ d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r,
        μ (q * d)) =
      ∑ d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r,
        -μ d := by
      apply Finset.sum_congr rfl
      intro d hd
      exact squareRootLowPrimeGoFullBirthBoundary_parentSourceWeight_eq_neg
        hq hr hrq
        (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
    _ = -(∑ d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r,
        μ d) := by
      rw [Finset.sum_neg_distrib]
    _ = -(frozenPrimeUniverseMass (primesUpTo (r - 1)) (q - 1) -
        frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootLowPrimeGoDefectSliceLowerCutoff q X r)) := by
      rw [squareRootLowPrimeGoSecondBoundaryDefect_moebiusSum_eq_frozenStrip
        hq hr hrq hcube]

/-! ## Global handoff: the liberty coefficient disappears -/

/-- Every defect parent is already in the rectangular ambient range used by the
weighted flattening. -/
theorem squareRootLowPrimeGoSecondBoundaryDefectParents_subset_range
    (q X r : ℕ) :
    squareRootLowPrimeGoSecondBoundaryDefectParents q X r ⊆ Finset.range q := by
  intro d hd
  rcases mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd with
    ⟨hfull, _hphysical⟩
  rcases mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull with
    ⟨hd1, hdq, _hsq, _hrough, _hbirth⟩
  exact Finset.mem_range.mpr (by omega)

/-- Filtering the ambient parent range by the exact defect predicate recovers
the defect-parent finset itself. -/
theorem squareRootLowPrimeGo_range_filter_defectParents_eq
    (q X r : ℕ) :
    (Finset.range q).filter
        (fun d => d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r) =
      squareRootLowPrimeGoSecondBoundaryDefectParents q X r := by
  ext d
  constructor
  · intro hd
    exact (Finset.mem_filter.mp hd).2
  · intro hd
    exact Finset.mem_filter.mpr
      ⟨squareRootLowPrimeGoSecondBoundaryDefectParents_subset_range q X r hd, hd⟩

/-- The rectangular raw defect mass is the sum of its actual prime-liberty
slice masses. -/
theorem squareRootLowPrimeGoOwnerRawDefectMass_eq_sum_primeSlices
    (q X : ℕ) :
    squareRootLowPrimeGoOwnerRawDefectMass q X =
      ∑ r ∈ Finset.range q,
        if r.Prime then
          squareRootLowPrimeGoDefectPrimeSliceSourceMass q X r
        else 0 := by
  classical
  unfold squareRootLowPrimeGoOwnerRawDefectMass
  apply Finset.sum_congr rfl
  intro r _hrange
  by_cases hr : r.Prime
  · simp only [hr, true_and, if_true]
    unfold squareRootLowPrimeGoDefectPrimeSliceSourceMass
    rw [← Finset.sum_filter,
      squareRootLowPrimeGo_range_filter_defectParents_eq q X r]
  · simp [hr]

/-- One strictly descending predecessor-strip contribution. -/
def squareRootLowPrimeGoFrozenLibertyStripContribution
    (q X r : ℕ) : ℤ :=
  -(frozenPrimeUniverseMass (primesUpTo (r - 1)) (q - 1) -
    frozenPrimeUniverseMass (primesUpTo (r - 1))
      (squareRootLowPrimeGoDefectSliceLowerCutoff q X r))

/-- Complete fixed-owner frozen-strip mass, with composite indices carrying zero. -/
def squareRootLowPrimeGoOwnerFrozenLibertyStripMass
    (q X : ℕ) : ℤ :=
  ∑ r ∈ Finset.range q,
    if r.Prime then squareRootLowPrimeGoFrozenLibertyStripContribution q X r
    else 0

/-- **Global weighted-liberty descent.**  The exact liberty-weighted parent
source mass is identically a sum of signed frozen predecessor strips with
strictly smaller prime owner `r < q`.  No estimate is taken. -/
theorem squareRootLowPrimeGoOwnerWeightedBoundaryMass_eq_frozenLibertyStrips
    {q X : ℕ} (hq : q.Prime) (hcube : q ^ 3 ≤ X) :
    squareRootLowPrimeGoOwnerWeightedBoundaryMass q X =
      squareRootLowPrimeGoOwnerFrozenLibertyStripMass q X := by
  rw [← squareRootLowPrimeGoOwnerRawDefectMass_eq_weightedBoundaryMass q X,
    squareRootLowPrimeGoOwnerRawDefectMass_eq_sum_primeSlices]
  unfold squareRootLowPrimeGoOwnerFrozenLibertyStripMass
  apply Finset.sum_congr rfl
  intro r hrange
  by_cases hr : r.Prime
  · have hrq : r < q := Finset.mem_range.mp hrange
    have hs :=
      squareRootLowPrimeGoDefectPrimeSliceSourceMass_eq_neg_frozenStrip
        hq hr hrq hcube
    rw [if_pos hr, if_pos hr]
    exact hs
  · simp [hr]

/-- **Outer signed handoff.**  Over any finite unfinished prime-owner schedule,
the complete raw second-boundary defect mass is exactly the signed sum of the
fixed-owner frozen liberty-strip masses.  Here every strip uses

`L(q,X,r) = min (q-1) (X/(q^2*r))`

through `squareRootLowPrimeGoDefectSliceLowerCutoff`.  Neither the inner `r`
sum nor the outer `q` sum is replaced by a sum of absolute values. -/
theorem squareRootLowPrimeGoRawDefectMassTotal_eq_frozenLibertyStrips
    {Q : Finset ℕ} {X : ℕ}
    (hlive : ∀ q ∈ Q, q.Prime ∧ q ^ 3 ≤ X) :
    (∑ q ∈ Q, squareRootLowPrimeGoOwnerRawDefectMass q X) =
      ∑ q ∈ Q, squareRootLowPrimeGoOwnerFrozenLibertyStripMass q X := by
  apply Finset.sum_congr rfl
  intro q hqQ
  rcases hlive q hqQ with ⟨hq, hcube⟩
  calc
    squareRootLowPrimeGoOwnerRawDefectMass q X =
        squareRootLowPrimeGoOwnerWeightedBoundaryMass q X :=
      squareRootLowPrimeGoOwnerRawDefectMass_eq_weightedBoundaryMass q X
    _ = squareRootLowPrimeGoOwnerFrozenLibertyStripMass q X :=
      squareRootLowPrimeGoOwnerWeightedBoundaryMass_eq_frozenLibertyStrips
        hq hcube

end RHLean.Proof
