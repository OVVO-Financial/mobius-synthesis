import Mathlib
import RHLean.Analysis.PhysicalDegreeOneMixingConjecture

/-!
# Physical degree-one transition estimate

This module splits the Mertens-visible physical transition mass into its three
linear Walsh coordinates.  No full transition-uniformity statement is used:
only the characters `chiA`, `chiB`, and `chiC` occur.

The three signed transition moments are kept intact.  Absolute values appear
only in the named quantitative estimate, together with the existing structured
zero-sector defect.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Integer sum over the canonical eight all-nonzero physical states. -/
def physicalNonzeroStateIntSum (f : Fin 27 → ℤ) : ℤ :=
  f 0 + f 2 + f 6 + f 8 + f 18 + f 20 + f 24 + f 26

/-- Signed transition mass against one destination character, with both source
and destination restricted to the canonical eight-state nonzero sector. -/
def physicalTransitionLinearMoment
    (K : ℕ) (χ : Fin 27 → ℤ) : ℤ :=
  physicalNonzeroStateIntSum (fun u =>
    threeSlotTransitionMomentOn (Finset.range K) u χ)

/-- First linear Walsh transition moment `T_a(K)`. -/
def physicalTransitionTa (K : ℕ) : ℤ :=
  physicalTransitionLinearMoment K chiA

/-- Second linear Walsh transition moment `T_b(K)`. -/
def physicalTransitionTb (K : ℕ) : ℤ :=
  physicalTransitionLinearMoment K chiB

/-- Third linear Walsh transition moment `T_c(K)`. -/
def physicalTransitionTc (K : ℕ) : ℤ :=
  physicalTransitionLinearMoment K chiC

/-- The structured zero-sector defect, retained without any internal absolute
value decomposition. -/
def physicalTransitionD (K : ℕ) : ℤ :=
  physicalDegreeOneD K

/-- The normalized centered discrepancy against a destination character:

`sum_{u,v in A} (N_{u,v}(K) - R_u(K)/8) * chi(v)`.
-/
def physicalTransitionCenteredDiscrepancy
    (K : ℕ) (χ : Fin 27 → ℤ) : ℝ :=
  physicalNonzeroStateSum (fun u =>
    physicalNonzeroStateSum (fun v =>
      (((physicalTransitionN K u v : ℕ) : ℝ) -
          ((physicalTransitionR K u : ℤ) : ℝ) / 8) *
        ((χ v : ℤ) : ℝ)))

private theorem physicalNonzeroStateIntSum_cast
    (f : Fin 27 → ℤ) :
    ((physicalNonzeroStateIntSum f : ℤ) : ℝ) =
      physicalNonzeroStateSum (fun u => ((f u : ℤ) : ℝ)) := by
  simp [physicalNonzeroStateIntSum, physicalNonzeroStateSum]

private theorem physicalTransitionLinearMoment_real_eq_rowSum
    (K : ℕ) (χ : Fin 27 → ℤ) :
    ((physicalTransitionLinearMoment K χ : ℤ) : ℝ) =
      physicalNonzeroStateSum (fun u =>
        ((threeSlotTransitionMomentOn
            (Finset.range K) u χ : ℤ) : ℝ)) := by
  unfold physicalTransitionLinearMoment
  exact physicalNonzeroStateIntSum_cast _

/-- A zero-mass destination character is unchanged by `1/8` row centering. -/
private theorem physicalTransitionRow_eq_centeredDiscrepancy
    (K : ℕ) (u : Fin 27) (χ : Fin 27 → ℤ)
    (hχ : threeSlotNonzeroCharacterMass χ = 0) :
    ((threeSlotTransitionMomentOn
        (Finset.range K) u χ : ℤ) : ℝ) =
      physicalNonzeroStateSum (fun v =>
        (((physicalTransitionN K u v : ℕ) : ℝ) -
            ((physicalTransitionR K u : ℤ) : ℝ) / 8) *
          ((χ v : ℤ) : ℝ)) := by
  symm
  calc
    physicalNonzeroStateSum (fun v =>
        (((physicalTransitionN K u v : ℕ) : ℝ) -
            ((physicalTransitionR K u : ℤ) : ℝ) / 8) *
          ((χ v : ℤ) : ℝ)) =
      ((threeSlotTransitionMomentOn
          (Finset.range K) u χ : ℤ) : ℝ) -
        (((threeSlotTransitionRowTotalOn
            (Finset.range K) u : ℤ) : ℝ) / 8) *
          ((threeSlotNonzeroCharacterMass χ : ℤ) : ℝ) := by
            norm_num [physicalNonzeroStateSum, physicalTransitionN,
              physicalTransitionR, threeSlotTransitionCount,
              threeSlotTransitionMomentOn, threeSlotNonzeroCharacterMass]
            ring
    _ = ((threeSlotTransitionMomentOn
          (Finset.range K) u χ : ℤ) : ℝ) := by
      simp [hχ]

/-- Generic centered identity for any zero-mass character on the nonzero
sector. -/
theorem physicalTransitionLinearMoment_eq_centeredDiscrepancy
    (K : ℕ) (χ : Fin 27 → ℤ)
    (hχ : threeSlotNonzeroCharacterMass χ = 0) :
    ((physicalTransitionLinearMoment K χ : ℤ) : ℝ) =
      physicalTransitionCenteredDiscrepancy K χ := by
  rw [physicalTransitionLinearMoment_real_eq_rowSum]
  unfold physicalTransitionCenteredDiscrepancy
  apply congrArg physicalNonzeroStateSum
  funext u
  exact physicalTransitionRow_eq_centeredDiscrepancy K u χ hχ

/-- Exact centered formula for the first linear mode. -/
theorem physicalTransitionTa_eq_centeredDiscrepancy (K : ℕ) :
    ((physicalTransitionTa K : ℤ) : ℝ) =
      physicalTransitionCenteredDiscrepancy K chiA := by
  simpa [physicalTransitionTa] using
    physicalTransitionLinearMoment_eq_centeredDiscrepancy
      K chiA threeSlotNonzeroCharacterMass_chiA

/-- Exact centered formula for the second linear mode. -/
theorem physicalTransitionTb_eq_centeredDiscrepancy (K : ℕ) :
    ((physicalTransitionTb K : ℤ) : ℝ) =
      physicalTransitionCenteredDiscrepancy K chiB := by
  simpa [physicalTransitionTb] using
    physicalTransitionLinearMoment_eq_centeredDiscrepancy
      K chiB threeSlotNonzeroCharacterMass_chiB

/-- Exact centered formula for the third linear mode. -/
theorem physicalTransitionTc_eq_centeredDiscrepancy (K : ℕ) :
    ((physicalTransitionTc K : ℤ) : ℝ) =
      physicalTransitionCenteredDiscrepancy K chiC := by
  simpa [physicalTransitionTc] using
    physicalTransitionLinearMoment_eq_centeredDiscrepancy
      K chiC threeSlotNonzeroCharacterMass_chiC

private theorem threeSlotTransitionMomentOn_add
    (F : Finset ℕ) (u : Fin 27) (χ ψ : Fin 27 → ℤ) :
    threeSlotTransitionMomentOn F u (fun v => χ v + ψ v) =
      threeSlotTransitionMomentOn F u χ +
        threeSlotTransitionMomentOn F u ψ := by
  unfold threeSlotTransitionMomentOn
  ring

/-- Transition character mass is linear in the destination character. -/
theorem physicalTransitionLinearMoment_add
    (K : ℕ) (χ ψ : Fin 27 → ℤ) :
    physicalTransitionLinearMoment K (fun v => χ v + ψ v) =
      physicalTransitionLinearMoment K χ +
        physicalTransitionLinearMoment K ψ := by
  unfold physicalTransitionLinearMoment physicalNonzeroStateIntSum
  simp_rw [threeSlotTransitionMomentOn_add]
  ring

private theorem physicalDegreeOneT_eq_linearMoment_degreeOne (K : ℕ) :
    physicalDegreeOneT K =
      physicalTransitionLinearMoment K threeSlotDegreeOneValue := by
  rfl

/-- The Mertens-visible transition mass contains exactly the three linear Walsh
modes and no pair or triple mode. -/
theorem physicalDegreeOneT_eq_linearTransitionMoments (K : ℕ) :
    physicalDegreeOneT K =
      physicalTransitionTa K + physicalTransitionTb K + physicalTransitionTc K := by
  rw [physicalDegreeOneT_eq_linearMoment_degreeOne]
  unfold physicalTransitionTa physicalTransitionTb physicalTransitionTc
  change physicalTransitionLinearMoment K
      (fun i => (chiA i + chiB i) + chiC i) =
    physicalTransitionLinearMoment K chiA +
      physicalTransitionLinearMoment K chiB +
      physicalTransitionLinearMoment K chiC
  rw [physicalTransitionLinearMoment_add]
  rw [physicalTransitionLinearMoment_add]

/-- Exact integer pushforward with the three linear transition moments exposed. -/
theorem moebiusPositivePrefix_four_mul_succ_eq_linearTransitionMoments
    (K : ℕ) :
    moebiusPositivePrefix (4 * (K + 1)) =
      threeSlotDegreeOneValue (threeSlotState 0) +
        physicalTransitionTa K + physicalTransitionTb K +
        physicalTransitionTc K + physicalTransitionD K := by
  rw [moebiusPositivePrefix_four_mul_succ_eq_physicalDegreeOne,
    physicalDegreeOneT_eq_linearTransitionMoments]
  simp [physicalTransitionD]
  ring

/-- Analytic Mertens pushforward with the three linear transition moments
exposed. -/
theorem mertensSummatory_four_mul_succ_eq_linearTransitionMoments
    (K : ℕ) :
    mertensSummatory (4 * (K + 1)) =
      (((threeSlotDegreeOneValue (threeSlotState 0) +
          physicalTransitionTa K + physicalTransitionTb K +
          physicalTransitionTc K + physicalTransitionD K : ℤ)) : ℂ) := by
  rw [mertensSummatory_four_mul_succ_eq_physicalDegreeOne,
    physicalDegreeOneT_eq_linearTransitionMoments]
  simp [physicalTransitionD]
  ring

@[simp] theorem physicalTransitionLinearMoment_zero
    (χ : Fin 27 → ℤ) :
    physicalTransitionLinearMoment 0 χ = 0 := by
  simp [physicalTransitionLinearMoment, physicalNonzeroStateIntSum,
    threeSlotTransitionMomentOn, threeSlotTransitionCountOn]

@[simp] theorem physicalTransitionD_zero : physicalTransitionD 0 = 0 := by
  simp [physicalTransitionD, physicalDegreeOneD,
    threeSlotTransitionDegreeOneDefect, threeSlotTransitionDegreeOneMass,
    threeSlotTransitionMomentOn, threeSlotTransitionCountOn]

/-- Triangle control of the combined transition mass by its three linear modes. -/
private theorem abs_physicalDegreeOneT_le_linearTransitionMoments
    (K : ℕ) :
    |((physicalDegreeOneT K : ℤ) : ℝ)| ≤
      |((physicalTransitionTa K : ℤ) : ℝ)| +
        |((physicalTransitionTb K : ℤ) : ℝ)| +
        |((physicalTransitionTc K : ℤ) : ℝ)| := by
  rw [physicalDegreeOneT_eq_linearTransitionMoments]
  push_cast
  have htri :
      ‖((physicalTransitionTa K : ℤ) : ℝ) +
          ((physicalTransitionTb K : ℤ) : ℝ) +
          ((physicalTransitionTc K : ℤ) : ℝ)‖ ≤
        ‖((physicalTransitionTa K : ℤ) : ℝ)‖ +
          ‖((physicalTransitionTb K : ℤ) : ℝ)‖ +
          ‖((physicalTransitionTc K : ℤ) : ℝ)‖ := by
    calc
      ‖((physicalTransitionTa K : ℤ) : ℝ) +
          ((physicalTransitionTb K : ℤ) : ℝ) +
          ((physicalTransitionTc K : ℤ) : ℝ)‖
          ≤ ‖((physicalTransitionTa K : ℤ) : ℝ) +
              ((physicalTransitionTb K : ℤ) : ℝ)‖ +
            ‖((physicalTransitionTc K : ℤ) : ℝ)‖ := norm_add_le _ _
      _ ≤ (‖((physicalTransitionTa K : ℤ) : ℝ)‖ +
              ‖((physicalTransitionTb K : ℤ) : ℝ)‖) +
            ‖((physicalTransitionTc K : ℤ) : ℝ)‖ := by
          gcongr
          exact norm_add_le _ _
  simpa [Real.norm_eq_abs] using htri

/-- **The open arithmetic estimate.**  Only the three Mertens-visible linear
transition moments and the structured zero-sector defect are required at
square-root scale. -/
def PhysicalDegreeOneTransitionEstimate : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ K : ℕ,
        |((physicalTransitionTa K : ℤ) : ℝ)| +
            |((physicalTransitionTb K : ℤ) : ℝ)| +
            |((physicalTransitionTc K : ℤ) : ℝ)| +
            |((physicalTransitionD K : ℤ) : ℝ)| ≤
          C * Real.rpow ((K + 1 : ℕ) : ℝ) ((1 : ℝ) / 2 + ε)

/-- The three-mode estimate implies the previously kernel-checked combined
physical mixing target.  The only scale conversion is
`K + 1 <= 2 K` for `K >= 1`, absorbed into the constant. -/
theorem physicalDegreeOneMixingConjecture_of_transitionEstimate
    (h : PhysicalDegreeOneTransitionEstimate) :
    PhysicalDegreeOneMixingConjecture := by
  intro ε hε
  let a : ℝ := (1 : ℝ) / 2 + ε
  have ha : 0 < a := by
    dsimp [a]
    linarith
  rcases h ε hε with ⟨C, hC, hbound⟩
  have htwo : 0 < Real.rpow 2 a :=
    Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨C * Real.rpow 2 a, mul_pos hC htwo, ?_⟩
  intro K
  cases K with
  | zero =>
      have hT0 : physicalDegreeOneT 0 = 0 := by
        rw [physicalDegreeOneT_eq_linearTransitionMoments]
        simp [physicalTransitionTa, physicalTransitionTb, physicalTransitionTc]
      have hD0 : physicalDegreeOneD 0 = 0 := by
        simpa [physicalTransitionD] using physicalTransitionD_zero
      rw [hT0, hD0]
      simp only [Int.cast_zero, abs_zero, zero_add]
      exact mul_nonneg
        (mul_nonneg hC.le (Real.rpow_nonneg (by norm_num) a))
        (Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 2 + ε))
  | succ K =>
      have hmodes :
          |((physicalTransitionTa (K + 1) : ℤ) : ℝ)| +
              |((physicalTransitionTb (K + 1) : ℤ) : ℝ)| +
              |((physicalTransitionTc (K + 1) : ℤ) : ℝ)| +
              |((physicalDegreeOneD (K + 1) : ℤ) : ℝ)| ≤
            C * Real.rpow (((K + 1) + 1 : ℕ) : ℝ) a := by
        simpa [physicalTransitionD, a] using hbound (K + 1)
      have hT := abs_physicalDegreeOneT_le_linearTransitionMoments (K + 1)
      have hTD :
          |((physicalDegreeOneT (K + 1) : ℤ) : ℝ)| +
              |((physicalDegreeOneD (K + 1) : ℤ) : ℝ)| ≤
            |((physicalTransitionTa (K + 1) : ℤ) : ℝ)| +
              |((physicalTransitionTb (K + 1) : ℤ) : ℝ)| +
              |((physicalTransitionTc (K + 1) : ℤ) : ℝ)| +
              |((physicalDegreeOneD (K + 1) : ℤ) : ℝ)| := by
        linarith
      have hbasele :
          ((((K + 1) + 1 : ℕ) : ℝ)) ≤
            2 * (((K + 1 : ℕ) : ℝ)) := by
        exact_mod_cast (show (K + 1) + 1 ≤ 2 * (K + 1) by omega)
      have hscale :
          Real.rpow (((K + 1) + 1 : ℕ) : ℝ) a ≤
            Real.rpow 2 a * Real.rpow ((K + 1 : ℕ) : ℝ) a := by
        calc
          Real.rpow (((K + 1) + 1 : ℕ) : ℝ) a
              ≤ Real.rpow (2 * (((K + 1 : ℕ) : ℝ))) a :=
                Real.rpow_le_rpow (by positivity) hbasele ha.le
          _ = Real.rpow 2 a * Real.rpow ((K + 1 : ℕ) : ℝ) a :=
                Real.mul_rpow (by norm_num) (by positivity)
      calc
        |((physicalDegreeOneT (K + 1) : ℤ) : ℝ)| +
              |((physicalDegreeOneD (K + 1) : ℤ) : ℝ)|
            ≤ C * Real.rpow (((K + 1) + 1 : ℕ) : ℝ) a :=
              hTD.trans hmodes
        _ ≤ C *
              (Real.rpow 2 a * Real.rpow ((K + 1 : ℕ) : ℝ) a) :=
              mul_le_mul_of_nonneg_left hscale hC.le
        _ = (C * Real.rpow 2 a) *
              Real.rpow ((K + 1 : ℕ) : ℝ) ((1 : ℝ) / 2 + ε) := by
              dsimp [a]
              ring

/-- **Terminal closure.**  The three signed linear transition moments plus the
structured defect are sufficient for the Riemann Hypothesis. -/
theorem rh_of_physicalDegreeOneTransitionEstimate
    (h : PhysicalDegreeOneTransitionEstimate) : RiemannHypothesis :=
  rh_of_physicalDegreeOneMixingConjecture
    (physicalDegreeOneMixingConjecture_of_transitionEstimate h)

end RHLean.Analysis

end
