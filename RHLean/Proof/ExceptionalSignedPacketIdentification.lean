import RHLean.Analysis.PhysicalExceptionalLocalIntertwine
import RHLean.Proof.TwoWheelQ2GoCompatibility

/-!
# Exact signed recovery on the exceptional physical carriers

The blocker wheel `P` selects a complete least-owner carrier.  The recovery
wheel `S` recovers actual Mobius values on that carrier.  Neither operation
changes a physical cell endpoint into an endpoint divided by `q^2`.
The blocker module's signed mass still uses `selectedDegreeOneProjection P`;
the source packet here deliberately uses the true Mobius observable instead.
Identifying these two weights requires the separate parity compensation and
does not follow from the carrier dictionary below.

This module gives the exact forward dictionary before any norm is taken:
the actual SOURCE observable on a complete owner carrier is an incidence sum
of `F_{q^-}-T_{q^-}` increments at `4*k` and `4*(k+1)`.  The existing LOCAL-BLOCK
theorems concern DESTINATION observables, at `4*(k+1)` and `4*(k+2)`.

The signed predecessor state is always the literal frozen cube minus its
high-owner column, including at cutoffs below the owner.  A finite certificate
then excludes replacing an uncompensated nine-edge LOCAL-BLOCK by a scalar
linear image of its one square-dilated Mertens value.  This does not exclude a
physical compensation theorem with additional parent and mate occurrences;
those occurrences still have to be constructed and identified.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The intact signed state on the existing predecessor/high-owner carrier. -/
def exceptionalSignedPredecessorState (q Y : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo (q - 1)) Y -
    ∑ p ∈ frozenPrimeUniverseHighPrimeSet (q - 1) Y,
      frozenPrimeUniverseMass (primesUpTo (p - 1)) (Y / p)

/-- Exact signed recovery at every cutoff, including a completed daughter. -/
theorem exceptionalSignedPredecessorState_eq_mertens
    {q : ℕ} (hq : q.Prime) (Y : ℕ) :
    exceptionalSignedPredecessorState q Y = mertensSummatoryInt Y := by
  by_cases hcut : q - 1 ≤ Y
  · exact (mertensSummatoryInt_eq_properSubwheel_sub_highOwnerColumn
      Y (q - 1) hcut).symm
  · have hYq : Y < q := by omega
    have hempty : frozenPrimeUniverseHighPrimeSet (q - 1) Y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hdata := mem_frozenPrimeUniverseHighPrimeSet.mp hp
      omega
    unfold exceptionalSignedPredecessorState
    rw [hempty, Finset.sum_empty, sub_zero]
    exact frozenPrimeUniverseMass_eq_mertensSummatoryInt_of_lt_owner hq hYq

private theorem mertensSummatoryInt_eq_moebiusPositivePrefix (Y : ℕ) :
    mertensSummatoryInt Y = moebiusPositivePrefix Y := by
  rw [mertensSummatoryInt_eq_Icc]
  rfl

/-- Coefficient-level recovery of one literal four-cell increment. -/
theorem fourSlotCellSum_eq_signedPredecessor_increment
    {q : ℕ} (hq : q.Prime) (k : ℕ) :
    fourSlotCellSum k =
      exceptionalSignedPredecessorState q (4 * (k + 1)) -
        exceptionalSignedPredecessorState q (4 * k) := by
  rw [exceptionalSignedPredecessorState_eq_mertens hq,
    exceptionalSignedPredecessorState_eq_mertens hq,
    mertensSummatoryInt_eq_moebiusPositivePrefix,
    mertensSummatoryInt_eq_moebiusPositivePrefix,
    moebiusPositivePrefix_four_mul_eq_fourSlotCellSum,
    moebiusPositivePrefix_four_mul_eq_fourSlotCellSum,
    Finset.sum_range_succ]
  ring

/-- The actual SOURCE observable has the source four-cell endpoints. -/
theorem physicalSourceDegreeOne_eq_signedPredecessor_increment
    {q : ℕ} (hq : q.Prime) (k : ℕ) :
    threeSlotDegreeOneValue (threeSlotState k) =
      exceptionalSignedPredecessorState q (4 * (k + 1)) -
        exceptionalSignedPredecessorState q (4 * k) := by
  have hcell : threeSlotDegreeOneValue (threeSlotState k) =
      fourSlotCellSum k := by
    simp [threeSlotDegreeOneValue_threeSlotState, fourSlotCellSum,
      moebius_four_mul_add_four]
  rw [hcell]
  exact fourSlotCellSum_eq_signedPredecessor_increment hq k

/-- The existing LOCAL-BLOCK observable is at the DESTINATION cell. -/
theorem physicalDefectEdgeValue_eq_signedPredecessor_increment
    {q : ℕ} (hq : q.Prime) (k : ℕ) :
    physicalDefectEdgeValue k =
      exceptionalSignedPredecessorState q (4 * (k + 1 + 1)) -
        exceptionalSignedPredecessorState q (4 * (k + 1)) := by
  rw [physicalDefectEdgeValue_eq_fourSlotCellSum]
  exact fourSlotCellSum_eq_signedPredecessor_increment hq (k + 1)

/-- The literal complete least-owner carrier selected by the blocker wheel. -/
def exceptionalCompleteOwnerCells (P : Finset ℕ) (R q : ℕ) : Finset ℕ :=
  (squareBlockOutsidePrimeLeastCompleteCells P R).filter fun k =>
    physicalLeastOddSquarePrime k = some q

/-- The true Mobius SOURCE packet on this carrier.  Its definition uses the
physical observable, and does not use a Mertens or recovered daughter value. -/
def exceptionalCompleteOwnerSourcePacket
    (P : Finset ℕ) (R q : ℕ) : ℤ :=
  ∑ k ∈ exceptionalCompleteOwnerCells P R q,
    threeSlotDegreeOneValue (threeSlotState k)

/-- Exact physical recovery with independent blocker and recovery wheels. -/
theorem exceptionalCompleteOwnerSourcePacket_eq_recoveredIncidence
    (P S : Finset ℕ) (upper R q : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hupper : ∀ k ∈ exceptionalCompleteOwnerCells P R q,
      4 * (k + 1) ≤ upper) :
    exceptionalCompleteOwnerSourcePacket P R q =
      ∑ k ∈ exceptionalCompleteOwnerCells P R q,
        recoveredThreeSlotCellIncrement S upper k := by
  unfold exceptionalCompleteOwnerSourcePacket
  apply Finset.sum_congr rfl
  intro k hk
  rw [recoveredThreeSlotCellIncrement_eq_fourSlotCellSum
    S upper k hprime hcover (hupper k hk)]
  simp [threeSlotDegreeOneValue_threeSlotState, fourSlotCellSum,
    moebius_four_mul_add_four]

/-- The same complete physical source packet as an atomic signed `F-T`
incidence.  These are the actual physical endpoints, with no q-square change
of scale claimed or hidden in the incidence operator. -/
theorem exceptionalCompleteOwnerSourcePacket_eq_signedPredecessorIncidence
    (P : Finset ℕ) (R : ℕ) {q : ℕ} (hq : q.Prime) :
    exceptionalCompleteOwnerSourcePacket P R q =
      ∑ k ∈ exceptionalCompleteOwnerCells P R q,
        (exceptionalSignedPredecessorState q (4 * (k + 1)) -
          exceptionalSignedPredecessorState q (4 * k)) := by
  unfold exceptionalCompleteOwnerSourcePacket
  apply Finset.sum_congr rfl
  intro k hk
  exact physicalSourceDegreeOne_eq_signedPredecessor_increment hq k

/-- Exact `F-T` form of the existing unrestricted nine-edge LOCAL-BLOCK. -/
theorem physicalD9_nine_step_eq_signedPredecessor_interval (L : ℕ) :
    physicalD9 (9 * (L + 1)) - physicalD9 (9 * L) =
      exceptionalSignedPredecessorState 3 (36 * L + 32) -
        exceptionalSignedPredecessorState 3 (36 * L + 8) := by
  rw [physicalD9_nine_step_recurrence,
    exceptionalSignedPredecessorState_eq_mertens (by norm_num : Nat.Prime 3),
    exceptionalSignedPredecessorState_eq_mertens (by norm_num : Nat.Prime 3),
    mertensSummatoryInt_eq_moebiusPositivePrefix,
    mertensSummatoryInt_eq_moebiusPositivePrefix]

/-- Exact signed least-five incidence, keeping both endpoints of every cell. -/
theorem physicalD25_225_step_eq_signedPredecessorIncidence (L : ℕ) :
    physicalD25 (225 * (L + 1)) - physicalD25 (225 * L) =
      ∑ r ∈ physicalTwentyFiveChannelResidues,
        (exceptionalSignedPredecessorState 5 (4 * (225 * L + r + 1 + 1)) -
          exceptionalSignedPredecessorState 5 (4 * (225 * L + r + 1))) := by
  rw [physicalD25_225_step_fourSlot_recurrence]
  apply Finset.sum_congr rfl
  intro r hr
  exact fourSlotCellSum_eq_signedPredecessor_increment
    (by norm_num : Nat.Prime 5) (225 * L + r + 1)

/-- Exact signed least-seven incidence on its full 11025-cell period. -/
theorem physicalD49_11025_step_eq_signedPredecessorIncidence (L : ℕ) :
    physicalD49 (11025 * (L + 1)) - physicalD49 (11025 * L) =
      ∑ r ∈ physicalFortyNineChannelResidues,
        (exceptionalSignedPredecessorState 7 (4 * (11025 * L + r + 1 + 1)) -
          exceptionalSignedPredecessorState 7 (4 * (11025 * L + r + 1))) := by
  rw [physicalD49_11025_step_fourSlot_recurrence]
  apply Finset.sum_congr rfl
  intro r hr
  exact fourSlotCellSum_eq_signedPredecessor_increment
    (by norm_num : Nat.Prime 7) (11025 * L + r + 1)

/-- A concrete literal LOCAL-BLOCK, before any extra compensation. -/
theorem physicalD9_block_thirtyNine_eq_neg_five :
    physicalD9 (9 * (39 + 1)) - physicalD9 (9 * 39) = -5 := by
  rw [physicalD9_nine_step_recurrence]
  native_decide

/-- At the corresponding parent endpoint `X=1440`, the single square-dilated
Mertens daughter is zero. -/
theorem mertensDaughter_three_1440_eq_zero :
    mertensSummatoryInt (1440 / (3 * 3)) = 0 := by
  native_decide

/-- The uncompensated LOCAL-BLOCK cannot be any scalar multiple of its single
Mertens daughter.  A parent/response/mate physical compensation is therefore
essential before invoking the algebraic q-square remainder theorem. -/
theorem physicalD9_block_thirtyNine_ne_scalar_mertensDaughter (a : ℤ) :
    physicalD9 (9 * (39 + 1)) - physicalD9 (9 * 39) ≠
      a * mertensSummatoryInt (1440 / (3 * 3)) := by
  rw [physicalD9_block_thirtyNine_eq_neg_five,
    mertensDaughter_three_1440_eq_zero]
  norm_num

end RHLean.Proof
