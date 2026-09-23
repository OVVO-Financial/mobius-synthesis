import Mathlib
import RHLean.Analysis.ElevenWeightOneFirstMoment
import RHLean.Analysis.OutsidePrimeDeletionMask

/-!
# Actual Möbius / finite-prime tensor compatibility

The exact prime-11 tensor theorem permits an arbitrary field on a *coprime
complementary CRT coordinate*.  It does not permit an arbitrary function of the
same 11^2 coordinate.  The full Möbius/recovered field contains arithmetic from
all other primes, and on a lone 11^2 period that complementary arithmetic is in
general correlated with the 11 residue.

There are therefore two logically distinct transfer issues:

* the actual all-prime zero-free population is obtained from the selected-prime
  zero-free population by outside-square deletion;
* even on an actually retained cell, `selectedDegreeOneProjection` contains
  only the selected-prime sign, while the Mertens-visible physical observable
  contains the parity of every prime factor.

The finite certificates below make both distinctions impossible to hide inside
a later norm estimate.  They do not contradict the exact finite-prime tensor
theorem itself.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-- The exact remaining bridge after the square-owner blocker has been applied:
a selected finite-prime degree-one observable must be transferred to the true
Möbius degree-one observable on the actual all-prime retained population.  This
is intentionally a proposition, not an assumption consumed by any theorem in
this file.  The finite counterexamples below show that it cannot be discharged
by pointwise equality or by the existing coprime tensor theorem alone. -/
def SelectedPrimeMobiusParityTransfer (P O : Finset ℕ) : Prop :=
  (∑ k ∈ outsidePrimeActualRetainedCells O,
      selectedDegreeOneProjection P k) =
    ∑ k ∈ outsidePrimeActualRetainedCells O,
      ((threeSlotDegreeOneValue (threeSlotState k) : ℤ) : ℝ)

/-- The first physical transition cell is genuinely all-prime zero-free: its
six sites are `1,2,3,5,6,7`, all squarefree. -/
theorem zero_is_actual_zeroFree_transition :
    outsidePrimeActualZeroFreeAt 0 := by
  native_decide

/-- On that retained physical cell, the selected `{11}` degree-one observable
sees no 11-divisibility and therefore equals `+1`. -/
theorem elevenSelectedDegreeOne_zero_eq_one :
    selectedDegreeOneProjection ({11} : Finset ℕ) 0 = 1 := by
  norm_num [selectedDegreeOneProjection, selectedPrimeSign, tActiveForm]

/-- The true Mertens-visible source degree-one value at the same cell is `-1`,
coming from the actual Möbius values of `1,2,3`. -/
theorem physicalDegreeOne_zero_eq_neg_one :
    threeSlotDegreeOneValue (threeSlotState 0) = -1 := by
  native_decide

/-- **Observable-transfer no-go.**  Even after the actual all-prime zero-free
mask has retained a cell, the selected-prime observable need not equal the true
Möbius observable.  Thus eliminating outside-prime square owners does not by
itself transfer a selected-prime Walsh contraction to the Mertens-visible
physical field; outside-prime first-power parity must also be reconstructed. -/
theorem elevenSelectedDegreeOne_ne_physical_on_actual_retained_cell :
    outsidePrimeActualZeroFreeAt 0 ∧
      selectedDegreeOneProjection ({11} : Finset ℕ) 0 ≠
        ((threeSlotDegreeOneValue (threeSlotState 0) : ℤ) : ℝ) := by
  refine ⟨zero_is_actual_zeroFree_transition, ?_⟩
  rw [elevenSelectedDegreeOne_zero_eq_one, physicalDegreeOne_zero_eq_neg_one]
  norm_num

/-- Integer selected-11 degree-one mass on the actually retained cells of the
complete aligned residue period `[0,121)`. -/
def elevenCompleteActualRetainedSelectedMass : ℤ :=
  ∑ k ∈ outsidePrimeActualRetainedCells (Finset.range 121),
    (selectedPrimeSign ({11} : Finset ℕ) (tActiveForm (0 : Fin 3) k) -
      selectedPrimeSign ({11} : Finset ℕ) (tActiveForm (1 : Fin 3) k) +
        selectedPrimeSign ({11} : Finset ℕ) (tActiveForm (2 : Fin 3) k))

/-- True Möbius degree-one mass on exactly the same retained cells. -/
def elevenCompleteActualRetainedMobiusMass : ℤ :=
  ∑ k ∈ outsidePrimeActualRetainedCells (Finset.range 121),
    threeSlotDegreeOneValue (threeSlotState k)

/-- Direct complete-orbit certificate for the selected observable. -/
theorem elevenCompleteActualRetainedSelectedMass_eq_twenty_one :
    elevenCompleteActualRetainedSelectedMass = 21 := by
  native_decide

/-- Direct complete-orbit certificate for the true Möbius observable. -/
theorem elevenCompleteActualRetainedMobiusMass_eq_neg_eleven :
    elevenCompleteActualRetainedMobiusMass = -11 := by
  native_decide

/-- **Complete-CRT parity-transfer no-go.**  Even over one entire aligned
`11^2` residue orbit, and even after imposing the actual all-prime zero-free
mask, the selected-prime signed degree-one mass is not the Mertens-visible
Möbius mass.  Complete selected-prime CRT geometry therefore cannot by itself
supply the missing first-power parity transfer. -/
theorem elevenCompleteActualRetained_selected_ne_mobius :
    elevenCompleteActualRetainedSelectedMass ≠
      elevenCompleteActualRetainedMobiusMass := by
  rw [elevenCompleteActualRetainedSelectedMass_eq_twenty_one,
    elevenCompleteActualRetainedMobiusMass_eq_neg_eleven]
  norm_num

/-- Actual Möbius mass on the first active affine coordinate over one complete
11^2 cell residue period, with 11-square-zero residues removed. -/
def elevenActualMobiusCoordinateMass : ℤ :=
  ∑ k : Fin 121,
    if tSquareZeroFreeAt 11 k.1 then μ (tTransitionForm (0 : Fin 6) k.1) else 0

/-- The same Möbius values after stripping the local first-power 11 sign.  If
this stripped field were independent of the 11^2 coordinate in the sense needed
by the tensor theorem, multiplying the 11 sign back in would produce the exact
19/23 factor. -/
def elevenStrippedMobiusCoordinateMass : ℤ :=
  ∑ k : Fin 121,
    if tSquareZeroFreeAt 11 k.1 then
      (if 11 ∣ tTransitionForm (0 : Fin 6) k.1 then
        -μ (tTransitionForm (0 : Fin 6) k.1)
       else μ (tTransitionForm (0 : Fin 6) k.1))
    else 0

/-- Direct finite arithmetic certificate. -/
theorem elevenActualMobiusCoordinateMass_eq_neg_eight :
    elevenActualMobiusCoordinateMass = -8 := by
  native_decide

/-- Direct finite arithmetic certificate for the stripped complementary mass. -/
theorem elevenStrippedMobiusCoordinateMass_eq_neg_fourteen :
    elevenStrippedMobiusCoordinateMass = -14 := by
  native_decide

/-- **Naive physical tensorization is false.**  On one complete 11^2 residue
period, the actual Möbius complement does not satisfy the selected-prime
weight-one factor `19/23`.  Therefore a proof that contracts the recovered field
must first construct a genuine coprime complementary coordinate (or an exact
signed compensation that removes this correlation). -/
theorem elevenActualMobius_not_weightOneTensor :
    (elevenActualMobiusCoordinateMass : ℚ) ≠
      onePrimeWalshFactor 11 1 *
        (elevenStrippedMobiusCoordinateMass : ℚ) := by
  rw [elevenActualMobiusCoordinateMass_eq_neg_eight,
    elevenStrippedMobiusCoordinateMass_eq_neg_fourteen,
    onePrimeWalshFactor_eleven_one]
  norm_num

/-- The observed one-period multiplier of the actual arithmetic field is 4/7,
not 19/23.  The statement is only a finite diagnostic equality; no limiting
claim is made. -/
theorem elevenActualMobius_onePeriod_ratio :
    (elevenActualMobiusCoordinateMass : ℚ) /
        (elevenStrippedMobiusCoordinateMass : ℚ) = (4 : ℚ) / 7 := by
  rw [elevenActualMobiusCoordinateMass_eq_neg_eight,
    elevenStrippedMobiusCoordinateMass_eq_neg_fourteen]
  norm_num

end RHLean.Analysis
