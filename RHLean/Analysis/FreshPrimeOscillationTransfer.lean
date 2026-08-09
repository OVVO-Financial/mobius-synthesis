import RHLean.Proof.OrthogonalResidual

open scoped InnerProductSpace

noncomputable section

namespace RHLean.Analysis

/--
The abstract fresh-prime update: retain the existing state and subtract a
compressed copy.  No contraction or sign assumption is built into this
definition.
-/
def freshPrimeUpdate {E : Type*} [NormedAddCommGroup E]
    (parent compressedCopy : E) : E :=
  parent - compressedCopy

/-- The component of `B` in the distinguished constant-mode direction `P`. -/
def constantModePart {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P B : E) (hP : P ≠ 0) : E :=
  orthogonalCoefficient (𝕜 := ℝ) P B hP • P

/-- The component of `B` orthogonal to the distinguished direction `P`. -/
def oscillatoryPart {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P B : E) (hP : P ≠ 0) : E :=
  orthogonalResidual (𝕜 := ℝ) P B hP

/--
The constant-mode coefficient of a fresh-prime update is the difference of the
parent and compressed-copy coefficients.
-/
theorem orthogonalCoefficient_freshPrimeUpdate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P parent compressedCopy : E) (hP : P ≠ 0) :
    orthogonalCoefficient (𝕜 := ℝ) P
        (freshPrimeUpdate parent compressedCopy) hP =
      orthogonalCoefficient (𝕜 := ℝ) P parent hP -
        orthogonalCoefficient (𝕜 := ℝ) P compressedCopy hP := by
  unfold freshPrimeUpdate orthogonalCoefficient
  rw [inner_sub_right, sub_div]

/-- The constant-mode projection respects the fresh-prime difference. -/
theorem constantModePart_freshPrimeUpdate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P parent compressedCopy : E) (hP : P ≠ 0) :
    constantModePart P (freshPrimeUpdate parent compressedCopy) hP =
      constantModePart P parent hP - constantModePart P compressedCopy hP := by
  unfold constantModePart
  rw [orthogonalCoefficient_freshPrimeUpdate]
  simp [sub_smul]

/-- The oscillatory residual also respects the fresh-prime difference. -/
theorem oscillatoryPart_freshPrimeUpdate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P parent compressedCopy : E) (hP : P ≠ 0) :
    oscillatoryPart P (freshPrimeUpdate parent compressedCopy) hP =
      oscillatoryPart P parent hP - oscillatoryPart P compressedCopy hP := by
  unfold oscillatoryPart orthogonalResidual
  rw [orthogonalCoefficient_freshPrimeUpdate]
  unfold freshPrimeUpdate
  simp [sub_smul]
  abel

/--
Exact decomposition of the updated state into oscillatory and constant-mode
energy.  This deliberately asserts no contraction.
-/
theorem freshPrimeUpdate_energy_decomposition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P parent compressedCopy : E) (hP : P ≠ 0) :
    ‖freshPrimeUpdate parent compressedCopy‖ ^ 2 =
      ‖oscillatoryPart P (freshPrimeUpdate parent compressedCopy) hP‖ ^ 2 +
        ‖constantModePart P (freshPrimeUpdate parent compressedCopy) hP‖ ^ 2 := by
  simpa [oscillatoryPart, constantModePart] using
    orthogonalResidual_energy_decomposition (𝕜 := ℝ) P
      (freshPrimeUpdate parent compressedCopy) hP

/--
Exact energy-transfer identity.  Any increase in total energy splits into an
oscillatory-energy change and a constant-mode-energy change.
-/
theorem freshPrimeUpdate_energy_transfer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P parent compressedCopy : E) (hP : P ≠ 0) :
    ‖freshPrimeUpdate parent compressedCopy‖ ^ 2 - ‖parent‖ ^ 2 =
      (‖oscillatoryPart P (freshPrimeUpdate parent compressedCopy) hP‖ ^ 2 -
        ‖oscillatoryPart P parent hP‖ ^ 2) +
      (‖constantModePart P (freshPrimeUpdate parent compressedCopy) hP‖ ^ 2 -
        ‖constantModePart P parent hP‖ ^ 2) := by
  rw [freshPrimeUpdate_energy_decomposition P parent compressedCopy hP]
  rw [show ‖parent‖ ^ 2 =
      ‖oscillatoryPart P parent hP‖ ^ 2 +
        ‖constantModePart P parent hP‖ ^ 2 by
    simpa [oscillatoryPart, constantModePart] using
      orthogonalResidual_energy_decomposition (𝕜 := ℝ) P parent hP]
  ring

/--
If total energy does not decrease while the constant-mode energy does not
increase, the excess energy is necessarily transferred into the oscillatory
component.
-/
theorem oscillatory_energy_nondecreasing_of_total_nondecreasing_of_constant_suppressed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P parent compressedCopy : E) (hP : P ≠ 0)
    (htotal : ‖parent‖ ^ 2 ≤ ‖freshPrimeUpdate parent compressedCopy‖ ^ 2)
    (hconstant :
      ‖constantModePart P (freshPrimeUpdate parent compressedCopy) hP‖ ^ 2 ≤
        ‖constantModePart P parent hP‖ ^ 2) :
    ‖oscillatoryPart P parent hP‖ ^ 2 ≤
      ‖oscillatoryPart P (freshPrimeUpdate parent compressedCopy) hP‖ ^ 2 := by
  have htransfer := freshPrimeUpdate_energy_transfer P parent compressedCopy hP
  nlinarith

/-- Equal constant-mode orientation cancels under the fresh-prime difference. -/
theorem orthogonalCoefficient_freshPrimeUpdate_eq_zero_of_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P parent compressedCopy : E) (hP : P ≠ 0)
    (hcoeff : orthogonalCoefficient (𝕜 := ℝ) P compressedCopy hP =
      orthogonalCoefficient (𝕜 := ℝ) P parent hP) :
    orthogonalCoefficient (𝕜 := ℝ) P
        (freshPrimeUpdate parent compressedCopy) hP = 0 := by
  rw [orthogonalCoefficient_freshPrimeUpdate, hcoeff]
  simp

/--
Opposite constant-mode orientation reinforces under subtraction: the updated
coefficient is twice the parent coefficient.
-/
theorem orthogonalCoefficient_freshPrimeUpdate_eq_two_mul_of_eq_neg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P parent compressedCopy : E) (hP : P ≠ 0)
    (hcoeff : orthogonalCoefficient (𝕜 := ℝ) P compressedCopy hP =
      -orthogonalCoefficient (𝕜 := ℝ) P parent hP) :
    orthogonalCoefficient (𝕜 := ℝ) P
        (freshPrimeUpdate parent compressedCopy) hP =
      2 * orthogonalCoefficient (𝕜 := ℝ) P parent hP := by
  rw [orthogonalCoefficient_freshPrimeUpdate, hcoeff]
  ring

end RHLean.Analysis
