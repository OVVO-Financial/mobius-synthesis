import RHLean.Geometry.CofactorParabolas

namespace RHLean.Geometry

/-- The imaginary coordinate of the squared point `a + b * I`. -/
noncomputable def twoAB (a b : ℝ) : ℝ := 2 * a * b

/-- The squared Fermat map's imaginary coordinate is exactly `2ab`. -/
theorem squareMapY_eq_twoAB (c q : ℝ) :
    squareMapY c q = twoAB (fermatA c q) (fermatB c q) := by
  unfold twoAB
  exact (squareMap_coordinates_eq_fermat c q).2

/-- Scanning the midpoint by `h` at fixed half-gap displaces `2ab` by `2bh`. -/
theorem twoAB_midpoint_displacement (a b h : ℝ) :
    twoAB (a + h) b - twoAB a b = 2 * b * h := by
  unfold twoAB
  ring

/-- Scanning the half-gap by `h` at fixed midpoint displaces `2ab` by `2ah`. -/
theorem twoAB_halfGap_displacement (a b h : ℝ) :
    twoAB a (b + h) - twoAB a b = 2 * a * h := by
  unfold twoAB
  ring

/-- A common shift of both factors shifts the Fermat midpoint by the same amount. -/
theorem fermatA_common_shift (c q h : ℝ) :
    fermatA (c + h) (q + h) = fermatA c q + h := by
  unfold fermatA
  ring

/-- A common shift of both factors preserves the Fermat half-gap. -/
theorem fermatB_common_shift (c q h : ℝ) :
    fermatB (c + h) (q + h) = fermatB c q := by
  unfold fermatB
  ring

/-- Exact upper-factor finite difference of the imaginary squared coordinate. -/
theorem squareMapY_upperFactor_displacement (c q h : ℝ) :
    squareMapY c (q + h) - squareMapY c q =
      h * (2 * q + h) / 2 := by
  unfold squareMapY
  ring

/-- Exact lower-factor finite difference of the imaginary squared coordinate. -/
theorem squareMapY_lowerFactor_displacement (c q h : ℝ) :
    squareMapY (c + h) q - squareMapY c q =
      -(h * (2 * c + h) / 2) := by
  unfold squareMapY
  ring

/-- Common factor translation cancels the quadratic terms and gives linear displacement. -/
theorem squareMapY_common_shift_displacement (c q h : ℝ) :
    squareMapY (c + h) (q + h) - squareMapY c q =
      h * (q - c) := by
  unfold squareMapY
  ring

/-- Additive form of the exact common-shift scan identity. -/
theorem squareMapY_common_shift_eq (c q h : ℝ) :
    squareMapY (c + h) (q + h) =
      squareMapY c q + h * (q - c) := by
  unfold squareMapY
  ring

/-- A parity-preserving common shift by `2n` has displacement `2n(q-c)`. -/
theorem squareMapY_even_common_shift_displacement (c q n : ℝ) :
    squareMapY (c + 2 * n) (q + 2 * n) - squareMapY c q =
      2 * n * (q - c) := by
  simpa using squareMapY_common_shift_displacement c q (2 * n)

/-- With ordered factors and a nonnegative scan, the vertical displacement is nonnegative. -/
theorem squareMapY_common_shift_displacement_nonneg
    {c q h : ℝ}
    (hcq : c ≤ q)
    (hh : 0 ≤ h) :
    0 ≤ squareMapY (c + h) (q + h) - squareMapY c q := by
  rw [squareMapY_common_shift_displacement]
  exact mul_nonneg hh (sub_nonneg.mpr hcq)

/-- With strictly ordered factors and a positive scan, the vertical displacement is positive. -/
theorem squareMapY_common_shift_displacement_pos
    {c q h : ℝ}
    (hcq : c < q)
    (hh : 0 < h) :
    0 < squareMapY (c + h) (q + h) - squareMapY c q := by
  rw [squareMapY_common_shift_displacement]
  exact mul_pos hh (sub_pos.mpr hcq)

/-- Common-shift scans are monotone when the lower factor does not exceed the upper factor. -/
theorem squareMapY_common_shift_monotone
    {c q h₁ h₂ : ℝ}
    (hcq : c ≤ q)
    (hh : h₁ ≤ h₂) :
    squareMapY (c + h₁) (q + h₁) ≤
      squareMapY (c + h₂) (q + h₂) := by
  rw [squareMapY_common_shift_eq, squareMapY_common_shift_eq]
  exact add_le_add_left
    (mul_le_mul_of_nonneg_right hh (sub_nonneg.mpr hcq))
    (squareMapY c q)

/-- A scan remains inside a vertical window when its exact displacement is at most the width. -/
def CommonShiftWithinVerticalWindow
    (c q h width : ℝ) : Prop :=
  squareMapY (c + h) (q + h) - squareMapY c q ≤ width

/-- Exact lifetime criterion for a common factor shift inside a vertical window. -/
theorem commonShiftWithinVerticalWindow_iff
    (c q h width : ℝ) :
    CommonShiftWithinVerticalWindow c q h width ↔
      h * (q - c) ≤ width := by
  unfold CommonShiftWithinVerticalWindow
  rw [squareMapY_common_shift_displacement]

/-- Once the exact linear displacement exceeds the window width, the scan has exited. -/
theorem commonShift_exits_verticalWindow
    {c q h width : ℝ}
    (hwidth : width < h * (q - c)) :
    ¬CommonShiftWithinVerticalWindow c q h width := by
  intro hinside
  have hbudget :=
    (commonShiftWithinVerticalWindow_iff c q h width).1 hinside
  exact (not_le_of_gt hwidth) hbudget

end RHLean.Geometry
