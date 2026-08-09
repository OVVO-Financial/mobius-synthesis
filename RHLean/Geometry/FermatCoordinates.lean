import Mathlib

namespace RHLean.Geometry

/-- Fermat midpoint coordinate. -/
noncomputable def fermatA (c q : ℝ) : ℝ := (c + q) / 2

/-- Fermat signed half-gap coordinate. -/
noncomputable def fermatB (c q : ℝ) : ℝ := (q - c) / 2

/-- The midpoint and half-gap recover the lower factor. -/
theorem fermatA_sub_fermatB (c q : ℝ) :
    fermatA c q - fermatB c q = c := by
  simp [fermatA, fermatB]
  ring

/-- The midpoint and half-gap recover the upper factor. -/
theorem fermatA_add_fermatB (c q : ℝ) :
    fermatA c q + fermatB c q = q := by
  simp [fermatA, fermatB]
  ring

/-- The real coordinate after squaring is the factor product. -/
theorem square_real_coordinate (c q : ℝ) :
    (fermatA c q) ^ 2 - (fermatB c q) ^ 2 = c * q := by
  simp [fermatA, fermatB]
  ring

/-- The imaginary coordinate after squaring is the factor imbalance. -/
theorem square_imaginary_coordinate (c q : ℝ) :
    2 * fermatA c q * fermatB c q = (q ^ 2 - c ^ 2) / 2 := by
  simp [fermatA, fermatB]
  ring

/-- Squared radius identity used to recover the original factors. -/
theorem radius_identity (c q : ℝ) :
    (c * q) ^ 2 + ((q ^ 2 - c ^ 2) / 2) ^ 2 =
      ((c ^ 2 + q ^ 2) / 2) ^ 2 := by
  ring

end RHLean.Geometry
