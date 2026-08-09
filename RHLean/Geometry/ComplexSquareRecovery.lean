import RHLean.Geometry.FermatCoordinates

namespace RHLean.Geometry

/-- The complex Fermat point associated with the factor pair `(c,q)`. -/
noncomputable def fermatPoint (c q : ℝ) : ℂ :=
  ⟨fermatA c q, fermatB c q⟩

/-- Squaring the Fermat point places the factor product on the real axis. -/
theorem fermatPoint_sq_re (c q : ℝ) :
    ((fermatPoint c q) ^ 2).re = c * q := by
  simpa [fermatPoint, pow_two] using square_real_coordinate c q

/-- The imaginary coordinate of the squared Fermat point is the factor imbalance. -/
theorem fermatPoint_sq_im (c q : ℝ) :
    ((fermatPoint c q) ^ 2).im = (q ^ 2 - c ^ 2) / 2 := by
  rw [show (fermatPoint c q) ^ 2 = fermatPoint c q * fermatPoint c q by
    rw [pow_two]]
  simp only [fermatPoint, Complex.mul_im]
  calc
    fermatA c q * fermatB c q + fermatB c q * fermatA c q =
        2 * fermatA c q * fermatB c q := by ring
    _ = (q ^ 2 - c ^ 2) / 2 := square_imaginary_coordinate c q

/-- The squared point is exactly the product/imbalance coordinate pair. -/
theorem fermatPoint_sq (c q : ℝ) :
    (fermatPoint c q) ^ 2 =
      ⟨c * q, (q ^ 2 - c ^ 2) / 2⟩ := by
  apply Complex.ext
  · exact fermatPoint_sq_re c q
  · exact fermatPoint_sq_im c q

/-- Radial and imaginary data recover the lower factor square exactly. -/
theorem recover_lower_factor_sq (c q : ℝ) :
    (c ^ 2 + q ^ 2) / 2 - (q ^ 2 - c ^ 2) / 2 = c ^ 2 := by
  ring

/-- Radial and imaginary data recover the upper factor square exactly. -/
theorem recover_upper_factor_sq (c q : ℝ) :
    (c ^ 2 + q ^ 2) / 2 + (q ^ 2 - c ^ 2) / 2 = q ^ 2 := by
  ring

/-- The squared complex coordinates recover both factor squares without a sign choice. -/
theorem recover_factor_squares (c q : ℝ) :
    ((c ^ 2 + q ^ 2) / 2 - ((fermatPoint c q) ^ 2).im = c ^ 2) ∧
    ((c ^ 2 + q ^ 2) / 2 + ((fermatPoint c q) ^ 2).im = q ^ 2) := by
  rw [fermatPoint_sq_im]
  exact ⟨recover_lower_factor_sq c q, recover_upper_factor_sq c q⟩

end RHLean.Geometry
