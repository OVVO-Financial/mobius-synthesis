import RHLean.Geometry.FermatCoordinates

namespace RHLean.Geometry

/-- Real coordinate of the squared Fermat map. -/
noncomputable def squareMapX (c q : ℝ) : ℝ := c * q

/-- Imaginary coordinate of the squared Fermat map. -/
noncomputable def squareMapY (c q : ℝ) : ℝ := (q ^ 2 - c ^ 2) / 2

/-- The parabola obtained by fixing the lower factor `c`. -/
def LowerCofactorParabola (c x y : ℝ) : Prop :=
  x ^ 2 = 2 * c ^ 2 * y + c ^ 4

/-- The parabola obtained by fixing the upper factor `q`. -/
def UpperCofactorParabola (q x y : ℝ) : Prop :=
  x ^ 2 = q ^ 4 - 2 * q ^ 2 * y

/-- Squared-map coordinates lie on the exact lower-factor parabola. -/
theorem squareMap_mem_lowerCofactorParabola
    (c q : ℝ) :
    LowerCofactorParabola c (squareMapX c q) (squareMapY c q) := by
  unfold LowerCofactorParabola squareMapX squareMapY
  ring

/-- Squared-map coordinates lie on the exact upper-factor parabola. -/
theorem squareMap_mem_upperCofactorParabola
    (c q : ℝ) :
    UpperCofactorParabola q (squareMapX c q) (squareMapY c q) := by
  unfold UpperCofactorParabola squareMapX squareMapY
  ring

/-- The lower-factor parabola can be read as an exact imbalance identity. -/
theorem lowerCofactorParabola_imbalance
    {c x y : ℝ}
    (h : LowerCofactorParabola c x y) :
    2 * c ^ 2 * y = x ^ 2 - c ^ 4 := by
  unfold LowerCofactorParabola at h
  linarith

/-- The upper-factor parabola can be read as an exact imbalance identity. -/
theorem upperCofactorParabola_imbalance
    {q x y : ℝ}
    (h : UpperCofactorParabola q x y) :
    2 * q ^ 2 * y = q ^ 4 - x ^ 2 := by
  unfold UpperCofactorParabola at h
  linarith

/-- Every squared factor pair lies simultaneously on both cofactor parabolas. -/
theorem squareMap_mem_bothCofactorParabolas
    (c q : ℝ) :
    LowerCofactorParabola c (squareMapX c q) (squareMapY c q) ∧
      UpperCofactorParabola q (squareMapX c q) (squareMapY c q) := by
  exact ⟨squareMap_mem_lowerCofactorParabola c q,
    squareMap_mem_upperCofactorParabola c q⟩

/-- The coordinate definitions agree with the previously proved squared complex coordinates. -/
theorem squareMap_coordinates_eq_fermat
    (c q : ℝ) :
    squareMapX c q = (fermatA c q) ^ 2 - (fermatB c q) ^ 2 ∧
      squareMapY c q = 2 * fermatA c q * fermatB c q := by
  constructor
  · rw [square_real_coordinate]
    rfl
  · rw [square_imaginary_coordinate]
    rfl

end RHLean.Geometry
