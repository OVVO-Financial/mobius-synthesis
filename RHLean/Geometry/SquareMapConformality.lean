import Mathlib

namespace RHLean.Geometry

/-- First coordinate of the differential of the complex squaring map. -/
def squareJacobianX (a b da db : ℝ) : ℝ :=
  2 * a * da - 2 * b * db

/-- Second coordinate of the differential of the complex squaring map. -/
def squareJacobianY (a b da db : ℝ) : ℝ :=
  2 * b * da + 2 * a * db

/-- The differential scales squared Euclidean length by `4 * (a^2 + b^2)`. -/
theorem squareJacobian_normSq
    (a b da db : ℝ) :
    squareJacobianX a b da db ^ 2 +
        squareJacobianY a b da db ^ 2 =
      4 * (a ^ 2 + b ^ 2) * (da ^ 2 + db ^ 2) := by
  unfold squareJacobianX squareJacobianY
  ring

/-- The differential scales every Euclidean inner product by the same factor. -/
theorem squareJacobian_dot
    (a b da db ea eb : ℝ) :
    squareJacobianX a b da db * squareJacobianX a b ea eb +
        squareJacobianY a b da db * squareJacobianY a b ea eb =
      4 * (a ^ 2 + b ^ 2) * (da * ea + db * eb) := by
  unfold squareJacobianX squareJacobianY
  ring

/-- Orthogonal tangent vectors remain orthogonal under the differential. -/
theorem squareJacobian_preserves_orthogonality
    {a b da db ea eb : ℝ}
    (h : da * ea + db * eb = 0) :
    squareJacobianX a b da db * squareJacobianX a b ea eb +
        squareJacobianY a b da db * squareJacobianY a b ea eb = 0 := by
  rw [squareJacobian_dot, h]
  ring

/-- The two Jacobian columns are orthogonal. -/
theorem squareJacobian_columns_orthogonal
    (a b : ℝ) :
    squareJacobianX a b 1 0 * squareJacobianX a b 0 1 +
        squareJacobianY a b 1 0 * squareJacobianY a b 0 1 = 0 := by
  unfold squareJacobianX squareJacobianY
  ring

/-- The first Jacobian column has the common conformal squared scale. -/
theorem squareJacobian_first_column_normSq
    (a b : ℝ) :
    squareJacobianX a b 1 0 ^ 2 +
        squareJacobianY a b 1 0 ^ 2 =
      4 * (a ^ 2 + b ^ 2) := by
  unfold squareJacobianX squareJacobianY
  ring

/-- The second Jacobian column has the same squared scale as the first. -/
theorem squareJacobian_second_column_normSq
    (a b : ℝ) :
    squareJacobianX a b 0 1 ^ 2 +
        squareJacobianY a b 0 1 ^ 2 =
      4 * (a ^ 2 + b ^ 2) := by
  unfold squareJacobianX squareJacobianY
  ring

/-- The Jacobian determinant is the conformal area scale. -/
theorem squareJacobian_determinant
    (a b : ℝ) :
    (2 * a) * (2 * a) - (-2 * b) * (2 * b) =
      4 * (a ^ 2 + b ^ 2) := by
  ring

/-- Away from the origin, the Jacobian determinant is strictly positive. -/
theorem squareJacobian_determinant_pos
    {a b : ℝ}
    (h : 0 < a ^ 2 + b ^ 2) :
    0 < (2 * a) * (2 * a) - (-2 * b) * (2 * b) := by
  rw [squareJacobian_determinant]
  nlinarith

end RHLean.Geometry
