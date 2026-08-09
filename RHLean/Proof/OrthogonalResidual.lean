import Mathlib

open scoped InnerProductSpace

noncomputable section

namespace RHLean.Analysis

/--
The true coefficient of the orthogonal projection of `B` onto the nonzero
prediction vector `P`. Mathlib's inner product is linear in its second argument,
so the coefficient is `⟪P, B⟫ / ⟪P, P⟫`.
-/
def orthogonalCoefficient {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (P B : E) (_hP : P ≠ 0) : 𝕜 :=
  inner 𝕜 P B / inner 𝕜 P P

/-- The residual after subtracting the true orthogonal projection onto `P`. -/
def orthogonalResidual {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (P B : E) (hP : P ≠ 0) : E :=
  B - orthogonalCoefficient (𝕜 := 𝕜) P B hP • P

/-- The prediction vector is orthogonal to the true orthogonal residual. -/
theorem inner_orthogonalResidual_eq_zero
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (P B : E) (hP : P ≠ 0) :
    inner 𝕜 P (orthogonalResidual (𝕜 := 𝕜) P B hP) = 0 := by
  have hPP : inner 𝕜 P P ≠ 0 :=
    (inner_self_ne_zero (𝕜 := 𝕜)).2 hP
  unfold orthogonalResidual
  rw [inner_sub_right, inner_smul_right]
  unfold orthogonalCoefficient
  rw [div_mul_cancel₀ _ hPP, sub_self]

/-- The true orthogonal residual is orthogonal to the prediction vector. -/
theorem orthogonalResidual_inner_eq_zero
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (P B : E) (hP : P ≠ 0) :
    inner 𝕜 (orthogonalResidual (𝕜 := 𝕜) P B hP) P = 0 := by
  exact (inner_eq_zero_symm (𝕜 := 𝕜)).2
    (inner_orthogonalResidual_eq_zero (𝕜 := 𝕜) P B hP)

/-- The projection component and orthogonal residual recombine exactly to `B`. -/
theorem orthogonalResidual_add_projection
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (P B : E) (hP : P ≠ 0) :
    orthogonalResidual (𝕜 := 𝕜) P B hP +
      orthogonalCoefficient (𝕜 := 𝕜) P B hP • P = B := by
  simp [orthogonalResidual]

/-- Exact Pythagorean energy decomposition for the true orthogonal residual. -/
theorem orthogonalResidual_energy_decomposition
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (P B : E) (hP : P ≠ 0) :
    ‖B‖ ^ 2 =
      ‖orthogonalResidual (𝕜 := 𝕜) P B hP‖ ^ 2 +
        ‖orthogonalCoefficient (𝕜 := 𝕜) P B hP • P‖ ^ 2 := by
  calc
    ‖B‖ ^ 2 =
        ‖orthogonalResidual (𝕜 := 𝕜) P B hP +
          orthogonalCoefficient (𝕜 := 𝕜) P B hP • P‖ ^ 2 := by
      rw [orthogonalResidual_add_projection (𝕜 := 𝕜) P B hP]
    _ = ‖orthogonalResidual (𝕜 := 𝕜) P B hP‖ ^ 2 +
        ‖orthogonalCoefficient (𝕜 := 𝕜) P B hP • P‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := 𝕜)]
      rw [inner_smul_right]
      rw [orthogonalResidual_inner_eq_zero (𝕜 := 𝕜) P B hP]
      simp

/--
The vector prescribed by a theorem-predicted coefficient. This is not identified
with the true orthogonal projection without a separate coefficient equality.
-/
def theoremPredictedSubtraction {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (betaPred : 𝕜) (P : E) : E :=
  betaPred • P

/--
The residual formed from a theorem-predicted coefficient. No orthogonality or
Pythagorean identity is attached to this definition.
-/
def theoremPredictedResidual {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (betaPred : 𝕜) (P B : E) : E :=
  B - theoremPredictedSubtraction (𝕜 := 𝕜) betaPred P

/--
A theorem-predicted residual agrees with the orthogonal residual only after a
separate proof that its coefficient is the true orthogonal coefficient.
-/
theorem theoremPredictedResidual_eq_orthogonalResidual_of_coefficient_eq
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (betaPred : 𝕜) (P B : E) (hP : P ≠ 0)
    (hbeta : betaPred = orthogonalCoefficient (𝕜 := 𝕜) P B hP) :
    theoremPredictedResidual (𝕜 := 𝕜) betaPred P B =
      orthogonalResidual (𝕜 := 𝕜) P B hP := by
  simp [theoremPredictedResidual, theoremPredictedSubtraction,
    orthogonalResidual, hbeta]

end RHLean.Analysis
