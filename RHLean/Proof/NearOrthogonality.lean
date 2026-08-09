import Mathlib
import RHLean.Proof.OrthogonalResidual

/-!
# Near-orthogonality and finite signed defect reduction

This module adds the exact finite algebra needed to compare a theorem-predicted
subtraction coefficient with the true orthogonal projection coefficient.

It proves:

* the exact projection defect for an arbitrary predicted coefficient;
* the normalized coefficient-gap identity;
* the exact excess-energy identity over the true orthogonal residual;
* a finite Abel summation identity;
* the exact Abel reduction of a finite weighted Hilbert-space defect.

No Möbius cancellation estimate, logarithmic-integral estimate, or RH implication
is asserted here.
-/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RHLean.Analysis

section Hilbert

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The failure of a theorem-predicted subtraction coefficient to be orthogonal.

Mathlib's inner product is linear in its second argument, so this is
`⟪P, B - betaPred • P⟫`.
-/
def projectionDefect (betaPred : 𝕜) (P B : E) : 𝕜 :=
  inner 𝕜 P (theoremPredictedResidual (𝕜 := 𝕜) betaPred P B)

/-- The projection defect is exactly `⟪P,B⟫ - betaPred * ⟪P,P⟫`. -/
theorem projectionDefect_eq_inner_sub_mul
    (betaPred : 𝕜) (P B : E) :
    projectionDefect (𝕜 := 𝕜) betaPred P B =
      inner 𝕜 P B - betaPred * inner 𝕜 P P := by
  simp [projectionDefect, theoremPredictedResidual,
    theoremPredictedSubtraction, inner_sub_right, inner_smul_right]

/-- The gap between the true projection coefficient and a predicted coefficient
is the normalized projection defect. -/
theorem orthogonalCoefficient_sub_predicted_eq_projectionDefect_div
    (betaPred : 𝕜) (P B : E) (hP : P ≠ 0) :
    orthogonalCoefficient (𝕜 := 𝕜) P B hP - betaPred =
      projectionDefect (𝕜 := 𝕜) betaPred P B / inner 𝕜 P P := by
  have hPP : inner 𝕜 P P ≠ 0 :=
    (inner_self_ne_zero (𝕜 := 𝕜)).2 hP
  rw [projectionDefect_eq_inner_sub_mul]
  unfold orthogonalCoefficient
  field_simp [hPP]

/-- Every theorem-predicted residual is the true orthogonal residual plus the
coefficient gap in the prediction direction. -/
theorem theoremPredictedResidual_eq_orthogonalResidual_add_coefficientGap
    (betaPred : 𝕜) (P B : E) (hP : P ≠ 0) :
    theoremPredictedResidual (𝕜 := 𝕜) betaPred P B =
      orthogonalResidual (𝕜 := 𝕜) P B hP +
        (orthogonalCoefficient (𝕜 := 𝕜) P B hP - betaPred) • P := by
  unfold theoremPredictedResidual theoremPredictedSubtraction orthogonalResidual
  module

/-- Exact excess-energy identity for a theorem-predicted subtraction coefficient.
No orthogonality is assigned to that coefficient itself. -/
theorem theoremPredictedResidual_energy_decomposition
    (betaPred : 𝕜) (P B : E) (hP : P ≠ 0) :
    ‖theoremPredictedResidual (𝕜 := 𝕜) betaPred P B‖ ^ 2 =
      ‖orthogonalResidual (𝕜 := 𝕜) P B hP‖ ^ 2 +
        ‖(orthogonalCoefficient (𝕜 := 𝕜) P B hP - betaPred) • P‖ ^ 2 := by
  calc
    ‖theoremPredictedResidual (𝕜 := 𝕜) betaPred P B‖ ^ 2 =
        ‖orthogonalResidual (𝕜 := 𝕜) P B hP +
          (orthogonalCoefficient (𝕜 := 𝕜) P B hP - betaPred) • P‖ ^ 2 := by
      rw [theoremPredictedResidual_eq_orthogonalResidual_add_coefficientGap
        (𝕜 := 𝕜) betaPred P B hP]
    _ = ‖orthogonalResidual (𝕜 := 𝕜) P B hP‖ ^ 2 +
        ‖(orthogonalCoefficient (𝕜 := 𝕜) P B hP - betaPred) • P‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := 𝕜)]
      rw [inner_smul_right]
      rw [orthogonalResidual_inner_eq_zero (𝕜 := 𝕜) P B hP]
      simp

/-- The same excess-energy identity with the coefficient gap replaced by the
normalized projection defect. -/
theorem theoremPredictedResidual_energy_eq_orthogonal_add_projectionDefect
    (betaPred : 𝕜) (P B : E) (hP : P ≠ 0) :
    ‖theoremPredictedResidual (𝕜 := 𝕜) betaPred P B‖ ^ 2 =
      ‖orthogonalResidual (𝕜 := 𝕜) P B hP‖ ^ 2 +
        ‖(projectionDefect (𝕜 := 𝕜) betaPred P B / inner 𝕜 P P) • P‖ ^ 2 := by
  rw [theoremPredictedResidual_energy_decomposition
    (𝕜 := 𝕜) betaPred P B hP]
  rw [orthogonalCoefficient_sub_predicted_eq_projectionDefect_div
    (𝕜 := 𝕜) betaPred P B hP]

/-- A dimensionless near-orthogonality condition for a predicted coefficient. -/
def NearOrthogonalAt
    (eta : ℝ) (betaPred : 𝕜) (P B : E) : Prop :=
  ‖projectionDefect (𝕜 := 𝕜) betaPred P B‖ ≤ eta * ‖P‖ ^ 2

end Hilbert

section FiniteAbel

variable {R : Type*} [CommRing R]

/-- Inclusive prefix sum `a 0 + ... + a n`. -/
def inclusivePrefix (a : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1), a k

/-- Exact finite Abel summation on the inclusive interval `0,...,n`. -/
theorem finite_abel_identity (a w : ℕ → R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), a k * w k) =
      inclusivePrefix a n * w n +
        ∑ k ∈ Finset.range n,
          inclusivePrefix a k * (w k - w (k + 1)) := by
  induction n with
  | zero => simp [inclusivePrefix]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      simp only [inclusivePrefix, Finset.sum_range_succ]
      ring

end FiniteAbel

section FiniteWeightedDefect

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A finite scalar-weighted prediction vector. -/
def finitePrediction
    (a : ℕ → 𝕜) (atom : ℕ → E) (n : ℕ) : E :=
  ∑ k ∈ Finset.range (n + 1), a k • atom k

/-- Prefix sum of the conjugated scalar coefficients. The conjugation is forced
by conjugate-linearity of the first inner-product argument. -/
def finiteConjugateCoefficientPrefix
    (a : ℕ → 𝕜) (n : ℕ) : 𝕜 :=
  inclusivePrefix (fun k => (starRingEnd 𝕜) (a k)) n

/-- The scalar defect weight attached to one prediction atom. -/
def finiteDefectWeight
    (atom : ℕ → E) (residual : E) (k : ℕ) : 𝕜 :=
  inner 𝕜 (atom k) residual

/-- Expanding a finite prediction in the first inner-product slot yields the
conjugated coefficient-weighted defect sum. -/
theorem projectionDefect_finitePrediction_eq_sum
    (betaPred : 𝕜) (a : ℕ → 𝕜) (atom : ℕ → E) (B : E) (n : ℕ) :
    projectionDefect (𝕜 := 𝕜) betaPred (finitePrediction a atom n) B =
      ∑ k ∈ Finset.range (n + 1),
        (starRingEnd 𝕜) (a k) *
          finiteDefectWeight atom
            (theoremPredictedResidual (𝕜 := 𝕜) betaPred
              (finitePrediction a atom n) B) k := by
  unfold projectionDefect finitePrediction finiteDefectWeight
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro k hk
  rw [inner_smul_left]

/-- Exact Abel reduction of a finite weighted Hilbert-space projection defect. -/
theorem projectionDefect_finitePrediction_eq_abel
    (betaPred : 𝕜) (a : ℕ → 𝕜) (atom : ℕ → E) (B : E) (n : ℕ) :
    projectionDefect (𝕜 := 𝕜) betaPred (finitePrediction a atom n) B =
      finiteConjugateCoefficientPrefix a n *
        finiteDefectWeight atom
          (theoremPredictedResidual (𝕜 := 𝕜) betaPred
            (finitePrediction a atom n) B) n +
      ∑ k ∈ Finset.range n,
        finiteConjugateCoefficientPrefix a k *
          (finiteDefectWeight atom
              (theoremPredictedResidual (𝕜 := 𝕜) betaPred
                (finitePrediction a atom n) B) k -
            finiteDefectWeight atom
              (theoremPredictedResidual (𝕜 := 𝕜) betaPred
                (finitePrediction a atom n) B) (k + 1)) := by
  rw [projectionDefect_finitePrediction_eq_sum]
  simpa [finiteConjugateCoefficientPrefix, finiteDefectWeight] using
    (finite_abel_identity
      (fun k => (starRingEnd 𝕜) (a k))
      (fun k => inner 𝕜 (atom k)
        (theoremPredictedResidual (𝕜 := 𝕜) betaPred
          (finitePrediction a atom n) B)) n)

end FiniteWeightedDefect

end RHLean.Analysis
