import Mathlib
import RHLean.Analysis.NativePNTInterceptGrowth

/-!
# Mild-update targets for the explicit native PNT intercept

The exact update is controlled by the onset `M_n`.  This file formalizes the
two onset scales that would give the desired linear or quadratic intercept
increments.
-/

noncomputable section

namespace RHLean.Analysis

/-- A uniform `C a_n^2 M_n` bound gives a linear-in-`a_n` intercept update. -/
theorem nativePNTCubicIntercept_succ_le_add_linear_of_onset_scale
    (n : ℕ) (K : ℝ)
    (hscale :
      nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 2 *
          (nativePNTCubicStepOnset
            (nativePNTCubicSlope n) (nativePNTCubicIntercept n) : ℝ) ≤ K) :
    nativePNTCubicIntercept (n + 1) ≤
      nativePNTCubicIntercept n + K * nativePNTCubicSlope n := by
  have ha0 : 0 ≤ nativePNTCubicSlope n :=
    (nativePNTCubicSlope_spec n).1.le
  have hmul := mul_le_mul_of_nonneg_right hscale ha0
  rw [nativePNTCubicIntercept_succ_eq]
  unfold nativePNTCubicInterceptIncrement
  nlinarith

/-- A uniform `C a_n M_n` bound gives the stronger quadratic-in-`a_n` update. -/
theorem nativePNTCubicIntercept_succ_le_add_quadratic_of_onset_scale
    (n : ℕ) (K : ℝ)
    (hscale :
      nativePNTCubicConstant * nativePNTCubicSlope n *
          (nativePNTCubicStepOnset
            (nativePNTCubicSlope n) (nativePNTCubicIntercept n) : ℝ) ≤ K) :
    nativePNTCubicIntercept (n + 1) ≤
      nativePNTCubicIntercept n + K * (nativePNTCubicSlope n) ^ 2 := by
  have ha2 : 0 ≤ (nativePNTCubicSlope n) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hscale ha2
  rw [nativePNTCubicIntercept_succ_eq]
  unfold nativePNTCubicInterceptIncrement
  nlinarith

/-- The hoped-for global linear-step bound, now isolated as a bound-level
statement. -/
def NativePNTCubicInterceptLinearStepBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
    nativePNTCubicIntercept (n + 1) ≤
      nativePNTCubicIntercept n + K * nativePNTCubicSlope n

/-- The stronger quadratic-step bound. -/
def NativePNTCubicInterceptQuadraticStepBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
    nativePNTCubicIntercept (n + 1) ≤
      nativePNTCubicIntercept n + K * (nativePNTCubicSlope n) ^ 2

/-- Uniform quadratic onset scaling would imply the linear intercept update. -/
theorem nativePNTCubicInterceptLinearStepBound_of_onset_scale
    (h : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 2 *
          (nativePNTCubicStepOnset
            (nativePNTCubicSlope n) (nativePNTCubicIntercept n) : ℝ) ≤ K) :
    NativePNTCubicInterceptLinearStepBound := by
  rcases h with ⟨K, hK, hscale⟩
  refine ⟨K, hK, ?_⟩
  intro n
  exact nativePNTCubicIntercept_succ_le_add_linear_of_onset_scale
    n K (hscale n)

/-- Uniform linear onset scaling would imply the quadratic intercept update. -/
theorem nativePNTCubicInterceptQuadraticStepBound_of_onset_scale
    (h : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      nativePNTCubicConstant * nativePNTCubicSlope n *
          (nativePNTCubicStepOnset
            (nativePNTCubicSlope n) (nativePNTCubicIntercept n) : ℝ) ≤ K) :
    NativePNTCubicInterceptQuadraticStepBound := by
  rcases h with ⟨K, hK, hscale⟩
  refine ⟨K, hK, ?_⟩
  intro n
  exact nativePNTCubicIntercept_succ_le_add_quadratic_of_onset_scale
    n K (hscale n)

end RHLean.Analysis
