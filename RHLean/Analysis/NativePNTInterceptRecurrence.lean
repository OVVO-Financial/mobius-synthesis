import Mathlib
import RHLean.Analysis.NativePNTInterceptStep
import RHLean.Analysis.NativePNTQuadraticBudget

/-!
# Canonical intercept along the native PNT cubic recurrence

This module defines the additive intercept `D_n` produced by iterating the
explicit one-step propagation theorem.  It is an admissible proof intercept,
not a claim of minimality.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Canonical additive intercept propagated by the current cubic PNT proof. -/
noncomputable def nativePNTCubicIntercept : ℕ → ℝ
  | 0 => 0
  | Nat.succ n =>
      nativePNTCubicIntercept n +
        nativePNTCubicStepDelta (nativePNTCubicSlope n) *
          (nativePNTCubicStepOnset
            (nativePNTCubicSlope n) (nativePNTCubicIntercept n) : ℝ)

@[simp] theorem nativePNTCubicIntercept_zero :
    nativePNTCubicIntercept 0 = 0 := rfl

@[simp] theorem nativePNTCubicIntercept_succ (n : ℕ) :
    nativePNTCubicIntercept (n + 1) =
      nativePNTCubicIntercept n +
        nativePNTCubicStepDelta (nativePNTCubicSlope n) *
          (nativePNTCubicStepOnset
            (nativePNTCubicSlope n) (nativePNTCubicIntercept n) : ℝ) := rfl

/-- Exact one-step intercept increment, written with the repository's cubic
constant. -/
def nativePNTCubicInterceptIncrement (n : ℕ) : ℝ :=
  nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3 *
    (nativePNTCubicStepOnset
      (nativePNTCubicSlope n) (nativePNTCubicIntercept n) : ℝ)

/-- Every propagated intercept is nonnegative. -/
theorem nativePNTCubicIntercept_nonneg :
    ∀ n : ℕ, 0 ≤ nativePNTCubicIntercept n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [nativePNTCubicIntercept_succ]
      apply add_nonneg ih
      apply mul_nonneg
      · rw [nativePNTCubicStepDelta_eq]
        exact mul_nonneg
          (by norm_num [nativePNTCubicConstant])
          (pow_nonneg (nativePNTCubicSlope_spec n).1.le 3)
      · positivity

/-- The pair `(a_n,D_n)` is a genuine affine PNT envelope at every step. -/
theorem nativePNTCubicIntercept_envelope :
    ∀ n : ℕ,
      NativePNTAffineEnvelopeAt
        (nativePNTCubicSlope n) (nativePNTCubicIntercept n) := by
  intro n
  induction n with
  | zero =>
      simpa using nativePNTAffineEnvelopeAt_six_zero
  | succ n ih =>
      have hspec := nativePNTCubicSlope_spec n
      have hstep := nativePNTAffineEnvelopeAt_cubic_step
        (nativePNTCubicSlope n) (nativePNTCubicIntercept n)
        hspec.1 hspec.2.1 ih
      simpa [nativePNTCubicIntercept_succ,
        nativePNTCubicSlope_succ, nativePNTCubicStepDelta_eq] using hstep

/-- The explicit intercept also witnesses the original existential affine
envelope. -/
theorem nativePNTCubicIntercept_hasAffineEnvelope (n : ℕ) :
    nativePNTHasAffineEnvelope (nativePNTCubicSlope n) :=
  nativePNTAffineEnvelopeAt.toHasAffineEnvelope
    (nativePNTCubicIntercept_envelope n)

/-- **Exact intercept recurrence.** -/
theorem nativePNTCubicIntercept_succ_eq (n : ℕ) :
    nativePNTCubicIntercept (n + 1) =
      nativePNTCubicIntercept n + nativePNTCubicInterceptIncrement n := by
  rw [nativePNTCubicIntercept_succ]
  unfold nativePNTCubicInterceptIncrement
  rw [nativePNTCubicStepDelta_eq]

/-- The propagated intercept is exactly the sum of the preceding one-step
costs. -/
theorem nativePNTCubicIntercept_eq_sum (n : ℕ) :
    nativePNTCubicIntercept n =
      ∑ j ∈ Finset.range n, nativePNTCubicInterceptIncrement j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [nativePNTCubicIntercept_succ_eq, ih]
      rw [Finset.sum_range_succ]

end RHLean.Analysis
