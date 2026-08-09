import Mathlib
import RHLean.Proof.PrimeCombDiscrepancyRecurrence

/-!
# Complete-wheel and boundary decomposition for prime-comb updates

A finite square block is an arbitrary interval relative to any fixed prime wheel.
For a wheel of period `Q`, the block decomposes into complete `Q`-cells together
with at most two incomplete fragments.  The complete cells carry the exact
prime-comb update law.  Every failure of exact wheel proportions is confined to
the incomplete boundary.

This module formalizes that reduction abstractly.  It does not assert the final
arithmetic estimate on the complete-wheel restoring term.
-/

noncomputable section

namespace RHLean.Proof

structure PrimeCombBoundaryState where
  before : ℤ
  after : ℤ
  length : ℕ
  beforeBound : |before| ≤ (length : ℤ)
  afterBound : |after| ≤ (length : ℤ)

theorem PrimeCombBoundaryState.abs_increment_le_two_mul_length
    (b : PrimeCombBoundaryState) :
    |b.after - b.before| ≤ 2 * (b.length : ℤ) := by
  calc
    |b.after - b.before| ≤ |b.after| + |b.before| := by
      simpa [sub_eq_add_neg] using abs_add_le b.after (-b.before)
    _ ≤ (b.length : ℤ) + (b.length : ℤ) :=
      add_le_add b.afterBound b.beforeBound
    _ = 2 * (b.length : ℤ) := by ring

structure PrimeCombWheelSplit where
  total : PrimeCombUpdate
  complete : PrimeCombUpdate
  boundary : PrimeCombBoundaryState
  beforeSplit : total.before = complete.before + boundary.before
  afterSplit : total.after = complete.after + boundary.after

theorem PrimeCombWheelSplit.increment_eq_complete_add_boundary
    (s : PrimeCombWheelSplit) :
    s.total.after - s.total.before =
      (s.complete.after - s.complete.before) +
      (s.boundary.after - s.boundary.before) := by
  rw [s.beforeSplit, s.afterSplit]
  ring

theorem PrimeCombWheelSplit.abs_increment_sub_complete_le_boundary
    (s : PrimeCombWheelSplit) :
    |(s.total.after - s.total.before) -
      (s.complete.after - s.complete.before)| ≤
      2 * (s.boundary.length : ℤ) := by
  have hcancel :
      (s.total.after - s.total.before) -
        (s.complete.after - s.complete.before) =
        s.boundary.after - s.boundary.before := by
    rw [s.beforeSplit, s.afterSplit]
    ring
  rw [hcancel]
  exact s.boundary.abs_increment_le_two_mul_length

theorem PrimeCombWheelSplit.abs_total_after_le_complete_add_boundary
    (s : PrimeCombWheelSplit) :
    |s.total.after| ≤ |s.complete.after| + (s.boundary.length : ℤ) := by
  rw [s.afterSplit]
  exact (abs_add_le _ _).trans (add_le_add_left s.boundary.afterBound _)

structure TwoFragmentWheelBoundary where
  period : ℕ
  leftLength : ℕ
  rightLength : ℕ
  left_lt : leftLength < period
  right_lt : rightLength < period

def TwoFragmentWheelBoundary.length (b : TwoFragmentWheelBoundary) : ℕ :=
  b.leftLength + b.rightLength

theorem TwoFragmentWheelBoundary.length_lt_two_mul_period
    (b : TwoFragmentWheelBoundary) :
    b.length < 2 * b.period := by
  have hleft := b.left_lt
  have hright := b.right_lt
  unfold TwoFragmentWheelBoundary.length
  omega

theorem TwoFragmentWheelBoundary.int_length_le_two_mul_period
    (b : TwoFragmentWheelBoundary) :
    (b.length : ℤ) ≤ 2 * (b.period : ℤ) := by
  exact_mod_cast (Nat.le_of_lt b.length_lt_two_mul_period)

theorem PrimeCombWheelSplit.abs_total_after_le_complete_add_two_periods
    (s : PrimeCombWheelSplit) (b : TwoFragmentWheelBoundary)
    (hlen : s.boundary.length = b.length) :
    |s.total.after| ≤ |s.complete.after| + 2 * (b.period : ℤ) := by
  have hmain := s.abs_total_after_le_complete_add_boundary
  rw [hlen] at hmain
  exact hmain.trans (add_le_add_left b.int_length_le_two_mul_period _)

theorem PrimeCombWheelSplit.abs_total_after_le_two_periods_of_complete_zero
    (s : PrimeCombWheelSplit) (b : TwoFragmentWheelBoundary)
    (hlen : s.boundary.length = b.length)
    (hcomplete : s.complete.after = 0) :
    |s.total.after| ≤ 2 * (b.period : ℤ) := by
  have h := s.abs_total_after_le_complete_add_two_periods b hlen
  simpa [hcomplete] using h

end RHLean.Proof
