import Mathlib

/-!
# Reciprocal-square contraction for exact cubic recurrences

For a positive exact cubic step
`a' = a - C * a^3 = a * (1 - C * a^2)`, the reciprocal square grows by at
least `2C`.  This is the elementary quantitative gain needed to improve the
PNT iteration budget from cubic to quadratic in the target inverse slope.
-/

noncomputable section

namespace RHLean.Analysis

/-- One positive exact cubic step grows the reciprocal square by at least `2C`. -/
theorem inv_sq_add_two_mul_le_inv_sq_cubic_step
    (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (hnext : 0 < a - C * a ^ 3) :
    1 / a ^ 2 + 2 * C ≤ 1 / (a - C * a ^ 3) ^ 2 := by
  have hfactorEq :
      a - C * a ^ 3 = a * (1 - C * a ^ 2) := by
    ring
  have hfactor : 0 < 1 - C * a ^ 2 := by
    rw [hfactorEq] at hnext
    rcases (mul_pos_iff.mp hnext) with hpos | hneg
    · exact hpos.2
    · exfalso
      exact (not_lt_of_ge ha.le) hneg.1
  have hx0 : 0 ≤ C * a ^ 2 :=
    mul_nonneg hC (sq_nonneg a)
  have hx1 : C * a ^ 2 ≤ 1 := by linarith
  have hnextSq : 0 < (a - C * a ^ 3) ^ 2 :=
    sq_pos_of_pos hnext
  apply (le_div_iff₀ hnextSq).2
  have ha0 : a ≠ 0 := ne_of_gt ha
  have heq :
      (1 / a ^ 2 + 2 * C) * (a - C * a ^ 3) ^ 2 =
        (1 + 2 * (C * a ^ 2)) * (1 - C * a ^ 2) ^ 2 := by
    rw [hfactorEq]
    field_simp [ha0]
  rw [heq]
  let x : ℝ := C * a ^ 2
  change (1 + 2 * x) * (1 - x) ^ 2 ≤ 1
  have hx0' : 0 ≤ x := by simpa [x] using hx0
  have hx1' : x ≤ 1 := by simpa [x] using hx1
  have hrem : 0 ≤ x ^ 2 * (3 - 2 * x) :=
    mul_nonneg (sq_nonneg x) (by linarith)
  nlinarith

/-- Any exact positive cubic recurrence has linear reciprocal-square growth. -/
theorem inv_sq_rate_of_exact_cubic_recurrence
    (a : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hpos : ∀ n, 0 < a n)
    (hrec : ∀ n, a (n + 1) = a n - C * (a n) ^ 3) :
    ∀ n : ℕ,
      1 / (a 0) ^ 2 + 2 * C * (n : ℝ) ≤ 1 / (a n) ^ 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hnext : 0 < a n - C * (a n) ^ 3 := by
        rw [← hrec n]
        exact hpos (n + 1)
      have hstep := inv_sq_add_two_mul_le_inv_sq_cubic_step
        (a n) C (hpos n) hC hnext
      calc
        1 / (a 0) ^ 2 + 2 * C * ((n + 1 : ℕ) : ℝ) =
            (1 / (a 0) ^ 2 + 2 * C * (n : ℝ)) + 2 * C := by
          push_cast
          ring
        _ ≤ 1 / (a n) ^ 2 + 2 * C := add_le_add_right ih _
        _ ≤ 1 / (a (n + 1)) ^ 2 := by
          simpa [hrec n] using hstep

end RHLean.Analysis
