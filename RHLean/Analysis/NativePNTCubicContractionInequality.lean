import Mathlib
import RHLean.Analysis.NativePNTReciprocalSquareCore

noncomputable section

namespace RHLean.Analysis

theorem inv_sq_rate_of_cubic_contraction_inequality
    (a : Nat -> Real) (C : Real)
    (hC : 0 <= C)
    (hpos : forall n, 0 < a n)
    (hrec : forall n, a (n + 1) <= a n - C * (a n) ^ 3) :
    forall n : Nat,
      1 / (a 0) ^ 2 + 2 * C * (n : Real) <= 1 / (a n) ^ 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hcubic : 0 < a n - C * (a n) ^ 3 :=
        lt_of_lt_of_le (hpos (n + 1)) (hrec n)
      have hstep := inv_sq_add_two_mul_le_inv_sq_cubic_step
        (a n) C (hpos n) hC hcubic
      have hsquare :
          (a (n + 1)) ^ 2 <= (a n - C * (a n) ^ 3) ^ 2 := by
        nlinarith [hpos (n + 1), hcubic, hrec n]
      have hinv :
          1 / (a n - C * (a n) ^ 3) ^ 2 <=
            1 / (a (n + 1)) ^ 2 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hcubic)
          (sq_pos_of_pos (hpos (n + 1)))).2
        simpa using hsquare
      calc
        1 / (a 0) ^ 2 + 2 * C * ((n + 1 : Nat) : Real) =
            (1 / (a 0) ^ 2 + 2 * C * (n : Real)) + 2 * C := by
          push_cast
          ring
        _ <= 1 / (a n) ^ 2 + 2 * C := add_le_add_right ih _
        _ <= 1 / (a n - C * (a n) ^ 3) ^ 2 := hstep
        _ <= 1 / (a (n + 1)) ^ 2 := hinv

theorem cubic_contraction_inequality_quadratic_rate
    (a : Nat -> Real) (C : Real)
    (hC : 0 <= C)
    (hpos : forall n, 0 < a n)
    (hrec : forall n, a (n + 1) <= a n - C * (a n) ^ 3)
    (n : Nat) :
    2 * C * (n : Real) * (a n) ^ 2 <= 1 := by
  have hinv := inv_sq_rate_of_cubic_contraction_inequality
    a C hC hpos hrec n
  have hbase : 0 <= 1 / (a 0) ^ 2 := by positivity
  have hdrop : 2 * C * (n : Real) <= 1 / (a n) ^ 2 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hdrop (sq_nonneg (a n))
  calc
    2 * C * (n : Real) * (a n) ^ 2 <=
        (1 / (a n) ^ 2) * (a n) ^ 2 := by
      simpa [mul_assoc] using hmul
    _ = 1 := by
      field_simp [ne_of_gt (hpos n)]

theorem cubic_contraction_inequality_le_eta_of_budget
    (a : Nat -> Real) (C eta : Real)
    (hC : 0 <= C) (heta : 0 < eta)
    (hpos : forall n, 0 < a n)
    (hrec : forall n, a (n + 1) <= a n - C * (a n) ^ 3)
    (n : Nat)
    (hbudget : 1 < 2 * C * (n : Real) * eta ^ 2) :
    a n <= eta := by
  have hrate := cubic_contraction_inequality_quadratic_rate
    a C hC hpos hrec n
  by_contra hnot
  have hetaSlope : eta < a n := lt_of_not_ge hnot
  have hsq : eta ^ 2 <= (a n) ^ 2 :=
    pow_le_pow_left₀ heta.le hetaSlope.le 2
  have hcoef0 : 0 <= 2 * C * (n : Real) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hC) (by positivity)
  have hmul :
      2 * C * (n : Real) * eta ^ 2 <=
        2 * C * (n : Real) * (a n) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hcoef0
  have hone : 1 < 2 * C * (n : Real) * (a n) ^ 2 :=
    hbudget.trans_le hmul
  linarith

end RHLean.Analysis
