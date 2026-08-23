import Mathlib
import RHLean.Analysis.PrimeSieveAffineExcursion
import RHLean.Analysis.PrimeSieveBackwardAffineExcursion
import RHLean.Analysis.PrimeSieveFiniteDifferenceModulus
import RHLean.Arithmetic.MobiusFiniteDifferenceIdentification

/-!
# Sharp Abel-face modulus through the finite-difference fibers at the pin

The backward affine modulus of the Abel-face discrepancy sum holds at the
canonical pin because the pin is support-stable: a backward step of size
`t ≤ y` does not move the quotient support level `x / (y + 1)`.  This module
transports that modulus through the finite Möbius difference operator.

The key arithmetic fact is that support stability survives every divisor
fiber: `pin / d` and `(pin - t) / d` sit at the same support level for every
`d`.  The sharp one-window modulus can therefore be applied once per fiber,
at the fiber's own (smaller) support level, and the slope/intercept
monotonicity in the support index rounds every fiber constant up to the pin
constants `A = primeSieveAffineSlope y y`, `B = primeSieveAffineIntercept y y`.

The headline bound charges the intercept only on moving fibers.  The
`2^|S|` relaxation is recorded as a worst-case audit figure only: for
`S = primesUpTo y` it is analytically useless, and no growing-wheel claim is
made anywhere in this module.  Everything here is bookkeeping; no estimate
on the frontier objects is asserted.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-! ## Monotonicity of the affine constants in the support index -/

/-- The harmonic weight is monotone in the truncation index. -/
theorem harmonicWeight_mono {K K' : ℕ} (h : K ≤ K') :
    harmonicWeight K ≤ harmonicWeight K' := by
  unfold harmonicWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right h)
  intro d _ _
  positivity

/-- The affine slope is monotone in the support index. -/
theorem primeSieveAffineSlope_mono (y : ℕ) (hy : 1 ≤ y) {K K' : ℕ}
    (h : K ≤ K') :
    primeSieveAffineSlope y K ≤ primeSieveAffineSlope y K' := by
  have hy' : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlog : 0 < Real.log ((y : ℝ) + 1) := Real.log_pos (by linarith)
  have hinv : (0 : ℝ) ≤ (Real.log ((y : ℝ) + 1))⁻¹ := (inv_pos.mpr hlog).le
  unfold primeSieveAffineSlope
  simp only [div_eq_mul_inv]
  have := mul_le_mul_of_nonneg_right (harmonicWeight_mono h) hinv
  linarith

/-- The affine intercept is monotone in the support index. -/
theorem primeSieveAffineIntercept_mono (y : ℕ) (hy : 1 ≤ y) {K K' : ℕ}
    (h : K ≤ K') :
    primeSieveAffineIntercept y K ≤ primeSieveAffineIntercept y K' := by
  have hy' : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlog : 0 < Real.log ((y : ℝ) + 1) := Real.log_pos (by linarith)
  have hinv : (0 : ℝ) ≤ (Real.log ((y : ℝ) + 1))⁻¹ := (inv_pos.mpr hlog).le
  unfold primeSieveAffineIntercept
  simp only [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) hinv

/-! ## Support stability of the pin on every divisor fiber -/

/-- **Pin divisor stability.**  A backward step of size `t ≤ y` at the
canonical pin does not move the support level of any divisor fiber.  Both
sides equal `y / d`; the statement is unconditional in `d` (at `d = 0` both
sides vanish). -/
theorem primeSieveCanonicalPin_divisor_backward_stable
    (y t d : ℕ) (ht : t ≤ y) :
    primeSieveCanonicalPin y / d / (y + 1) =
      (primeSieveCanonicalPin y - t) / d / (y + 1) := by
  calc primeSieveCanonicalPin y / d / (y + 1)
      = primeSieveCanonicalPin y / (d * (y + 1)) :=
        Nat.div_div_eq_div_mul _ _ _
    _ = primeSieveCanonicalPin y / ((y + 1) * d) := by
        rw [Nat.mul_comm d (y + 1)]
    _ = primeSieveCanonicalPin y / (y + 1) / d :=
        (Nat.div_div_eq_div_mul _ _ _).symm
    _ = y / d := by rw [primeSieveCanonicalPin_div]
    _ = (primeSieveCanonicalPin y - t) / (y + 1) / d := by
        rw [primeSieveCanonicalPin_backward_stable y t ht]
    _ = (primeSieveCanonicalPin y - t) / ((y + 1) * d) :=
        Nat.div_div_eq_div_mul _ _ _
    _ = (primeSieveCanonicalPin y - t) / (d * (y + 1)) := by
        rw [Nat.mul_comm (y + 1) d]
    _ = (primeSieveCanonicalPin y - t) / d / (y + 1) :=
        (Nat.div_div_eq_div_mul _ _ _).symm

/-- **Fiberwise sharp modulus at the pin.**  On each divisor fiber, the
backward increment of the Abel-face discrepancy sum obeys the affine modulus
with the pin constants, via slope/intercept monotonicity from the fiber's
own support level. -/
theorem primeSieveMoebiusDiscrepancySum_fiber_backward_increment_norm_le
    (y t d : ℕ) (hy : 1 ≤ y) (ht : t ≤ y) :
    ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y / d) -
        primeSieveMoebiusDiscrepancySum y
          ((primeSieveCanonicalPin y - t) / d)‖
      ≤ primeSieveAffineSlope y y *
          (((primeSieveCanonicalPin y / d -
            (primeSieveCanonicalPin y - t) / d : ℕ)) : ℝ)
        + primeSieveAffineIntercept y y := by
  have hab : (primeSieveCanonicalPin y - t) / d ≤
      primeSieveCanonicalPin y / d :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have hsum : (primeSieveCanonicalPin y - t) / d +
      (primeSieveCanonicalPin y / d - (primeSieveCanonicalPin y - t) / d) =
        primeSieveCanonicalPin y / d :=
    Nat.add_sub_cancel' hab
  have hsq : (primeSieveCanonicalPin y - t) / d +
      (primeSieveCanonicalPin y / d - (primeSieveCanonicalPin y - t) / d) <
        (y + 1) ^ 2 := by
    rw [hsum]
    exact lt_of_le_of_lt (Nat.div_le_self _ _)
      (primeSieveCanonicalPin_lt_sq y)
  have hsupp : ((primeSieveCanonicalPin y - t) / d +
      (primeSieveCanonicalPin y / d - (primeSieveCanonicalPin y - t) / d)) /
        (y + 1) = ((primeSieveCanonicalPin y - t) / d) / (y + 1) := by
    rw [hsum]
    exact primeSieveCanonicalPin_divisor_backward_stable y t d ht
  have hmain := primeSieveMoebiusDiscrepancySum_increment_norm_le_affine
    y ((primeSieveCanonicalPin y - t) / d)
    (primeSieveCanonicalPin y / d - (primeSieveCanonicalPin y - t) / d)
    hy hsq hsupp
  rw [hsum] at hmain
  have hlev : ((primeSieveCanonicalPin y - t) / d) / (y + 1) ≤ y := by
    have haP : (primeSieveCanonicalPin y - t) / d ≤
        primeSieveCanonicalPin y :=
      le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
    calc ((primeSieveCanonicalPin y - t) / d) / (y + 1)
        ≤ primeSieveCanonicalPin y / (y + 1) :=
          Nat.div_le_div_right haP
      _ = y := primeSieveCanonicalPin_div y
  have hslope := primeSieveAffineSlope_mono y hy hlev
  have hicpt := primeSieveAffineIntercept_mono y hy hlev
  have hδ : (0 : ℝ) ≤
      (((primeSieveCanonicalPin y / d -
        (primeSieveCanonicalPin y - t) / d : ℕ)) : ℝ) :=
    Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hslope hδ
  linarith

/-! ## The transported modulus -/

/-- **Sharp Abel-face modulus through the fibers at the canonical pin.**
The intercept is charged only on moving fibers; the displacement sum is
bounded by the Euler reciprocal product of the wheel.  Bookkeeping only. -/
theorem primeSieveFiniteDifference_backward_increment_norm_le_active
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (y t : ℕ) (hy : 1 ≤ y) (ht : t ≤ y) :
    ‖finiteDifferenceOperator S (primeSieveMoebiusDiscrepancySum y)
          (primeSieveCanonicalPin y) -
        finiteDifferenceOperator S (primeSieveMoebiusDiscrepancySum y)
          (primeSieveCanonicalPin y - t)‖
      ≤ primeSieveAffineSlope y y * (t : ℝ) *
          (∏ p ∈ S, (1 + ((p : ℝ))⁻¹))
        + (primeSieveAffineSlope y y + primeSieveAffineIntercept y y) *
          (((primorial S).divisors.filter (fun d =>
              (primeSieveCanonicalPin y - t) / d <
                primeSieveCanonicalPin y / d)).card : ℝ) := by
  classical
  have hA : (0 : ℝ) ≤ primeSieveAffineSlope y y :=
    (primeSieveAffineSlope_pos y y hy).le
  have hB : (0 : ℝ) ≤ primeSieveAffineIntercept y y :=
    primeSieveAffineIntercept_nonneg y y hy
  rw [finiteDifferenceOperator_apply, finiteDifferenceOperator_apply,
    ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ d ∈ (primorial S).divisors,
      ‖(((μ d : ℤ) : ℂ)) *
          primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y / d) -
        (((μ d : ℤ) : ℂ)) *
          primeSieveMoebiusDiscrepancySum y
            ((primeSieveCanonicalPin y - t) / d)‖ ≤
        primeSieveAffineSlope y y *
          (((primeSieveCanonicalPin y / d -
            (primeSieveCanonicalPin y - t) / d : ℕ)) : ℝ) +
        primeSieveAffineIntercept y y *
          (if (primeSieveCanonicalPin y - t) / d <
              primeSieveCanonicalPin y / d then (1 : ℝ) else 0) := by
    intro d _
    rw [← mul_sub, norm_mul]
    by_cases hmove : (primeSieveCanonicalPin y - t) / d <
        primeSieveCanonicalPin y / d
    · rw [if_pos hmove]
      have hstep :=
        primeSieveMoebiusDiscrepancySum_fiber_backward_increment_norm_le
          y t d hy ht
      calc ‖((μ d : ℤ) : ℂ)‖ *
            ‖primeSieveMoebiusDiscrepancySum y
                (primeSieveCanonicalPin y / d) -
              primeSieveMoebiusDiscrepancySum y
                ((primeSieveCanonicalPin y - t) / d)‖
          ≤ 1 * (primeSieveAffineSlope y y *
              (((primeSieveCanonicalPin y / d -
                (primeSieveCanonicalPin y - t) / d : ℕ)) : ℝ) +
              primeSieveAffineIntercept y y) :=
            mul_le_mul (norm_moebius_le_one d) hstep (norm_nonneg _)
              zero_le_one
        _ = primeSieveAffineSlope y y *
              (((primeSieveCanonicalPin y / d -
                (primeSieveCanonicalPin y - t) / d : ℕ)) : ℝ) +
              primeSieveAffineIntercept y y * 1 := by ring
    · have hle : (primeSieveCanonicalPin y - t) / d ≤
          primeSieveCanonicalPin y / d :=
        Nat.div_le_div_right (Nat.sub_le _ _)
      have heq : primeSieveCanonicalPin y / d =
          (primeSieveCanonicalPin y - t) / d := by omega
      have hδ0 : (primeSieveCanonicalPin y / d -
          (primeSieveCanonicalPin y - t) / d : ℕ) = 0 := by omega
      rw [if_neg hmove, hδ0, heq, sub_self, norm_zero, mul_zero]
      simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_boole]
  have hδsum : ∑ d ∈ (primorial S).divisors,
      (((primeSieveCanonicalPin y / d -
        (primeSieveCanonicalPin y - t) / d : ℕ)) : ℝ) ≤
      (t : ℝ) * (∏ p ∈ S, (1 + ((p : ℝ))⁻¹)) +
        (((primorial S).divisors.filter (fun d =>
            (primeSieveCanonicalPin y - t) / d <
              primeSieveCanonicalPin y / d)).card : ℝ) := by
    have hper : ∀ d ∈ (primorial S).divisors,
        (((primeSieveCanonicalPin y / d -
          (primeSieveCanonicalPin y - t) / d : ℕ)) : ℝ) ≤
          (t : ℝ) * ((d : ℝ))⁻¹ +
            (if (primeSieveCanonicalPin y - t) / d <
                primeSieveCanonicalPin y / d then (1 : ℝ) else 0) := by
      intro d hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      by_cases hmove : (primeSieveCanonicalPin y - t) / d <
          primeSieveCanonicalPin y / d
      · rw [if_pos hmove]
        have htP : t ≤ primeSieveCanonicalPin y :=
          le_trans ht (le_primeSieveCanonicalPin y)
        have hcancel : primeSieveCanonicalPin y - t + t =
            primeSieveCanonicalPin y := Nat.sub_add_cancel htP
        have hfloor := floor_add_div_sub_le
          (primeSieveCanonicalPin y - t) t d hd0
        rw [hcancel] at hfloor
        have hcast : (((primeSieveCanonicalPin y / d -
            (primeSieveCanonicalPin y - t) / d : ℕ)) : ℝ) ≤
            ((t / d : ℕ) : ℝ) + 1 := by exact_mod_cast hfloor
        have hdivle : ((t / d : ℕ) : ℝ) ≤ (t : ℝ) / (d : ℝ) :=
          Nat.cast_div_le
        have hdinv : (t : ℝ) / (d : ℝ) = (t : ℝ) * ((d : ℝ))⁻¹ :=
          div_eq_mul_inv _ _
        linarith
      · have hle : (primeSieveCanonicalPin y - t) / d ≤
            primeSieveCanonicalPin y / d :=
          Nat.div_le_div_right (Nat.sub_le _ _)
        have hδ0 : (primeSieveCanonicalPin y / d -
            (primeSieveCanonicalPin y - t) / d : ℕ) = 0 := by omega
        rw [if_neg hmove, hδ0]
        simp only [Nat.cast_zero, add_zero]
        positivity
    calc ∑ d ∈ (primorial S).divisors,
        (((primeSieveCanonicalPin y / d -
          (primeSieveCanonicalPin y - t) / d : ℕ)) : ℝ)
        ≤ ∑ d ∈ (primorial S).divisors,
            ((t : ℝ) * ((d : ℝ))⁻¹ +
              (if (primeSieveCanonicalPin y - t) / d <
                  primeSieveCanonicalPin y / d then (1 : ℝ) else 0)) :=
          Finset.sum_le_sum hper
      _ = (t : ℝ) * (∑ d ∈ (primorial S).divisors, ((d : ℝ))⁻¹) +
            (((primorial S).divisors.filter (fun d =>
                (primeSieveCanonicalPin y - t) / d <
                  primeSieveCanonicalPin y / d)).card : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]
      _ = (t : ℝ) * (∏ p ∈ S, (1 + ((p : ℝ))⁻¹)) +
            (((primorial S).divisors.filter (fun d =>
                (primeSieveCanonicalPin y - t) / d <
                  primeSieveCanonicalPin y / d)).card : ℝ) := by
          rw [sum_inv_divisors_primorial S hprime]
  have hmulA := mul_le_mul_of_nonneg_left hδsum hA
  nlinarith [hmulA]

/-- **Worst-case audit figure only.**  The moving-fiber count never exceeds
the full face count `2^|S|` of the wheel.  For `S = primesUpTo y` this bound
is analytically useless; it is recorded to make the exponential worst case
explicit, not as progress on any estimate. -/
theorem primeSieveFiniteDifference_backward_increment_norm_le_euler
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (y t : ℕ) (hy : 1 ≤ y) (ht : t ≤ y) :
    ‖finiteDifferenceOperator S (primeSieveMoebiusDiscrepancySum y)
          (primeSieveCanonicalPin y) -
        finiteDifferenceOperator S (primeSieveMoebiusDiscrepancySum y)
          (primeSieveCanonicalPin y - t)‖
      ≤ primeSieveAffineSlope y y * (t : ℝ) *
          (∏ p ∈ S, (1 + ((p : ℝ))⁻¹))
        + (primeSieveAffineSlope y y + primeSieveAffineIntercept y y) *
          ((2 : ℝ) ^ S.card) := by
  have hA : (0 : ℝ) ≤ primeSieveAffineSlope y y :=
    (primeSieveAffineSlope_pos y y hy).le
  have hB : (0 : ℝ) ≤ primeSieveAffineIntercept y y :=
    primeSieveAffineIntercept_nonneg y y hy
  have hcard : (((primorial S).divisors.filter (fun d =>
      (primeSieveCanonicalPin y - t) / d <
        primeSieveCanonicalPin y / d)).card : ℝ) ≤ (2 : ℝ) ^ S.card := by
    have h1 : ((primorial S).divisors.filter (fun d =>
        (primeSieveCanonicalPin y - t) / d <
          primeSieveCanonicalPin y / d)).card ≤
        (primorial S).divisors.card :=
      Finset.card_filter_le _ _
    have h2 := card_divisors_primorial S hprime
    have : ((primorial S).divisors.filter (fun d =>
        (primeSieveCanonicalPin y - t) / d <
          primeSieveCanonicalPin y / d)).card ≤ 2 ^ S.card := by omega
    exact_mod_cast this
  have hmain := primeSieveFiniteDifference_backward_increment_norm_le_active
    S hprime y t hy ht
  have hmul := mul_le_mul_of_nonneg_left hcard (by linarith : (0 : ℝ) ≤
    primeSieveAffineSlope y y + primeSieveAffineIntercept y y)
  linarith

end RHLean.Analysis

end
