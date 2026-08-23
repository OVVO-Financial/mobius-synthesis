import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import RHLean.Analysis.K2RecipMomentBoundaryScratch

noncomputable section

open Filter Set Topology
open scoped ArithmeticFunction.Moebius

namespace RHLean.Analysis

private def k2LogRecipRealTwo (x : ℝ) : ℝ :=
  (Real.log x) ^ 2 / x

private theorem k2LogRecipRealTwo_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt k2LogRecipRealTwo
      ((2 * Real.log x - (Real.log x) ^ 2) / x ^ 2) x := by
  have h := ((Real.hasDerivAt_log hx).pow 2).div (hasDerivAt_id x) hx
  convert h using 1
  field_simp [hx]
  simp
  ring

/-- Adjacent order-two reciprocal-log weights differ by at most the natural
`log^2(n) / n^2` derivative scale. -/
theorem k2LogRecipWeight_two_diff_abs_le
    (n : ℕ) (hn : 3 ≤ n) :
    |k2LogRecipWeight 2 n - k2LogRecipWeight 2 (n + 1)| ≤
      8 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ 2 := by
  let a : ℝ := n
  let b : ℝ := n + 1
  let C : ℝ := 8 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ 2
  have ha3 : (3 : ℝ) ≤ a := by
    dsimp [a]
    exact_mod_cast hn
  have ha0 : 0 < a := by linarith
  have halog : 1 < Real.log a := logt_gt_one ha3
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hb_le_sq : b ≤ a ^ 2 := by
    dsimp [a, b]
    have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hlog_sq : Real.log (a ^ 2) = 2 * Real.log a := by
    rw [Real.log_pow]
    norm_num
  have hf : ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt k2LogRecipRealTwo
        ((2 * Real.log x - (Real.log x) ^ 2) / x ^ 2)
        (Set.Icc a b) x := by
    intro x hx
    have hx0 : 0 < x := ha0.trans_le hx.1
    exact (k2LogRecipRealTwo_hasDerivAt hx0.ne').hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico a b,
      ‖(2 * Real.log x - (Real.log x) ^ 2) / x ^ 2‖ ≤ C := by
    intro x hx
    have hx0 : 0 < x := ha0.trans_le hx.1
    have hloga0 : 0 ≤ Real.log a := le_trans zero_le_one halog.le
    have hx3 : (3 : ℝ) ≤ x := ha3.trans hx.1
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hx_le_sq : x ≤ a ^ 2 := hx.2.le.trans hb_le_sq
    have hlogx_le : Real.log x ≤ 2 * Real.log a := by
      calc
        Real.log x ≤ Real.log (a ^ 2) := Real.log_le_log hx0 hx_le_sq
        _ = 2 * Real.log a := hlog_sq
    have hnum : |2 * Real.log x - (Real.log x) ^ 2| ≤
        8 * (Real.log a) ^ 2 := by
      calc
        |2 * Real.log x - (Real.log x) ^ 2| =
            |2 * Real.log x + (-(Real.log x) ^ 2)| := by ring_nf
        _ ≤ |2 * Real.log x| + |-(Real.log x) ^ 2| := abs_add_le _ _
        _ = 2 * Real.log x + (Real.log x) ^ 2 := by
          rw [abs_of_nonneg (by positivity), abs_neg,
            abs_of_nonneg (sq_nonneg _)]
        _ ≤ 8 * (Real.log a) ^ 2 := by
          nlinarith [sq_nonneg (Real.log x), sq_nonneg (Real.log a)]
    have hsq : a ^ 2 ≤ x ^ 2 :=
      pow_le_pow_left₀ ha0.le hx.1 2
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hx0)]
    dsimp [C]
    calc
      |2 * Real.log x - (Real.log x) ^ 2| / x ^ 2
          ≤ (8 * (Real.log a) ^ 2) / x ^ 2 := by gcongr
      _ ≤ (8 * (Real.log a) ^ 2) / a ^ 2 := by
        apply div_le_div_of_nonneg_left
        · positivity
        · positivity
        · exact hsq
      _ = 8 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ 2 := by rfl
  have hseg := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := k2LogRecipRealTwo) (a := a) (b := b)
    (f' := fun x => (2 * Real.log x - (Real.log x) ^ 2) / x ^ 2)
    (C := C) hf hbound b (right_mem_Icc.mpr hab)
  have hba : b - a = 1 := by
    dsimp [a, b]
    ring
  rw [hba, mul_one] at hseg
  rw [abs_sub_comm]
  simpa [k2LogRecipRealTwo, k2LogRecipWeight, a, b, C] using hseg

private def k2LogRecipRealThree (x : ℝ) : ℝ :=
  (Real.log x) ^ 3 / x

private theorem k2LogRecipRealThree_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt k2LogRecipRealThree
      ((3 * (Real.log x) ^ 2 - (Real.log x) ^ 3) / x ^ 2) x := by
  have h := ((Real.hasDerivAt_log hx).pow 3).div (hasDerivAt_id x) hx
  convert h using 1
  field_simp [hx]
  simp
  ring

/-- Adjacent order-three reciprocal-log weights differ by at most the natural
`log^3(n) / n^2` derivative scale. -/
theorem k2LogRecipWeight_three_diff_abs_le
    (n : ℕ) (hn : 3 ≤ n) :
    |k2LogRecipWeight 3 n - k2LogRecipWeight 3 (n + 1)| ≤
      24 * (Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ 2 := by
  let a : ℝ := n
  let b : ℝ := n + 1
  let C : ℝ := 24 * (Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ 2
  have ha3 : (3 : ℝ) ≤ a := by
    dsimp [a]
    exact_mod_cast hn
  have ha0 : 0 < a := by linarith
  have halog : 1 < Real.log a := logt_gt_one ha3
  have hloga0 : 0 ≤ Real.log a := le_trans zero_le_one halog.le
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hb_le_sq : b ≤ a ^ 2 := by
    dsimp [a, b]
    have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hlog_sq : Real.log (a ^ 2) = 2 * Real.log a := by
    rw [Real.log_pow]
    norm_num
  have hf : ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt k2LogRecipRealThree
        ((3 * (Real.log x) ^ 2 - (Real.log x) ^ 3) / x ^ 2)
        (Set.Icc a b) x := by
    intro x hx
    have hx0 : 0 < x := ha0.trans_le hx.1
    exact (k2LogRecipRealThree_hasDerivAt hx0.ne').hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico a b,
      ‖(3 * (Real.log x) ^ 2 - (Real.log x) ^ 3) / x ^ 2‖ ≤ C := by
    intro x hx
    have hx0 : 0 < x := ha0.trans_le hx.1
    have hx1 : (1 : ℝ) ≤ x :=
      (by norm_num : (1 : ℝ) ≤ 3).trans (ha3.trans hx.1)
    have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hx_le_sq : x ≤ a ^ 2 := hx.2.le.trans hb_le_sq
    have hlogx_le : Real.log x ≤ 2 * Real.log a := by
      calc
        Real.log x ≤ Real.log (a ^ 2) := Real.log_le_log hx0 hx_le_sq
        _ = 2 * Real.log a := hlog_sq
    have hpow2 : (Real.log x) ^ 2 ≤ (2 * Real.log a) ^ 2 :=
      pow_le_pow_left₀ hlogx0 hlogx_le 2
    have hpow3 : (Real.log x) ^ 3 ≤ (2 * Real.log a) ^ 3 :=
      pow_le_pow_left₀ hlogx0 hlogx_le 3
    have hloga_sq_le_cube : (Real.log a) ^ 2 ≤ (Real.log a) ^ 3 := by
      have hnonneg : 0 ≤ (Real.log a) ^ 2 * (Real.log a - 1) :=
        mul_nonneg (sq_nonneg _) (sub_nonneg.mpr halog.le)
      nlinarith
    have hnum : |3 * (Real.log x) ^ 2 - (Real.log x) ^ 3| ≤
        24 * (Real.log a) ^ 3 := by
      calc
        |3 * (Real.log x) ^ 2 - (Real.log x) ^ 3| =
            |3 * (Real.log x) ^ 2 + (-(Real.log x) ^ 3)| := by ring_nf
        _ ≤ |3 * Real.log x ^ 2| + |-(Real.log x) ^ 3| := abs_add_le _ _
        _ = 3 * (Real.log x) ^ 2 + (Real.log x) ^ 3 := by
          rw [abs_of_nonneg (by positivity), abs_neg,
            abs_of_nonneg (pow_nonneg hlogx0 3)]
        _ ≤ 3 * (2 * Real.log a) ^ 2 + (2 * Real.log a) ^ 3 := by
          gcongr
        _ = 12 * (Real.log a) ^ 2 + 8 * (Real.log a) ^ 3 := by ring
        _ ≤ 24 * (Real.log a) ^ 3 := by
          have hcub : 0 ≤ (Real.log a) ^ 3 := pow_nonneg hloga0 3
          linarith [hloga_sq_le_cube]
    have hsq : a ^ 2 ≤ x ^ 2 :=
      pow_le_pow_left₀ ha0.le hx.1 2
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hx0)]
    dsimp [C]
    calc
      |3 * (Real.log x) ^ 2 - (Real.log x) ^ 3| / x ^ 2
          ≤ (24 * (Real.log a) ^ 3) / x ^ 2 := by gcongr
      _ ≤ (24 * (Real.log a) ^ 3) / a ^ 2 := by
        apply div_le_div_of_nonneg_left
        · positivity
        · positivity
        · exact hsq
      _ = 24 * (Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ 2 := by rfl
  have hseg := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := k2LogRecipRealThree) (a := a) (b := b)
    (f' := fun x => (3 * (Real.log x) ^ 2 - (Real.log x) ^ 3) / x ^ 2)
    (C := C) hf hbound b (right_mem_Icc.mpr hab)
  have hba : b - a = 1 := by
    dsimp [a, b]
    ring
  rw [hba, mul_one] at hseg
  rw [abs_sub_comm]
  simpa [k2LogRecipRealThree, k2LogRecipWeight, a, b, C] using hseg

end RHLean.Analysis
