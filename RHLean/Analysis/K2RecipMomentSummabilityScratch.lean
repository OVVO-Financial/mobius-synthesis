import RHLean.Analysis.K2RecipMomentWeightScratch

noncomputable section

open Filter Set Topology
open scoped ArithmeticFunction.Moebius

namespace RHLean.Analysis

/-- Strong Mertens makes the order-two Abel increments absolutely summable. -/
theorem k2MertensAbelTerm_two_summable :
    Summable (k2MertensAbelTerm 2) := by
  obtain ⟨c, C, hc, hC, hM⟩ := strongNativeMertensSubexp
  let g : ℕ → ℝ := fun N =>
    8 * C * (1 / ((N : ℝ) * (Real.log (N : ℝ)) ^ 3))
  have hbase : Summable (fun N : ℕ =>
      1 / ((N : ℝ) * (Real.log (N : ℝ)) ^ 3)) := by
    rw [← summable_nat_add_iff 3 (G := ℝ)]
    exact (k2LogHarmonicTail_summable (p := 3) (by norm_num)).congr fun n => by
      simp [k2LogHarmonicTail, one_div, mul_inv_rev]
  have hg : Summable g := by
    exact hbase.mul_left (8 * C)
  have hpowNat :
      ∀ᶠ N : ℕ in atTop,
        strongMertensScale (N : ℝ) ^ 50 ≤
          Real.exp (c * strongMertensScale (N : ℝ)) :=
    tendsto_natCast_atTop_atTop.eventually
      (strongMertens_scale_pow_le_exp_eventually 50 hc)
  apply Summable.of_norm_bounded_eventually_nat hg
  filter_upwards [eventually_ge_atTop 3, hpowNat] with N hN hpow
  have hNposNat : 0 < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNposNat
  have hL : 1 < Real.log (N : ℝ) := logt_gt_one (by exact_mod_cast hN : (3 : ℝ) ≤ N)
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  let r := strongMertensScale (N : ℝ)
  have hr50 : (Real.log (N : ℝ)) ^ 5 = r ^ 50 := by
    have hs := strongMertensScale_pow_ten (X := (N : ℝ)) hN1
    dsimp [r]
    rw [← hs]
    ring
  have hdecay5 :
      Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 5 ≤ 1 := by
    rw [hr50]
    calc
      Real.exp (-c * r) * r ^ 50
          ≤ Real.exp (-c * r) * Real.exp (c * r) :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
  have hdecay2 :
      Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 2 ≤
        1 / (Real.log (N : ℝ)) ^ 3 := by
    rw [le_div_iff₀ (pow_pos hLpos 3)]
    calc
      Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 2 *
          (Real.log (N : ℝ)) ^ 3
          = Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 5 := by ring
      _ ≤ 1 := hdecay5
  have hweight := k2LogRecipWeight_two_diff_abs_le N hN
  rw [Real.norm_eq_abs, k2MertensAbelTerm, abs_mul]
  calc
    |nativeMertensSummatory N| *
        |k2LogRecipWeight 2 N - k2LogRecipWeight 2 (N + 1)|
      ≤ (C * (N : ℝ) * Real.exp (-c * r)) *
          |k2LogRecipWeight 2 N - k2LogRecipWeight 2 (N + 1)| := by
        apply mul_le_mul_of_nonneg_right
        · simpa [r, strongMertensScale, one_div] using hM N hN
        · exact abs_nonneg _
    _ ≤ (C * (N : ℝ) * Real.exp (-c * r)) *
          (8 * (Real.log (N : ℝ)) ^ 2 / (N : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left hweight
        positivity
    _ = (8 * C / (N : ℝ)) *
          (Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 2) := by
        field_simp [ne_of_gt hNpos]
    _ ≤ (8 * C / (N : ℝ)) *
          (1 / (Real.log (N : ℝ)) ^ 3) := by
        apply mul_le_mul_of_nonneg_left hdecay2
        positivity
    _ = g N := by
        dsimp [g]
        field_simp [ne_of_gt hNpos]

/-- Strong Mertens makes the order-three Abel increments absolutely summable. -/
theorem k2MertensAbelTerm_three_summable :
    Summable (k2MertensAbelTerm 3) := by
  obtain ⟨c, C, hc, hC, hM⟩ := strongNativeMertensSubexp
  let g : ℕ → ℝ := fun N =>
    24 * C * (1 / ((N : ℝ) * (Real.log (N : ℝ)) ^ 3))
  have hbase : Summable (fun N : ℕ =>
      1 / ((N : ℝ) * (Real.log (N : ℝ)) ^ 3)) := by
    rw [← summable_nat_add_iff 3 (G := ℝ)]
    exact (k2LogHarmonicTail_summable (p := 3) (by norm_num)).congr fun n => by
      simp [k2LogHarmonicTail, one_div, mul_inv_rev]
  have hg : Summable g := by
    exact hbase.mul_left (24 * C)
  have hpowNat :
      ∀ᶠ N : ℕ in atTop,
        strongMertensScale (N : ℝ) ^ 60 ≤
          Real.exp (c * strongMertensScale (N : ℝ)) :=
    tendsto_natCast_atTop_atTop.eventually
      (strongMertens_scale_pow_le_exp_eventually 60 hc)
  apply Summable.of_norm_bounded_eventually_nat hg
  filter_upwards [eventually_ge_atTop 3, hpowNat] with N hN hpow
  have hNposNat : 0 < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNposNat
  have hL : 1 < Real.log (N : ℝ) := logt_gt_one (by exact_mod_cast hN : (3 : ℝ) ≤ N)
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  let r := strongMertensScale (N : ℝ)
  have hr60 : (Real.log (N : ℝ)) ^ 6 = r ^ 60 := by
    have hs := strongMertensScale_pow_ten (X := (N : ℝ)) hN1
    dsimp [r]
    rw [← hs]
    ring
  have hdecay6 :
      Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 6 ≤ 1 := by
    rw [hr60]
    calc
      Real.exp (-c * r) * r ^ 60
          ≤ Real.exp (-c * r) * Real.exp (c * r) :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
  have hdecay3 :
      Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 3 ≤
        1 / (Real.log (N : ℝ)) ^ 3 := by
    rw [le_div_iff₀ (pow_pos hLpos 3)]
    calc
      Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 3 *
          (Real.log (N : ℝ)) ^ 3
          = Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 6 := by ring
      _ ≤ 1 := hdecay6
  have hweight := k2LogRecipWeight_three_diff_abs_le N hN
  rw [Real.norm_eq_abs, k2MertensAbelTerm, abs_mul]
  calc
    |nativeMertensSummatory N| *
        |k2LogRecipWeight 3 N - k2LogRecipWeight 3 (N + 1)|
      ≤ (C * (N : ℝ) * Real.exp (-c * r)) *
          |k2LogRecipWeight 3 N - k2LogRecipWeight 3 (N + 1)| := by
        apply mul_le_mul_of_nonneg_right
        · simpa [r, strongMertensScale, one_div] using hM N hN
        · exact abs_nonneg _
    _ ≤ (C * (N : ℝ) * Real.exp (-c * r)) *
          (24 * (Real.log (N : ℝ)) ^ 3 / (N : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left hweight
        positivity
    _ = (24 * C / (N : ℝ)) *
          (Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 3) := by
        field_simp [ne_of_gt hNpos]
    _ ≤ (24 * C / (N : ℝ)) *
          (1 / (Real.log (N : ℝ)) ^ 3) := by
        apply mul_le_mul_of_nonneg_left hdecay3
        positivity
    _ = g N := by
        dsimp [g]
        field_simp [ne_of_gt hNpos]

end RHLean.Analysis
