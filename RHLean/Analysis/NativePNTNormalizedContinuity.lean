import Mathlib
import RHLean.Analysis.NativePNTNormalizedSignedRecurrence

/-!
# Multiplicative continuity of the normalized PNT error

The scale-free signed Selberg recurrence becomes quantitative only if a large
normalized error cannot disappear instantly on a nearby multiplicative scale.
The existing local Selberg increment estimate already gives exactly this
regularity.  This module records it directly for

`e(N) = nativePNTError N / N`.

On a factor-two interval `A <= B <= 2 A`, the normalized error changes by at
most an absolute multiple of the relative gap plus `O(1 / log A)`.  No affine
intercept and no eventual threshold are introduced.
-/

noncomputable section

namespace RHLean.Analysis

/-- Forward one-sided normalized continuity.  Increasing `psi` and the local
Selberg increment estimate control the upward change of normalized error. -/
theorem nativePNTNormalizedError_sub_le_of_factor_two
    (A B : ℕ) (hA : 3 ≤ A) (hAB : A ≤ B) (hB2 : B ≤ 2 * A)
    (hlog : 1 ≤ Real.log (A : ℝ)) :
    nativePNTNormalizedError B - nativePNTNormalizedError A ≤
      2 * (((B : ℝ) - (A : ℝ)) / (A : ℝ)) +
        550 / Real.log (A : ℝ) := by
  have hApos : (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast (show 0 < A by omega)
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (show 0 < B by omega)
  have hlogpos : 0 < Real.log (A : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hABR : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
  have hpsiB0 : 0 ≤ nativePsi B := nativePsi_nonneg B
  have hratio :
      nativePsi B / (B : ℝ) ≤ nativePsi B / (A : ℝ) := by
    rw [div_le_div_iff₀ hBpos hApos]
    exact mul_le_mul_of_nonneg_left hABR hpsiB0
  have hforward :
      nativePNTNormalizedError B - nativePNTNormalizedError A ≤
        (nativePsi B - nativePsi A) / (A : ℝ) := by
    rw [nativePNTNormalizedError_eq_psi_div_sub_one B (by omega),
      nativePNTNormalizedError_eq_psi_div_sub_one A (by omega)]
    calc
      (nativePsi B / (B : ℝ) - 1) -
          (nativePsi A / (A : ℝ) - 1) =
        nativePsi B / (B : ℝ) - nativePsi A / (A : ℝ) := by ring
      _ ≤ nativePsi B / (A : ℝ) - nativePsi A / (A : ℝ) :=
        sub_le_sub_right hratio _
      _ = (nativePsi B - nativePsi A) / (A : ℝ) := by ring
  have hinc := nativePsi_interval_le_gap_tail A B hA hAB hB2 hlog
  have hincDiv :
      (nativePsi B - nativePsi A) / (A : ℝ) ≤
        2 * (((B : ℝ) - (A : ℝ)) / (A : ℝ)) +
          550 / Real.log (A : ℝ) := by
    have h := (div_le_div_iff_of_pos_right hApos).2 hinc
    calc
      (nativePsi B - nativePsi A) / (A : ℝ) ≤
          (2 * ((B : ℝ) - (A : ℝ)) +
            550 * (A : ℝ) / Real.log (A : ℝ)) / (A : ℝ) := h
      _ = 2 * (((B : ℝ) - (A : ℝ)) / (A : ℝ)) +
          550 / Real.log (A : ℝ) := by
        field_simp [ne_of_gt hApos, ne_of_gt hlogpos]
  exact hforward.trans hincDiv

/-- Backward one-sided normalized continuity.  Monotonicity of `psi` and the
Chebyshev upper bound make this direction purely scale-geometric. -/
theorem nativePNTNormalizedError_sub_le_reverse_of_factor_two
    (A B : ℕ) (hA : 3 ≤ A) (hAB : A ≤ B) :
    nativePNTNormalizedError A - nativePNTNormalizedError B ≤
      6 * (((B : ℝ) - (A : ℝ)) / (A : ℝ)) := by
  have hApos : (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast (show 0 < A by omega)
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (show 0 < B by omega)
  have hABR : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
  have hpsiMono : nativePsi A ≤ nativePsi B := nativePsi_monotone hAB
  have hpsiB0 : 0 ≤ nativePsi B := nativePsi_nonneg B
  have hlog4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  have hC6 : Real.log 4 + 2 ≤ (6 : ℝ) := by
    norm_num at hlog4 ⊢
    linarith
  have hpsiB := nativePsi_le_const_mul B
  have hpsiB6 : nativePsi B ≤ 6 * (B : ℝ) := by
    exact hpsiB.trans (mul_le_mul_of_nonneg_right hC6 (by positivity))
  have hrecip0 : 0 ≤ 1 / (A : ℝ) - 1 / (B : ℝ) := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hApos hABR
  have hmonoBound :
      nativePNTNormalizedError A - nativePNTNormalizedError B ≤
        nativePsi B * (1 / (A : ℝ) - 1 / (B : ℝ)) := by
    rw [nativePNTNormalizedError_eq_psi_div_sub_one A (by omega),
      nativePNTNormalizedError_eq_psi_div_sub_one B (by omega)]
    calc
      (nativePsi A / (A : ℝ) - 1) -
          (nativePsi B / (B : ℝ) - 1) =
        nativePsi A / (A : ℝ) - nativePsi B / (B : ℝ) := by ring
      _ ≤ nativePsi B / (A : ℝ) - nativePsi B / (B : ℝ) := by
        exact sub_le_sub_right
          ((div_le_div_iff_of_pos_right hApos).2 hpsiMono) _
      _ = nativePsi B * (1 / (A : ℝ) - 1 / (B : ℝ)) := by ring
  have hscale :
      nativePsi B * (1 / (A : ℝ) - 1 / (B : ℝ)) ≤
        6 * (B : ℝ) * (1 / (A : ℝ) - 1 / (B : ℝ)) :=
    mul_le_mul_of_nonneg_right hpsiB6 hrecip0
  calc
    nativePNTNormalizedError A - nativePNTNormalizedError B ≤
        nativePsi B * (1 / (A : ℝ) - 1 / (B : ℝ)) := hmonoBound
    _ ≤ 6 * (B : ℝ) * (1 / (A : ℝ) - 1 / (B : ℝ)) := hscale
    _ = 6 * (((B : ℝ) - (A : ℝ)) / (A : ℝ)) := by
      field_simp [ne_of_gt hApos, ne_of_gt hBpos]

/-- **Absolute multiplicative continuity.**  On every factor-two interval,
normalized Chebyshev error has an explicit modulus of continuity with no
scale-growing remainder. -/
theorem nativePNTNormalizedError_sub_abs_le_of_factor_two
    (A B : ℕ) (hA : 3 ≤ A) (hAB : A ≤ B) (hB2 : B ≤ 2 * A)
    (hlog : 1 ≤ Real.log (A : ℝ)) :
    |nativePNTNormalizedError B - nativePNTNormalizedError A| ≤
      6 * (((B : ℝ) - (A : ℝ)) / (A : ℝ)) +
        550 / Real.log (A : ℝ) := by
  rw [abs_le]
  constructor
  · have hrev := nativePNTNormalizedError_sub_le_reverse_of_factor_two A B hA hAB
    have htail0 : 0 ≤ 550 / Real.log (A : ℝ) := by
      have hlogpos : 0 < Real.log (A : ℝ) := lt_of_lt_of_le zero_lt_one hlog
      positivity
    linarith
  · have hfwd := nativePNTNormalizedError_sub_le_of_factor_two A B hA hAB hB2 hlog
    have hApos : (0 : ℝ) < (A : ℝ) := by
      exact_mod_cast (show 0 < A by omega)
    have hABR : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
    have hgap0 : 0 ≤ ((B : ℝ) - (A : ℝ)) / (A : ℝ) :=
      div_nonneg (sub_nonneg.mpr hABR) hApos.le
    linarith

end RHLean.Analysis
