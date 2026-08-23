import Mathlib
import Mathlib.NumberTheory.LSeries.Dirichlet
-- See the note in `StrongMertensZetaKernel`: `StrongPNT.PNT5_Strong` and
-- `PrimeNumberTheoremAnd.MediumPNT` cannot both be imported, and this route
-- takes the StrongPNT side.
import StrongPNT.PNT5_Strong
import RHLean.Analysis.StrongMertensLogNineEnvelope

/-!
# Sharp-cutoff bridge for the native strong Mertens contour

This file contains only the finite smoothing argument.  No prime number theorem
or reciprocal-zeta estimate is used here.

The real extension `nativeMertensSharpReal X` agrees with
`nativeMertensSummatory N` at natural arguments.  The smoothed Perron transform
is first identified with the weighted Mobius sum, then the transition window of
`Smooth1` is bounded using `|mu(n)| <= 1`.
-/

noncomputable section

open Filter Asymptotics Finset Complex Real MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius LSeries.notation

namespace RHLean.Analysis

local notation "I" => Complex.I

/-- Real extension of the repository-native Mertens summatory function.  The
zero term is harmless because `mu 0 = 0`. -/
noncomputable def nativeMertensSharpReal (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (μ n : ℝ)

@[simp] theorem nativeMertensSharpReal_nat (N : ℕ) :
    nativeMertensSharpReal (N : ℝ) = nativeMertensSummatory N := by
  simp [nativeMertensSharpReal, nativeMertensSummatory]

/-- Range form used by the transition-window counting argument. -/
theorem nativeMertensSharpReal_eq_sum_range (X : ℝ) :
    nativeMertensSharpReal X =
      ∑ n ∈ Finset.range (⌊X⌋₊ + 1), (μ n : ℝ) := by
  rw [nativeMertensSharpReal]
  have hset : Finset.range (⌊X⌋₊ + 1) =
      insert 0 (Finset.Icc 1 ⌊X⌋₊) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert]
  · simp
  · simp

/-- Pure transition-window estimate for Mobius coefficients. -/
theorem strongMertens_smoothed_close_aux
    {Smooth : (ℝ → ℝ) → ℝ → ℝ → ℝ} (SmoothingF : ℝ → ℝ)
    (c1 : ℝ) (c1_pos : 0 < c1) (c1_lt : c1 < 1)
    (c2 : ℝ) (c2_pos : 0 < c2) (_c2_lt : c2 < 2)
    (hc2 : ∀ (eps x : ℝ), eps ∈ Set.Ioo 0 1 →
      1 + c2 * eps ≤ x → Smooth SmoothingF eps x = 0)
    (C : ℝ) (C_eq : C = 6 * (3 * c1 + c2))
    (eps : ℝ) (eps_pos : 0 < eps) (eps_lt_one : eps < 1)
    (X : ℝ) (X_pos : 0 < X) (X_gt_three : 3 < X)
    (X_bound_1 : 1 ≤ X * eps * c1) (X_bound_2 : 1 ≤ X * eps * c2)
    (smooth_le_one : ∀ (n : ℕ), 0 < n → Smooth SmoothingF eps ((n : ℝ) / X) ≤ 1)
    (smooth_nonneg : ∀ (n : ℕ), 0 < n → Smooth SmoothingF eps ((n : ℝ) / X) ≥ 0)
    (smooth_eq_one : ∀ (n : ℕ), 0 < n → (n : ℝ) ≤ X * (1 - c1 * eps) →
      Smooth SmoothingF eps ((n : ℝ) / X) = 1)
    (smooth_eq_zero : ∀ (n : ℕ), 1 + c2 * eps ≤ (n : ℝ) / X →
      Smooth SmoothingF eps ((n : ℝ) / X) = 0) :
    ‖((∑' (n : ℕ), (μ n : ℝ) * Smooth SmoothingF eps ((n : ℝ) / X) : ℝ) : ℂ) -
        (nativeMertensSharpReal X : ℂ)‖ ≤ C * eps * X := by
  norm_cast
  rw [nativeMertensSharpReal_eq_sum_range]
  let F := Smooth SmoothingF eps
  let n0 := ⌈X * (1 - c1 * eps)⌉₊
  have n0_pos : 0 < n0 := by
    simp only [Nat.ceil_pos, n0]
    subst C_eq
    have hprod : c1 * eps < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left c1_pos.le c1_lt eps_lt_one.le
    have : (0 : ℝ) < 1 - c1 * eps := by linarith
    positivity
  have n0_inside_le_X : X * (1 - c1 * eps) ≤ X := by
    nth_rewrite 2 [← mul_one X]
    apply mul_le_mul_of_nonneg_left _ X_pos.le
    exact sub_le_self _ (by positivity)
  have n0_le : (n0 : ℝ) ≤ X * (1 - c1 * eps) + 1 := by
    simp only [n0]
    exact le_of_lt (Nat.ceil_lt_add_one (by bound))
  have n0_gt : X * (1 - c1 * eps) ≤ (n0 : ℝ) := by
    simp only [n0]
    exact Nat.le_ceil (X * (1 - c1 * eps))
  have sum_mu : Summable (fun n : ℕ => (μ n : ℝ) * F ((n : ℝ) / X)) := by
    apply summable_of_ne_finset_zero (s := Finset.range ⌈X * (1 + c2 * eps)⌉₊)
    intro a ha
    apply mul_eq_zero_of_right
    apply hc2 _ _ ⟨eps_pos, eps_lt_one⟩
    rw [Finset.mem_range, not_lt] at ha
    rw [le_div_iff₀ X_pos]
    have hcl : X * (1 + c2 * eps) ≤ (a : ℝ) := (Nat.ceil_le).1 ha
    rw [mul_comm]
    exact hcl
  have sum_mu_shift (k : ℕ) :
      Summable (fun n => (μ (n + k) : ℝ) * F (((n + k : ℕ) : ℝ) / X)) := by
    exact_mod_cast sum_mu.comp_injective fun q => by omega
  rw [← Summable.sum_add_tsum_nat_add' (k := n0) (mod_cast sum_mu_shift n0)]
  let n1 := ⌊X * (1 + c2 * eps)⌋₊
  have n1_pos : 0 < n1 := by
    dsimp only [n1]
    apply Nat.le_floor
    rw [Nat.succ_eq_add_one, zero_add]
    norm_cast
    apply one_le_mul_of_one_le_of_one_le (by linarith)
    exact le_add_of_nonneg_right (by positivity)
  have n1_ge : X * (1 + c2 * eps) - 1 ≤ (n1 : ℝ) := by
    simp only [tsub_le_iff_right, n1]
    exact le_of_lt (Nat.lt_floor_add_one (X * (1 + c2 * eps)))
  have n1_le : (n1 : ℝ) ≤ X * (1 + c2 * eps) := by
    simp only [n1]
    exact Nat.floor_le (by bound)
  have n1_ge_n0 : n0 ≤ n1 := by
    exact_mod_cast le_imp_le_of_le_of_le n0_le n1_ge (by linarith)
  have n1_sub_n0 : (n1 : ℝ) - n0 ≤ X * eps * (c2 + c1) := by
    calc
      (n1 : ℝ) - n0 ≤ X * (1 + c2 * eps) - n0 := sub_le_sub_right n1_le _
      _ ≤ X * (1 + c2 * eps) - X * (1 - c1 * eps) :=
        sub_le_sub_left n0_gt _
      _ = X * eps * (c2 + c1) := by ring
  rw [show (∑' n : ℕ, (μ (n + n0) : ℝ) *
        Smooth SmoothingF eps (((n + n0 : ℕ) : ℝ) / X)) =
      (∑ n ∈ Finset.range (n1 - n0), (μ (n + n0) : ℝ) *
        Smooth SmoothingF eps (((n + n0 : ℕ) : ℝ) / X)) +
      (∑' n : ℕ, (μ (n + n1) : ℝ) *
        Smooth SmoothingF eps (((n + n1 : ℕ) : ℝ) / X)) by
    rw [← Summable.sum_add_tsum_nat_add' (k := n1 - n0)
      (f := fun n => (μ (n + n0) : ℝ) *
        Smooth SmoothingF eps (((n + n0 : ℕ) : ℝ) / X))]
    · congr 1
      apply tsum_congr
      intro n
      rw [show n + (n1 - n0) + n0 = n + n1 by omega]
    · have h := sum_mu_shift n1
      apply h.congr
      intro n
      rw [show n + (n1 - n0) + n0 = n + n1 by omega]]
  rw [show (∑' n : ℕ, (μ (n + n1) : ℝ) * F (((n + n1 : ℕ) : ℝ) / X)) =
      (μ n1 : ℝ) * F ((n1 : ℝ) / X) by
    have hsplit : (∑' n : ℕ, (μ (n + n1) : ℝ) * F (((n + n1 : ℕ) : ℝ) / X)) =
        (μ n1 : ℝ) * F ((n1 : ℝ) / X) +
          (∑' n : ℕ, (μ (n + 1 + n1) : ℝ) * F (((n + 1 + n1 : ℕ) : ℝ) / X)) := by
      simpa [Nat.cast_add] using (sum_mu_shift n1).tsum_eq_zero_add
    rw [hsplit]
    apply add_eq_left.mpr
    convert tsum_zero with n
    convert mul_zero _
    apply smooth_eq_zero
    rw [← mul_le_mul_iff_left₀ X_pos]
    rw [(by field_simp : ((n + 1 + n1 : ℕ) : ℝ) / X * X = (n + 1 + n1 : ℕ)),
      (by ring : (1 + c2 * eps) * X = 1 + (X * (1 + c2 * eps) - 1))]
    push_cast
    linarith [n1_ge]]
  have X_le_floor_add_one : X ≤ (⌊X + 1⌋₊ : ℝ) := by
    rw [Nat.floor_add_one (by linarith), Nat.cast_add, Nat.cast_one]
    apply le_trans (Nat.le_ceil X)
    exact_mod_cast Nat.ceil_le_floor_add_one X
  have floor_X_add_one_le_self : (⌊X + 1⌋₊ : ℝ) ≤ X + 1 := Nat.floor_le (by positivity)
  have hn0_le_floorX1 : n0 ≤ ⌊X + 1⌋₊ := by
    simp only [Nat.ceil_le, n0]
    exact n0_inside_le_X.trans X_le_floor_add_one
  rw [show ∑ n ∈ Finset.range (⌊X⌋₊ + 1), (μ n : ℝ) =
      (∑ x ∈ Finset.range n0, (μ x : ℝ)) +
        ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n0), (μ (x + n0) : ℝ) by
    rw [show ⌊X⌋₊ + 1 = ⌊X + 1⌋₊ by rw [Nat.floor_add_one X_pos.le]]
    conv_lhs => rw [show ⌊X + 1⌋₊ = n0 + (⌊X + 1⌋₊ - n0) by omega]
    rw [Finset.sum_range_add]
    simp only [add_comm n0]]
  rw [show ∑ n ∈ Finset.range n0, (μ n : ℝ) * F ((n : ℝ) / X) =
      ∑ n ∈ Finset.range n0, (μ n : ℝ) by
    apply Finset.sum_congr rfl
    intro n hn
    obtain rfl | hn0 := eq_or_ne n 0
    · simp
    · convert mul_one _
      apply smooth_eq_one n (Nat.zero_lt_of_ne_zero hn0)
      simp only [Finset.mem_range, n0] at hn
      exact (Nat.lt_ceil.mp hn).le]
  have mu_bnd1 : ∀ n ∈ Finset.range (n1 - n0), ‖(μ (n + n0) : ℝ)‖ ≤ 1 := by
    intro n _
    rw [Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have bnd1 :
      ∑ n ∈ Finset.range (n1 - n0), ‖(μ (n + n0) : ℝ)‖ *
        ‖F (((n : ℝ) + n0) / X)‖ ≤ ((n1 : ℝ) - n0) := by
    rw [show ((n1 : ℝ) - n0) = ∑ _n ∈ Finset.range (n1 - n0), (1 : ℝ) by
      rw [← Nat.cast_sub n1_ge_n0]
      simp]
    apply Finset.sum_le_sum
    intro n hn
    rw [← mul_one (1 : ℝ)]
    apply mul_le_mul (mu_bnd1 n hn) _ (norm_nonneg _) (by norm_num)
    rw [Real.norm_of_nonneg]
    · simpa [F, Nat.cast_add] using smooth_le_one (n + n0) (by omega)
    · simpa [F, Nat.cast_add] using smooth_nonneg (n + n0) (by omega)
  have bnd2 :
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n0), ‖(μ (x + n0) : ℝ)‖ ≤
        (⌊X + 1⌋₊ : ℝ) - n0 := by
    rw [show (⌊X + 1⌋₊ : ℝ) - n0 =
      ∑ _n ∈ Finset.range (⌊X + 1⌋₊ - n0), (1 : ℝ) by
        rw [← Nat.cast_sub hn0_le_floorX1]
        simp]
    apply Finset.sum_le_sum
    intro n _
    rw [Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have mu_bnd_last : ‖(μ n1 : ℝ)‖ * ‖F ((n1 : ℝ) / X)‖ ≤ 1 := by
    rw [← mul_one (1 : ℝ)]
    apply mul_le_mul _ _ (norm_nonneg _) (by norm_num)
    · rw [Real.norm_eq_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    · rw [Real.norm_of_nonneg (smooth_nonneg n1 n1_pos)]
      exact smooth_le_one n1 n1_pos
  calc
    _ = ‖∑ n ∈ Finset.range (n1 - n0), (μ (n + n0) : ℝ) *
          F (((n : ℝ) + n0) / X) -
        ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n0), (μ (x + n0) : ℝ) +
        (μ n1 : ℝ) * F ((n1 : ℝ) / X)‖ := by
      congr 1
      push_cast
      ring
    _ ≤ (∑ n ∈ Finset.range (n1 - n0), ‖(μ (n + n0) : ℝ)‖ *
          ‖F (((n : ℝ) + n0) / X)‖) +
        ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n0), ‖(μ (x + n0) : ℝ)‖ +
        ‖(μ n1 : ℝ)‖ * ‖F ((n1 : ℝ) / X)‖ := by
      apply norm_add_le_of_le
      · apply norm_sub_le_of_le
        · apply norm_sum_le_of_le
          intro b _
          exact norm_mul_le_of_le (by rfl) (by rfl)
        · apply norm_sum_le_of_le
          intro b _
          rfl
      · exact_mod_cast norm_mul_le_of_le (by rfl) (by rfl)
    _ ≤ ((n1 : ℝ) - n0) + ((⌊X + 1⌋₊ : ℝ) - n0) + 1 := by
      exact add_le_add (add_le_add bnd1 bnd2) mu_bnd_last
    _ ≤ C * eps * X := by
      have hfloor_n0 : ((⌊X + 1⌋₊ : ℝ) - n0) ≤ 2 * (X * eps * c1) := by
        rw [(by ring : 2 * (X * eps * c1) =
          X * (1 + eps * c1) - X * (1 - eps * c1))]
        apply sub_le_sub
        · apply floor_X_add_one_le_self.trans
          ring_nf
          linarith [X_bound_1]
        · simpa [mul_comm c1 eps] using n0_gt
      have hkey : ((n1 : ℝ) - n0) + ((⌊X + 1⌋₊ : ℝ) - n0) + 1 ≤
          X * eps * (c2 + c1) + 2 * (X * eps * c1) + X * eps * c1 := by
        apply add_le_add (add_le_add n1_sub_n0 hfloor_n0)
        linarith [X_bound_1]
      calc
        _ ≤ X * eps * (c2 + c1) + 2 * (X * eps * c1) + X * eps * c1 := hkey
        _ = (4 * c1 + c2) * (eps * X) := by ring
        _ ≤ C * eps * X := by
          rw [C_eq]
          have h0 : 0 ≤ eps * X := by positivity
          nlinarith [h0, c1_pos, c2_pos]

-- Mobius L-series summability on `Re s > 1`.

end RHLean.Analysis
