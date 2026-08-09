import Mathlib
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import RHLean.Analysis.MertensMellinContinuation

/-!
# Identify the Mertens Mellin continuation with the Möbius L-series

On `Re(s) > 1`, the ordinary Möbius L-series converges absolutely. Abel
summation expresses it as the same integral used to define the Mertens Mellin
continuation. The only difference in the integral domains is `(0,1]`, where
the Mertens step function vanishes except at the measure-zero endpoint `1`.

Consequently the continuation agrees with the ordinary Möbius L-series on its
classical half-plane. Combining this with Mathlib's exact zeta/Möbius
Dirichlet-convolution identity gives `zeta(s) * F(s) = 1` there.
-/

open scoped ArithmeticFunction.Moebius BigOperators LSeries.notation

noncomputable section

namespace RHLean.Analysis

open Complex Filter Set MeasureTheory

/-- The Mellin integral over `(0,∞)` reduces to the Abel integral over `(1,∞)`
because the Mertens step function vanishes below one; the endpoint is null. -/
theorem mellin_mertensStep_neg_eq_integral_Ioi_one (s : ℂ) :
    mellin mertensStep (-s) =
      ∫ t in Set.Ioi (1 : ℝ),
        mertensStep t * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin
  rw [← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [(countable_singleton (1 : ℝ)).ae_notMem volume] with t ht1
  have ht1' : t ≠ 1 := by simpa using ht1
  by_cases h1 : 1 < t
  · have h0 : 0 < t := zero_lt_one.trans h1
    have ht0 : t ∈ Set.Ioi (0 : ℝ) := h0
    have ht1Ioi : t ∈ Set.Ioi (1 : ℝ) := h1
    rw [Set.indicator_of_mem ht0, Set.indicator_of_mem ht1Ioi]
    simp only [smul_eq_mul]
    ring_nf
  · have hle : t ≤ 1 := le_of_not_gt h1
    have hlt : t < 1 := lt_of_le_of_ne hle ht1'
    have hz : mertensStep t = 0 := mertensStep_eq_zero_of_lt_one hlt
    have hn1 : t ∉ Set.Ioi (1 : ℝ) := h1
    by_cases h0 : 0 < t
    · have ht0 : t ∈ Set.Ioi (0 : ℝ) := h0
      rw [Set.indicator_of_mem ht0, Set.indicator_of_notMem hn1, hz]
      simp
    · have hn0 : t ∉ Set.Ioi (0 : ℝ) := h0
      rw [Set.indicator_of_notMem hn0, Set.indicator_of_notMem hn1]

/-- On the classical half-plane, the Mellin continuation is exactly the
ordinary Möbius L-series. -/
theorem mertensMellinContinuation_eq_LSeries_moebius
    (hM : MertensEnergyBoundedStatement) {s : ℂ}
    (hs : 1 < s.re) :
    mertensMellinContinuation s = L ↗ArithmeticFunction.moebius s := by
  let r : ℝ := 3 / 4
  have hr0 : 0 ≤ r := by
    dsimp [r]
    norm_num
  have hrs : r < s.re := by
    dsimp [r]
    linarith
  have hhalf : (1 : ℝ) / 2 < r := by
    dsimp [r]
    norm_num
  have hO :
      (fun n : ℕ =>
        ∑ k ∈ Finset.Icc 1 n,
          (((ArithmeticFunction.moebius k : ℤ) : ℂ))) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ r) := by
    simpa only [sum_Icc_one_moebius_eq_mertensSummatory] using
      mertensSummatory_isBigO_rpow hM hhalf
  have hS : LSeriesSummable (↗ArithmeticFunction.moebius) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  rw [mertensMellinContinuation,
    mellin_mertensStep_neg_eq_integral_Ioi_one]
  symm
  rw [LSeries_eq_mul_integral
    (↗ArithmeticFunction.moebius) hr0 hrs hS hO]
  apply congrArg (fun z : ℂ => s * z)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  unfold mertensStep
  rfl

/-- Exact reciprocal identity on `Re(s) > 1`, obtained entirely from Mathlib's
zeta/Möbius convolution theorem after the integral identification. -/
theorem riemannZeta_mul_mertensMellinContinuation_eq_one
    (hM : MertensEnergyBoundedStatement) {s : ℂ}
    (hs : 1 < s.re) :
    riemannZeta s * mertensMellinContinuation s = 1 := by
  rw [mertensMellinContinuation_eq_LSeries_moebius hM hs]
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs

end RHLean.Analysis
