import Mathlib.Analysis.PSeries
import RHLean.Analysis.K2RecipMomentAnalyticClosure
import RHLean.Analysis.StrongMertensLogNineBalance

noncomputable section

open Filter Set Topology
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RHLean.Analysis

local notation "gammaE" => Real.eulerMascheroniConstant

/-- The log-square Mobius L-series has the reciprocal-zeta boundary value from
the right of `1`. -/
theorem k2MobiusLogSqLSeries_tendsto_right_one :
    Tendsto
      (fun sigma : ℝ =>
        LSeries (LSeries.logMul^[2] (fun n : ℕ => (μ n : ℂ))) (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (-2 * gammaE : ℂ)) := by
  have hfun :
      (fun s : ℂ => iteratedDeriv 2 k2InvZetaRegular s) =
        deriv (deriv k2InvZetaRegular) := by
    funext s
    simp [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  have hval :
      deriv (deriv k2InvZetaRegular) (1 : ℂ) = (-2 * gammaE : ℂ) := by
    simpa [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ] using
      k2InvZetaRegular_iteratedDeriv_two
  have hcomplex :
      Tendsto (fun s : ℂ => iteratedDeriv 2 k2InvZetaRegular s)
        (𝓝 (1 : ℂ)) (𝓝 (-2 * gammaE : ℂ)) := by
    rw [hfun]
    have h := (k2InvZetaRegular_analyticAt_one.iterated_deriv 2).continuousAt.tendsto
    simpa [hval] using h
  have hreal :
      Tendsto (fun sigma : ℝ => (sigma : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds
      RCLike.continuous_ofReal.continuousAt.tendsto
  apply (hcomplex.comp hreal).congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  have hs : 1 < sigma := by simpa using hsigma
  simpa using
    (k2InvZetaRegular_iteratedDeriv_two_eq_moebiusLogSqLSeries
      (s := (sigma : ℂ)) (by simpa using hs))

/-- Strong Mertens kills every fixed logarithmic reciprocal endpoint.  This is
the endpoint term in Abel summation for the order-two and order-three K2
moments. -/
theorem k2StrongMertens_logRecip_endpoint_tendsto_zero (m : ℕ) :
    Tendsto
      (fun N : ℕ => nativeMertensSummatory N * k2LogRecipWeight m N)
      atTop (𝓝 0) := by
  obtain ⟨c, C, hc, _hC, hM⟩ := strongNativeMertensSubexp
  have hpolyexp :
      Tendsto (fun r : ℝ => r ^ (10 * m) * Real.exp (-c * r)) atTop (𝓝 0) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop (10 * m) hc).tendsto_div_nhds_zero
    refine h.congr' ?_
    filter_upwards with r
    rw [div_eq_mul_inv, ← Real.exp_neg]
    ring_nf
  have hscaleN :
      Tendsto (fun N : ℕ => strongMertensScale (N : ℝ)) atTop atTop :=
    strongMertensScale_tendsto_atTop.comp tendsto_natCast_atTop_atTop
  have hmajor :
      Tendsto
        (fun N : ℕ =>
          C * (strongMertensScale (N : ℝ) ^ (10 * m) *
            Real.exp (-c * strongMertensScale (N : ℝ))))
        atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hpolyexp.comp hscaleN)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hmajor
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hNposNat : 0 < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNposNat
  have hw_nonneg : 0 ≤ k2LogRecipWeight m N := by
    unfold k2LogRecipWeight
    positivity
  have hlogpow :
      (Real.log (N : ℝ)) ^ m =
        strongMertensScale (N : ℝ) ^ (10 * m) := by
    have hs := strongMertensScale_pow_ten (X := (N : ℝ)) hN1
    calc
      (Real.log (N : ℝ)) ^ m = (strongMertensScale (N : ℝ) ^ 10) ^ m := by rw [hs]
      _ = strongMertensScale (N : ℝ) ^ (10 * m) := (pow_mul _ _ _).symm
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw_nonneg]
  calc
    |nativeMertensSummatory N| * k2LogRecipWeight m N
        ≤ (C * (N : ℝ) *
            Real.exp (-c * strongMertensScale (N : ℝ))) *
          k2LogRecipWeight m N :=
      mul_le_mul_of_nonneg_right (hM N hN) hw_nonneg
    _ = C * (Real.log (N : ℝ)) ^ m *
        Real.exp (-c * strongMertensScale (N : ℝ)) := by
      unfold k2LogRecipWeight
      field_simp [ne_of_gt hNpos]
    _ = C * (strongMertensScale (N : ℝ) ^ (10 * m) *
        Real.exp (-c * strongMertensScale (N : ℝ))) := by
      rw [hlogpow]
      ring

/-- Shifted logarithmic harmonic majorant used in the K2 Abel tails. -/
def k2LogHarmonicTail (p n : ℕ) : ℝ :=
  1 / (((n + 3 : ℕ) : ℝ) * (Real.log ((n + 3 : ℕ) : ℝ)) ^ p)

/-- Elementary logarithmic harmonic summability.  Cauchy condensation turns the
tail into a constant multiple of a p-series. -/
theorem k2LogHarmonicTail_summable {p : ℕ} (hp : 1 < p) :
    Summable (k2LogHarmonicTail p) := by
  have hnonneg : ∀ n, 0 ≤ k2LogHarmonicTail p n := by
    intro n
    unfold k2LogHarmonicTail
    positivity
  have hmono : ∀ ⦃m n⦄, 0 < m → m ≤ n →
      k2LogHarmonicTail p n ≤ k2LogHarmonicTail p m := by
    intro m n _hm hmn
    unfold k2LogHarmonicTail
    have hmnNat : m + 3 ≤ n + 3 := by omega
    have hmnR : (((m + 3 : ℕ) : ℝ)) ≤ ((n + 3 : ℕ) : ℝ) := by
      exact_mod_cast hmnNat
    have hmpos : 0 < (((m + 3 : ℕ) : ℝ)) := by positivity
    have hlogm : 0 ≤ Real.log ((m + 3 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 3 by omega))
    have hlogmpos : 0 < Real.log ((m + 3 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m + 3 by omega))
    have hlogle : Real.log ((m + 3 : ℕ) : ℝ) ≤ Real.log ((n + 3 : ℕ) : ℝ) :=
      Real.log_le_log hmpos hmnR
    have hpowle : (Real.log ((m + 3 : ℕ) : ℝ)) ^ p ≤
        (Real.log ((n + 3 : ℕ) : ℝ)) ^ p :=
      pow_le_pow_left₀ hlogm hlogle p
    have hdenle : (((m + 3 : ℕ) : ℝ)) * (Real.log ((m + 3 : ℕ) : ℝ)) ^ p ≤
        ((n + 3 : ℕ) : ℝ) * (Real.log ((n + 3 : ℕ) : ℝ)) ^ p := by
      exact mul_le_mul hmnR hpowle (by positivity) (by positivity)
    exact one_div_le_one_div_of_le (mul_pos hmpos (pow_pos hlogmpos p)) hdenle
  rw [← summable_condensed_iff_of_nonneg hnonneg hmono]
  rw [← summable_nat_add_iff 1 (G := ℝ)]
  let D : ℝ := 1 / (Real.log 2) ^ p
  have hpseries0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) :=
    Real.summable_one_div_nat_pow.mpr hp
  have hpseries : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ p)) :=
    (summable_nat_add_iff 1 (G := ℝ)).2 hpseries0
  have hmajor : Summable (fun k : ℕ => D * (1 / (((k + 1 : ℕ) : ℝ) ^ p))) :=
    hpseries.mul_left D
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (by positivity) (hnonneg (2 ^ (k + 1)))) ?_ hmajor
  intro k
  let q : ℕ := 2 ^ (k + 1)
  have hqNatPos : 0 < q := by
    dsimp [q]
    positivity
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqNatPos
  have hqleNat : q ≤ q + 3 := by omega
  have hqle : (q : ℝ) ≤ ((q + 3 : ℕ) : ℝ) := by exact_mod_cast hqleNat
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : Real.log (q : ℝ) = ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
    dsimp [q]
    push_cast
    rw [Real.log_pow]
    push_cast
    rfl
  have hlogle : Real.log (q : ℝ) ≤ Real.log ((q + 3 : ℕ) : ℝ) :=
    Real.log_le_log hqpos hqle
  have hlogqpos : 0 < Real.log (q : ℝ) := by
    rw [hlogq]
    positivity
  have hpowle : (Real.log (q : ℝ)) ^ p ≤ (Real.log ((q + 3 : ℕ) : ℝ)) ^ p :=
    pow_le_pow_left₀ hlogqpos.le hlogle p
  have hsmallpos : 0 < (q : ℝ) * (Real.log (q : ℝ)) ^ p := by
    positivity
  have hq3nat : 1 < q + 3 := by omega
  have hq3 : (1 : ℝ) < ((q + 3 : ℕ) : ℝ) := by exact_mod_cast hq3nat
  have hlogbigpos : 0 < Real.log ((q + 3 : ℕ) : ℝ) := Real.log_pos hq3
  have hbigpos : 0 < ((q + 3 : ℕ) : ℝ) * (Real.log ((q + 3 : ℕ) : ℝ)) ^ p :=
    mul_pos (by positivity) (pow_pos hlogbigpos p)
  have hdenle : (q : ℝ) * (Real.log (q : ℝ)) ^ p ≤
      ((q + 3 : ℕ) : ℝ) * (Real.log ((q + 3 : ℕ) : ℝ)) ^ p := by
    exact mul_le_mul hqle hpowle (by positivity) (by positivity)
  have hquot :
      (q : ℝ) / (((q + 3 : ℕ) : ℝ) * (Real.log ((q + 3 : ℕ) : ℝ)) ^ p) ≤
        (q : ℝ) / ((q : ℝ) * (Real.log (q : ℝ)) ^ p) := by
    exact (div_le_div_iff_of_pos_left hqpos hbigpos hsmallpos).2 hdenle
  calc
    (2 : ℝ) ^ (k + 1) * k2LogHarmonicTail p (2 ^ (k + 1)) =
        (q : ℝ) / (((q + 3 : ℕ) : ℝ) * (Real.log ((q + 3 : ℕ) : ℝ)) ^ p) := by
      dsimp [q, k2LogHarmonicTail]
      push_cast
      ring
    _ ≤ (q : ℝ) / ((q : ℝ) * (Real.log (q : ℝ)) ^ p) := hquot
    _ = 1 / (Real.log (q : ℝ)) ^ p := by
      field_simp [ne_of_gt hqpos]
    _ = D * (1 / (((k + 1 : ℕ) : ℝ) ^ p)) := by
      dsimp [D]
      rw [hlogq, mul_pow]
      field_simp [ne_of_gt hlog2]

end RHLean.Analysis
