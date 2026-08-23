import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import RHLean.Analysis.StrongMertensSmoothing

/-!
# Balancing the log-nine strong Mertens contour

For `r = (log X)^(1/10)` choose

* `T = exp r`,
* `eps = exp (-(A/4) r)`.

Then the three contour envelopes become exponential decays in `r`, with only
fixed polynomial factors.  The polynomial factors are absorbed by weakening the
exponential constant once.  This file does not touch the zeta or contour
geometry; the same `StrongMertensLogNineCorridor` object is threaded through.
-/

noncomputable section

open Filter Asymptotics Set

namespace RHLean.Analysis

def strongMertensScale (X : ℝ) : ℝ :=
  (Real.log X) ^ ((1 : ℝ) / 10)

def strongMertensBalanceHeight (X : ℝ) : ℝ :=
  Real.exp (strongMertensScale X)

def strongMertensBalanceEps
    (corridor : StrongMertensLogNineCorridor) (X : ℝ) : ℝ :=
  Real.exp (-(corridor.A / 4) * strongMertensScale X)

def strongMertensFinalDecay
    (corridor : StrongMertensLogNineCorridor) : ℝ :=
  min (corridor.A / 8) (1 / 8 : ℝ)

lemma strongMertensFinalDecay_pos (corridor : StrongMertensLogNineCorridor) :
    0 < strongMertensFinalDecay corridor := by
  rw [strongMertensFinalDecay]
  exact lt_min
    (div_pos corridor.A_mem.1 (by norm_num))
    (by norm_num)

lemma strongMertensScale_tendsto_atTop :
    Tendsto strongMertensScale atTop atTop := by
  unfold strongMertensScale
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
    Real.tendsto_log_atTop

lemma strongMertensScale_pow_ten {X : ℝ} (hX : 1 ≤ X) :
    strongMertensScale X ^ 10 = Real.log X := by
  unfold strongMertensScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_nonneg hX)]
  norm_num

lemma strongMertensScale_pos {X : ℝ} (hX : 1 < X) :
    0 < strongMertensScale X := by
  unfold strongMertensScale
  exact Real.rpow_pos_of_pos (Real.log_pos hX) _

lemma strongMertensBalanceHeight_log (X : ℝ) :
    Real.log (strongMertensBalanceHeight X) = strongMertensScale X := by
  simp [strongMertensBalanceHeight]

lemma strongMertensBalanceHeight_sqrt (X : ℝ) :
    Real.sqrt (strongMertensBalanceHeight X) =
      Real.exp ((1 / 2 : ℝ) * strongMertensScale X) := by
  rw [strongMertensBalanceHeight, Real.sqrt_eq_rpow, ← Real.exp_mul]
  ring_nf

lemma strongMertensBalanceEps_pos
    (corridor : StrongMertensLogNineCorridor) (X : ℝ) :
    0 < strongMertensBalanceEps corridor X := by
  exact Real.exp_pos _

lemma strongMertensBalanceEps_lt_one
    (corridor : StrongMertensLogNineCorridor) {X : ℝ} (hX : 1 < X) :
    strongMertensBalanceEps corridor X < 1 := by
  rw [strongMertensBalanceEps, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  have hr := strongMertensScale_pos hX
  have hA := corridor.A_mem.1
  nlinarith

/-- Every fixed natural power is eventually bounded by `exp(b r)`. -/
lemma strongMertens_pow_le_exp_eventually (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ r : ℝ in atTop, r ^ k ≤ Real.exp (b * r) := by
  have hlim : Tendsto (fun r : ℝ => r ^ k * Real.exp (-b * r)) atTop (nhds 0) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop k hb).tendsto_div_nhds_zero
    refine h.congr' ?_
    filter_upwards with r
    rw [div_eq_mul_inv, ← Real.exp_neg]
    ring_nf
  filter_upwards [hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (0 : ℝ)] with r hr hnonneg
  calc
    r ^ k = (r ^ k * Real.exp (-b * r)) * Real.exp (b * r) := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    _ ≤ 1 * Real.exp (b * r) :=
      mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
    _ = Real.exp (b * r) := one_mul _

lemma strongMertens_scale_pow_le_exp_eventually
    (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ X : ℝ in atTop,
      strongMertensScale X ^ k ≤ Real.exp (b * strongMertensScale X) :=
  strongMertensScale_tendsto_atTop.eventually
    (strongMertens_pow_le_exp_eventually k hb)

/-- `X * eps(X)` tends to infinity, hence the finite smoothing bridge is
available eventually. -/
lemma strongMertens_two_lt_X_mul_balanceEps
    (corridor : StrongMertensLogNineCorridor) :
    ∀ᶠ X : ℝ in atTop, 2 < X * strongMertensBalanceEps corridor X := by
  let d : ℝ := corridor.A / 4
  have hdlt : d < 1 := by
    dsimp [d]
    have hA := corridor.A_mem.2
    linarith
  have hcoef : 0 < 1 - d := by linarith
  suffices htop : Tendsto
      (fun X : ℝ => X * strongMertensBalanceEps corridor X) atTop atTop by
    exact htop.eventually_gt_atTop 2
  apply tendsto_atTop_mono' atTop
    (f₁ := fun X : ℝ => Real.exp ((1 - d) * strongMertensScale X))
  · filter_upwards [eventually_gt_atTop (1 : ℝ),
      strongMertensScale_tendsto_atTop.eventually_ge_atTop (1 : ℝ)] with X hX hr1
    have hlog := strongMertensScale_pow_ten hX.le
    have hpow : strongMertensScale X ≤ strongMertensScale X ^ 10 := by
      calc
        strongMertensScale X = strongMertensScale X * 1 := by ring
        _ ≤ strongMertensScale X * strongMertensScale X ^ 9 := by
          apply mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 9) hr1) (by linarith)
        _ = strongMertensScale X ^ 10 := by ring
    calc
      Real.exp ((1 - d) * strongMertensScale X)
          ≤ Real.exp (Real.log X - d * strongMertensScale X) := by
        apply Real.exp_le_exp.mpr
        rw [← hlog]
        nlinarith
      _ = Real.exp (Real.log X) *
          Real.exp (-(corridor.A / 4) * strongMertensScale X) := by
        rw [← Real.exp_add]
        dsimp [d]
        congr 1
        ring
      _ = X * strongMertensBalanceEps corridor X := by
        rw [Real.exp_log (by linarith), strongMertensBalanceEps]
  · exact Real.tendsto_exp_atTop.comp
      ((tendsto_const_mul_atTop_of_pos hcoef).2 strongMertensScale_tendsto_atTop)

/-- Exact far-tail envelope at the balanced parameters. -/
lemma strongMertensFarEnvelope_balance {corridor : StrongMertensLogNineCorridor}
    {X : ℝ} (hX : 1 < X) :
    strongMertensFarEnvelope (strongMertensBalanceEps corridor X) X
      (strongMertensBalanceHeight X) =
      X * strongMertensScale X ^ 10 *
        Real.exp (-(1 / 2 - corridor.A / 4) * strongMertensScale X) := by
  have hpow := strongMertensScale_pow_ten hX.le
  rw [strongMertensFarEnvelope, ← hpow, strongMertensBalanceEps,
    strongMertensBalanceHeight_sqrt]
  rw [div_eq_mul_inv, mul_inv]
  simp_rw [← Real.exp_neg]
  rw [← Real.exp_add]
  ring_nf

/-- Exact horizontal envelope at the balanced parameters. -/
lemma strongMertensHorizontalEnvelope_balance
    {corridor : StrongMertensLogNineCorridor} {X : ℝ} (_hX : 1 < X) :
    strongMertensHorizontalEnvelope (strongMertensBalanceEps corridor X) X
      (strongMertensBalanceHeight X) =
      X * (1 + strongMertensScale X ^ 10) *
        Real.exp (-(2 - corridor.A / 4) * strongMertensScale X) := by
  rw [strongMertensHorizontalEnvelope, strongMertensBalanceHeight_log,
    strongMertensBalanceEps]
  rw [show strongMertensBalanceHeight X ^ 2 =
      Real.exp (2 * strongMertensScale X) by
        rw [strongMertensBalanceHeight, ← Real.exp_nat_mul]
        ring_nf]
  rw [div_eq_mul_inv, mul_inv]
  simp_rw [← Real.exp_neg]
  rw [← Real.exp_add]
  ring_nf

/-- Exact shifted-vertical envelope at the balanced parameters. -/
lemma strongMertensVerticalEnvelope_balance
    {corridor : StrongMertensLogNineCorridor} {X : ℝ} (hX : 1 < X) :
    strongMertensVerticalEnvelope corridor (strongMertensBalanceEps corridor X) X
      (strongMertensBalanceHeight X) =
      X * (1 + strongMertensScale X ^ 7) *
        Real.exp (-(3 * corridor.A / 4) * strongMertensScale X) := by
  have hr := strongMertensScale_pos hX
  have hpow := strongMertensScale_pow_ten hX.le
  have hratio : Real.log X / strongMertensScale X ^ 9 = strongMertensScale X := by
    rw [← hpow]
    field_simp [ne_of_gt hr]
  have hexp :
      -corridor.A * Real.log X / strongMertensScale X ^ 9 =
        -corridor.A * strongMertensScale X := by
    calc
      _ = -corridor.A * (Real.log X / strongMertensScale X ^ 9) := by ring
      _ = _ := by rw [hratio]
  rw [strongMertensVerticalEnvelope, strongMertensBalanceHeight_log,
    strongMertensBalanceEps, hexp]
  rw [div_eq_mul_inv]
  simp_rw [← Real.exp_neg]
  have hcombine :
      Real.exp (-corridor.A * strongMertensScale X) *
          Real.exp (-(-(corridor.A / 4) * strongMertensScale X)) =
        Real.exp (-(3 * corridor.A / 4) * strongMertensScale X) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    X * Real.exp (-corridor.A * strongMertensScale X) *
          (1 + strongMertensScale X ^ 7) *
          Real.exp (-(-(corridor.A / 4) * strongMertensScale X))
      = X * (1 + strongMertensScale X ^ 7) *
          (Real.exp (-corridor.A * strongMertensScale X) *
            Real.exp (-(-(corridor.A / 4) * strongMertensScale X))) := by ring
    _ = X * (1 + strongMertensScale X ^ 7) *
        Real.exp (-(3 * corridor.A / 4) * strongMertensScale X) := by rw [hcombine]

/-- All three balanced contour envelopes are eventually bounded by one
`X * exp(-c r)` envelope. -/
theorem strongMertens_balanced_envelopes_eventually
    (corridor : StrongMertensLogNineCorridor) :
    ∀ᶠ X : ℝ in atTop,
      strongMertensFarEnvelope (strongMertensBalanceEps corridor X) X
          (strongMertensBalanceHeight X) +
        strongMertensHorizontalEnvelope (strongMertensBalanceEps corridor X) X
          (strongMertensBalanceHeight X) +
        strongMertensVerticalEnvelope corridor (strongMertensBalanceEps corridor X) X
          (strongMertensBalanceHeight X) ≤
        5 * X * Real.exp (-strongMertensFinalDecay corridor * strongMertensScale X) := by
  let c := strongMertensFinalDecay corridor
  have hc : 0 < c := strongMertensFinalDecay_pos corridor
  have h10 := strongMertens_scale_pow_le_exp_eventually 10 hc
  have h7 := strongMertens_scale_pow_le_exp_eventually 7 hc
  filter_upwards [eventually_gt_atTop (3 : ℝ), h10, h7] with X hX h10 h7
  have hr := strongMertensScale_pos (by linarith : 1 < X)
  have hA := corridor.A_mem
  have hcA : c ≤ corridor.A / 8 := by
    dsimp [c, strongMertensFinalDecay]
    exact min_le_left _ _
  have hc1 : c ≤ (1 : ℝ) / 8 := by
    dsimp [c, strongMertensFinalDecay]
    exact min_le_right _ _
  rw [strongMertensFarEnvelope_balance (corridor := corridor) (by linarith),
    strongMertensHorizontalEnvelope_balance (corridor := corridor) (by linarith),
    strongMertensVerticalEnvelope_balance (corridor := corridor) (by linarith)]
  have hfar_exp :
      Real.exp (c * strongMertensScale X) *
          Real.exp (-(1 / 2 - corridor.A / 4) * strongMertensScale X) ≤
        Real.exp (-c * strongMertensScale X) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hA.2]
  have hhor_exp :
      Real.exp (c * strongMertensScale X) *
          Real.exp (-(2 - corridor.A / 4) * strongMertensScale X) ≤
        Real.exp (-c * strongMertensScale X) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hA.2]
  have hvert_exp :
      Real.exp (c * strongMertensScale X) *
          Real.exp (-(3 * corridor.A / 4) * strongMertensScale X) ≤
        Real.exp (-c * strongMertensScale X) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hA.1]
  have hfar : strongMertensScale X ^ 10 *
      Real.exp (-(1 / 2 - corridor.A / 4) * strongMertensScale X) ≤
      Real.exp (-c * strongMertensScale X) :=
    calc
      _ ≤ Real.exp (c * strongMertensScale X) *
          Real.exp (-(1 / 2 - corridor.A / 4) * strongMertensScale X) :=
        mul_le_mul_of_nonneg_right h10 (Real.exp_pos _).le
      _ ≤ _ := hfar_exp
  have hhor : (1 + strongMertensScale X ^ 10) *
      Real.exp (-(2 - corridor.A / 4) * strongMertensScale X) ≤
      2 * Real.exp (-c * strongMertensScale X) := by
    have h1 : 1 ≤ Real.exp (c * strongMertensScale X) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      exact mul_nonneg hc.le hr.le
    have hpoly :
        1 + strongMertensScale X ^ 10 ≤
          2 * Real.exp (c * strongMertensScale X) := by
      nlinarith [h1, h10]
    calc
      _ ≤ (2 * Real.exp (c * strongMertensScale X)) *
          Real.exp (-(2 - corridor.A / 4) * strongMertensScale X) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = 2 * (Real.exp (c * strongMertensScale X) *
          Real.exp (-(2 - corridor.A / 4) * strongMertensScale X)) := by ring
      _ ≤ 2 * Real.exp (-c * strongMertensScale X) :=
        mul_le_mul_of_nonneg_left hhor_exp (by norm_num)
  have hvert : (1 + strongMertensScale X ^ 7) *
      Real.exp (-(3 * corridor.A / 4) * strongMertensScale X) ≤
      2 * Real.exp (-c * strongMertensScale X) := by
    have h1 : 1 ≤ Real.exp (c * strongMertensScale X) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      exact mul_nonneg hc.le hr.le
    have hpoly :
        1 + strongMertensScale X ^ 7 ≤
          2 * Real.exp (c * strongMertensScale X) := by
      nlinarith [h1, h7]
    calc
      _ ≤ (2 * Real.exp (c * strongMertensScale X)) *
          Real.exp (-(3 * corridor.A / 4) * strongMertensScale X) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = 2 * (Real.exp (c * strongMertensScale X) *
          Real.exp (-(3 * corridor.A / 4) * strongMertensScale X)) := by ring
      _ ≤ 2 * Real.exp (-c * strongMertensScale X) :=
        mul_le_mul_of_nonneg_left hvert_exp (by norm_num)
  have hX0 : 0 ≤ X := by linarith
  have hfarX :
      X * strongMertensScale X ^ 10 *
          Real.exp (-(1 / 2 - corridor.A / 4) * strongMertensScale X) ≤
        X * Real.exp (-c * strongMertensScale X) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hfar hX0
  have hhorX :
      X * (1 + strongMertensScale X ^ 10) *
          Real.exp (-(2 - corridor.A / 4) * strongMertensScale X) ≤
        X * (2 * Real.exp (-c * strongMertensScale X)) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hhor hX0
  have hvertX :
      X * (1 + strongMertensScale X ^ 7) *
          Real.exp (-(3 * corridor.A / 4) * strongMertensScale X) ≤
        X * (2 * Real.exp (-c * strongMertensScale X)) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hvert hX0
  calc
    X * strongMertensScale X ^ 10 *
          Real.exp (-(1 / 2 - corridor.A / 4) * strongMertensScale X) +
        X * (1 + strongMertensScale X ^ 10) *
          Real.exp (-(2 - corridor.A / 4) * strongMertensScale X) +
        X * (1 + strongMertensScale X ^ 7) *
          Real.exp (-(3 * corridor.A / 4) * strongMertensScale X)
      ≤ X * Real.exp (-c * strongMertensScale X) +
          X * (2 * Real.exp (-c * strongMertensScale X)) +
          X * (2 * Real.exp (-c * strongMertensScale X)) :=
        add_le_add (add_le_add hfarX hhorX) hvertX
    _ = 5 * X * Real.exp (-c * strongMertensScale X) := by ring

end RHLean.Analysis
