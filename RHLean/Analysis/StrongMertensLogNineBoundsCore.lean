import Mathlib
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import PrimeNumberTheoremAnd.ZetaBounds
import StrongPNT.PNT5_Strong
import RHLean.Analysis.StrongMertensLogNineContour
import RHLean.Analysis.StrongMertensSmallHeight

/-!
# Quantitative boundary estimates for the shared log-nine Mertens contour

All contour legs consume the single corridor from
`StrongMertensLogNineCorridor`.  No theorem in this file reselects an analytic
width constant and no wide-strip reciprocal-zeta hypothesis is introduced.

The shifted vertical line is

  `sigma_T = 1 - A / log(T)^9`.

Large heights on this line use PNT+'s `ZetaInvBnd`; bounded heights use the
compact removable-zero estimate from `StrongMertensSmallHeight`.  On the
horizontal legs, each point is treated by a pointwise dichotomy:

* `sigma <= 1 + A/log(T)^9`: use the shared narrow `ZetaInvBnd` window;
* `sigma > 1 + A/log(T)^9`: use `ZetaInvBound2` on `Re s > 1`.

Thus there is no `NativeMertensHorizontalCompatible` side condition.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset Topology Asymptotics Complex Real MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius LSeries.notation

namespace RHLean.Analysis

local notation "zetaC" => riemannZeta

-- `StrongPNT.PNT1_ComplexAnalysis` declares a root-level `def I := Complex.I`,
-- so with `Complex` open the bare token `I` resolves two ways.
local notation "I" => Complex.I

/-- One uniform inverse-zeta estimate on the fixed shifted line for an
already-selected corridor. -/
theorem nativeInvZeta_logNine_shift_uniform_for
    (corridor : StrongMertensLogNineCorridor) :
    ∃ C > 0,
      (∀ {T t : ℝ}, 3 < T → |t| ≤ T →
        1 / ‖zetaC (strongMertensLogNineShift corridor.A T + t * I)‖ ≤
          C * (1 + (Real.log T) ^ 7)) ∧
      (∀ {T : ℝ}, 3 < T →
        ∀ s ∈ (((Set.Icc (strongMertensLogNineShift corridor.A T) 2) ×ℂ
          (Set.Icc (-T) T)) \ {(1 : ℂ)}), zetaC s ≠ 0) := by
  obtain ⟨M, hM, hSmall⟩ := strongMertens_inv_zeta_small_height_bdd corridor
  let C : ℝ := corridor.invConst + M + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith [corridor.invConst_pos, hM]
  refine ⟨C, hC, ?_, ?_⟩
  · intro T t hT htT
    by_cases ht : 3 < |t|
    · have hlarge := corridor.inv_shift_large T t hT ht htT
      have hlogle : Real.log |t| ≤ Real.log T :=
        Real.log_le_log (by linarith) htT
      have hlognn : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
      have hp7 : (Real.log |t|) ^ 7 ≤ (Real.log T) ^ 7 :=
        pow_le_pow_left₀ hlognn hlogle 7
      calc
        1 / ‖zetaC (strongMertensLogNineShift corridor.A T + t * I)‖
            ≤ corridor.invConst * (Real.log |t|) ^ 7 := by simpa using hlarge
        _ ≤ corridor.invConst * (Real.log T) ^ 7 :=
          mul_le_mul_of_nonneg_left hp7 corridor.invConst_pos.le
        _ ≤ C * (1 + (Real.log T) ^ 7) := by
          dsimp [C]
          have hp : 0 ≤ (Real.log T) ^ 7 :=
            pow_nonneg (Real.log_nonneg (by linarith)) 7
          nlinarith [corridor.invConst_pos.le, hM]
    · have hsmallt : |t| ≤ 3 := le_of_not_gt ht
      have hb := hSmall T hT.le t hsmallt
      calc
        1 / ‖zetaC (strongMertensLogNineShift corridor.A T + t * I)‖ ≤ M := hb
        _ ≤ C * (1 + (Real.log T) ^ 7) := by
          dsimp [C]
          have hp : 0 ≤ (Real.log T) ^ 7 :=
            pow_nonneg (Real.log_nonneg (by linarith)) 7
          nlinarith [corridor.invConst_pos.le, hM]
  · intro T hT
    exact corridor.zero_free_box T hT.le

/-- Canonical existential facade.  Core contour assembly should use
`nativeInvZeta_logNine_shift_uniform_for` so all legs share the same corridor
object. -/
theorem nativeInvZeta_logNine_shift_uniform :
    ∃ A ∈ Set.Ioc (0 : ℝ) (1 / 2), ∃ C > 0,
      (∀ {T t : ℝ}, 3 < T → |t| ≤ T →
        1 / ‖zetaC (strongMertensLogNineShift A T + t * I)‖ ≤
          C * (1 + (Real.log T) ^ 7)) ∧
      (∀ {T : ℝ}, 3 < T →
        ∀ s ∈ (((Set.Icc (strongMertensLogNineShift A T) 2) ×ℂ
          (Set.Icc (-T) T)) \ {(1 : ℂ)}), zetaC s ≠ 0) := by
  let corridor : StrongMertensLogNineCorridor := strongMertensLogNineCorridor
  obtain ⟨C, hC, hInv, hZero⟩ := nativeInvZeta_logNine_shift_uniform_for corridor
  exact ⟨corridor.A, corridor.A_mem, C, hC, hInv, hZero⟩

/-! ## The logarithmic tail kernel -/

/-- Pointwise domination of the logarithmic tail by an integrable power tail.
This is kept separate so both the quantitative tail bound and the M1 proof use
exactly the same domination inequality. -/
private lemma nativeLogSqOverTSq_pointwise :
    ∃ C > 0, ∀ t : ℝ, 3 ≤ t →
      (Real.log t)^2 / t^2 ≤ C / t^(3/2 : ℝ) := by
  have h_log_sq_le_sqrt :
      ∃ C > 0, ∀ t : ℝ, 3 ≤ t → Real.log t ^ 2 ≤ C * t ^ (1 / 2 : ℝ) := by
    refine ⟨16, by norm_num, ?_⟩
    intro t ht
    have hlog : Real.log t ≤ 4 * t ^ (1 / 4 : ℝ) := by
      have h := Real.log_le_sub_one_of_pos
        (by positivity : 0 < t ^ (1 / 4 : ℝ))
      rw [Real.log_rpow (by positivity)] at h
      linarith
    have hsq := pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog 2
    have hrpow : (t ^ (1 / 4 : ℝ)) ^ 2 = t ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    calc
      Real.log t ^ 2 ≤ (4 * t ^ (1 / 4 : ℝ)) ^ 2 := hsq
      _ = 16 * (t ^ (1 / 4 : ℝ)) ^ 2 := by ring
      _ = 16 * t ^ (1 / 2 : ℝ) := by rw [hrpow]
  obtain ⟨C, hC, hCb⟩ := h_log_sq_le_sqrt
  refine ⟨C, hC, ?_⟩
  intro t ht
  rw [div_le_div_iff₀] <;> try positivity
  convert mul_le_mul_of_nonneg_right (hCb t ht)
    (Real.rpow_nonneg (by linarith : 0 ≤ t) (3 / 2)) using 1
  rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
  norm_num

/-- The log-square over square kernel is integrable on every positive tail
starting beyond three. -/
lemma nativeLogSqOverTSq_integrableOn_Ici {T : ℝ} (hT : 3 < T) :
    IntegrableOn (fun t : ℝ => (Real.log t)^2 / t^2) (Set.Ici T) := by
  obtain ⟨C, hC, hCb⟩ := nativeLogSqOverTSq_pointwise
  have hpowIoi : IntegrableOn (fun t : ℝ => t ^ (-3 / 2 : ℝ)) (Set.Ioi T) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by linarith)
  have hpowIci : IntegrableOn (fun t : ℝ => t ^ (-3 / 2 : ℝ)) (Set.Ici T) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hpowIoi
  have hdom : IntegrableOn (fun t : ℝ => C / t ^ (3 / 2 : ℝ)) (Set.Ici T) := by
    apply IntegrableOn.congr_fun (hpowIci.const_mul C) ?_ measurableSet_Ici
    intro t ht
    simp only
    rw [show (-3 / 2 : ℝ) = -(3 / 2) by ring,
      Real.rpow_neg (by linarith [Set.mem_Ici.mp ht])]
    simp only [div_eq_mul_inv]
  have hMeas : AEStronglyMeasurable (fun t : ℝ => Real.log t ^ 2 / t ^ 2)
      (volume.restrict (Set.Ici T)) :=
    ((Real.measurable_log.pow_const 2).div
      (measurable_id.pow_const 2)).aestronglyMeasurable
  apply hdom.mono' hMeas
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  have ht3 : 3 ≤ t := by linarith [Set.mem_Ici.mp ht]
  have hnonneg : 0 ≤ Real.log t ^ 2 / t ^ 2 := by positivity
  rw [Real.norm_of_nonneg hnonneg]
  exact hCb t ht3

/-- The reflected log-square kernel is integrable on every negative tail. -/
lemma nativeLogSqOverTSq_integrableOn_Iic_neg {T : ℝ} (hT : 3 < T) :
    IntegrableOn (fun t : ℝ => (Real.log (-t))^2 / (-t)^2) (Set.Iic (-T)) := by
  have hneg := (nativeLogSqOverTSq_integrableOn_Ici hT).comp_neg
  have hset : -Set.Ici T = Set.Iic (-T) := by
    ext x
    simp
  rw [hset] at hneg
  exact hneg

/-- A convenient quantitative tail bound for the logarithmic kernel. -/
lemma nativeIntegralLogSqOverTSqBound : ∃ C > 0, ∀ T, 3 < T →
    ∫ t in Set.Ici T, (Real.log t)^2 / t^2 ≤ C / Real.sqrt T := by
  obtain ⟨C, hC, hCb⟩ := nativeLogSqOverTSq_pointwise
  refine ⟨C * 2, by positivity, ?_⟩
  intro T hT
  have hint : ∫ t in Set.Ici T, t ^ (-3 / 2 : ℝ) = 2 / Real.sqrt T := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt] <;>
      norm_num
    · rw [Real.sqrt_eq_rpow, Real.rpow_neg] <;> ring_nf
      linarith
    · linarith
  have hCint : ∫ t in Set.Ici T, C / t^(3/2 : ℝ) = C * 2 / Real.sqrt T := by
    convert congrArg (fun x => C * x) hint using 1 <;> ring_nf
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun x hx => ?_
    rw [← Real.rpow_neg (by linarith [Set.mem_Ici.mp hx])]
    ring_nf
  have hdom : IntegrableOn (fun t : ℝ => C / t ^ (3 / 2 : ℝ)) (Set.Ici T) := by
    have hpowIoi : IntegrableOn (fun t : ℝ => t ^ (-3 / 2 : ℝ)) (Set.Ioi T) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by linarith)
    have hpowIci : IntegrableOn (fun t : ℝ => t ^ (-3 / 2 : ℝ)) (Set.Ici T) :=
      (integrableOn_Ici_iff_integrableOn_Ioi).2 hpowIoi
    apply IntegrableOn.congr_fun (hpowIci.const_mul C) ?_ measurableSet_Ici
    intro t ht
    simp only
    rw [show (-3 / 2 : ℝ) = -(3 / 2) by ring,
      Real.rpow_neg (by linarith [Set.mem_Ici.mp ht])]
    simp only [div_eq_mul_inv]
  refine (MeasureTheory.setIntegral_mono_on
    (nativeLogSqOverTSq_integrableOn_Ici hT) hdom measurableSet_Ici
    (fun t ht => hCb t (by linarith [ht.out]))).trans ?_
  exact le_of_eq hCint

/-- The quantitative positive-tail estimate reflected to the negative axis. -/
lemma nativeIntegralNegLogSqOverTSqBound : ∃ C > 0, ∀ T, 3 < T →
    ∫ t in Set.Iic (-T), (Real.log (-t))^2 / (-t)^2 ≤ C / Real.sqrt T := by
  obtain ⟨C, hC, hpos⟩ := nativeIntegralLogSqOverTSqBound
  refine ⟨C, hC, ?_⟩
  intro T hT
  calc
    ∫ t in Set.Iic (-T), (Real.log (-t))^2 / (-t)^2 =
        ∫ t in Set.Ioi T, (Real.log t)^2 / t^2 := by
      simpa only [neg_neg] using
        (integral_comp_neg_Iic (-T) (fun t : ℝ => (Real.log t)^2 / t^2))
    _ = ∫ t in Set.Ici T, (Real.log t)^2 / t^2 := by
      rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    _ ≤ C / Real.sqrt T := hpos T hT

/-! ## Quantitative five-leg estimates -/

/-- Right-tail pointwise bound from `ZetaInvBound2`.  We deliberately enlarge
the fractional powers to ordinary logarithms so the existing log-square tail
integral can be reused. -/
theorem nativeMertensFarTail_pointwise {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0, ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 →
      3 < X → 3 < T → ∀ t : ℝ, t ≤ -T →
      ‖nativeSmoothedMobiusIntegrand f eps X
          ((1 + (Real.log X)⁻¹) + t * I)‖ ≤
        C * (X * Real.log X / eps) * (Real.log (-t)) ^ 2 / (-t) ^ 2 := by
  obtain ⟨Cz, hCz, hZ⟩ := ZetaInvBound2
  obtain ⟨Cm, hCm, hMel⟩ := MellinOfSmooth1b hdiff hsupp
  refine ⟨8 * Cz * Cm * Real.exp 1, by positivity, ?_⟩
  intro eps X T heps hX hT t ht
  have hXpos : 0 < X := by linarith
  have htneg : t < 0 := by linarith
  have habs : |t| = -t := abs_of_neg htneg
  have hlogX : 1 < Real.log X := logt_gt_one hX.le
  have hlogt : 1 < Real.log (-t) := by
    apply logt_gt_one
    rw [← habs]
    linarith
  have hlogXpos : 0 < Real.log X := by linarith
  have hlogXinv : 0 < (Real.log X)⁻¹ := inv_pos.mpr hlogXpos
  let sigma : ℝ := 1 + (Real.log X)⁻¹
  have hsigma : sigma ∈ Set.Ioc (1 : ℝ) 2 := by
    dsimp [sigma]
    constructor
    · linarith
    · have : (Real.log X)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlogX.le
      linarith
  have hzb := hZ hsigma t (by rw [habs]; linarith)
  have hxfrac : ((Real.log X)⁻¹) ^ (-(3 : ℝ) / 4) ≤ Real.log X := by
    rw [show (-(3 : ℝ) / 4) = -((3 : ℝ) / 4) by ring,
      Real.rpow_neg hlogXinv.le, Real.inv_rpow hlogXpos.le, inv_inv]
    exact Real.rpow_le_self_of_one_le hlogX.le (by norm_num)
  have htfrac : (Real.log |t|) ^ ((1 : ℝ) / 4) ≤ Real.log (-t) := by
    rw [habs]
    exact Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
  have hlogabs_nonneg : 0 ≤ Real.log |t| := by
    rw [habs]
    linarith
  have htfrac_nonneg : 0 ≤ (Real.log |t|) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg hlogabs_nonneg _
  have hzb' : 1 / ‖zetaC ((sigma : ℂ) + t * I)‖ ≤
      Cz * Real.log X * Real.log (-t) := by
    calc
      1 / ‖zetaC ((sigma : ℂ) + t * I)‖
          ≤ Cz * (((Real.log X)⁻¹) ^ (-(3 : ℝ) / 4)) *
              (Real.log |t|) ^ ((1 : ℝ) / 4) := by simpa [sigma] using hzb
      _ ≤ Cz * Real.log X * Real.log (-t) := by
        gcongr
  let s : ℂ := (sigma : ℂ) + t * I
  have hsre : s.re = sigma := by simp [s]
  have hMelS := hMel (1/2) (by norm_num) s (by
      rw [hsre]
      dsimp [sigma]
      linarith) (by
      rw [hsre]
      exact hsigma.2) eps heps.1 heps.2
  have hXs : ‖(X : ℂ) ^ s‖ = X * Real.exp 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos, hsre]
    dsimp [sigma]
    rw [Real.rpow_add hXpos, Real.rpow_one,
      Real.rpow_inv_log (by linarith) (ne_of_gt (by linarith))]
  have hnorm2 : (-t) ^ 2 ≤ ‖s‖ ^ 2 := by
    have hnsq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [hnsq, hsre]
    have hsim : s.im = t := by simp [s]
    rw [hsim]
    nlinarith [sq_nonneg sigma]
  have hsarg : (1 : ℂ) + ((Real.log X)⁻¹ : ℝ) + (t : ℂ) * I = s := by
    simp [s, sigma]
  rw [nativeSmoothedMobiusIntegrand_norm_eq, hsarg, hXs]
  have htpos : 0 < -t := by linarith
  have hsqpos : 0 < (-t) ^ 2 := sq_pos_of_pos htpos
  have hinv : (‖s‖ ^ 2)⁻¹ ≤ ((-t) ^ 2)⁻¹ := by
    apply inv_anti₀ hsqpos
    exact hnorm2
  calc
    1 / ‖zetaC s‖ *
        ‖mellin (fun x => (Smooth1 f eps x : ℂ)) s‖ *
        (X * Real.exp 1)
      ≤ (Cz * Real.log X * Real.log (-t)) *
          (Cm * (eps * ‖s‖ ^ 2)⁻¹) * (X * Real.exp 1) := by
        gcongr
    _ ≤ (Cz * Real.log X * Real.log (-t)) *
          (Cm * (eps⁻¹ * ((-t) ^ 2)⁻¹)) * (X * Real.exp 1) := by
        have hepsinv : 0 ≤ eps⁻¹ := inv_nonneg.mpr heps.1.le
        have hkernel :
            (eps * ‖s‖ ^ 2)⁻¹ ≤ eps⁻¹ * ((-t) ^ 2)⁻¹ := by
          rw [mul_inv]
          exact mul_le_mul_of_nonneg_left hinv hepsinv
        have hleft : 0 ≤ Cz * Real.log X * Real.log (-t) := by positivity
        have hright : 0 ≤ X * Real.exp 1 := by positivity
        have hmid :
            Cm * (eps * ‖s‖ ^ 2)⁻¹ ≤
              Cm * (eps⁻¹ * ((-t) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hkernel hCm.le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmid hleft) hright
    _ = Cz * Cm * Real.exp 1 * (X * Real.log X / eps) *
          Real.log (-t) / (-t) ^ 2 := by
        field_simp [ne_of_gt heps.1, ne_of_gt htpos]
    _ ≤ Cz * Cm * Real.exp 1 * (X * Real.log X / eps) *
          (Real.log (-t)) ^ 2 / (-t) ^ 2 := by
        have hlog_le_sq : Real.log (-t) ≤ (Real.log (-t)) ^ 2 := by
          have hlogt : 1 < Real.log (-t) := by
            apply logt_gt_one
            linarith
          nlinarith [sq_nonneg (Real.log (-t) - 1)]
        rw [div_le_div_iff₀ hsqpos hsqpos]
        have hnum : 0 ≤ X * Real.log X :=
          mul_nonneg hXpos.le hlogXpos.le
        have hratio : 0 ≤ X * Real.log X / eps :=
          div_nonneg hnum heps.1.le
        have hcoeff :
            0 ≤ Cz * Cm * Real.exp 1 * (X * Real.log X / eps) :=
          mul_nonneg
            (mul_nonneg (mul_nonneg hCz.le hCm.le) (Real.exp_pos 1).le)
            hratio
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog_le_sq hcoeff) hsqpos.le
    _ ≤ 8 * (Cz * Cm * Real.exp 1 * (X * Real.log X / eps) *
          (Real.log (-t)) ^ 2 / (-t) ^ 2) := by
        have hnum : 0 ≤ X * Real.log X :=
          mul_nonneg hXpos.le hlogXpos.le
        have hratio : 0 ≤ X * Real.log X / eps :=
          div_nonneg hnum heps.1.le
        have hprefix :
            0 ≤ Cz * Cm * Real.exp 1 * (X * Real.log X / eps) :=
          mul_nonneg
            (mul_nonneg (mul_nonneg hCz.le hCm.le) (Real.exp_pos 1).le)
            hratio
        have hbase : 0 ≤ Cz * Cm * Real.exp 1 *
            (X * Real.log X / eps) * (Real.log (-t)) ^ 2 / (-t) ^ 2 :=
          div_nonneg
            (mul_nonneg hprefix (sq_nonneg (Real.log (-t))))
            (sq_nonneg (-t))
        nlinarith
    _ = 8 * Cz * Cm * Real.exp 1 * (X * Real.log X / eps) *
          (Real.log (-t)) ^ 2 / (-t) ^ 2 := by ring

/-- Norm estimate for the lower right-line tail before applying the contour
normalization factor.  Keeping this as its own declaration prevents the
integrability and integral-comparison proof from sharing a heartbeat budget
with the final algebraic normalization. -/
private lemma nativeMertensM1_integral_norm_bound {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0, ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 →
      3 < X → 3 < T →
      ‖∫ t in Set.Iic (-T), nativeSmoothedMobiusIntegrand f eps X
          ((1 + (Real.log X)⁻¹) + t * I)‖ ≤
        C * (X * Real.log X / (eps * Real.sqrt T)) := by
  obtain ⟨C1, hC1, hpw⟩ := nativeMertensFarTail_pointwise hsupp hdiff
  obtain ⟨C2, hC2, hint⟩ := nativeIntegralNegLogSqOverTSqBound
  refine ⟨C1 * C2, by positivity, ?_⟩
  intro eps X T heps hX hT
  have hInt : IntegrableOn (fun t : ℝ => (Real.log (-t))^2 / (-t)^2)
      (Set.Iic (-T)) := nativeLogSqOverTSq_integrableOn_Iic_neg hT
  have hscaled : IntegrableOn
      (fun t : ℝ => C1 * (X * Real.log X / eps) *
        ((Real.log (-t))^2 / (-t)^2)) (Set.Iic (-T)) := by
    simpa only [mul_assoc] using hInt.const_mul (C1 * (X * Real.log X / eps))
  calc
    ‖∫ t in Set.Iic (-T), nativeSmoothedMobiusIntegrand f eps X
        ((1 + (Real.log X)⁻¹) + t * I)‖
      ≤ ∫ t in Set.Iic (-T), ‖nativeSmoothedMobiusIntegrand f eps X
        ((1 + (Real.log X)⁻¹) + t * I)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Iic (-T),
        C1 * (X * Real.log X / eps) * ((Real.log (-t)) ^ 2 / (-t) ^ 2) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
      · exact hscaled
      · filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
        simpa only [mul_div_assoc] using hpw heps hX hT t ht
    _ = C1 * (X * Real.log X / eps) *
        (∫ t in Set.Iic (-T), (Real.log (-t))^2 / (-t)^2) := by
      rw [← MeasureTheory.integral_const_mul]
    _ ≤ C1 * (X * Real.log X / eps) * (C2 / Real.sqrt T) := by
      apply mul_le_mul_of_nonneg_left (hint T hT)
      have hX0 : 0 ≤ X := by linarith
      have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
      exact mul_nonneg hC1.le
        (div_nonneg (mul_nonneg hX0 hlogX0) heps.1.le)
    _ = C1 * C2 * (X * Real.log X / (eps * Real.sqrt T)) := by
      field_simp

/-- Lower far-tail bound. -/
theorem nativeMertensM1_logNine_bound {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0, ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 →
      3 < X → 3 < T →
      ‖nativeMertensContourM1 f eps X T‖ ≤
        C * (X * Real.log X / (eps * Real.sqrt T)) := by
  obtain ⟨C0, hC0, htail⟩ := nativeMertensM1_integral_norm_bound hsupp hdiff
  refine ⟨C0 / (2 * Real.pi), by positivity, ?_⟩
  intro eps X T heps hX hT
  unfold nativeMertensContourM1
  have hpref : ‖(1 / (2 * (Real.pi : ℂ) * I)) * I‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * (Real.pi : ℂ) * I)) * I = 1 / (2 * (Real.pi : ℂ)) by field_simp,
      norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      show ‖(Real.pi : ℂ)‖ = Real.pi from
        (RCLike.norm_ofReal _).trans (abs_of_pos Real.pi_pos)]
  rw [show (1 / (2 * (Real.pi : ℂ) * I)) * (I * ∫ t in Set.Iic (-T),
      nativeSmoothedMobiusIntegrand f eps X ((1 + (Real.log X)⁻¹) + t * I)) =
      ((1 / (2 * (Real.pi : ℂ) * I)) * I) *
        (∫ t in Set.Iic (-T), nativeSmoothedMobiusIntegrand f eps X
          ((1 + (Real.log X)⁻¹) + t * I)) by ring,
    norm_mul, hpref]
  calc
    1 / (2 * Real.pi) * ‖∫ t in Set.Iic (-T),
        nativeSmoothedMobiusIntegrand f eps X
          ((1 + (Real.log X)⁻¹) + t * I)‖
      ≤ 1 / (2 * Real.pi) *
          (C0 * (X * Real.log X / (eps * Real.sqrt T))) := by
        gcongr
        exact htail heps hX hT
    _ = C0 / (2 * Real.pi) *
          (X * Real.log X / (eps * Real.sqrt T)) := by ring

/-- Conjugation symmetry for the Mobius integrand. -/
theorem nativeSmoothedMobiusIntegrand_conj {f : ℝ → ℝ} {eps X : ℝ}
    (hX : 0 < X) (s : ℂ) :
    nativeSmoothedMobiusIntegrand f eps X (starRingEnd ℂ s) =
      starRingEnd ℂ (nativeSmoothedMobiusIntegrand f eps X s) := by
  unfold nativeSmoothedMobiusIntegrand strongMertensSmoothedIntegrand
  have hmellin :
      mellin (fun x => (Smooth1 f eps x : ℂ)) (starRingEnd ℂ s) =
        starRingEnd ℂ (mellin (fun x => (Smooth1 f eps x : ℂ)) s) := by
    unfold mellin
    rw [← integral_conj]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
    congr 1
    nth_rw 1 [← map_one (starRingEnd ℂ)]
    rw [← map_sub, Complex.cpow_conj, Complex.conj_ofReal]
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  have hcpow :
      (X : ℂ) ^ (starRingEnd ℂ s) = starRingEnd ℂ ((X : ℂ) ^ s) := by
    rw [Complex.cpow_conj, Complex.conj_ofReal]
    rw [Complex.arg_ofReal_of_nonneg hX.le]
    exact Real.pi_ne_zero.symm
  rw [map_mul, map_mul, map_inv₀, riemannZeta_conj, hmellin, hcpow]

/-- Upper far-tail bound, by conjugation. -/
theorem nativeMertensM5_logNine_bound {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0, ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 →
      3 < X → 3 < T →
      ‖nativeMertensContourM5 f eps X T‖ ≤
        C * (X * Real.log X / (eps * Real.sqrt T)) := by
  obtain ⟨C, hC, hM1⟩ := nativeMertensM1_logNine_bound hsupp hdiff
  refine ⟨C, hC, ?_⟩
  intro eps X T heps hX hT
  have hXpos : 0 < X := by linarith
  have hconj : nativeMertensContourM5 f eps X T =
      starRingEnd ℂ (nativeMertensContourM1 f eps X T) := by
    unfold nativeMertensContourM1 nativeMertensContourM5
    simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
    rw [neg_mul, mul_neg, ← neg_mul]
    congr 1
    · ring
    · rw [← integral_conj, ← integral_comp_neg_Ioi, integral_Ici_eq_integral_Ioi]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hc := nativeSmoothedMobiusIntegrand_conj
        (f := f) (eps := eps) (X := X) hXpos
        ((1 + (Real.log X)⁻¹) + (-x) * I)
      simpa using hc
  rw [hconj, RCLike.norm_conj]
  exact hM1 heps hX hT

-- The horizontal legs are bounded in `StrongMertensLogNineHorizontal`, which
-- splits pointwise at the right edge of the shared PNT+ log-nine window.

end RHLean.Analysis
