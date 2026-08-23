import RHLean.Analysis.StrongMertensLogNineHorizontal

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset Topology Asymptotics Complex Real MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius LSeries.notation

namespace RHLean.Analysis

local notation "zetaC" => riemannZeta

-- `StrongPNT.PNT1_ComplexAnalysis` declares a root-level `def I := Complex.I`,
-- so with `Complex` open the bare token `I` resolves two ways.
local notation "I" => Complex.I

/-! ### The scaled Cauchy kernel

Mathlib carries the Cauchy integral only at `a = 1`
(`integral_univ_inv_one_add_sq : ∫ x, (1 + x ^ 2)⁻¹ = π`).  The shifted
vertical leg needs it at `a = sigmaLeft`, so both the integrability and the
value are obtained here by rescaling that case. -/

private theorem inv_sq_add_sq_eq {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    (a ^ 2)⁻¹ * (1 + (a⁻¹ * t) ^ 2)⁻¹ = (a ^ 2 + t ^ 2)⁻¹ := by
  have hprod : a ^ 2 * (1 + (a⁻¹ * t) ^ 2) = a ^ 2 + t ^ 2 := by
    have hcancel : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
    have hsplit : a ^ 2 * (a⁻¹ * t) ^ 2 = (a * a⁻¹) ^ 2 * t ^ 2 := by ring
    rw [mul_add, mul_one, hsplit, hcancel, one_pow, one_mul]
  rw [← mul_inv, hprod]

private theorem integrable_inv_sq_add_sq {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun t : ℝ => (a ^ 2 + t ^ 2)⁻¹) := by
  have hscaled : Integrable (fun t : ℝ => (1 + (a⁻¹ * t) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero ha)
  refine (hscaled.const_mul ((a ^ 2)⁻¹)).congr
    (Filter.Eventually.of_forall fun t => ?_)
  exact inv_sq_add_sq_eq ha t

private theorem integral_inv_sq_add_sq {a : ℝ} (ha : a ≠ 0) :
    ∫ t : ℝ, (a ^ 2 + t ^ 2)⁻¹ = Real.pi / |a| := by
  have habs : (0 : ℝ) < |a| := abs_pos.mpr ha
  have habs_ne : |a| ≠ 0 := ne_of_gt habs
  have hsq : a ^ 2 = |a| * |a| := by rw [sq, ← abs_mul_abs_self]
  calc
    ∫ t : ℝ, (a ^ 2 + t ^ 2)⁻¹
        = ∫ t : ℝ, (a ^ 2)⁻¹ * (1 + (a⁻¹ * t) ^ 2)⁻¹ := by
          simp_rw [inv_sq_add_sq_eq ha]
    _ = (a ^ 2)⁻¹ * ∫ t : ℝ, (1 + (a⁻¹ * t) ^ 2)⁻¹ :=
          MeasureTheory.integral_const_mul _ _
    _ = (a ^ 2)⁻¹ * (|(a⁻¹)⁻¹| • ∫ u : ℝ, (1 + u ^ 2)⁻¹) := by
          congr 1
          exact MeasureTheory.Measure.integral_comp_mul_left
            (fun u : ℝ => (1 + u ^ 2)⁻¹) a⁻¹
    _ = (a ^ 2)⁻¹ * (|a| * Real.pi) := by
          rw [inv_inv, integral_univ_inv_one_add_sq, smul_eq_mul]
    _ = Real.pi / |a| := by
          rw [eq_div_iff habs_ne, hsq, mul_inv]
          have hcancel : |a|⁻¹ * |a| = 1 := inv_mul_cancel₀ habs_ne
          calc
            |a|⁻¹ * |a|⁻¹ * (|a| * Real.pi) * |a|
                = (|a|⁻¹ * |a|) * (|a|⁻¹ * |a|) * Real.pi := by ring
            _ = Real.pi := by rw [hcancel, one_mul, one_mul]

theorem nativeMertensM3_logNine_bound_for
    (corridor : StrongMertensLogNineCorridor) {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ f x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), f x / x = 1)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0,
      ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 → 3 < X → 3 < T →
        let sigmaLeft := strongMertensLogNineShift corridor.A T
        ‖nativeMertensContourM3 f eps X T sigmaLeft‖ ≤
          C * X * Real.exp (-corridor.A * Real.log X / (Real.log T)^9) *
            (1 + (Real.log T)^7) / eps := by
  obtain ⟨Cz, hCz, hInv, _hzero⟩ := nativeInvZeta_logNine_shift_uniform_for corridor
  obtain ⟨Cm, hCm, hMel⟩ := MellinOfSmooth1b hdiff hsupp
  refine ⟨4 * Cz * Cm, by positivity, ?_⟩
  intro eps X T heps hX hT
  simp only []
  let sigmaLeft : ℝ := strongMertensLogNineShift corridor.A T
  have hsigpos : 0 < sigmaLeft := by
    dsimp [sigmaLeft]
    exact corridor.shift_pos T hT.le
  have hlogTnonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hZnonneg : 0 ≤ Cz * (1 + (Real.log T)^7) := by
    exact mul_nonneg hCz.le (by positivity)
  have hpoint : ∀ t ∈ Set.Icc (-T) T,
      ‖nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I)‖ ≤
        Cz * (1 + (Real.log T)^7) *
          (Cm * (eps * (sigmaLeft^2 + t^2))⁻¹) * X^sigmaLeft := by
    intro t ht
    have habs : |t| ≤ T := abs_le.2 ht
    have hz := hInv hT habs
    let s : ℂ := (sigmaLeft : ℂ) + t * I
    have hsre : s.re = sigmaLeft := by simp [s]
    have hsigle2 : sigmaLeft ≤ 2 := by
      linarith [corridor.shift_lt_one T hT.le]
    have hM := hMel sigmaLeft hsigpos s (by rw [hsre])
      (by rw [hsre]; exact hsigle2) eps heps.1 heps.2
    have hnormsq : ‖s‖^2 = sigmaLeft^2 + t^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [s]
      ring
    rw [hnormsq] at hM
    have hz' : 1 / ‖zetaC s‖ ≤ Cz * (1 + (Real.log T)^7) := by
      simpa [s, sigmaLeft] using hz
    rw [nativeSmoothedMobiusIntegrand_norm_eq,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), hsre]
    have hprod := mul_le_mul hz' hM (norm_nonneg _) hZnonneg
    exact mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg (by linarith) _)
  have hHolo := strongMertensSmoothedIntegrand_holomorphicOn_punctured_box
    corridor heps.1 heps.2 hsupp hnonneg hmass hdiff
    (X := X) (T := T) (by linarith : 0 < X) hT.le
  have hVerticalMaps : Set.MapsTo
      (fun t : ℝ => (sigmaLeft : ℂ) + t * I)
      (Set.Icc (-T) T)
      (((Set.Icc (strongMertensLogNineShift corridor.A T) 2) ×ℂ
        Set.Icc (-T) T) \ {(1 : ℂ)}) := by
    intro t ht
    constructor
    · rw [Complex.mem_reProdIm]
      constructor
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
          I_im, mul_one, sub_self, add_zero]
        exact ⟨le_rfl, by linarith [corridor.shift_lt_one T hT.le]⟩
      · simpa using ht
    · intro heq
      have hre := congrArg Complex.re heq
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
        I_im, mul_one, sub_self, add_zero, one_re] at hre
      exact (corridor.shift_lt_one T hT.le).ne hre
  have hVerticalContinuous : ContinuousOn
      (fun t : ℝ => nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I))
      (Set.Icc (-T) T) := by
    exact ContinuousOn.comp' hHolo.continuousOn (by fun_prop) hVerticalMaps
  unfold nativeMertensContourM3
  have hpref : ‖(1 / (2 * (Real.pi : ℂ) * I)) * I‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * (Real.pi : ℂ) * I)) * I = 1 / (2 * (Real.pi : ℂ)) by field_simp,
      norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      show ‖(Real.pi : ℂ)‖ = Real.pi from (RCLike.norm_ofReal _).trans (abs_of_pos Real.pi_pos)]
  rw [show (1 / (2 * (Real.pi : ℂ) * I)) * (I * ∫ t in Set.Icc (-T) T,
      nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I)) =
      ((1 / (2 * (Real.pi : ℂ) * I)) * I) *
        (∫ t in Set.Icc (-T) T,
          nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I)) by ring,
    norm_mul, hpref]
  calc
    1 / (2 * Real.pi) * ‖∫ t in Set.Icc (-T) T,
        nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I)‖
      ≤ 1 / (2 * Real.pi) * ∫ t in Set.Icc (-T) T,
          ‖nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I)‖ := by
        gcongr
        exact norm_integral_le_integral_norm _
    _ ≤ 1 / (2 * Real.pi) *
        (Cz * (1 + (Real.log T)^7) * Cm / eps * X^sigmaLeft *
          (Real.pi / sigmaLeft)) := by
        gcongr
        calc
          ∫ t in Set.Icc (-T) T,
              ‖nativeSmoothedMobiusIntegrand f eps X (sigmaLeft + t * I)‖
            ≤ ∫ t in Set.Icc (-T) T,
              (Cz * (1 + (Real.log T)^7) * Cm / eps * X^sigmaLeft) *
                (sigmaLeft^2 + t^2)⁻¹ := by
                apply setIntegral_mono_on
                · exact hVerticalContinuous.norm.integrableOn_compact isCompact_Icc
                · exact ((integrable_inv_sq_add_sq (ne_of_gt hsigpos)).const_mul
                    (Cz * (1 + (Real.log T)^7) * Cm / eps * X^sigmaLeft)).integrableOn
                · exact measurableSet_Icc
                · intro t ht
                  have hp := hpoint t ht
                  convert hp using 1
                  field_simp [ne_of_gt heps.1]
          _ ≤ (Cz * (1 + (Real.log T)^7) * Cm / eps * X^sigmaLeft) *
                (Real.pi / sigmaLeft) := by
                rw [MeasureTheory.integral_const_mul]
                have hfull := integral_inv_sq_add_sq (ne_of_gt hsigpos)
                have hkernel :
                    ∫ t in Set.Icc (-T) T, (sigmaLeft^2+t^2)⁻¹ ≤
                      Real.pi / sigmaLeft := by
                  calc
                    ∫ t in Set.Icc (-T) T, (sigmaLeft^2+t^2)⁻¹
                      ≤ ∫ t : ℝ, (sigmaLeft^2+t^2)⁻¹ :=
                        MeasureTheory.setIntegral_le_integral
                          (integrable_inv_sq_add_sq (ne_of_gt hsigpos))
                          (Filter.Eventually.of_forall fun t =>
                            inv_nonneg.mpr (by positivity))
                    _ = Real.pi / sigmaLeft := by
                      simpa [abs_of_pos hsigpos] using hfull
                have hcoeff : 0 ≤
                    Cz * (1 + (Real.log T)^7) * Cm / eps * X^sigmaLeft := by
                  exact mul_nonneg
                    (div_nonneg (mul_nonneg hZnonneg hCm.le) heps.1.le)
                    (Real.rpow_nonneg (by linarith) _)
                exact mul_le_mul_of_nonneg_left hkernel hcoeff
    _ ≤ 4 * Cz * Cm * X *
        Real.exp (-corridor.A * Real.log X / (Real.log T)^9) *
          (1 + (Real.log T)^7) / eps := by
      have hsigInv : sigmaLeft⁻¹ ≤ 2 := by
        have hhalf : (1 : ℝ) / 2 ≤ sigmaLeft := by
          dsimp [sigmaLeft, strongMertensLogNineShift]
          have hlogT : 1 < Real.log T := logt_gt_one hT.le
          have hfrac : corridor.A / (Real.log T)^9 ≤ 1/2 := by
            apply (div_le_iff₀ (by positivity)).2
            nlinarith [corridor.A_mem.2, one_le_pow₀ (n := 9) hlogT.le]
          linarith
        rw [inv_le_comm₀ hsigpos (by norm_num)]
        nlinarith
      have hXshift := LogNineContour.rpow_logNine_shift
        (A := corridor.A) (X := X) (T := T) (by linarith : 0 < X)
      rw [show X ^ sigmaLeft =
          X * Real.exp (-corridor.A * Real.log X / (Real.log T)^9) by
        dsimp [sigmaLeft, strongMertensLogNineShift]
        exact hXshift]
      let K : ℝ := Cz * Cm * X *
        Real.exp (-corridor.A * Real.log X / (Real.log T)^9) *
          (1 + (Real.log T)^7) / eps
      have hK : 0 ≤ K := by
        dsimp [K]
        have hXnonneg : 0 ≤ X := by linarith
        have hpoly : 0 ≤ 1 + (Real.log T)^7 := by
          exact add_nonneg zero_le_one (pow_nonneg hlogTnonneg 7)
        exact div_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg hCz.le hCm.le)
                hXnonneg)
              (Real.exp_pos _).le)
            hpoly)
          heps.1.le
      have hfac : sigmaLeft⁻¹ / 2 ≤ 4 := by
        linarith
      calc
        1 / (2 * Real.pi) *
            (Cz * (1 + (Real.log T)^7) * Cm / eps *
              (X * Real.exp (-corridor.A * Real.log X / (Real.log T)^9)) *
              (Real.pi / sigmaLeft))
          = K * (sigmaLeft⁻¹ / 2) := by
              dsimp [K]
              field_simp [Real.pi_ne_zero, ne_of_gt heps.1, ne_of_gt hsigpos]
        _ ≤ K * 4 := mul_le_mul_of_nonneg_left hfac hK
        _ = 4 * Cz * Cm * X *
            Real.exp (-corridor.A * Real.log X / (Real.log T)^9) *
              (1 + (Real.log T)^7) / eps := by
              dsimp [K]
              ring

/-- Canonical existential facade for the shifted vertical estimate. -/
theorem nativeMertensM3_logNine_bound {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ f x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), f x / x = 1)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ A ∈ Set.Ioc (0 : ℝ) (1 / 2), ∃ C > 0,
      ∀ {eps X T : ℝ}, eps ∈ Set.Ioo (0 : ℝ) 1 → 3 < X → 3 < T →
        let sigmaLeft := strongMertensLogNineShift A T
        ‖nativeMertensContourM3 f eps X T sigmaLeft‖ ≤
          C * X * Real.exp (-A * Real.log X / (Real.log T)^9) *
            (1 + (Real.log T)^7) / eps := by
  let corridor : StrongMertensLogNineCorridor := strongMertensLogNineCorridor
  obtain ⟨C, hC, hBound⟩ :=
    nativeMertensM3_logNine_bound_for corridor hsupp hnonneg hmass hdiff
  exact ⟨corridor.A, corridor.A_mem, C, hC, hBound⟩

end RHLean.Analysis