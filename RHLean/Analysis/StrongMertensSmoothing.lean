import RHLean.Analysis.StrongMertensSmoothingFinite

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset Topology Asymptotics Complex Real MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius LSeries.notation

namespace RHLean.Analysis

-- `StrongPNT.PNT1_ComplexAnalysis` declares a root-level `def I := Complex.I`,
-- so with `Complex` open the bare token `I` resolves two ways.
local notation "I" => Complex.I
theorem strongMertens_lseriesSummable_moebius {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (μ n : ℂ)) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    (fun n _ => by
      simp only [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one) hs

/-- Sum-integral interchange used by the Mobius Perron identity. -/
theorem strongMertens_smoothedMobius_aux_tsum_integral
    {SmoothingF : ℝ → ℝ}
    (diffF : ContDiff ℝ 1 SmoothingF)
    (nonnegF : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (massF : ∫ x in Set.Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {eps : ℝ} (eps_pos : 0 < eps)
    (eps_lt_one : eps < 1) {sigma : ℝ} (sigma_gt : 1 < sigma) (sigma_le : sigma ≤ 2) :
    ∫ t : ℝ, ∑' n : ℕ, (μ n : ℂ) / (n : ℂ) ^ (sigma + t * I) *
        mellin (fun x => (Smooth1 SmoothingF eps x : ℂ)) (sigma + t * I) *
        (X : ℂ) ^ (sigma + t * I) =
      ∑' n : ℕ, ∫ t : ℝ, (μ n : ℂ) / (n : ℂ) ^ (sigma + t * I) *
        mellin (fun x => (Smooth1 SmoothingF eps x : ℂ)) (sigma + t * I) *
        (X : ℂ) ^ (sigma + t * I) := by
  have abs_two : ∀ a : ℝ, ∀ i : ℕ,
      ‖(i : ℂ) ^ ((sigma : ℂ) + (a : ℂ) * I)‖₊ = i ^ sigma := by
    intro a i
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp; linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero,
      Real.toNNReal_of_nonneg (rpow_nonneg (Nat.cast_nonneg i) _)]
    apply NNReal.eq
    norm_cast
  rw [MeasureTheory.integral_tsum]
  · intro i
    by_cases hi : i = 0
    · simpa [hi] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      have hcont : Continuous fun a : ℝ =>
          mellin (fun x => (Smooth1 SmoothingF eps x : ℂ))
            (sigma + (a : ℂ) * I) := by
        rw [← continuousOn_univ]
        refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re})
        · refine continuousOn_of_forall_continuousAt ?_
          intro z hz
          exact (Smooth1MellinDifferentiable diffF suppF ⟨eps_pos, eps_lt_one⟩
            nonnegF massF hz).continuousAt
        · fun_prop
        · simp; linarith
      fun_prop (disch := simp [hi, X_pos.ne'])
  · rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ sigma).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top
    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]
    rw [ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top
    · rw [lt_top_iff_ne_top]
      have hsumm : Summable (fun i : ℕ => ‖(μ i : ℂ)‖₊ / (i : NNReal) ^ sigma) := by
        apply NNReal.summable_coe.mp
        have h := (strongMertens_lseriesSummable_moebius (s := sigma)
          (by simp; linarith)).norm
        apply h.congr
        intro n
        rw [LSeries.term_def]
        split_ifs with hn
        · simp [hn]
        · rw [NNReal.coe_div]
          simp only [coe_nnnorm, NNReal.coe_rpow, NNReal.coe_natCast]
          rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega), Complex.ofReal_re]
      exact (ENNReal.tsum_coe_ne_top_iff_summable).mpr hsumm
    · exact MeasureTheory.hasFiniteIntegral_iff_enorm.mp
        (SmoothedChebyshevDirichlet_aux_integrable diffF nonnegF suppF massF
          eps_pos eps_lt_one sigma_gt sigma_le).hasFiniteIntegral

/-- Perron-to-Dirichlet identity for the native smoothed Mobius transform. -/
theorem strongMertens_smoothedMobius_dirichlet
    {SmoothingF : ℝ → ℝ}
    (diffF : ContDiff ℝ 1 SmoothingF)
    (nonnegF : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (massF : ∫ x in Set.Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X : ℝ} (X_gt : 3 < X) {eps : ℝ} (eps_pos : 0 < eps) (eps_lt_one : eps < 1) :
    nativeSmoothedMobius SmoothingF eps X =
      ∑' n : ℕ, (μ n : ℂ) * Smooth1 SmoothingF eps ((n : ℝ) / X) := by
  dsimp [nativeSmoothedMobius, strongMertensSmoothedMobius,
    nativeSmoothedMobiusIntegrand, strongMertensSmoothedIntegrand,
    VerticalIntegral', VerticalIntegral]
  set sigma : ℝ := 1 + (Real.log X)⁻¹
  have hlog : 1 < Real.log X := logt_gt_one X_gt.le
  have sigma_gt : 1 < sigma := by
    dsimp [sigma]
    have : 0 < (Real.log X)⁻¹ := by positivity
    linarith
  have sigma_le : sigma ≤ 2 := by
    dsimp [sigma]
    have : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlog
    linarith
  calc
    _ = 1 / (2 * Real.pi * I) * (I * ∫ t : ℝ, ∑' n : ℕ,
        (μ n : ℂ) / (n : ℂ) ^ (sigma + (t : ℂ) * I) *
        mellin (fun x => (Smooth1 SmoothingF eps x : ℂ)) (sigma + (t : ℂ) * I) *
        (X : ℂ) ^ (sigma + (t : ℂ) * I)) := by
      congr 2
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      rw [show (riemannZeta (sigma + (t : ℂ) * I))⁻¹ =
          ∑' n : ℕ, (μ n : ℂ) / (n : ℂ) ^ (sigma + (t : ℂ) * I) from by
        rw [← nativeLSeries_moebius_eq_inv_zeta (by simp [sigma_gt])]
        dsimp only [LSeries, LSeries.term]
        apply tsum_congr
        intro n
        by_cases hn : n = 0 <;> simp [hn]]
      rw [← tsum_mul_right, ← tsum_mul_right]
    _ = 1 / (2 * Real.pi * I) * (I * ∑' n : ℕ, ∫ t : ℝ,
        (μ n : ℂ) / (n : ℂ) ^ (sigma + (t : ℂ) * I) *
        mellin (fun x => (Smooth1 SmoothingF eps x : ℂ)) (sigma + (t : ℂ) * I) *
        (X : ℂ) ^ (sigma + (t : ℂ) * I)) := by
      congr 2
      exact strongMertens_smoothedMobius_aux_tsum_integral diffF nonnegF suppF massF
        (by linarith) eps_pos eps_lt_one sigma_gt sigma_le
    _ = 1 / (2 * Real.pi * I) * (I * ∑' n : ℕ, (μ n : ℂ) * ∫ t : ℝ,
        mellin (fun x => (Smooth1 SmoothingF eps x : ℂ)) (sigma + (t : ℂ) * I) *
          (X / (n : ℂ)) ^ (sigma + (t : ℂ) * I)) := by
      field_simp
      congr 2
      ext n
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      ext t
      by_cases hn : n = 0
      · simp [hn]
      rw [mul_div_assoc, mul_assoc]
      congr 1
      rw [(div_eq_iff (by simp [hn])).mpr]
      have hcp := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ))
        (r := sigma + I * t) (by positivity) (by positivity)
      push_cast at hcp ⊢
      rw [← hcp, div_mul_cancel₀]
      simp [hn]
    _ = 1 / (2 * Real.pi) * (∑' n : ℕ, (μ n : ℂ) * ∫ t : ℝ,
        mellin (fun x => (Smooth1 SmoothingF eps x : ℂ)) (sigma + (t : ℂ) * I) *
          (X / (n : ℂ)) ^ (sigma + (t : ℂ) * I)) := by
      field_simp
    _ = ∑' n : ℕ, (μ n : ℂ) * (1 / (2 * Real.pi) * ∫ t : ℝ,
        mellin (fun x => (Smooth1 SmoothingF eps x : ℂ)) (sigma + (t : ℂ) * I) *
          (X / (n : ℂ)) ^ (sigma + (t : ℂ) * I)) := by
      simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
    _ = ∑' n : ℕ, (μ n : ℂ) * (1 / (2 * Real.pi) * ∫ t : ℝ,
        mellin (fun x => (Smooth1 SmoothingF eps x : ℂ)) (sigma + (t : ℂ) * I) *
          ((n : ℂ) / X) ^ (-(sigma + (t : ℂ) * I))) := by
      congr 1
      ext n
      congr 2
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      have ht : -(sigma + t * I) = (-1) * (sigma + t * I) := by simp
      have hn : ((n : ℂ) / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
      have hdiv_nonneg : 0 ≤ (n : ℝ) / X :=
        div_nonneg (Nat.cast_nonneg n) (by linarith)
      have hlogim : (Complex.log ((n : ℂ) / (X : ℂ))).im = 0 := by
        simp [Complex.log_im, arg_eq_zero_iff, hdiv_nonneg]
      have hpow : ((n : ℂ) / X) ^ ((-1 : ℂ) * (sigma + t * I)) =
          (((n : ℂ) / X) ^ (-1 : ℂ)) ^ (sigma + t * I) := by
        rw [cpow_mul] <;> simp [hlogim, Real.pi_pos, Real.pi_nonneg]
      rw [ht, hpow, hn]
    _ = _ := by
      congr 1
      ext n
      by_cases hn : n = 0
      · simp [hn]
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      congr 1
      -- Mathlib 4.24 spells this `mellin_inversion`.
      have hinv := mellin_inversion sigma
        (f := fun x => (Smooth1 SmoothingF eps x : ℂ)) (x := (n : ℝ) / X)
        (div_pos (by exact_mod_cast hnpos) (by linarith))
        (by
          apply Smooth1MellinConvergent diffF suppF ⟨eps_pos, eps_lt_one⟩ nonnegF massF
          simp
          linarith)
        (by
          dsimp [VerticalIntegrable]
          exact SmoothedChebyshevDirichlet_aux_integrable diffF nonnegF suppF massF
            eps_pos eps_lt_one sigma_gt sigma_le)
        (by
          refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
          exact Smooth1ContinuousAt diffF nonnegF suppF eps_pos (by positivity))
      beta_reduce at hinv
      dsimp [mellinInv, VerticalIntegral] at hinv
      convert hinv using 4 <;> try norm_cast
      rw [mul_comm]

/-- The native smoothed transform differs from the sharp real Mertens sum by
`O(eps * X)`. -/
theorem strongMertens_smoothed_close_eps
    {SmoothingF : ℝ → ℝ}
    (diffF : ContDiff ℝ 1 SmoothingF)
    (suppF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (nonnegF : ∀ x > 0, 0 ≤ SmoothingF x)
    (massF : ∫ x in Set.Ioi (0 : ℝ), SmoothingF x / x = 1) :
    ∃ C > 0, ∀ X : ℝ, 3 < X → ∀ eps : ℝ, 0 < eps → eps < 1 → 2 < X * eps →
      ‖nativeSmoothedMobius SmoothingF eps X - (nativeMertensSharpReal X : ℂ)‖ ≤
        C * eps * X := by
  obtain ⟨c1, c1_pos, c1_eq, hc1⟩ := Smooth1Properties_below suppF massF
  obtain ⟨c2, c2_pos, c2_eq, hc2⟩ := Smooth1Properties_above suppF
  have c1_lt : c1 < 1 := by
    rw [c1_eq]
    exact Real.log_two_lt_d9.trans (by norm_num)
  have c2_lt : c2 < 2 := by
    rw [c2_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    · rfl
    · exact Real.log_two_lt_d9.trans (by norm_num)
    · exact Real.log_nonneg (by norm_num)
    · positivity
  let C : ℝ := 6 * (3 * c1 + c2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro X hX eps heps heps1 hXeps
  have hXpos : 0 < X := by linarith
  have ndivpos {n : ℕ} (hn : 0 < n) : 0 < (n : ℝ) / X := by positivity
  have hsle (n : ℕ) (hn : 0 < n) : Smooth1 SmoothingF eps ((n : ℝ) / X) ≤ 1 :=
    Smooth1LeOne nonnegF massF heps (ndivpos hn)
  have hsnonneg (n : ℕ) (hn : 0 < n) : 0 ≤ Smooth1 SmoothingF eps ((n : ℝ) / X) :=
    Smooth1Nonneg nonnegF (ndivpos hn) heps
  have hseq1 (n : ℕ) (hn : 0 < n) (hle : (n : ℝ) ≤ X * (1 - c1 * eps)) :
      Smooth1 SmoothingF eps ((n : ℝ) / X) = 1 := by
    apply hc1 eps ((n : ℝ) / X) heps (ndivpos hn)
    exact (div_le_iff₀' hXpos).mpr hle
  have hseq0 (n : ℕ) (hle : 1 + c2 * eps ≤ (n : ℝ) / X) :
      Smooth1 SmoothingF eps ((n : ℝ) / X) = 0 :=
    hc2 eps ((n : ℝ) / X) ⟨heps, heps1⟩ hle
  have hb1 : 1 ≤ X * eps * c1 := by
    have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [c1_eq, ← div_le_iff₀ hlogpos]
    have htwo : 1 / Real.log 2 < 2 := by
      rw [div_lt_iff₀ hlogpos]
      have hl := Real.log_two_gt_d9
      nlinarith
    exact (le_of_lt htwo).trans (le_of_lt hXeps)
  have hb2 : 1 ≤ X * eps * c2 := by
    have hden : 0 < 2 * Real.log 2 := by positivity
    rw [c2_eq, ← div_le_iff₀ hden]
    have htwo : 1 / (2 * Real.log 2) < 2 := by
      rw [div_lt_iff₀ hden]
      have hl := Real.log_two_gt_d9
      nlinarith
    exact (le_of_lt htwo).trans (le_of_lt hXeps)
  rw [strongMertens_smoothedMobius_dirichlet diffF nonnegF suppF massF hX heps heps1]
  have hsum_real : (∑' n : ℕ, (μ n : ℂ) * Smooth1 SmoothingF eps ((n : ℝ) / X)) =
      ((∑' n : ℕ, (μ n : ℝ) * Smooth1 SmoothingF eps ((n : ℝ) / X) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    push_cast
    ring
  rw [hsum_real]
  exact strongMertens_smoothed_close_aux SmoothingF c1 c1_pos c1_lt c2 c2_pos c2_lt hc2
    C rfl eps heps heps1 X hXpos hX hb1 hb2 hsle hsnonneg hseq1 hseq0

end RHLean.Analysis
