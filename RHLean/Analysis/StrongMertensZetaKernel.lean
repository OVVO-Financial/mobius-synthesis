import Mathlib
import Mathlib.NumberTheory.LSeries.Dirichlet
-- `StrongPNT.PNT5_Strong` is a fork of `PrimeNumberTheoremAnd.MediumPNT` and
-- redeclares 55 of its 57 names, so no Lean environment can hold both.  This
-- route is the StrongPNT one, and the only name it needs from either --
-- `SmoothedChebyshevDirichlet_aux_integrable` -- is common to the two with the
-- same signature.
import StrongPNT.PNT5_Strong
import PrimeNumberTheoremAnd.MellinCalculus
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import RHLean.Analysis.NativePNTAxer
import RHLean.Analysis.StrongMertensLogNineCorridor

/-!
# Reciprocal-zeta kernel for the unconditional strong Mertens route

This file contains only the reusable analytic kernel.  In particular, the
literal reciprocal zeta function is used on punctured neighborhoods of `1`,
because Mathlib assigns `riemannZeta 1` a junk value.  The removable value of
`1 / zeta` at the pole is therefore handled by the residue limit rather than by
pretending the literal function is continuous there.
-/

noncomputable section

open Filter Asymptotics Finset Complex Real MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators LSeries.notation Topology

namespace RHLean.Analysis

local notation "zetaC" => riemannZeta

-- `StrongPNT.PNT1_ComplexAnalysis` declares a root-level `def I := Complex.I`,
-- so with `Complex` open the bare token `I` resolves two ways.  Fix it the way
-- the corridor and StrongPNT's own PNT5 do.
local notation "I" => Complex.I

/-- The Mobius Dirichlet series is reciprocal zeta on `Re s > 1`. -/
theorem strongMertens_LSeries_moebius_eq_inv_zeta {s : ℂ} (hs : 1 < s.re) :
    L ↗μ s = (zetaC s)⁻¹ := by
  -- Both of these live in the root namespace, not in `ArithmeticFunction`.
  have hmul := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hmul
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hmul)

/-- Smoothed Mobius Perron integrand. -/
noncomputable def strongMertensSmoothedIntegrand
    (SmoothingF : ℝ → ℝ) (epsilon X : ℝ) : ℂ → ℂ :=
  fun s => (zetaC s)⁻¹ *
    mellin (fun x => (Smooth1 SmoothingF epsilon x : ℂ)) s * (X : ℂ) ^ s

/-- Smoothed Mobius transform on the standard right Perron line. -/
noncomputable def strongMertensSmoothedMobius
    (SmoothingF : ℝ → ℝ) (epsilon X : ℝ) : ℂ :=
  VerticalIntegral' (strongMertensSmoothedIntegrand SmoothingF epsilon X)
    (1 + (Real.log X)⁻¹)

/-- Dirichlet-series form of the integrand on the half-plane of absolute
convergence. -/
theorem strongMertensSmoothedIntegrand_eq_dirichlet
    (SmoothingF : ℝ → ℝ) (epsilon X : ℝ) {s : ℂ} (hs : 1 < s.re) :
    strongMertensSmoothedIntegrand SmoothingF epsilon X s =
      L ↗μ s * mellin (fun x => (Smooth1 SmoothingF epsilon x : ℂ)) s *
        (X : ℂ) ^ s := by
  unfold strongMertensSmoothedIntegrand
  rw [strongMertens_LSeries_moebius_eq_inv_zeta hs]

/-- Reciprocal zeta tends to zero on the punctured neighborhood of the pole. -/
theorem strongMertens_inv_zeta_tendsto_zero_near_one :
    Tendsto (fun s => (zetaC s)⁻¹) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
  have hres : Tendsto (fun s => (s - 1) * zetaC s) (𝓝[≠] 1) (𝓝 1) :=
    riemannZeta_residue_one
  have hinv : Tendsto (fun s => ((s - 1) * zetaC s)⁻¹) (𝓝[≠] 1) (𝓝 1) := by
    have h := hres.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
    simpa using h
  have hsub : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 1) (𝓝 0) := by
    have h : Tendsto (fun s : ℂ => s - 1) (𝓝 1) (𝓝 (1 - 1)) :=
      (continuous_id.sub continuous_const).tendsto 1
    simpa using h.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto
      (fun s : ℂ => (s - 1) * ((s - 1) * zetaC s)⁻¹)
      (𝓝[≠] 1) (𝓝 (0 * 1)) := hsub.mul hinv
  rw [zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hs1, one_mul]

/-- Reciprocal zeta with the removable value at `1` filled by zero.  This is
the version to which compactness may safely be applied. -/
noncomputable def nativeInvZetaRegularized : ℂ → ℂ :=
  Function.update (fun s => (zetaC s)⁻¹) (1 : ℂ) 0

/-- Continuity of the regularized reciprocal on any set on which zeta has no
zeros away from the removable point. -/
theorem nativeInvZetaRegularized_continuousOn {K : Set ℂ}
    (hzero : ∀ s ∈ K, s ≠ 1 → zetaC s ≠ 0) :
    ContinuousOn nativeInvZetaRegularized K := by
  intro s hs
  by_cases hs1 : s = 1
  · subst s
    exact ((continuousAt_update_same).2
      strongMertens_inv_zeta_tendsto_zero_near_one).continuousWithinAt
  · have hbase : ContinuousAt (fun z => (zetaC z)⁻¹) s :=
      ((differentiableAt_riemannZeta hs1).inv (hzero s hs hs1)).continuousAt
    have hneighborhood : ({(1 : ℂ)}ᶜ : Set ℂ) ∈ 𝓝 s :=
      isOpen_compl_singleton.mem_nhds (by simpa using hs1)
    have hev : nativeInvZetaRegularized =ᶠ[𝓝 s] (fun z => (zetaC z)⁻¹) := by
      filter_upwards [hneighborhood] with z hz
      have hz1 : z ≠ (1 : ℂ) := by simpa using hz
      exact Function.update_of_ne hz1 0 (fun w => (zetaC w)⁻¹)
    exact (hbase.congr_of_eventuallyEq hev).continuousWithinAt

/-- The full integrand is bounded near `1`; this is the zero-residue input for
contour pulling. -/
theorem strongMertensSmoothedIntegrand_isBigO_one_near_one
    {SmoothingF : ℝ → ℝ} {epsilon : ℝ}
    (epsilon_pos : 0 < epsilon) (epsilon_lt_one : epsilon < 1)
    (suppF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (nonnegF : ∀ x > 0, 0 ≤ SmoothingF x)
    (massF : ∫ x in Set.Ioi (0 : ℝ), SmoothingF x / x = 1)
    (diffF : ContDiff ℝ 1 SmoothingF)
    {X : ℝ} (hX : 0 < X) :
    strongMertensSmoothedIntegrand SmoothingF epsilon X
      =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  have hmellin1 : DifferentiableAt ℂ
      (fun z => mellin (fun x => (Smooth1 SmoothingF epsilon x : ℂ)) z) (1 : ℂ) :=
    Smooth1MellinDifferentiable diffF suppF ⟨epsilon_pos, epsilon_lt_one⟩
      nonnegF massF (by norm_num)
  have hcpow1 : ContinuousAt (fun z : ℂ => (X : ℂ) ^ z) (1 : ℂ) :=
    continuousAt_const_cpow (by exact_mod_cast hX.ne')
  have hg : Tendsto
      (fun s => mellin (fun x => (Smooth1 SmoothingF epsilon x : ℂ)) s *
        (X : ℂ) ^ s)
      (𝓝 (1 : ℂ))
      (𝓝 (mellin (fun x => (Smooth1 SmoothingF epsilon x : ℂ)) 1 *
        (X : ℂ) ^ (1 : ℂ))) :=
    (hmellin1.continuousAt.mul hcpow1).tendsto
  have hkernel := strongMertens_inv_zeta_tendsto_zero_near_one
  have hprod : Tendsto (strongMertensSmoothedIntegrand SmoothingF epsilon X)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (0 * (mellin (fun x => (Smooth1 SmoothingF epsilon x : ℂ)) 1 *
        (X : ℂ) ^ (1 : ℂ)))) := by
    have h := hkernel.mul (hg.mono_left nhdsWithin_le_nhds)
    apply h.congr
    intro s
    simp only [strongMertensSmoothedIntegrand]
    ring
  rw [zero_mul] at hprod
  exact hprod.isBigO_one ℂ

/-- Holomorphy of the full integrand on the shared punctured log-nine box. -/
theorem strongMertensSmoothedIntegrand_holomorphicOn_punctured_box
    (corridor : StrongMertensLogNineCorridor)
    {SmoothingF : ℝ → ℝ} {epsilon : ℝ}
    (epsilon_pos : 0 < epsilon) (epsilon_lt_one : epsilon < 1)
    (suppF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (nonnegF : ∀ x > 0, 0 ≤ SmoothingF x)
    (massF : ∫ x in Set.Ioi (0 : ℝ), SmoothingF x / x = 1)
    (diffF : ContDiff ℝ 1 SmoothingF)
    {X T : ℝ} (hX : 0 < X) (hT : 3 ≤ T) :
    HolomorphicOn (strongMertensSmoothedIntegrand SmoothingF epsilon X)
      (((Set.Icc (strongMertensLogNineShift corridor.A T) 2) ×ℂ
        (Set.Icc (-T) T)) \ {(1 : ℂ)}) := by
  intro s hs
  have hs_ne_one : s ≠ 1 := by
    intro h
    exact hs.2 (by simp [h])
  have hmem := Complex.mem_reProdIm.mp hs.1
  have hre_lb : strongMertensLogNineShift corridor.A T ≤ s.re := hmem.1.1
  have hre_pos : 0 < s.re := (corridor.shift_pos T hT).trans_le hre_lb
  have hinvz : DifferentiableAt ℂ (fun z => (zetaC z)⁻¹) s :=
    (differentiableAt_riemannZeta hs_ne_one).inv
      (corridor.zero_free_box T hT s hs)
  have hmellin : DifferentiableAt ℂ
      (fun z => mellin (fun x => (Smooth1 SmoothingF epsilon x : ℂ)) z) s :=
    Smooth1MellinDifferentiable diffF suppF ⟨epsilon_pos, epsilon_lt_one⟩
      nonnegF massF hre_pos
  have hcpow : DifferentiableAt ℂ (fun z => (X : ℂ) ^ z) s := by
    apply DifferentiableAt.const_cpow (by fun_prop)
    left
    exact_mod_cast hX.ne'
  unfold strongMertensSmoothedIntegrand
  exact ((hinvz.mul hmellin).mul hcpow).differentiableWithinAt

/-- Reciprocal zeta is uniformly bounded on each fixed vertical line to the
right of one. -/
theorem strongMertens_inv_zeta_bdd_on_vertical_line_gt_one
    {sigma0 : ℝ} (hsigma0 : 1 < sigma0) :
    ∃ C > 0, ∀ t : ℝ,
      ‖(zetaC ((sigma0 : ℂ) + t * I))⁻¹‖ ≤ C := by
  set C : ℝ :=
    (∑' n, ‖LSeries.term (fun n => (μ n : ℂ)) (sigma0 : ℂ) n‖) + 1 with hC
  have hCpos : 0 < C := by
    have hnonneg : 0 ≤ ∑' n, ‖LSeries.term (fun n => (μ n : ℂ)) (sigma0 : ℂ) n‖ :=
      tsum_nonneg (fun _ => norm_nonneg _)
    rw [hC]
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro t
  set s : ℂ := (sigma0 : ℂ) + t * I with hs
  have hsre : s.re = sigma0 := by simp [hs]
  have hsre_gt : 1 < s.re := by rw [hsre]; exact hsigma0
  rw [← strongMertens_LSeries_moebius_eq_inv_zeta hsre_gt]
  have hsum : LSeriesSummable (fun n => (μ n : ℂ)) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (f := fun n => (μ n : ℂ)) (m := 1)
      (fun n _ => by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one) hsre_gt
  have hterm_eq : ∀ n : ℕ,
      ‖LSeries.term (fun n => (μ n : ℂ)) s n‖ =
        ‖LSeries.term (fun n => (μ n : ℂ)) (sigma0 : ℂ) n‖ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_def _ _ _, LSeries.term_def _ _ _]
      simp only [hn.ne', if_neg, not_false_eq_true]
      rw [norm_div, norm_div, Complex.norm_natCast_cpow_of_pos hn,
        Complex.norm_natCast_cpow_of_pos hn, hsre, Complex.ofReal_re]
  calc
    ‖LSeries (fun n => (μ n : ℂ)) s‖
        = ‖∑' n, LSeries.term (fun n => (μ n : ℂ)) s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term (fun n => (μ n : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ = ∑' n, ‖LSeries.term (fun n => (μ n : ℂ)) (sigma0 : ℂ) n‖ :=
      tsum_congr hterm_eq
    _ ≤ C := by rw [hC]; linarith

set_option maxHeartbeats 1000000 in
/-- The smoothed integrand is integrable on the standard right Perron line. -/
theorem strongMertensSmoothedIntegrand_integrable_right_line
    {SmoothingF : ℝ → ℝ} {epsilon : ℝ}
    (epsilon_pos : 0 < epsilon) (epsilon_lt_one : epsilon < 1)
    {X : ℝ} (hX : 3 < X)
    (suppF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (nonnegF : ∀ x > 0, 0 ≤ SmoothingF x)
    (massF : ∫ x in Set.Ioi (0 : ℝ), SmoothingF x / x = 1)
    (diffF : ContDiff ℝ 1 SmoothingF) :
    Integrable (fun t : ℝ =>
      strongMertensSmoothedIntegrand SmoothingF epsilon X
        ((1 + (Real.log X)⁻¹) + t * I)) := by
  set sigma0 : ℝ := 1 + (Real.log X)⁻¹ with hsigma0
  have hsigma0gt : 1 < sigma0 := by
    rw [hsigma0]
    have hlog : 0 < Real.log X := Real.log_pos (by linarith)
    have : 0 < (Real.log X)⁻¹ := by positivity
    linarith
  have hlogXgt1 : 1 < Real.log X := logt_gt_one hX.le
  have hsigma0le2 : sigma0 ≤ 2 := by
    rw [hsigma0, ← one_add_one_eq_two]
    gcongr
    exact (inv_lt_one_of_one_lt₀ hlogXgt1).le
  obtain ⟨C, hC, hCbdd⟩ :=
    strongMertens_inv_zeta_bdd_on_vertical_line_gt_one hsigma0gt
  have hMint : Integrable (fun t : ℝ =>
      mellin (fun x => (Smooth1 SmoothingF epsilon x : ℂ))
        ((sigma0 : ℂ) + (t : ℂ) * I)) :=
    SmoothedChebyshevDirichlet_aux_integrable diffF nonnegF suppF massF
      epsilon_pos epsilon_lt_one hsigma0gt hsigma0le2
  let c : ℝ := C * X ^ sigma0
  have hbdd : ∀ t : ℝ,
      ‖(zetaC ((sigma0 : ℂ) + (t : ℂ) * I))⁻¹ *
        (X : ℂ) ^ ((sigma0 : ℂ) + (t : ℂ) * I)‖ ≤ c := by
    intro t
    rw [Complex.norm_mul]
    dsimp [c]
    gcongr
    · exact hCbdd t
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      simp
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (zetaC ((sigma0 : ℂ) + (t : ℂ) * I))⁻¹ *
        (X : ℂ) ^ ((sigma0 : ℂ) + (t : ℂ) * I)) := by
    apply Continuous.aestronglyMeasurable
    rw [← continuousOn_univ]
    intro t _
    have hs_ne_one : (sigma0 : ℂ) + (t : ℂ) * I ≠ 1 := by
      intro h
      have : sigma0 = 1 := by
        have := congrArg Complex.re h
        simpa using this
      linarith
    apply ContinuousAt.continuousWithinAt
    have hg : ContinuousAt (fun x : ℝ => (sigma0 : ℂ) + (x : ℂ) * I) t := by
      fun_prop
    apply ContinuousAt.mul
    · apply ContinuousAt.inv₀
      · exact ContinuousAt.comp
          (differentiableAt_riemannZeta hs_ne_one).continuousAt hg
      · exact riemannZeta_ne_zero_of_one_lt_re (by simp [hsigma0gt])
    · exact ContinuousAt.comp
        (continuousAt_const_cpow (by exact_mod_cast (show 0 < X by linarith).ne')) hg
  -- `Integrable.bdd_mul` wants a genuine uniform bound, not an a.e. one.
  have key := hMint.bdd_mul hmeas ⟨c, hbdd⟩
  apply key.congr
  filter_upwards with t
  unfold strongMertensSmoothedIntegrand
  rw [hsigma0]
  push_cast
  ring

/-- Public names used by the quantitative contour modules. -/
abbrev nativeSmoothedMobiusIntegrand := strongMertensSmoothedIntegrand
abbrev nativeSmoothedMobius := strongMertensSmoothedMobius

theorem nativeLSeries_moebius_eq_inv_zeta {s : ℂ} (hs : 1 < s.re) :
    L ↗μ s = (zetaC s)⁻¹ :=
  strongMertens_LSeries_moebius_eq_inv_zeta hs

theorem nativeInvZeta_tendsto_zero_near_one :
    Tendsto (fun s => (zetaC s)⁻¹) (𝓝[≠] (1 : ℂ)) (𝓝 0) :=
  strongMertens_inv_zeta_tendsto_zero_near_one

theorem nativeSmoothedMobiusIntegrand_isBigO_one_near_one
    {SmoothingF : ℝ → ℝ} {epsilon : ℝ}
    (epsilon_pos : 0 < epsilon) (epsilon_lt_one : epsilon < 1)
    (suppF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (nonnegF : ∀ x > 0, 0 ≤ SmoothingF x)
    (massF : ∫ x in Set.Ioi (0 : ℝ), SmoothingF x / x = 1)
    (diffF : ContDiff ℝ 1 SmoothingF)
    {X : ℝ} (hX : 0 < X) :
    nativeSmoothedMobiusIntegrand SmoothingF epsilon X
      =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) :=
  strongMertensSmoothedIntegrand_isBigO_one_near_one
    epsilon_pos epsilon_lt_one suppF nonnegF massF diffF hX

theorem nativeSmoothedMobiusIntegrand_norm_eq
    (SmoothingF : ℝ → ℝ) (epsilon X : ℝ) (s : ℂ) :
    ‖nativeSmoothedMobiusIntegrand SmoothingF epsilon X s‖ =
      (1 / ‖zetaC s‖) *
        ‖mellin (fun x => (Smooth1 SmoothingF epsilon x : ℂ)) s‖ *
        ‖(X : ℂ) ^ s‖ := by
  unfold nativeSmoothedMobiusIntegrand strongMertensSmoothedIntegrand
  rw [norm_mul, norm_mul, norm_inv, one_div]

/-- Global natural-endpoint target.  The balance module first proves the
corresponding eventual real-endpoint estimate. -/
def StrongNativeMertensSubexp : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ N : ℕ, 3 ≤ N →
      |nativeMertensSummatory N| ≤
        C * (N : ℝ) *
          Real.exp (-c * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 10))

namespace LogNineContour

/-- Power saving contributed by the log-nine shifted line. -/
theorem rpow_logNine_shift {A X T : ℝ} (hX : 0 < X) :
    X ^ (1 - A / (Real.log T) ^ 9) =
      X * Real.exp (-A * Real.log X / (Real.log T) ^ 9) := by
  rw [Real.rpow_def_of_pos hX]
  -- Rewriting `X` into `exp (log X)` has to be confined to the standalone `X`:
  -- done blindly it also rewrites the `X` inside `Real.log X`.
  rw [show X * Real.exp (-A * Real.log X / (Real.log T) ^ 9) =
      Real.exp (Real.log X) * Real.exp (-A * Real.log X / (Real.log T) ^ 9) by
    rw [Real.exp_log hX]]
  rw [← Real.exp_add]
  congr 1
  ring

end LogNineContour

end RHLean.Analysis
