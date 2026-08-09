import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import RHLean.Analysis.MertensMellinLSeriesBridge

/-!
# Propagate the Mertens-zeta reciprocal identity to the critical half-plane

The previous Mertens layers prove two facts under `MertensEnergyBoundedStatement`:

* `mertensMellinContinuation` is holomorphic on `Re(s) > 1/2`;
* `riemannZeta s * mertensMellinContinuation s = 1` on `Re(s) > 1`.

This file performs only the identity-theorem continuation step.  Since zeta has
a pole at `s = 1`, we propagate on convex open regions that avoid that point:
the upper and lower parts of the critical half-plane and then the left strip
`1/2 < Re(s) < 1`.  This avoids introducing any global punctured-half-plane
topology lemma.

No zero-free conclusion, functional-equation reflection, or RH theorem is
proved here.
-/

open scoped Topology

noncomputable section

namespace RHLean.Analysis

open Complex Filter Set

private def mertensZetaProduct (s : ℂ) : ℂ :=
  riemannZeta s * mertensMellinContinuation s

private def criticalUpperHalfPlane : Set ℂ :=
  {s : ℂ | (1 : ℝ) / 2 < s.re} ∩ {s : ℂ | 0 < s.im}

private def criticalLowerHalfPlane : Set ℂ :=
  {s : ℂ | (1 : ℝ) / 2 < s.re} ∩ {s : ℂ | s.im < 0}

private def criticalLeftStrip : Set ℂ :=
  {s : ℂ | (1 : ℝ) / 2 < s.re} ∩ {s : ℂ | s.re < 1}

private theorem isOpen_criticalUpperHalfPlane : IsOpen criticalUpperHalfPlane := by
  unfold criticalUpperHalfPlane
  exact (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_const continuous_im)

private theorem isOpen_criticalLowerHalfPlane : IsOpen criticalLowerHalfPlane := by
  unfold criticalLowerHalfPlane
  exact (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_im continuous_const)

private theorem isOpen_criticalLeftStrip : IsOpen criticalLeftStrip := by
  unfold criticalLeftStrip
  exact (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)

private theorem convex_criticalUpperHalfPlane : Convex ℝ criticalUpperHalfPlane := by
  unfold criticalUpperHalfPlane
  exact (convex_halfSpace_re_gt ((1 : ℝ) / 2)).inter
    (convex_halfSpace_im_gt 0)

private theorem convex_criticalLowerHalfPlane : Convex ℝ criticalLowerHalfPlane := by
  unfold criticalLowerHalfPlane
  exact (convex_halfSpace_re_gt ((1 : ℝ) / 2)).inter
    (convex_halfSpace_im_lt 0)

private theorem convex_criticalLeftStrip : Convex ℝ criticalLeftStrip := by
  unfold criticalLeftStrip
  exact (convex_halfSpace_re_gt ((1 : ℝ) / 2)).inter
    (convex_halfSpace_re_lt 1)

private theorem analyticOnNhd_mertensZetaProduct
    (hM : MertensEnergyBoundedStatement) {U : Set ℂ}
    (hUopen : IsOpen U)
    (hhalf : ∀ z ∈ U, (1 : ℝ) / 2 < z.re)
    (hone : ∀ z ∈ U, z ≠ 1) :
    AnalyticOnNhd ℂ mertensZetaProduct U := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
  exact ((differentiableAt_riemannZeta (hone z hz)).mul
    (differentiableAt_mertensMellinContinuation hM (hhalf z hz))).differentiableWithinAt

private theorem mertensZetaProduct_eq_one_on_upper
    (hM : MertensEnergyBoundedStatement) :
    Set.EqOn mertensZetaProduct (fun _ : ℂ => (1 : ℂ)) criticalUpperHalfPlane := by
  have hP : AnalyticOnNhd ℂ mertensZetaProduct criticalUpperHalfPlane := by
    apply analyticOnNhd_mertensZetaProduct hM isOpen_criticalUpperHalfPlane
    · intro z hz
      exact hz.1
    · intro z hz hzone
      subst z
      have him := hz.2
      norm_num at him
  have hconst :
      AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) criticalUpperHalfPlane :=
    analyticOnNhd_const
  have hz0 : (2 : ℂ) + I ∈ criticalUpperHalfPlane := by
    change (1 : ℝ) / 2 < ((2 : ℂ) + I).re ∧ 0 < ((2 : ℂ) + I).im
    norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    hP hconst convex_criticalUpperHalfPlane.isPreconnected hz0 ?_
  have hnhd : {z : ℂ | 1 < z.re} ∈ 𝓝 ((2 : ℂ) + I) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  filter_upwards [hnhd] with z hz
  simpa [mertensZetaProduct] using
    riemannZeta_mul_mertensMellinContinuation_eq_one hM hz

private theorem mertensZetaProduct_eq_one_on_lower
    (hM : MertensEnergyBoundedStatement) :
    Set.EqOn mertensZetaProduct (fun _ : ℂ => (1 : ℂ)) criticalLowerHalfPlane := by
  have hP : AnalyticOnNhd ℂ mertensZetaProduct criticalLowerHalfPlane := by
    apply analyticOnNhd_mertensZetaProduct hM isOpen_criticalLowerHalfPlane
    · intro z hz
      exact hz.1
    · intro z hz hzone
      subst z
      have him := hz.2
      norm_num at him
  have hconst :
      AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) criticalLowerHalfPlane :=
    analyticOnNhd_const
  have hz0 : (2 : ℂ) - I ∈ criticalLowerHalfPlane := by
    change (1 : ℝ) / 2 < ((2 : ℂ) - I).re ∧ ((2 : ℂ) - I).im < 0
    norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    hP hconst convex_criticalLowerHalfPlane.isPreconnected hz0 ?_
  have hnhd : {z : ℂ | 1 < z.re} ∈ 𝓝 ((2 : ℂ) - I) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  filter_upwards [hnhd] with z hz
  simpa [mertensZetaProduct] using
    riemannZeta_mul_mertensMellinContinuation_eq_one hM hz

private theorem mertensZetaProduct_eq_one_on_leftStrip
    (hM : MertensEnergyBoundedStatement) :
    Set.EqOn mertensZetaProduct (fun _ : ℂ => (1 : ℂ)) criticalLeftStrip := by
  have hP : AnalyticOnNhd ℂ mertensZetaProduct criticalLeftStrip := by
    apply analyticOnNhd_mertensZetaProduct hM isOpen_criticalLeftStrip
    · intro z hz
      exact hz.1
    · intro z hz hzone
      subst z
      have hre := hz.2
      norm_num at hre
  have hconst :
      AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) criticalLeftStrip :=
    analyticOnNhd_const
  let z0 : ℂ := (3 : ℂ) / 4 + I
  have hz0strip : z0 ∈ criticalLeftStrip := by
    dsimp [z0]
    change (1 : ℝ) / 2 < (((3 : ℂ) / 4 + I).re) ∧
      (((3 : ℂ) / 4 + I).re) < 1
    norm_num
  have hz0upper : z0 ∈ criticalUpperHalfPlane := by
    dsimp [z0]
    change (1 : ℝ) / 2 < (((3 : ℂ) / 4 + I).re) ∧
      0 < (((3 : ℂ) / 4 + I).im)
    norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    hP hconst convex_criticalLeftStrip.isPreconnected hz0strip ?_
  have hupperNhd : criticalUpperHalfPlane ∈ 𝓝 z0 :=
    isOpen_criticalUpperHalfPlane.mem_nhds hz0upper
  filter_upwards [hupperNhd] with z hz
  exact mertensZetaProduct_eq_one_on_upper hM hz

/-- Under the Mertens energy criterion, the reciprocal identity propagated from
`Re(s) > 1` holds at every point of `Re(s) > 1/2` except the zeta pole `s = 1`.
This is the identity-theorem step only. -/
theorem riemannZeta_mul_mertensMellinContinuation_eq_one_of_half_lt_re
    (hM : MertensEnergyBoundedStatement) {s : ℂ}
    (hs : (1 : ℝ) / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s * mertensMellinContinuation s = 1 := by
  by_cases hgt : 1 < s.re
  · exact riemannZeta_mul_mertensMellinContinuation_eq_one hM hgt
  by_cases hlt : s.re < 1
  · have hsstrip : s ∈ criticalLeftStrip := ⟨hs, hlt⟩
    simpa [mertensZetaProduct] using
      mertensZetaProduct_eq_one_on_leftStrip hM hsstrip
  · have hre : s.re = 1 :=
      le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
    have himne : s.im ≠ 0 := by
      intro him
      apply hs1
      apply Complex.ext
      · change s.re = 1
        exact hre
      · change s.im = 0
        exact him
    rcases lt_or_gt_of_ne himne with himlt | himgt
    · have hslower : s ∈ criticalLowerHalfPlane := ⟨hs, himlt⟩
      simpa [mertensZetaProduct] using
        mertensZetaProduct_eq_one_on_lower hM hslower
    · have hsupper : s ∈ criticalUpperHalfPlane := ⟨hs, himgt⟩
      simpa [mertensZetaProduct] using
        mertensZetaProduct_eq_one_on_upper hM hsupper

end RHLean.Analysis
