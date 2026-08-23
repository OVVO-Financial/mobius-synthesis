import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import RHLean.Analysis.StrongMertensRecipMomentTransfer

/-!
# Analytic closure of the reciprocal Mobius moments for centered K2

This module is the analytic side of the centered K2 closure.  The finite K2
algebra remains in `K2CenteredFinite` and `K2CenteredClassicalInterface`.

The first step removes the pole of the Riemann zeta function at `1` using
Mathlib's proved limit

`zeta(s) - 1 / (s - 1) -> gamma`.

The resulting regular part is analytic at `1`.  The reciprocal germ is then
factored as `(s - 1) q(s)`.  Differentiating this factorization twice reads the
second Taylor coefficient directly and gives

`(1 / zeta)''(1) = -2 * gamma`.

On `re s > 1` the same second derivative is identified with the logarithmic
square Mobius L-series.  The remaining Abel-boundary step therefore has a
single explicit target: carry that Dirichlet series continuously to `s = 1`.
-/

noncomputable section

open Filter Set Topology
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RHLean.Analysis

local notation "gammaE" => Real.eulerMascheroniConstant

/-- Zeta with its simple pole at `1` removed and the removable value filled by
Euler's constant. -/
def k2ZetaRegularPart : ℂ → ℂ :=
  Function.update
    (fun s : ℂ => riemannZeta s - 1 / (s - 1))
    (1 : ℂ) (gammaE : ℂ)

@[simp]
theorem k2ZetaRegularPart_one :
    k2ZetaRegularPart 1 = (gammaE : ℂ) := by
  simp [k2ZetaRegularPart]

theorem k2ZetaRegularPart_eq {s : ℂ} (hs : s ≠ 1) :
    k2ZetaRegularPart s = riemannZeta s - 1 / (s - 1) := by
  simp [k2ZetaRegularPart, hs]

/-- The filled regular part is continuous at the removed pole. -/
theorem k2ZetaRegularPart_continuousAt_one :
    ContinuousAt k2ZetaRegularPart (1 : ℂ) := by
  rw [k2ZetaRegularPart]
  exact continuousAt_update_same.mpr tendsto_riemannZeta_sub_one_div

/-- Away from the filled point the regular part is the ordinary differentiable
zeta-minus-pole function. -/
theorem k2ZetaRegularPart_differentiable_punctured :
    ∀ᶠ s : ℂ in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ k2ZetaRegularPart s := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ (1 : ℂ) := by
    simpa only [mem_compl_singleton_iff] using hs
  have hbase : DifferentiableAt ℂ
      (fun z : ℂ => riemannZeta z - 1 / (z - 1)) s := by
    refine (differentiableAt_riemannZeta hs1).sub ((differentiableAt_const _).div ?_ ?_)
    · fun_prop
    · exact sub_ne_zero.mpr hs1
  have hne : ({(1 : ℂ)}ᶜ : Set ℂ) ∈ 𝓝 s :=
    isOpen_compl_singleton.mem_nhds hs
  have heq : k2ZetaRegularPart =ᶠ[𝓝 s]
      (fun z : ℂ => riemannZeta z - 1 / (z - 1)) := by
    filter_upwards [hne] with z hz
    exact k2ZetaRegularPart_eq (by
      simpa only [mem_compl_singleton_iff] using hz)
  exact hbase.congr_of_eventuallyEq heq

/-- The pole-removed zeta germ is analytic at `1`. -/
theorem k2ZetaRegularPart_analyticAt_one :
    AnalyticAt ℂ k2ZetaRegularPart (1 : ℂ) :=
  Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    k2ZetaRegularPart_differentiable_punctured
    k2ZetaRegularPart_continuousAt_one

/-- The analytic unit factor in the reciprocal-zeta germ. -/
def k2InvZetaFactor (s : ℂ) : ℂ :=
  (1 + (s - 1) * k2ZetaRegularPart s)⁻¹

@[simp]
theorem k2InvZetaFactor_one : k2InvZetaFactor 1 = 1 := by
  simp [k2InvZetaFactor]

/-- The unit factor is analytic at the filled point. -/
theorem k2InvZetaFactor_analyticAt_one :
    AnalyticAt ℂ k2InvZetaFactor (1 : ℂ) := by
  have hlin : AnalyticAt ℂ (fun s : ℂ => s - 1) (1 : ℂ) :=
    analyticAt_id.sub analyticAt_const
  have hden : AnalyticAt ℂ
      (fun s : ℂ => 1 + (s - 1) * k2ZetaRegularPart s) (1 : ℂ) :=
    analyticAt_const.add (hlin.mul k2ZetaRegularPart_analyticAt_one)
  exact hden.fun_inv (by simp)

/-- The analytic reciprocal-zeta germ, factored into its simple zero and a
unit analytic factor. -/
def k2InvZetaRegular (s : ℂ) : ℂ :=
  (s - 1) * k2InvZetaFactor s

@[simp]
theorem k2InvZetaRegular_one : k2InvZetaRegular 1 = 0 := by
  simp [k2InvZetaRegular]

/-- The regular reciprocal is analytic at the filled point. -/
theorem k2InvZetaRegular_analyticAt_one :
    AnalyticAt ℂ k2InvZetaRegular (1 : ℂ) := by
  have hlin : AnalyticAt ℂ (fun s : ℂ => s - 1) (1 : ℂ) :=
    analyticAt_id.sub analyticAt_const
  exact hlin.mul k2InvZetaFactor_analyticAt_one

/-- The derivative of the analytic unit factor at one is `-gamma`. -/
theorem k2InvZetaFactor_hasDerivAt_one :
    HasDerivAt k2InvZetaFactor (-(gammaE : ℂ)) (1 : ℂ) := by
  have hlin : HasDerivAt (fun s : ℂ => s - 1) 1 (1 : ℂ) :=
    (hasDerivAt_id (1 : ℂ)).sub_const 1
  have hreg := k2ZetaRegularPart_analyticAt_one.differentiableAt.hasDerivAt
  have hprod := hlin.fun_mul hreg
  have hden : HasDerivAt
      (fun s : ℂ => 1 + (s - 1) * k2ZetaRegularPart s)
      (gammaE : ℂ) (1 : ℂ) := by
    simpa [k2ZetaRegularPart_one] using hprod.const_add 1
  have hinv := hden.fun_inv (by simp)
  simpa [k2InvZetaFactor] using hinv

/-- The reciprocal germ has the expected simple zero with first derivative
one. -/
theorem k2InvZetaRegular_hasDerivAt_one :
    HasDerivAt k2InvZetaRegular 1 (1 : ℂ) := by
  have hlin : HasDerivAt (fun s : ℂ => s - 1) 1 (1 : ℂ) :=
    (hasDerivAt_id (1 : ℂ)).sub_const 1
  have h := hlin.fun_mul k2InvZetaFactor_hasDerivAt_one
  simpa [k2InvZetaRegular] using h

/-- Coefficient extraction at the filled pole: the second derivative of the
regular reciprocal-zeta germ is exactly `-2 * gamma`. -/
theorem k2InvZetaRegular_iteratedDeriv_two :
    iteratedDeriv 2 k2InvZetaRegular (1 : ℂ) =
      (-2 * gammaE : ℂ) := by
  let H : ℂ → ℂ := fun s =>
    k2InvZetaFactor s + (s - 1) * deriv k2InvZetaFactor s
  have hfactor_eventually :
      ∀ᶠ s : ℂ in 𝓝 (1 : ℂ), DifferentiableAt ℂ k2InvZetaFactor s := by
    filter_upwards [((isOpen_analyticAt ℂ k2InvZetaFactor).mem_nhds
      k2InvZetaFactor_analyticAt_one)] with s hs
    exact hs.differentiableAt
  have hderiv_eq : deriv k2InvZetaRegular =ᶠ[𝓝 (1 : ℂ)] H := by
    filter_upwards [hfactor_eventually] with s hs
    have hlin : HasDerivAt (fun z : ℂ => z - 1) 1 s :=
      (hasDerivAt_id s).sub_const 1
    have h := hlin.fun_mul hs.hasDerivAt
    simpa [H, k2InvZetaRegular] using h.deriv
  have hfactor_deriv_value :
      deriv k2InvZetaFactor (1 : ℂ) = -(gammaE : ℂ) :=
    k2InvZetaFactor_hasDerivAt_one.deriv
  have hderiv_factor_diff :
      DifferentiableAt ℂ (deriv k2InvZetaFactor) (1 : ℂ) :=
    k2InvZetaFactor_analyticAt_one.deriv.differentiableAt
  have hlin : HasDerivAt (fun s : ℂ => s - 1) 1 (1 : ℂ) :=
    (hasDerivAt_id (1 : ℂ)).sub_const 1
  have hprod := hlin.fun_mul hderiv_factor_diff.hasDerivAt
  have hH : HasDerivAt H (-2 * (gammaE : ℂ)) (1 : ℂ) := by
    have hsum := k2InvZetaFactor_hasDerivAt_one.fun_add hprod
    have hsum' := hsum
    rw [hfactor_deriv_value] at hsum'
    have hsumH : HasDerivAt H
        (-(gammaE : ℂ) + -(gammaE : ℂ)) (1 : ℂ) := by
      simpa [H] using hsum'
    convert hsumH using 1
    ring
  have hsecond :
      deriv (deriv k2InvZetaRegular) (1 : ℂ) = -2 * (gammaE : ℂ) := by
    rw [hderiv_eq.deriv_eq]
    exact hH.deriv
  simpa [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ] using hsecond

/-- On the absolutely convergent half-plane the regular reciprocal is the
ordinary reciprocal of the Riemann zeta function. -/
theorem k2InvZetaRegular_eq_inv_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    k2InvZetaRegular s = (riemannZeta s)⁻¹ := by
  have hs1 : s ≠ (1 : ℂ) := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hz0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hden :
      1 + (s - 1) * (riemannZeta s - 1 / (s - 1)) =
        (s - 1) * riemannZeta s := by
    field_simp [hsub]
    ring
  rw [k2InvZetaRegular, k2InvZetaFactor, k2ZetaRegularPart_eq hs1, hden]
  field_simp [hsub, hz0]

/-- On `re s > 1`, the regular reciprocal is exactly the Mobius L-series. -/
theorem k2InvZetaRegular_eq_moebiusLSeries {s : ℂ} (hs : 1 < s.re) :
    k2InvZetaRegular s = L ↗μ s := by
  rw [k2InvZetaRegular_eq_inv_riemannZeta hs]
  have hprod := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hprod
  have hz0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  calc
    (riemannZeta s)⁻¹ = (riemannZeta s)⁻¹ * 1 := by simp
    _ = (riemannZeta s)⁻¹ * (riemannZeta s * L ↗μ s) := by rw [hprod]
    _ = L ↗μ s := by simp [hz0]

/-- The Mobius Dirichlet series has abscissa of absolute convergence at most
one; this is the exact half-plane on which termwise L-series differentiation is
available. -/
theorem k2Mobius_abscissaOfAbsConv_le_one :
    LSeries.abscissaOfAbsConv (fun n : ℕ => (μ n : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_le_const
  refine ⟨1, ?_⟩
  intro n _hn
  simp only [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- On `re s > 1`, the second derivative of the reciprocal-zeta germ is exactly
the log-square Mobius L-series.  This is the analytic coefficient identity that
will be continued to the Abel boundary `s = 1`. -/
theorem k2InvZetaRegular_iteratedDeriv_two_eq_moebiusLogSqLSeries
    {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv 2 k2InvZetaRegular s =
      LSeries (LSeries.logMul^[2] (fun n : ℕ => (μ n : ℂ))) s := by
  let U : Set ℂ := {z : ℂ | 1 < z.re}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_lt continuous_const Complex.continuous_re
  have heq : Set.EqOn k2InvZetaRegular
      (LSeries (fun n : ℕ => (μ n : ℂ))) U := by
    intro z hz
    exact k2InvZetaRegular_eq_moebiusLSeries hz
  have hderiv := heq.iteratedDeriv_of_isOpen hUopen 2 hs
  rw [hderiv]
  have hsE : (1 : EReal) < (s.re : EReal) := by
    exact_mod_cast hs
  have habs :
      LSeries.abscissaOfAbsConv (fun n : ℕ => (μ n : ℂ)) < (s.re : EReal) :=
    k2Mobius_abscissaOfAbsConv_le_one.trans_lt hsE
  rw [LSeries_iteratedDeriv 2 habs]
  norm_num

end RHLean.Analysis
