import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelbergWheelFrontier
import RHLean.Analysis.NativePNTSquarePrefixCubic

/-!
# Signed wheel-frontier audit and square-prefix PNT contraction

This module is the architecture-native correction after
`NativePNTSignedSecondSelbergWheelFrontier`.

The prime-wheel side stays exact.  Below `N < 2 * y^2`, every unresolved
partial-wheel site is one of the two faces classified by the frontier theorem:
a negative prime-square diagonal or a positive mixed product of two distinct
primes.  We retain that sign information and do not assert a false pointwise
positivity statement.  The reciprocal quotient of every such site is exactly
one, so its contribution to the signed second-kernel error mass is the negative
of its raw frontier charge.

The quantitative PNT contraction stays on the repository's proved square-block
path.  The square-prefix good-mass theorem supplies the existing coefficient
`beta^2 / 6600000`.  In the low-slope regime `alpha <= 3/2`, the admissible
choice `beta = 2 * alpha / 3` maximizes the already-proved cubic gain and improves
the square-prefix cubic constant from

`1 / 1140480000`

to

`1 / 178200000`.

Thus this correction satisfies both architectural gates without conflating
them: the signed prime-wheel frontier remains an exact finite face ledger, and
the generalized proved affine PNT envelope is strictly contracted on the same
square-prefix mechanism.  This is a quantitative step toward the later RH-scale
intercept problem, not a claim that the half-power bound has already been
proved.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-! ## Exact signed prime-wheel frontier -/

/-- The actual unresolved partial-wheel sites at cutoff `y` and endpoint `N`. -/
def nativePNTSignedSecondSelbergWheelFrontierSites
    (y N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun n => μ n - partialPrimeWheelSite y N n ≠ 0)

@[simp] theorem mem_nativePNTSignedSecondSelbergWheelFrontierSites
    {y N n : ℕ} :
    n ∈ nativePNTSignedSecondSelbergWheelFrontierSites y N ↔
      n ∈ Finset.Icc 1 N ∧
        μ n - partialPrimeWheelSite y N n ≠ 0 := by
  simp [nativePNTSignedSecondSelbergWheelFrontierSites]

/-- Raw signed second-kernel charge on the unresolved wheel frontier. -/
def nativePNTSignedSecondSelbergWheelFrontierCharge
    (y N : ℕ) : ℝ :=
  ∑ n ∈ nativePNTSignedSecondSelbergWheelFrontierSites y N,
    nativePNTSignedSecondSelbergKernel n

/-- The same frontier charge with the actual PNT error at the reciprocal
quotient. -/
def nativePNTSignedSecondSelbergWheelFrontierErrorMass
    (y N : ℕ) : ℝ :=
  ∑ n ∈ nativePNTSignedSecondSelbergWheelFrontierSites y N,
    nativePNTSignedSecondSelbergKernel n * nativePNTError (N / n)

/-- Below twice the square of the wheel cutoff, every frontier site has
reciprocal quotient exactly one.  This is the square-block geometry behind the
frontier extraction: both unresolved prime factors are larger than `y`, so the
site itself is larger than `y^2`, while `N < 2 y^2`. -/
theorem nativePNTSignedSecondSelbergWheelFrontier_div_eq_one
    {y N n : ℕ} (hscale : N < 2 * y ^ 2)
    (hn : n ∈ nativePNTSignedSecondSelbergWheelFrontierSites y N) :
    N / n = 1 := by
  have hnData := mem_nativePNTSignedSecondSelbergWheelFrontierSites.mp hn
  have hnI := Finset.mem_Icc.mp hnData.1
  have hnpos : 0 < n := by omega
  rcases partialPrimeWheel_nonzero_error_factorization_of_two_mul_sq
      y N hscale hnpos hnI.2 hnData.2 with
    ⟨q, r, _hqPrime, _hrPrime, hyq, hyr, _hresolved, hnqr⟩
  have hyq1 : y + 1 ≤ q := by omega
  have hyr1 : y + 1 ≤ r := by omega
  have hsqStep : (y + 1) ^ 2 ≤ q * r := by
    simpa [pow_two] using Nat.mul_le_mul hyq1 hyr1
  have hySqLtSuccSq : y ^ 2 < (y + 1) ^ 2 :=
    Nat.pow_lt_pow_left (by omega) (by omega)
  have hySqLtN : y ^ 2 < n := by
    rw [hnqr]
    exact hySqLtSuccSq.trans_le hsqStep
  have hNltTwoN : N < 2 * n := by omega
  have hlo : 1 * n ≤ N := by simpa using hnI.2
  have hhi : N < (1 + 1) * n := by simpa using hNltTwoN
  exact Nat.div_eq_of_lt_le hlo hhi

@[simp] theorem nativePNTError_one : nativePNTError 1 = -1 := by
  simp [nativePNTError, nativePsi]

/-- On the true unresolved frontier, the signed second-kernel error mass is
exactly the negative raw charge.  No absolute value or auxiliary remainder is
inserted at this step. -/
theorem nativePNTSignedSecondSelbergWheelFrontierErrorMass_eq_neg_charge
    {y N : ℕ} (hscale : N < 2 * y ^ 2) :
    nativePNTSignedSecondSelbergWheelFrontierErrorMass y N =
      -nativePNTSignedSecondSelbergWheelFrontierCharge y N := by
  unfold nativePNTSignedSecondSelbergWheelFrontierErrorMass
    nativePNTSignedSecondSelbergWheelFrontierCharge
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hdiv := nativePNTSignedSecondSelbergWheelFrontier_div_eq_one hscale hn
  rw [hdiv, nativePNTError_one]
  ring

/-- Re-expose the frontier-charge identity on the actual frontier-site finset.  Every site is exactly
one of the two signed prime-wheel faces, with no third case. -/
theorem nativePNTSignedSecondSelbergWheelFrontierSite_classification
    {y N n : ℕ} (hscale : N < 2 * y ^ 2)
    (hn : n ∈ nativePNTSignedSecondSelbergWheelFrontierSites y N) :
    (∃ q : ℕ,
      q.Prime ∧ y < q ∧ n = q ^ 2 ∧
        μ n - partialPrimeWheelSite y N n = 1 ∧
        nativePNTSignedSecondSelbergKernel n =
          -(Real.log (q : ℝ)) ^ 2) ∨
    (∃ q r : ℕ,
      q.Prime ∧ r.Prime ∧ q ≠ r ∧ y < q ∧ y < r ∧ n = q * r ∧
        μ n - partialPrimeWheelSite y N n = 2 ∧
        nativePNTSignedSecondSelbergKernel n =
          2 * Real.log (q : ℝ) * Real.log (r : ℝ)) := by
  have hnData := mem_nativePNTSignedSecondSelbergWheelFrontierSites.mp hn
  have hnI := Finset.mem_Icc.mp hnData.1
  have hnpos : 0 < n := by omega
  exact nativePNTSignedSecondSelbergKernel_wheelFrontier_classification
    y N hscale hnpos hnI.2 hnData.2

/-! ## Proven square-prefix contraction -/

/-- Improved cubic constant on the fully rederived square-prefix path once the
current affine slope is at most `3/2`. -/
def nativePNTSquarePrefixLowSlopeCubicConstant : ℝ := 1 / 178200000

/-- The square-prefix low-slope constant is exactly `32/5` times the existing
fully rederived square-prefix constant. -/
theorem nativePNTSquarePrefixLowSlopeCubicConstant_eq_scaled :
    nativePNTSquarePrefixLowSlopeCubicConstant =
      (32 / 5 : ℝ) * nativePNTSquarePrefixRederivedCubicConstant := by
  norm_num [nativePNTSquarePrefixLowSlopeCubicConstant,
    nativePNTSquarePrefixRederivedCubicConstant]

/-- Hence the low-slope square-prefix coefficient is strictly stronger than the
current general square-prefix coefficient. -/
theorem nativePNTSquarePrefixRederivedCubicConstant_lt_lowSlope :
    nativePNTSquarePrefixRederivedCubicConstant <
      nativePNTSquarePrefixLowSlopeCubicConstant := by
  norm_num [nativePNTSquarePrefixLowSlopeCubicConstant,
    nativePNTSquarePrefixRederivedCubicConstant]

/-- **Sharpened square-prefix PNT contraction.**  For `0 < alpha <= 3/2`, use
the same fully rederived square-prefix good-mass theorem, but choose the optimal
admissible threshold `beta = 2*alpha/3`.  This changes no analytic premise and
improves the one-step cubic coefficient by the exact factor `32/5`. -/
theorem nativePNTSquarePrefixHasAffineEnvelope_lowSlope_cubic_step
    (alpha : ℝ) (halpha : 0 < alpha) (halphaSmall : alpha ≤ 3 / 2)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
      (alpha - nativePNTSquarePrefixLowSlopeCubicConstant * alpha ^ 3) := by
  let beta : ℝ := 2 * alpha / 3
  have hbeta : 0 < beta := by
    dsimp [beta]
    positivity
  have hbeta0 : 0 ≤ beta := hbeta.le
  have hbeta1 : beta ≤ 1 := by
    dsimp [beta]
    nlinarith
  have hba : beta < alpha := by
    dsimp [beta]
    nlinarith
  let c : ℝ := beta ^ 2 / 6600000
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hprod : 0 ≤ beta * (1 - beta) :=
    mul_nonneg hbeta0 (sub_nonneg.mpr hbeta1)
  have hsq : beta ^ 2 ≤ 1 := by
    nlinarith
  have hc1 : c ≤ 1 := by
    dsimp [c]
    nlinarith
  have hgood : ∀ᶠ N : ℕ in atTop,
      c * (Real.log (N : ℝ)) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N beta := by
    simpa [c] using
      nativeLambdaTwoGoodRecipMass_eventually_quadratic_squarePrefix_rate
        beta hbeta hbeta1
  have himp := nativePNTSquarePrefixHasAffineEnvelope_improve_of_goodMass
    alpha beta c halpha hbeta0 hba hc hc1 hgood henv
  have hcoef :
      alpha - (alpha - beta) * c / 4 =
        alpha - nativePNTSquarePrefixLowSlopeCubicConstant * alpha ^ 3 := by
    dsimp [beta, c, nativePNTSquarePrefixLowSlopeCubicConstant]
    ring
  rw [hcoef] at himp
  exact himp

/-- The new low-slope update is pointwise strictly smaller than the previously
proved square-prefix cubic update for every positive slope.  This is the bound
contraction gate in a form that can be consumed directly by later quantitative
PNT and intercept arguments. -/
theorem nativePNTSquarePrefixLowSlope_step_lt_rederived_step
    (alpha : ℝ) (halpha : 0 < alpha) :
    alpha - nativePNTSquarePrefixLowSlopeCubicConstant * alpha ^ 3 <
      alpha - nativePNTSquarePrefixRederivedCubicConstant * alpha ^ 3 := by
  have hC := nativePNTSquarePrefixRederivedCubicConstant_lt_lowSlope
  have hpow : 0 < alpha ^ 3 := pow_pos halpha 3
  have hmul :
      nativePNTSquarePrefixRederivedCubicConstant * alpha ^ 3 <
        nativePNTSquarePrefixLowSlopeCubicConstant * alpha ^ 3 :=
    mul_lt_mul_of_pos_right hC hpow
  linarith

/-- Public bound-level acceptance theorem: in the low-slope regime the existing
square-prefix affine envelope advances to a rigorously valid and strictly
smaller slope than the old square-prefix step. -/
theorem nativePNTSquarePrefixLowSlope_affineEnvelope_strictly_tighter
    (alpha : ℝ) (halpha : 0 < alpha) (halphaSmall : alpha ≤ 3 / 2)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
        (alpha - nativePNTSquarePrefixLowSlopeCubicConstant * alpha ^ 3) ∧
      alpha - nativePNTSquarePrefixLowSlopeCubicConstant * alpha ^ 3 <
        alpha - nativePNTSquarePrefixRederivedCubicConstant * alpha ^ 3 := by
  exact ⟨
    nativePNTSquarePrefixHasAffineEnvelope_lowSlope_cubic_step
      alpha halpha halphaSmall henv,
    nativePNTSquarePrefixLowSlope_step_lt_rederived_step alpha halpha⟩

end RHLean.Analysis
