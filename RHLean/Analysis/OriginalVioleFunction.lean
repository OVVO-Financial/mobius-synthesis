import Mathlib

/-!
# Original parameter-free Viole function

This module formalizes the original Viole Function exactly as published.  It
has no fitted coefficients and does not use `pi(x)` as an input.

For a real input `x`, set

```text
N(x) = floor(sqrt(x))^2,
t(x) = log_10(x),
C(x) = (1 + 1 / t(x))^(1 + t(x)).
```

The continuous core of the original estimator is

```text
VF(x) = N(x) / log(N(x) / C(x)).
```

The published R implementation then applies `floor` and truncates below at
zero.  The dynamic object is the parameter-free correction `C(x)`, not a pair
of calibrated coefficients.

The same estimator has an implied logarithmic base.  Its normalized form is

```text
log b_VF(x) = 1 / (1 - log(C(x)) / log(N(x))).
```

Consequently, once the correction ratio tends to zero, the implied base tends
to `exp 1 = e`.  The final theorem below isolates this elementary analytic
step from the separate limit proofs for the Euler sequence and square-floor
numerator.
-/

noncomputable section

open Filter Topology

namespace RHLean.Analysis

/-- Base-ten logarithm written by change of base. -/
def originalVFLog10 (x : ℝ) : ℝ :=
  Real.log x / Real.log 10

/-- The squared floor of the square root used by the published VF numerator. -/
def originalVFSquareNumerator (x : ℝ) : ℝ :=
  ((Nat.floor (Real.sqrt x) : ℕ) : ℝ) ^ 2

/-- The parameter-free Euler correction from the original VF. -/
def originalVFEulerCorrection (x : ℝ) : ℝ :=
  let t := originalVFLog10 x
  Real.rpow (1 + 1 / t) (1 + t)

/-- The natural-log denominator appearing in the original VF. -/
def originalVFDenominator (x : ℝ) : ℝ :=
  Real.log (originalVFSquareNumerator x / originalVFEulerCorrection x)

/-- The continuous core of the published estimator, before flooring and
truncation at zero. -/
def originalVFContinuous (x : ℝ) : ℝ :=
  originalVFSquareNumerator x / originalVFDenominator x

/-- The exact integer-valued post-processing used in the published R code. -/
def originalVF (x : ℝ) : ℕ :=
  Nat.floor (max 0 (originalVFContinuous x))

/-- Ratio controlling the implied dynamic logarithmic base. -/
def originalVFCorrectionRatio (x : ℝ) : ℝ :=
  Real.log (originalVFEulerCorrection x) /
    Real.log (originalVFSquareNumerator x)

/-- The implied logarithm of the dynamic base of the original VF. -/
def originalVFImpliedLogBase (x : ℝ) : ℝ :=
  1 / (1 - originalVFCorrectionRatio x)

/-- The implied dynamic logarithmic base of the original VF. -/
def originalVFImpliedBase (x : ℝ) : ℝ :=
  Real.exp (originalVFImpliedLogBase x)

/-- The original VF implied base is positive at every input. -/
theorem originalVFImpliedBase_pos (x : ℝ) :
    0 < originalVFImpliedBase x := by
  exact Real.exp_pos _

/-- The analytic final step: if the correction contributes a vanishing share
of the main logarithm, then the original VF's implied base tends to `e`. -/
theorem originalVFImpliedBase_tendsto_e
    (hRatio : Tendsto originalVFCorrectionRatio atTop (𝓝 0)) :
    Tendsto originalVFImpliedBase atTop (𝓝 (Real.exp 1)) := by
  have hcont : ContinuousAt (fun z : ℝ => Real.exp (1 / (1 - z))) 0 := by
    fun_prop (disch := norm_num)
  change Tendsto (fun x : ℝ => Real.exp (1 / (1 - originalVFCorrectionRatio x)))
    atTop (𝓝 (Real.exp 1))
  have htarget : Real.exp (1 / (1 - (0 : ℝ))) = Real.exp 1 := by
    norm_num
  simpa only [Function.comp_apply, htarget] using hcont.tendsto.comp hRatio

end RHLean.Analysis