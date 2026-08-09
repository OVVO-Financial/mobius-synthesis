import Mathlib
import RHLean.Proof.SquareBlockTransportBaseline

/-!
# Dynamic-denominator Viole baseline

This module formalizes the square-block prime-counting baseline tested in
`experiments/vf_dynamic_e_asymptote_test.py`.

The original Viole function used one fixed logarithmic-base convergence rate.
The corrected empirical study replaces that fixed rate by

```text
log b(x) = 1 + a / log x + b / (log x)^2,
a = 40.64408021414064,
b = -233.433772115277.
```

The leading constant is `1`, so the effective base satisfies `b(x) -> e` as
`x -> infinity`. The coefficients below are represented as exact rationals.
They were fitted on square-block midpoints from `10^3` through `10^5` and then
frozen before testing through `10^8`.

This file formalizes only the deterministic function and its exact insertion
into the existing arbitrary-baseline decomposition. It does not assert any
prime-counting error estimate, asymptotic superiority over `li`, or RH
implication.
-/

noncomputable section

namespace RHLean.Proof

/-- Fitted coefficient of `1 / log x` in the corrected dynamic logarithmic-base
exponent. The full fitted decimal `40.64408021414064` is stored exactly. -/
def dynamicVioleFitA : ℝ :=
  4064408021414064 / 100000000000000

/-- Fitted coefficient of `1 / (log x)^2` in the corrected dynamic
logarithmic-base exponent. The full fitted decimal `-233.433772115277` is
stored exactly. -/
def dynamicVioleFitB : ℝ :=
  -(233433772115277 / 1000000000000)

/-- The fitted value of `log b(x)`, where `b(x)` is the effective logarithmic
base used by the dynamic Viole denominator. The leading constant `1` encodes
the intended asymptotic base `e`. -/
def dynamicVioleLogBaseExponent (x : ℝ) : ℝ :=
  1 + dynamicVioleFitA / Real.log x +
    dynamicVioleFitB / (Real.log x) ^ 2

/-- The corresponding positive formal base `b(x) = exp(log b(x))`.
Positivity follows from `Real.exp_pos`; no claim is made here that the fitted
exponent itself is positive on every real input. -/
def dynamicVioleLogBase (x : ℝ) : ℝ :=
  Real.exp (dynamicVioleLogBaseExponent x)

/-- Dynamic replacement for the original fixed-base convergence correction.
Writing `L = log x` and `s = log b(x)`, this is

`(1 + L / s) * log (1 + s / L)`,

the logarithm of `(1 + 1 / log_b x)^(1 + log_b x)`. -/
def dynamicVioleCorrection (x : ℝ) : ℝ :=
  let L := Real.log x
  let s := dynamicVioleLogBaseExponent x
  (1 + L / s) * Real.log (1 + s / L)

/-- Square-block midpoint `r^2 + r + 1/2`. -/
def dynamicVioleSquareMidpoint (r : ℕ) : ℝ :=
  ((r ^ 2 : ℕ) : ℝ) + (r : ℝ) + 1 / 2

/-- The original square-block numerator `r^2`. -/
def dynamicVioleSquareNumerator (r : ℕ) : ℝ :=
  ((r ^ 2 : ℕ) : ℝ)

/-- Dynamic Viole denominator at the midpoint of square block `r`.
This is the exact denominator used by the empirically selected model. -/
def dynamicVioleDenominator (r : ℕ) : ℝ :=
  Real.log (dynamicVioleSquareNumerator r) -
    dynamicVioleCorrection (dynamicVioleSquareMidpoint r)

/-- Dynamic Viole anchor attached to the midpoint of square block `r`. -/
def dynamicVioleAnchor (r : ℕ) : ℝ :=
  dynamicVioleSquareNumerator r / dynamicVioleDenominator r

/-- Distance between consecutive square-block midpoint nodes. -/
theorem dynamicVioleSquareMidpoint_succ_sub (r : ℕ) :
    dynamicVioleSquareMidpoint (r + 1) - dynamicVioleSquareMidpoint r =
      2 * (r : ℝ) + 2 := by
  unfold dynamicVioleSquareMidpoint
  push_cast
  ring

/-- Linear interpolation of the dynamic Viole anchors on the segment from the
`r`th square midpoint to the next midpoint. -/
def dynamicVioleLinearSegment (r : ℕ) (x : ℝ) : ℝ :=
  dynamicVioleAnchor r +
    ((x - dynamicVioleSquareMidpoint r) / (2 * (r : ℝ) + 2)) *
      (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r)

@[simp] theorem dynamicVioleLinearSegment_left (r : ℕ) :
    dynamicVioleLinearSegment r (dynamicVioleSquareMidpoint r) =
      dynamicVioleAnchor r := by
  simp [dynamicVioleLinearSegment]

@[simp] theorem dynamicVioleLinearSegment_right (r : ℕ) :
    dynamicVioleLinearSegment r (dynamicVioleSquareMidpoint (r + 1)) =
      dynamicVioleAnchor (r + 1) := by
  have h : (2 * (r : ℝ) + 2) ≠ 0 := by positivity
  simp [dynamicVioleLinearSegment, dynamicVioleSquareMidpoint_succ_sub, h]

/-- Index of the midpoint segment containing a nonnegative real coordinate.
The closed-form inversion comes from solving `r^2 + r + 1/2 ≤ x` for `r`.
For inputs below the first meaningful prime-counting block, natural flooring
provides the harmless fallback index `0`. -/
def dynamicVioleMidpointIndex (x : ℝ) : ℕ :=
  Nat.floor ((Real.sqrt (4 * x - 1) - 1) / 2)

/-- Continuous piecewise-linear dynamic Viole baseline through the midpoint
anchors. This is the cumulative real-valued baseline used in the exact-activity
interval experiment. -/
def dynamicVioleBaselineReal (x : ℝ) : ℝ :=
  dynamicVioleLinearSegment (dynamicVioleMidpointIndex x) x

/-- Complex-valued wrapper required by the generic square-block transport
baseline API. -/
def dynamicVioleBaseline (x : ℝ) : ℂ :=
  (dynamicVioleBaselineReal x : ℂ)

/-- Exact specialization of the existing arbitrary-baseline decomposition to
the corrected dynamic Viole baseline. This is algebraic and imports no
empirical error claim. -/
theorem squarePrefixMertens_eq_dynamicVioleMain_sub_error (n : ℕ) :
    RHLean.Analysis.squarePrefixMertens n =
      squareBlockBaselineMainPrefix dynamicVioleBaseline n -
        squareBlockBaselineTransportErrorPrefix dynamicVioleBaseline n := by
  exact squarePrefixMertens_eq_baselineMain_sub_error dynamicVioleBaseline n

end RHLean.Proof
