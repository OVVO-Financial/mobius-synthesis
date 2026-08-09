import Mathlib

/-!
# Exact optimum logarithmic base

For a real-valued counting function `P`, the logarithmic base that makes

`x / log_b(x) = P(x)`

is obtained exactly from change of base:

`log b = P(x) * log x / x`.

Thus

`b_opt(x) = exp (P(x) * log x / x) = x ^ (P(x) / x)`

on the positive real domain.  When `P` is the prime-counting function, the
prime number theorem is precisely the statement that the exponent tends to
`1`; continuity of `exp` then gives `b_opt(x) -> e`.

This file deliberately states the asymptotic theorem against the PNT ratio as
an explicit hypothesis.  It therefore isolates the elementary optimum-base
argument from whichever formal prime-number-theorem theorem is later used to
supply that hypothesis.
-/

noncomputable section

open Filter Topology

namespace RHLean.Analysis

/-- Real logarithm to an arbitrary base, written by change of base. -/
def logBase (b x : ℝ) : ℝ :=
  Real.log x / Real.log b

/-- The exact logarithmic base that makes `x / log_b x` reproduce the supplied
counting function `P`, whenever the relevant denominators are nonzero. -/
def optimalLogBase (P : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (P x * Real.log x / x)

/-- The exact optimum logarithmic base is always positive. -/
theorem optimalLogBase_pos (P : ℝ → ℝ) (x : ℝ) :
    0 < optimalLogBase P x := by
  exact Real.exp_pos _

/-- The logarithm of the optimum base is exactly the normalized counting
ratio. -/
@[simp] theorem log_optimalLogBase (P : ℝ → ℝ) (x : ℝ) :
    Real.log (optimalLogBase P x) = P x * Real.log x / x := by
  simp [optimalLogBase]

/-- Multiplicative change-of-base form of the exact reconstruction identity. -/
theorem optimalLogBase_reconstructs_mul
    (P : ℝ → ℝ) {x : ℝ} (hx : x ≠ 0) (hlogx : Real.log x ≠ 0) :
    x * Real.log (optimalLogBase P x) / Real.log x = P x := by
  rw [log_optimalLogBase]
  field_simp

/-- Exact reconstruction in the original form `x / log_(b_opt x) x = P x`. -/
theorem x_div_logBase_optimalLogBase
    (P : ℝ → ℝ) {x : ℝ}
    (hx : x ≠ 0) (hlogx : Real.log x ≠ 0) (hPx : P x ≠ 0) :
    x / logBase (optimalLogBase P x) x = P x := by
  rw [logBase, log_optimalLogBase]
  field_simp

/-- A prime-number-theorem ratio tending to `1` forces the corresponding exact
optimum logarithmic base to tend to Euler's number `e = exp 1`. -/
theorem optimalLogBase_tendsto_e
    (P : ℝ → ℝ)
    (hPNT : Tendsto (fun x : ℝ => P x * Real.log x / x) atTop (𝓝 1)) :
    Tendsto (optimalLogBase P) atTop (𝓝 (Real.exp 1)) := by
  have hExp : ContinuousAt Real.exp (1 : ℝ) := by
    fun_prop
  simpa [optimalLogBase, Function.comp_def] using hExp.tendsto.comp hPNT

/-- Equivalent formulation using the normalized ratio as a named function. -/
def normalizedCountingRatio (P : ℝ → ℝ) (x : ℝ) : ℝ :=
  P x * Real.log x / x

@[simp] theorem optimalLogBase_eq_exp_normalizedCountingRatio
    (P : ℝ → ℝ) (x : ℝ) :
    optimalLogBase P x = Real.exp (normalizedCountingRatio P x) := by
  rfl

/-- The asymptotic result in terms of `normalizedCountingRatio`. -/
theorem optimalLogBase_tendsto_e_of_normalizedCountingRatio
    (P : ℝ → ℝ)
    (hPNT : Tendsto (normalizedCountingRatio P) atTop (𝓝 1)) :
    Tendsto (optimalLogBase P) atTop (𝓝 (Real.exp 1)) := by
  apply optimalLogBase_tendsto_e P
  simpa [normalizedCountingRatio] using hPNT

end RHLean.Analysis