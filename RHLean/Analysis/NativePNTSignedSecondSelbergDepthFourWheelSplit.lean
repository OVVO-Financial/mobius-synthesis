import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelbergDepthFourShell

/-!
# Exact partial-wheel split of the depth-four signed K2 shell

This module keeps the factor-four reciprocal interval in the prime-wheel
coordinate.  The Möbius coefficient is split pointwise into the corrected
partial wheel through `y` plus its exact wheel error.  Under `N < 4*y^2`, the
wheel-error term is supported entirely in the top factor-four shell and every
active reciprocal quotient is one of `1,2,3`.

No estimate is taken here.  The purpose is to isolate the two pieces on which
the depth-controlled interval cancellation theorem must act.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Reciprocal log-square weight attached to the corrected partial wheel. -/
def nativePNTDepthFourResolvedWheelWeight
    (y N d : ℕ) : ℝ :=
  ((partialPrimeWheelSite y N d : ℤ) : ℝ) *
    (Real.log (d : ℝ)) ^ 2 / (d : ℝ)

/-- Reciprocal log-square weight carried by the exact partial-wheel error. -/
def nativePNTDepthFourFrontierWheelWeight
    (y N d : ℕ) : ℝ :=
  (((μ : ArithmeticFunction ℝ) d) -
      ((partialPrimeWheelSite y N d : ℤ) : ℝ)) *
    (Real.log (d : ℝ)) ^ 2 / (d : ℝ)

/-- Resolved partial-wheel contribution to the factor-four harmonic shell. -/
def nativePNTDepthFourResolvedWheelShell
    (y N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    nativePNTDepthFourResolvedWheelWeight y N d *
      nativePNTDepthFourHarmonicShell N d

/-- Exact wheel-frontier contribution to the factor-four harmonic shell. -/
def nativePNTDepthFourFrontierWheelShell
    (y N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    nativePNTDepthFourFrontierWheelWeight y N d *
      nativePNTDepthFourHarmonicShell N d

/-- Pointwise Möbius log-square weight splits exactly into the corrected wheel
weight and the wheel-error weight. -/
theorem nativeMobiusLogSquareRecipWeight_eq_depthFourWheel_split
    (y N d : ℕ) :
    nativeMobiusLogSquareRecipWeight d =
      nativePNTDepthFourResolvedWheelWeight y N d +
        nativePNTDepthFourFrontierWheelWeight y N d := by
  unfold nativeMobiusLogSquareRecipWeight
    nativePNTDepthFourResolvedWheelWeight
    nativePNTDepthFourFrontierWheelWeight
  ring_nf

/-- **Exact depth-four wheel split.**  The signed K2 reciprocal interval is the
sum of its resolved partial-wheel shell and its exact unresolved frontier. -/
theorem nativePNTSignedK2RecipInterval_four_eq_resolved_add_frontier
    (y N : ℕ) :
    nativePNTSignedK2RecipInterval N 4 =
      nativePNTDepthFourResolvedWheelShell y N +
        nativePNTDepthFourFrontierWheelShell y N := by
  rw [nativePNTSignedK2RecipInterval_four_eq_mobius_harmonic_shell]
  unfold nativePNTDepthFourResolvedWheelShell
    nativePNTDepthFourFrontierWheelShell
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [nativeMobiusLogSquareRecipWeight_eq_depthFourWheel_split]
  ring_nf

/-- Above the lower factor-four endpoint, the lower harmonic endpoint is zero. -/
theorem nativePNTDepthFourHarmonicShell_eq_harmonic_of_quarter_lt
    (N d : ℕ) (hquarter : N / 4 < d) :
    nativePNTDepthFourHarmonicShell N d = (harmonic (N / d) : ℝ) := by
  unfold nativePNTDepthFourHarmonicShell
  have hzero : (N / 4) / d = 0 := Nat.div_eq_of_lt hquarter
  simp [hzero]

/-- A nonzero depth-four wheel error sees only the finite harmonic weights
`H_1`, `H_2`, or `H_3`. -/
theorem nativePNTDepthFour_frontier_harmonic_finite
    (y N d : ℕ)
    (hscale : N < 4 * y ^ 2)
    (hd : d ∈ Finset.Icc 1 N)
    (herr : μ d - partialPrimeWheelSite y N d ≠ 0) :
    nativePNTDepthFourHarmonicShell N d = (harmonic (N / d) : ℝ) ∧
      1 ≤ N / d ∧ N / d < 4 := by
  have hshell := partialPrimeWheel_nonzero_error_depth_four_shell
    y N d hscale hd herr
  exact ⟨
    nativePNTDepthFourHarmonicShell_eq_harmonic_of_quarter_lt
      N d hshell.1,
    hshell.2.1,
    hshell.2.2⟩

/-- Explicit finite list of possible harmonic values on the depth-four wheel
frontier. -/
theorem nativePNTDepthFour_frontier_harmonic_eq_one_or_three_halves_or_eleven_sixths
    (y N d : ℕ)
    (hscale : N < 4 * y ^ 2)
    (hd : d ∈ Finset.Icc 1 N)
    (herr : μ d - partialPrimeWheelSite y N d ≠ 0) :
    nativePNTDepthFourHarmonicShell N d = 1 ∨
      nativePNTDepthFourHarmonicShell N d = (3 : ℝ) / 2 ∨
      nativePNTDepthFourHarmonicShell N d = (11 : ℝ) / 6 := by
  rcases nativePNTDepthFour_frontier_harmonic_finite
      y N d hscale hd herr with ⟨hshell, hlo, hhi⟩
  have hcases : N / d = 1 ∨ N / d = 2 ∨ N / d = 3 := by omega
  rcases hcases with hq | hq | hq
  · left
    rw [hshell, hq]
    norm_num [harmonic]
  · right; left
    rw [hshell, hq]
    norm_num [harmonic, harmonic_succ]
  · right; right
    rw [hshell, hq]
    norm_num [harmonic, harmonic_succ]

end RHLean.Analysis
