import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixCompensated
import RHLean.Analysis.NativePNTSquarePrefixGoodMassRate

/-!
# Cubic contraction on the fully rederived square-prefix path

The density input is the complete-square good-mass theorem.  The contraction
input is the Möbius-rederived compensated squared recurrence.  This module
therefore supplies a fresh cubic slope sequence whose dependency graph does not
pass through the earlier compensated recurrence.
-/

noncomputable section

open Filter
open scoped Topology

namespace RHLean.Analysis

/-- Cubic constant supplied by the square-prefix good-mass coefficient. -/
def nativePNTSquarePrefixRederivedCubicConstant : ℝ := 1 / 1140480000

/-- One fully rederived affine-envelope contraction step. -/
theorem nativePNTSquarePrefixRederivedHasAffineEnvelope_cubic_step
    (alpha : ℝ) (halpha : 0 < alpha) (halpha6 : alpha ≤ 6)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
      (alpha - nativePNTSquarePrefixRederivedCubicConstant * alpha ^ 3) := by
  let beta : ℝ := alpha / 6
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hbeta0 : 0 ≤ beta := hbeta.le
  have hbeta1 : beta ≤ 1 := by dsimp [beta]; linarith
  have hba : beta < alpha := by dsimp [beta]; nlinarith
  let c : ℝ := beta ^ 2 / 6600000
  have hc : 0 < c := by dsimp [c]; positivity
  have hsq : beta ^ 2 ≤ 1 := by
    have hprod : 0 ≤ beta * (1 - beta) :=
      mul_nonneg hbeta0 (sub_nonneg.mpr hbeta1)
    nlinarith
  have hc1 : c ≤ 1 := by dsimp [c]; nlinarith
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
        alpha - nativePNTSquarePrefixRederivedCubicConstant * alpha ^ 3 := by
    dsimp [beta, c, nativePNTSquarePrefixRederivedCubicConstant]
    ring
  rw [hcoef] at himp
  exact himp

private theorem nativePNTSquarePrefixRederived_cubic_step_pos
    (alpha : ℝ) (halpha : 0 < alpha) (halpha6 : alpha ≤ 6) :
    0 < alpha - nativePNTSquarePrefixRederivedCubicConstant * alpha ^ 3 := by
  have hsq : alpha ^ 2 ≤ (6 : ℝ) ^ 2 :=
    pow_le_pow_left₀ halpha.le halpha6 2
  have hC0 : 0 ≤ nativePNTSquarePrefixRederivedCubicConstant := by
    norm_num [nativePNTSquarePrefixRederivedCubicConstant]
  have hmul :
      nativePNTSquarePrefixRederivedCubicConstant * alpha ^ 2 ≤
        nativePNTSquarePrefixRederivedCubicConstant * (6 : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hC0
  have hC36 : nativePNTSquarePrefixRederivedCubicConstant * (6 : ℝ) ^ 2 < 1 := by
    norm_num [nativePNTSquarePrefixRederivedCubicConstant]
  have hfactor : 0 < 1 - nativePNTSquarePrefixRederivedCubicConstant * alpha ^ 2 := by
    linarith
  have hrewrite :
      alpha - nativePNTSquarePrefixRederivedCubicConstant * alpha ^ 3 =
        alpha * (1 - nativePNTSquarePrefixRederivedCubicConstant * alpha ^ 2) := by
    ring
  rw [hrewrite]
  exact mul_pos halpha hfactor

/-- Slope sequence driven by the fully rederived square-prefix contraction. -/
def nativePNTSquarePrefixRederivedCubicSlope : ℕ → ℝ
  | 0 => 6
  | Nat.succ n =>
      nativePNTSquarePrefixRederivedCubicSlope n -
        nativePNTSquarePrefixRederivedCubicConstant *
          (nativePNTSquarePrefixRederivedCubicSlope n) ^ 3

@[simp] theorem nativePNTSquarePrefixRederivedCubicSlope_zero :
    nativePNTSquarePrefixRederivedCubicSlope 0 = 6 := rfl

@[simp] theorem nativePNTSquarePrefixRederivedCubicSlope_succ (n : ℕ) :
    nativePNTSquarePrefixRederivedCubicSlope (n + 1) =
      nativePNTSquarePrefixRederivedCubicSlope n -
        nativePNTSquarePrefixRederivedCubicConstant *
          (nativePNTSquarePrefixRederivedCubicSlope n) ^ 3 := rfl

/-- Every rederived square-prefix slope remains positive, at most six, and is
realized by an affine error envelope. -/
theorem nativePNTSquarePrefixRederivedCubicSlope_spec :
    ∀ n : ℕ,
      0 < nativePNTSquarePrefixRederivedCubicSlope n ∧
      nativePNTSquarePrefixRederivedCubicSlope n ≤ 6 ∧
      nativePNTHasAffineEnvelope (nativePNTSquarePrefixRederivedCubicSlope n) := by
  intro n
  induction n with
  | zero => exact ⟨by norm_num, le_rfl, nativePNTHasAffineEnvelope_six⟩
  | succ n ih =>
      rcases ih with ⟨hpos, hle6, henv⟩
      have hnextpos := nativePNTSquarePrefixRederived_cubic_step_pos
        (nativePNTSquarePrefixRederivedCubicSlope n) hpos hle6
      have hnextenv := nativePNTSquarePrefixRederivedHasAffineEnvelope_cubic_step
        (nativePNTSquarePrefixRederivedCubicSlope n) hpos hle6 henv
      have hdrop :
          0 ≤ nativePNTSquarePrefixRederivedCubicConstant *
            (nativePNTSquarePrefixRederivedCubicSlope n) ^ 3 :=
        mul_nonneg (by norm_num [nativePNTSquarePrefixRederivedCubicConstant])
          (pow_nonneg hpos.le 3)
      have hnextle :
          nativePNTSquarePrefixRederivedCubicSlope (n + 1) ≤
            nativePNTSquarePrefixRederivedCubicSlope n := by
        rw [nativePNTSquarePrefixRederivedCubicSlope_succ]
        exact sub_le_self _ hdrop
      exact ⟨by simpa using hnextpos, hnextle.trans hle6,
        by simpa using hnextenv⟩

/-- The fully rederived cubic slope tends to zero. -/
theorem nativePNTSquarePrefixRederivedCubicSlope_tendsto_zero :
    Tendsto nativePNTSquarePrefixRederivedCubicSlope atTop (𝓝 0) := by
  refine tendsto_zero_of_cubic_recurrence
    nativePNTSquarePrefixRederivedCubicSlope
    nativePNTSquarePrefixRederivedCubicConstant ?_ ?_ ?_
  · norm_num [nativePNTSquarePrefixRederivedCubicConstant]
  · intro n
    exact (nativePNTSquarePrefixRederivedCubicSlope_spec n).1.le
  · intro n
    rw [nativePNTSquarePrefixRederivedCubicSlope_succ]

/-- Explicit finite-step rate for the fully rederived cubic sequence. -/
theorem nativePNTSquarePrefixRederivedCubicSlope_rate (n : ℕ) :
    nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) *
        (nativePNTSquarePrefixRederivedCubicSlope n) ^ 3 ≤ 6 := by
  have hC : 0 < nativePNTSquarePrefixRederivedCubicConstant := by
    norm_num [nativePNTSquarePrefixRederivedCubicConstant]
  have hnonneg : ∀ m, 0 ≤ nativePNTSquarePrefixRederivedCubicSlope m :=
    fun m => (nativePNTSquarePrefixRederivedCubicSlope_spec m).1.le
  have hrec : ∀ m,
      nativePNTSquarePrefixRederivedCubicSlope (m + 1) ≤
        nativePNTSquarePrefixRederivedCubicSlope m -
          nativePNTSquarePrefixRederivedCubicConstant *
            (nativePNTSquarePrefixRederivedCubicSlope m) ^ 3 := by
    intro m
    rw [nativePNTSquarePrefixRederivedCubicSlope_succ]
  simpa using
    (cubic_recurrence_rate nativePNTSquarePrefixRederivedCubicSlope
      nativePNTSquarePrefixRederivedCubicConstant hC hnonneg hrec n)

/-- Any finite budget satisfying the cubic inequality realizes the target
square-prefix affine slope. -/
theorem nativePNTSquarePrefixRederivedHasAffineEnvelope_of_cubic_budget
    (eta : ℝ) (heta : 0 < eta) (n : ℕ)
    (hbudget :
      6 < nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) * eta ^ 3) :
    nativePNTHasAffineEnvelope eta := by
  have hspec := nativePNTSquarePrefixRederivedCubicSlope_spec n
  have hslopeEta : nativePNTSquarePrefixRederivedCubicSlope n ≤ eta := by
    by_contra hnot
    have hetaSlope : eta < nativePNTSquarePrefixRederivedCubicSlope n :=
      lt_of_not_ge hnot
    have hcube : eta ^ 3 ≤ (nativePNTSquarePrefixRederivedCubicSlope n) ^ 3 :=
      pow_le_pow_left₀ heta.le hetaSlope.le 3
    have hcoef0 :
        0 ≤ nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) :=
      mul_nonneg
        (by norm_num [nativePNTSquarePrefixRederivedCubicConstant]) (by positivity)
    have hmul :
        nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) * eta ^ 3 ≤
          nativePNTSquarePrefixRederivedCubicConstant * (n : ℝ) *
            (nativePNTSquarePrefixRederivedCubicSlope n) ^ 3 :=
      mul_le_mul_of_nonneg_left hcube hcoef0
    have hrate := nativePNTSquarePrefixRederivedCubicSlope_rate n
    linarith
  exact nativePNTHasAffineEnvelope_mono hslopeEta hspec.2.2

end RHLean.Analysis
