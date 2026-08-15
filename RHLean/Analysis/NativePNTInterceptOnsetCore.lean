import Mathlib
import RHLean.Analysis.NativePNTErdosContraction

/-!
# Explicit onset for one native PNT cubic contraction

This module exposes the exact large-scale conditions used by the existing
one-step contraction proof and chooses their least natural-number onset.
-/

noncomputable section

open Filter

namespace RHLean.Analysis

/-- An affine PNT envelope with a specified additive intercept. -/
def NativePNTAffineEnvelopeAt (alpha D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ N : ℕ,
    |nativePNTError N| ≤ alpha * (N : ℝ) + D

/-- Forgetting the specified intercept recovers the existing existential notion. -/
theorem nativePNTAffineEnvelopeAt.toHasAffineEnvelope
    {alpha D : ℝ} (h : NativePNTAffineEnvelopeAt alpha D) :
    nativePNTHasAffineEnvelope alpha := by
  exact ⟨D, h.1, h.2⟩

/-- The initial cubic envelope has intercept zero. -/
theorem nativePNTAffineEnvelopeAt_six_zero :
    NativePNTAffineEnvelopeAt 6 0 := by
  refine ⟨le_rfl, ?_⟩
  intro N
  have herr := nativePNTError_abs_le_const_mul N
  have hlog4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  have hC : Real.log 4 + 3 ≤ (6 : ℝ) := by
    norm_num at hlog4 ⊢
    linarith
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hC hN0
  simpa using herr.trans hmul

/-- Calibrated good-fibre threshold. -/
def nativePNTCubicStepBeta (alpha : ℝ) : ℝ := alpha / 6

/-- Calibrated quadratic good-mass coefficient. -/
def nativePNTCubicStepGoodCoeff (alpha : ℝ) : ℝ :=
  (nativePNTCubicStepBeta alpha) ^ 2 / 6500000

/-- One-step slope decrement before cubic normalization. -/
def nativePNTCubicStepDelta (alpha : ℝ) : ℝ :=
  (alpha - nativePNTCubicStepBeta alpha) *
    nativePNTCubicStepGoodCoeff alpha / 4

/-- Lower-order coefficient absorbed in the current proof. -/
def nativePNTCubicStepC0 (alpha D : ℝ) : ℝ :=
  3000 * alpha + 784 * D + 3000

/-- The calibrated decrement is exactly the repository cubic term. -/
theorem nativePNTCubicStepDelta_eq (alpha : ℝ) :
    nativePNTCubicStepDelta alpha =
      nativePNTCubicConstant * alpha ^ 3 := by
  change
    (alpha - alpha / 6) * ((alpha / 6) ^ 2 / 6500000) / 4 =
      (1 / 1123200000 : ℝ) * alpha ^ 3
  ring

/-- Exact sufficient large-scale conditions used by the current one-step proof. -/
def nativePNTCubicStepReady (alpha D : ℝ) (M : ℕ) : Prop :=
  ∀ N : ℕ, M ≤ N →
    3 ≤ N ∧
    nativePNTCubicStepGoodCoeff alpha *
        (Real.log (N : ℝ)) ^ 2 ≤
      nativeLambdaTwoGoodRecipMass N (nativePNTCubicStepBeta alpha) ∧
    (1 : ℝ) ≤ Real.log (N : ℝ) ∧
    nativePNTCubicStepC0 alpha D /
        (3 * nativePNTCubicStepDelta alpha) ≤
      Real.log (N : ℝ)

/-- The good-mass theorem and divergence of `log N` give a finite onset. -/
theorem nativePNTCubicStepReady_exists
    (alpha D : ℝ) (halpha : 0 < alpha) (halpha6 : alpha ≤ 6) :
    ∃ M : ℕ, nativePNTCubicStepReady alpha D M := by
  let beta : ℝ := nativePNTCubicStepBeta alpha
  let c : ℝ := nativePNTCubicStepGoodCoeff alpha
  let delta : ℝ := nativePNTCubicStepDelta alpha
  let C0 : ℝ := nativePNTCubicStepC0 alpha D
  have hbeta : 0 < beta := by
    dsimp [beta, nativePNTCubicStepBeta]
    positivity
  have hbeta1 : beta ≤ 1 := by
    dsimp [beta, nativePNTCubicStepBeta]
    linarith
  have hdelta : 0 < delta := by
    dsimp [delta]
    rw [nativePNTCubicStepDelta_eq]
    exact mul_pos
      (by norm_num [nativePNTCubicConstant])
      (pow_pos halpha 3)
  have hgood : ∀ᶠ N : ℕ in atTop,
      c * (Real.log (N : ℝ)) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N beta := by
    simpa [c, beta, nativePNTCubicStepGoodCoeff,
      nativePNTCubicStepBeta] using
      nativeLambdaTwoGoodRecipMass_eventually_quadratic_rate
        beta hbeta hbeta1
  have hlogTop :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog1 : ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) ≤ Real.log (N : ℝ) :=
    hlogTop.eventually_ge_atTop 1
  have hlogC : ∀ᶠ N : ℕ in atTop,
      C0 / (3 * delta) ≤ Real.log (N : ℝ) :=
    hlogTop.eventually_ge_atTop (C0 / (3 * delta))
  have hready : ∀ᶠ N : ℕ in atTop,
      3 ≤ N ∧
      c * (Real.log (N : ℝ)) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N beta ∧
      (1 : ℝ) ≤ Real.log (N : ℝ) ∧
      C0 / (3 * delta) ≤ Real.log (N : ℝ) := by
    filter_upwards [eventually_ge_atTop 3, hgood, hlog1, hlogC]
      with N hN hgoodN hL1 hLC
    exact ⟨hN, hgoodN, hL1, hLC⟩
  rcases eventually_atTop.1 hready with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro N hMN
  have h := hM N hMN
  simpa [nativePNTCubicStepReady, c, beta, delta, C0] using h

/-- Least onset for the sufficient conditions of the current cubic step. -/
noncomputable def nativePNTCubicStepOnset (alpha D : ℝ) : ℕ := by
  classical
  exact if h : 0 < alpha ∧ alpha ≤ 6 ∧ 0 ≤ D then
    Nat.find (nativePNTCubicStepReady_exists alpha D h.1 h.2.1)
  else 0

/-- The canonical onset satisfies all sufficient conditions. -/
theorem nativePNTCubicStepOnset_spec
    (alpha D : ℝ) (halpha : 0 < alpha) (halpha6 : alpha ≤ 6)
    (hD : 0 ≤ D) :
    nativePNTCubicStepReady alpha D
      (nativePNTCubicStepOnset alpha D) := by
  classical
  rw [nativePNTCubicStepOnset, dif_pos ⟨halpha, halpha6, hD⟩]
  exact Nat.find_spec
    (nativePNTCubicStepReady_exists alpha D halpha halpha6)

/-- The current onset is at least three. -/
theorem nativePNTCubicStepOnset_three_le
    (alpha D : ℝ) (halpha : 0 < alpha) (halpha6 : alpha ≤ 6)
    (hD : 0 ≤ D) :
    3 ≤ nativePNTCubicStepOnset alpha D := by
  have hready := nativePNTCubicStepOnset_spec
    alpha D halpha halpha6 hD
  exact (hready _ le_rfl).1

/-- The current lower-order absorption forces this logarithmic onset. -/
theorem nativePNTCubicStepOnset_log_lower
    (alpha D : ℝ) (halpha : 0 < alpha) (halpha6 : alpha ≤ 6)
    (hD : 0 ≤ D) :
    nativePNTCubicStepC0 alpha D /
        (3 * nativePNTCubicStepDelta alpha) ≤
      Real.log ((nativePNTCubicStepOnset alpha D : ℕ) : ℝ) := by
  have hready := nativePNTCubicStepOnset_spec
    alpha D halpha halpha6 hD
  exact (hready _ le_rfl).2.2.2

/-- Exponentiated form of the onset obstruction. -/
theorem nativePNTCubicStepOnset_exp_lower
    (alpha D : ℝ) (halpha : 0 < alpha) (halpha6 : alpha ≤ 6)
    (hD : 0 ≤ D) :
    Real.exp
        (nativePNTCubicStepC0 alpha D /
          (3 * nativePNTCubicStepDelta alpha)) ≤
      (nativePNTCubicStepOnset alpha D : ℝ) := by
  have hlog := nativePNTCubicStepOnset_log_lower
    alpha D halpha halpha6 hD
  have hM3 := nativePNTCubicStepOnset_three_le
    alpha D halpha halpha6 hD
  have hMpos : (0 : ℝ) < (nativePNTCubicStepOnset alpha D : ℝ) := by
    exact_mod_cast (show 0 < nativePNTCubicStepOnset alpha D by omega)
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hMpos] at hexp
  exact hexp

end RHLean.Analysis
