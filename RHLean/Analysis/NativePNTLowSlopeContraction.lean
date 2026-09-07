import Mathlib
import RHLean.Analysis.NativePNTErdosContraction

/-!
# Sharpen the native PNT cubic coefficient at low slope

The global PNT recurrence uses the convenient choice `beta = alpha / 6`.
For `alpha <= 3/2`, the deficit is proportional to
`(alpha-beta) * beta^2`, so the optimal admissible choice is
`beta = 2*alpha/3`.

There was one further purely quantitative loss in the existing contraction:
`nativePNTHasAffineEnvelope_improve_of_goodMass` retained only one quarter of
the available good-mass deficit.  The other three quarters were spent absorbing
terms of size `O(N log N)`, although the deficit itself has size
`N (log N)^2`.  Moving the onset farther out lets the same argument retain one
half of the deficit with no new analytic premise.

This file therefore improves the actual affine-envelope bound.  No new carrier,
coordinate, reindexing, or auxiliary state is introduced.
-/

noncomputable section

open Filter

namespace RHLean.Analysis

/-- **Half-deficit affine contraction.**  This is the same good-mass mechanism
as `nativePNTHasAffineEnvelope_improve_of_goodMass`, but it retains one half of
the available quadratic good-mass deficit instead of one quarter.  The only
change is a later onset: the positive remainder is `O(N log N)`, so it can be
made smaller than one half of the `N (log N)^2` deficit. -/
theorem nativePNTHasAffineEnvelope_improve_of_goodMass_half
    (alpha beta c : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 ≤ beta) (hba : beta < alpha)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hgood : ∀ᶠ N : ℕ in atTop,
      c * (Real.log (N : ℝ)) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N beta)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
      (alpha - (alpha - beta) * c / 2) := by
  rcases henv with ⟨D, hD, henv⟩
  let delta : ℝ := (alpha - beta) * c / 2
  have habpos : 0 < alpha - beta := sub_pos.mpr hba
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hable : alpha - beta ≤ alpha := by linarith
  have hmul : (alpha - beta) * c ≤ alpha := by
    have := mul_le_mul hable hc1 hc.le halpha.le
    simpa using this
  have hdeltale : delta ≤ alpha / 2 := by
    dsimp [delta]
    nlinarith
  have hnewnonneg : 0 ≤ alpha - delta := by
    nlinarith
  let C0 : ℝ := 3000 * alpha + 784 * D + 3000
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hlogTop :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog1 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (N : ℝ) :=
    hlogTop.eventually_ge_atTop 1
  have hlogC : ∀ᶠ N : ℕ in atTop,
      C0 / delta ≤ Real.log (N : ℝ) :=
    hlogTop.eventually_ge_atTop (C0 / delta)
  have hlarge : ∀ᶠ N : ℕ in atTop,
      |nativePNTError N| ≤ (alpha - delta) * (N : ℝ) := by
    filter_upwards [eventually_ge_atTop 3, hgood, hlog1, hlogC]
      with N hN hgoodN hL1 hLC
    have hN1 : 1 ≤ N := by omega
    have hNR0 : 0 ≤ (N : ℝ) := by positivity
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    let L : ℝ := Real.log (N : ℝ)
    have hL1' : (1 : ℝ) ≤ L := by simpa [L] using hL1
    have hL0 : 0 ≤ L := le_trans (by norm_num) hL1'
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL1'
    have hden : 0 < delta := hdelta
    have hCLe0 : C0 ≤ L * delta := by
      apply (div_le_iff₀ hden).mp
      simpa [L] using hLC
    have hCLe : C0 ≤ delta * L := by
      simpa [mul_comm] using hCLe0
    have hB0 : 0 ≤ 2000 * alpha + 782 * D := by positivity
    have hBLe :
        2000 * alpha + 782 * D ≤
          (2000 * alpha + 782 * D) * L := by
      have h := mul_le_mul_of_nonneg_left hL1' hB0
      simpa using h
    have hleft :
        alpha * (1000 * L + 2000) +
            D * (2 * L + 782) + 3000 * L ≤ C0 * L := by
      dsimp [C0]
      nlinarith [hBLe]
    have hCLmul : C0 * L ≤ (delta * L) * L :=
      mul_le_mul_of_nonneg_right hCLe hL0
    have hinner :
        alpha * (1000 * L + 2000) +
            D * (2 * L + 782) + 3000 * L ≤
          delta * L ^ 2 := by
      calc
        alpha * (1000 * L + 2000) +
              D * (2 * L + 782) + 3000 * L ≤ C0 * L := hleft
        _ ≤ (delta * L) * L := hCLmul
        _ = delta * L ^ 2 := by ring
    have hD600 : D * 600 ≤ D * 600 * (N : ℝ) := by
      have h600D : 0 ≤ D * 600 := by positivity
      have h := mul_le_mul_of_nonneg_left hN1R h600D
      simpa [mul_assoc] using h
    have hinnerN := mul_le_mul_of_nonneg_left hinner hNR0
    have hoverhead :
        alpha * (N : ℝ) * (1000 * L + 2000) +
            D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
            3000 * (N : ℝ) * L ≤
          delta * (N : ℝ) * L ^ 2 := by
      have hreshape :
          alpha * (N : ℝ) * (1000 * L + 2000) +
              D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
              3000 * (N : ℝ) * L ≤
            (N : ℝ) *
              (alpha * (1000 * L + 2000) +
                D * (2 * L + 782) + 3000 * L) := by
        nlinarith [hD600]
      calc
        alpha * (N : ℝ) * (1000 * L + 2000) +
              D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
              3000 * (N : ℝ) * L ≤
            (N : ℝ) *
              (alpha * (1000 * L + 2000) +
                D * (2 * L + 782) + 3000 * L) := hreshape
        _ ≤ (N : ℝ) * (delta * L ^ 2) := hinnerN
        _ = delta * (N : ℝ) * L ^ 2 := by ring
    have hcoef0 : 0 ≤ (alpha - beta) * (N : ℝ) :=
      mul_nonneg habpos.le hNR0
    have hgoodN' : c * L ^ 2 ≤ nativeLambdaTwoGoodRecipMass N beta := by
      simpa [L] using hgoodN
    have hgoodMul := mul_le_mul_of_nonneg_left hgoodN' hcoef0
    have hdeficit :
        -(alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta ≤
          -2 * delta * (N : ℝ) * L ^ 2 := by
      calc
        -(alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta =
            -((alpha - beta) * (N : ℝ) *
              nativeLambdaTwoGoodRecipMass N beta) := by ring
        _ ≤ -((alpha - beta) * (N : ℝ) * (c * L ^ 2)) :=
          neg_le_neg hgoodMul
        _ = -2 * delta * (N : ℝ) * L ^ 2 := by
          dsimp [delta]
          ring
    have htail :
        (alpha * (N : ℝ) * (1000 * L + 2000) +
            D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
            3000 * (N : ℝ) * L) +
          (-(alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodRecipMass N beta) ≤
          -delta * (N : ℝ) * L ^ 2 := by
      nlinarith [hoverhead, hdeficit]
    have hrec := nativePNTError_abs_log_sq_le_affine_compensated
      N hN alpha beta D halpha.le hbeta hba.le hD henv
    have hrearrange :
        alpha * (N : ℝ) *
              (L ^ 2 + 1000 * L + 2000) -
            (alpha - beta) * (N : ℝ) *
              nativeLambdaTwoGoodRecipMass N beta +
            D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
            3000 * (N : ℝ) * L =
          alpha * (N : ℝ) * L ^ 2 +
            ((alpha * (N : ℝ) * (1000 * L + 2000) +
                D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
                3000 * (N : ℝ) * L) +
              (-(alpha - beta) * (N : ℝ) *
                nativeLambdaTwoGoodRecipMass N beta)) := by
      ring
    have hsq :
        |nativePNTError N| * L ^ 2 ≤
          (alpha - delta) * (N : ℝ) * L ^ 2 := by
      have hrec' :
          |nativePNTError N| * L ^ 2 ≤
            alpha * (N : ℝ) * L ^ 2 +
              ((alpha * (N : ℝ) * (1000 * L + 2000) +
                  D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
                  3000 * (N : ℝ) * L) +
                (-(alpha - beta) * (N : ℝ) *
                  nativeLambdaTwoGoodRecipMass N beta)) := by
        simpa [L, hrearrange] using hrec
      calc
        |nativePNTError N| * L ^ 2 ≤
            alpha * (N : ℝ) * L ^ 2 +
              ((alpha * (N : ℝ) * (1000 * L + 2000) +
                  D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
                  3000 * (N : ℝ) * L) +
                (-(alpha - beta) * (N : ℝ) *
                  nativeLambdaTwoGoodRecipMass N beta)) := hrec'
        _ ≤ alpha * (N : ℝ) * L ^ 2 - delta * (N : ℝ) * L ^ 2 := by
          simpa [sub_eq_add_neg] using
            (add_le_add_left htail (alpha * (N : ℝ) * L ^ 2))
        _ = (alpha - delta) * (N : ℝ) * L ^ 2 := by ring
    have hLsq : 0 < L ^ 2 := sq_pos_of_pos hLpos
    have hsq' :
        |nativePNTError N| * L ^ 2 ≤
          ((alpha - delta) * (N : ℝ)) * L ^ 2 := by
      simpa [mul_assoc] using hsq
    exact (mul_le_mul_iff_left₀ hLsq).mp hsq'
  rcases (eventually_atTop.1 hlarge) with ⟨M, hM⟩
  refine ⟨D + delta * (M : ℝ), ?_, ?_⟩
  · positivity
  · intro N
    by_cases hMN : M ≤ N
    · exact (hM N hMN).trans
        (le_add_of_nonneg_right (by positivity))
    · have hNM : N ≤ M := Nat.le_of_lt (lt_of_not_ge hMN)
      have hNMR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
      have hdeltaNM := mul_le_mul_of_nonneg_left hNMR hdelta.le
      have hold := henv N
      have htarget :
          alpha * (N : ℝ) + D ≤
            (alpha - delta) * (N : ℝ) +
              (D + delta * (M : ℝ)) := by
        nlinarith
      exact hold.trans htarget

/-- Improved cubic constant available once the affine PNT slope is at most
`3/2`.  Retaining half of the good-mass deficit doubles the previous constant. -/
def nativePNTLowSlopeCubicConstant : ℝ := 1 / 87750000

/-- The low-slope constant is exactly `64/5` times the global one. -/
theorem nativePNTLowSlopeCubicConstant_eq_scaled :
    nativePNTLowSlopeCubicConstant =
      (64 / 5 : ℝ) * nativePNTCubicConstant := by
  norm_num [nativePNTLowSlopeCubicConstant, nativePNTCubicConstant]

/-- **Stronger low-slope PNT contraction.**  For `0 < alpha <= 3/2`, choosing
`beta = 2*alpha/3` and retaining half of the proved good-mass deficit improves
one affine-envelope step to the cubic coefficient `1/87750000`, exactly twice
the previous `1/175500000`. -/
theorem nativePNTHasAffineEnvelope_lowSlope_cubic_step
    (alpha : ℝ) (halpha : 0 < alpha) (halphaSmall : alpha ≤ 3 / 2)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
      (alpha - nativePNTLowSlopeCubicConstant * alpha ^ 3) := by
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
  let c : ℝ := beta ^ 2 / 6500000
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
      nativeLambdaTwoGoodRecipMass_eventually_quadratic_rate
        beta hbeta hbeta1
  have himp := nativePNTHasAffineEnvelope_improve_of_goodMass_half
    alpha beta c halpha hbeta0 hba hc hc1 hgood henv
  have hcoef :
      alpha - (alpha - beta) * c / 2 =
        alpha - nativePNTLowSlopeCubicConstant * alpha ^ 3 := by
    dsimp [beta, c, nativePNTLowSlopeCubicConstant]
    ring
  rw [hcoef] at himp
  exact himp

end RHLean.Analysis
