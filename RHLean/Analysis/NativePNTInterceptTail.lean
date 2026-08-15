import Mathlib
import RHLean.Analysis.NativePNTInterceptOnset
import RHLean.Analysis.NativePNTInterceptAbsorption

/-!
# Tail bound for one explicit native PNT intercept step

Once the calibrated onset is reached, the current compensated PNT recurrence
already gives the smaller slope with no additive intercept.  The intercept cost
enters only when this tail estimate is globalized over the finite prefix.
-/

noncomputable section

namespace RHLean.Analysis

/-- Beyond the explicit onset, one cubic contraction gives the pure smaller
slope bound. -/
theorem nativePNTError_abs_le_cubicStep_tail
    (alpha D : ℝ) (halpha : 0 < alpha) (halpha6 : alpha ≤ 6)
    (henvAt : NativePNTAffineEnvelopeAt alpha D)
    (N : ℕ) (hMN : nativePNTCubicStepOnset alpha D ≤ N) :
    |nativePNTError N| ≤
      (alpha - nativePNTCubicStepDelta alpha) * (N : ℝ) := by
  rcases henvAt with ⟨hD, henv⟩
  let beta : ℝ := nativePNTCubicStepBeta alpha
  let c : ℝ := nativePNTCubicStepGoodCoeff alpha
  let delta : ℝ := nativePNTCubicStepDelta alpha
  let C0 : ℝ := nativePNTCubicStepC0 alpha D
  have hbeta : 0 < beta := by
    dsimp [beta, nativePNTCubicStepBeta]
    positivity
  have hbeta0 : 0 ≤ beta := hbeta.le
  have hba : beta < alpha := by
    dsimp [beta, nativePNTCubicStepBeta]
    nlinarith
  have hab : 0 ≤ alpha - beta := (sub_pos.mpr hba).le
  have hdelta : 0 < delta := by
    dsimp [delta]
    rw [nativePNTCubicStepDelta_eq]
    exact mul_pos
      (by norm_num [nativePNTCubicConstant])
      (pow_pos halpha 3)
  have hdeltaDef : delta = (alpha - beta) * c / 4 := by
    rfl
  have hready := nativePNTCubicStepOnset_spec
    alpha D halpha halpha6 hD
  have hreadyN := hready N hMN
  rcases hreadyN with ⟨hN, hgoodN0, hL1, hLC0⟩
  have hN1 : 1 ≤ N := by omega
  have hNR0 : 0 ≤ (N : ℝ) := by positivity
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  let L : ℝ := Real.log (N : ℝ)
  have hL1' : (1 : ℝ) ≤ L := by simpa [L] using hL1
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL1'
  have hgoodN :
      c * L ^ 2 ≤ nativeLambdaTwoGoodRecipMass N beta := by
    simpa [c, beta, L] using hgoodN0
  have hLC : C0 / (3 * delta) ≤ L := by
    simpa [C0, delta, L] using hLC0
  have hden : 0 < 3 * delta := by positivity
  have hCLe0 : C0 ≤ L * (3 * delta) :=
    (div_le_iff₀ hden).mp hLC
  have hCLe :
      3000 * alpha + 784 * D + 3000 ≤ 3 * delta * L := by
    have hcomm : C0 ≤ 3 * delta * L := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hCLe0
    simpa [C0, nativePNTCubicStepC0] using hcomm
  have hoverhead := nativePNTCubicStep_overhead_le
    alpha D delta (N : ℝ) L halpha.le hD hN1R hL1' hCLe
  have hdeficit := nativePNTCubicStep_deficit_le
    alpha beta c delta (N : ℝ) L
      (nativeLambdaTwoGoodRecipMass N beta)
      hab hNR0 hgoodN hdeltaDef
  have htail :
      (alpha * (N : ℝ) * (1000 * L + 2000) +
          D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
          3000 * (N : ℝ) * L) +
        (-(alpha - beta) * (N : ℝ) *
          nativeLambdaTwoGoodRecipMass N beta) ≤
        -delta * (N : ℝ) * L ^ 2 := by
    nlinarith [hoverhead, hdeficit]
  have hrec := nativePNTError_abs_log_sq_le_affine_compensated
    N hN alpha beta D halpha.le hbeta0 hba.le hD henv
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
  have hrec' :
      |nativePNTError N| * L ^ 2 ≤
        alpha * (N : ℝ) * L ^ 2 +
          ((alpha * (N : ℝ) * (1000 * L + 2000) +
              D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
              3000 * (N : ℝ) * L) +
            (-(alpha - beta) * (N : ℝ) *
              nativeLambdaTwoGoodRecipMass N beta)) := by
    simpa [L, hrearrange] using hrec
  have hsqMain :
      |nativePNTError N| * L ^ 2 ≤
        (alpha - delta) * (N : ℝ) * L ^ 2 := by
    calc
      |nativePNTError N| * L ^ 2 ≤
          alpha * (N : ℝ) * L ^ 2 +
            ((alpha * (N : ℝ) * (1000 * L + 2000) +
                D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
                3000 * (N : ℝ) * L) +
              (-(alpha - beta) * (N : ℝ) *
                nativeLambdaTwoGoodRecipMass N beta)) := hrec'
      _ ≤ alpha * (N : ℝ) * L ^ 2 -
            delta * (N : ℝ) * L ^ 2 := by
        simpa [sub_eq_add_neg] using
          (add_le_add_left htail (alpha * (N : ℝ) * L ^ 2))
      _ = (alpha - delta) * (N : ℝ) * L ^ 2 := by ring
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hLpos
  have hsq' :
      |nativePNTError N| * L ^ 2 ≤
        ((alpha - delta) * (N : ℝ)) * L ^ 2 := by
    simpa [mul_assoc] using hsqMain
  have hlargeN :
      |nativePNTError N| ≤ (alpha - delta) * (N : ℝ) :=
    (mul_le_mul_iff_left₀ hLsq).mp hsq'
  simpa [delta] using hlargeN

end RHLean.Analysis
