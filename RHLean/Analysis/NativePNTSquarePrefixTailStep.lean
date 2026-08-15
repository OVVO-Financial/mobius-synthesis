import RHLean.Analysis.NativePNTSquarePrefixTailGoodRetention
import RHLean.Analysis.NativePNTSquarePrefixTailContraction

noncomputable section

namespace RHLean.Analysis

/-- **Finite no-intercept PNT contraction.**  A previously established pure
tail slope `alpha` contracts at the actual endpoint `N`.  The only finite-scale
cost is the small-quotient reciprocal mass `S`; no affine intercept appears.
This is the recurrence intended for quantitative tail iteration.
-/
theorem nativePNTError_tail_pointwise_improve
    (N M : ℕ) (alpha beta c : ℝ)
    (hN : 3 ≤ N)
    (halpha : 0 < alpha) (halpha6 : alpha ≤ 6)
    (hbeta : 0 ≤ beta) (hba : beta < alpha) (hc : 0 < c)
    (htail : ∀ q : ℕ, M ≤ q →
      |nativePNTError q| ≤ alpha * (q : ℝ))
    (hgood : c * (Real.log (N : ℝ)) ^ 2 ≤
      nativeLambdaTwoGoodRecipMass N beta)
    (hcost :
      (6 - beta) * nativeLambdaTwoSmallQuotientRecipMass N M +
          alpha * (1000 * Real.log (N : ℝ) + 2000) +
          3000 * Real.log (N : ℝ) ≤
        3 * (((alpha - beta) * c) / 4) *
          (Real.log (N : ℝ)) ^ 2) :
    |nativePNTError N| ≤
      (alpha - ((alpha - beta) * c) / 4) * (N : ℝ) := by
  have _halpha6 := halpha6
  let L : ℝ := Real.log (N : ℝ)
  let delta : ℝ := ((alpha - beta) * c) / 4
  let S : ℝ := nativeLambdaTwoSmallQuotientRecipMass N M
  let G : ℝ := nativeLambdaTwoGoodRecipMass N beta
  let GT : ℝ := nativeLambdaTwoGoodTailRecipMass N M beta
  have hab : 0 < alpha - beta := sub_pos.mpr hba
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hcoef : 0 ≤ (alpha - beta) * (N : ℝ) :=
    mul_nonneg hab.le hN0
  have hsplit := nativeLambdaTwoGoodRecipMass_le_goodTail_add_small N M beta
  have hGTlower : c * L ^ 2 - S ≤ GT := by
    dsimp [L, S, G, GT]
    linarith
  have hdeficit :
      -(alpha - beta) * (N : ℝ) * GT ≤
        -(alpha - beta) * (N : ℝ) * (c * L ^ 2 - S) := by
    have hmul := mul_le_mul_of_nonneg_left hGTlower hcoef
    nlinarith
  have hrec := nativePNTError_abs_log_sq_le_tail_compensated_mobius_rederived
    N M hN alpha beta halpha.le hbeta hba.le htail
  have hcost' :
      (6 - beta) * S + alpha * (1000 * L + 2000) + 3000 * L ≤
        3 * delta * L ^ 2 := by
    simpa [L, S, delta] using hcost
  have hbound :
      |nativePNTError N| * L ^ 2 ≤
        (alpha - delta) * (N : ℝ) * L ^ 2 := by
    have hrec' :
        |nativePNTError N| * L ^ 2 ≤
          alpha * (N : ℝ) * (L ^ 2 + 1000 * L + 2000) -
            (alpha - beta) * (N : ℝ) * GT +
            (6 - alpha) * (N : ℝ) * S +
            3000 * (N : ℝ) * L := by
      simpa [L, S, GT] using hrec
    calc
      |nativePNTError N| * L ^ 2 ≤
          alpha * (N : ℝ) * (L ^ 2 + 1000 * L + 2000) -
            (alpha - beta) * (N : ℝ) * GT +
            (6 - alpha) * (N : ℝ) * S +
            3000 * (N : ℝ) * L := hrec'
      _ ≤ alpha * (N : ℝ) * (L ^ 2 + 1000 * L + 2000) -
            (alpha - beta) * (N : ℝ) * (c * L ^ 2 - S) +
            (6 - alpha) * (N : ℝ) * S +
            3000 * (N : ℝ) * L := by
        linarith
      _ = alpha * (N : ℝ) * L ^ 2 -
            4 * delta * (N : ℝ) * L ^ 2 +
            (N : ℝ) *
              ((6 - beta) * S + alpha * (1000 * L + 2000) + 3000 * L) := by
        dsimp [delta]
        ring
      _ ≤ alpha * (N : ℝ) * L ^ 2 -
            4 * delta * (N : ℝ) * L ^ 2 +
            (N : ℝ) * (3 * delta * L ^ 2) := by
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left hcost' hN0) _
      _ = (alpha - delta) * (N : ℝ) * L ^ 2 := by ring
  have hL : 0 < L := by
    dsimp [L]
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
  have hcancel := (mul_le_mul_iff_left₀ hLsq).mp
    (show |nativePNTError N| * L ^ 2 ≤
      ((alpha - delta) * (N : ℝ)) * L ^ 2 by
        simpa [mul_assoc] using hbound)
  simpa [delta] using hcancel

end RHLean.Analysis
