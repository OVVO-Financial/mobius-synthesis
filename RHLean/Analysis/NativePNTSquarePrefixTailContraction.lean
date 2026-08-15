import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixTailCompensation

noncomputable section

namespace RHLean.Analysis

/-- **Thresholded compensated squared recurrence.**  This is the rederived PNT
contraction with the affine intercept removed.  The sole finite-scale loss is
the reciprocal `Lambda_2` mass of quotients below the previous tail cutoff `M`.
-/
theorem nativePNTError_abs_log_sq_le_tail_compensated_mobius_rederived
    (N M : ℕ) (hN : 3 ≤ N)
    (alpha beta : ℝ)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hba : beta ≤ alpha)
    (htail : ∀ q : ℕ, M ≤ q →
      |nativePNTError q| ≤ alpha * (q : ℝ)) :
    |nativePNTError N| * (Real.log N) ^ 2 ≤
      alpha * (N : ℝ) *
          ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) -
        (alpha - beta) * (N : ℝ) *
          nativeLambdaTwoGoodTailRecipMass N M beta +
        (6 - alpha) * (N : ℝ) *
          nativeLambdaTwoSmallQuotientRecipMass N M +
        3000 * (N : ℝ) * Real.log N := by
  have hsq := nativePNTError_abs_log_sq_le_lambdaTwo_mobius_rederived N hN
  have hcomp := nativeLambdaTwoErrorMass_tail_compensation
    N M alpha beta halpha hbeta hba htail
  have hrec := nativeLambdaTwoRecipMass_upper N hN
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hrecMul :
      alpha * (N : ℝ) * nativeLambdaTwoRecipMass N ≤
        alpha * (N : ℝ) *
          ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) :=
    mul_le_mul_of_nonneg_left hrec (mul_nonneg halpha hN0)
  have hsplit := nativeLambdaTwoTailRecipMass_add_small_eq N M
  have hmass :
      nativeLambdaTwoErrorMass N ≤
        alpha * (N : ℝ) * nativeLambdaTwoRecipMass N -
          (alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodTailRecipMass N M beta +
          (6 - alpha) * (N : ℝ) *
            nativeLambdaTwoSmallQuotientRecipMass N M := by
    calc
      nativeLambdaTwoErrorMass N ≤
          alpha * (N : ℝ) * nativeLambdaTwoTailRecipMass N M -
            (alpha - beta) * (N : ℝ) *
              nativeLambdaTwoGoodTailRecipMass N M beta +
            6 * (N : ℝ) * nativeLambdaTwoSmallQuotientRecipMass N M := hcomp
      _ = alpha * (N : ℝ) * nativeLambdaTwoRecipMass N -
            (alpha - beta) * (N : ℝ) *
              nativeLambdaTwoGoodTailRecipMass N M beta +
            (6 - alpha) * (N : ℝ) *
              nativeLambdaTwoSmallQuotientRecipMass N M := by
        rw [← hsplit]
        ring
  have hmass' :
      nativeLambdaTwoErrorMass N ≤
        alpha * (N : ℝ) *
            ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) -
          (alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodTailRecipMass N M beta +
          (6 - alpha) * (N : ℝ) *
            nativeLambdaTwoSmallQuotientRecipMass N M := by
    exact hmass.trans
      (add_le_add_right
        (sub_le_sub_right hrecMul
          ((alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodTailRecipMass N M beta))
        ((6 - alpha) * (N : ℝ) *
          nativeLambdaTwoSmallQuotientRecipMass N M))
  calc
    |nativePNTError N| * (Real.log N) ^ 2 ≤
        nativeLambdaTwoErrorMass N +
          3000 * (N : ℝ) * Real.log N := hsq
    _ ≤ (alpha * (N : ℝ) *
            ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) -
          (alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodTailRecipMass N M beta +
          (6 - alpha) * (N : ℝ) *
            nativeLambdaTwoSmallQuotientRecipMass N M) +
          3000 * (N : ℝ) * Real.log N := add_le_add_right hmass' _
    _ = _ := by ring

end RHLean.Analysis
