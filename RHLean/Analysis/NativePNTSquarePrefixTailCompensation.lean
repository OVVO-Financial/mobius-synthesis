import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixTailErrorPartition

noncomputable section

namespace RHLean.Analysis

/-- **Thresholded reciprocal compensation with no affine intercept.**  The
finite quotient prefix now costs only its reciprocal `Lambda_2` mass. -/
theorem nativeLambdaTwoErrorMass_tail_compensation
    (N M : ℕ) (alpha beta : ℝ)
    (halpha : 0 ≤ alpha) (_hbeta : 0 ≤ beta) (_hba : beta ≤ alpha)
    (htail : ∀ q : ℕ, M ≤ q →
      |nativePNTError q| ≤ alpha * (q : ℝ)) :
    nativeLambdaTwoErrorMass N ≤
      alpha * (N : ℝ) * nativeLambdaTwoTailRecipMass N M -
        (alpha - beta) * (N : ℝ) *
          nativeLambdaTwoGoodTailRecipMass N M beta +
        6 * (N : ℝ) * nativeLambdaTwoSmallQuotientRecipMass N M := by
  have hG := nativeLambdaTwoGoodTailErrorMass_le N M beta
  have hB := nativeLambdaTwoBadTailErrorMass_le N M alpha beta halpha htail
  have hS := nativeLambdaTwoSmallQuotientErrorMass_le N M
  have hRec := nativeLambdaTwoGoodTailRecipMass_add_bad_eq N M beta
  rw [nativeLambdaTwoErrorMass_eq_tail_add_small,
    nativeLambdaTwoTailErrorMass_eq_good_add_bad]
  calc
    nativeLambdaTwoGoodTailErrorMass N M beta +
          nativeLambdaTwoBadTailErrorMass N M beta +
          nativeLambdaTwoSmallQuotientErrorMass N M ≤
        beta * (N : ℝ) * nativeLambdaTwoGoodTailRecipMass N M beta +
          alpha * (N : ℝ) * nativeLambdaTwoBadTailRecipMass N M beta +
          6 * (N : ℝ) * nativeLambdaTwoSmallQuotientRecipMass N M :=
      add_le_add (add_le_add hG hB) hS
    _ = alpha * (N : ℝ) * nativeLambdaTwoTailRecipMass N M -
          (alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodTailRecipMass N M beta +
          6 * (N : ℝ) * nativeLambdaTwoSmallQuotientRecipMass N M := by
      rw [← hRec]
      ring

end RHLean.Analysis
