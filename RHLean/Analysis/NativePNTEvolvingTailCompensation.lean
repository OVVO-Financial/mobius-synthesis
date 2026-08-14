import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixTailCompensation

noncomputable section

namespace RHLean.Analysis

/-- Tail compensation retaining the exact small-quotient error mass. -/
theorem nativeLambdaTwoErrorMass_tail_compensation_exactSmall
    (N M : Nat) (alpha beta : Real)
    (halpha : 0 <= alpha)
    (htail : forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real)) :
    nativeLambdaTwoErrorMass N <=
      alpha * (N : Real) * nativeLambdaTwoTailRecipMass N M -
        (alpha - beta) * (N : Real) *
          nativeLambdaTwoGoodTailRecipMass N M beta +
        nativeLambdaTwoSmallQuotientErrorMass N M := by
  have hG := nativeLambdaTwoGoodTailErrorMass_le N M beta
  have hB := nativeLambdaTwoBadTailErrorMass_le N M alpha beta halpha htail
  have hRec := nativeLambdaTwoGoodTailRecipMass_add_bad_eq N M beta
  rw [nativeLambdaTwoErrorMass_eq_tail_add_small,
    nativeLambdaTwoTailErrorMass_eq_good_add_bad]
  calc
    nativeLambdaTwoGoodTailErrorMass N M beta +
          nativeLambdaTwoBadTailErrorMass N M beta +
          nativeLambdaTwoSmallQuotientErrorMass N M <=
        beta * (N : Real) * nativeLambdaTwoGoodTailRecipMass N M beta +
          alpha * (N : Real) * nativeLambdaTwoBadTailRecipMass N M beta +
          nativeLambdaTwoSmallQuotientErrorMass N M :=
      add_le_add (add_le_add hG hB) (le_refl _)
    _ = alpha * (N : Real) * nativeLambdaTwoTailRecipMass N M -
          (alpha - beta) * (N : Real) *
            nativeLambdaTwoGoodTailRecipMass N M beta +
          nativeLambdaTwoSmallQuotientErrorMass N M := by
      rw [hRec.symm]
      ring

end RHLean.Analysis
