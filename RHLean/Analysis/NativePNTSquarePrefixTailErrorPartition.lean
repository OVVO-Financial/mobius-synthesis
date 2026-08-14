import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixSmallQuotient

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Error mass over quotients which have reached the contracted tail. -/
def nativeLambdaTwoTailErrorMass (N M : ℕ) : ℝ :=
  ∑ n ∈ nativePNTSquarePrefixTailFiberSet N M,
    nativeLambdaTwo n * |nativePNTError (N / n)|

/-- Tail error mass splits exactly into good and bad tail fibres. -/
theorem nativeLambdaTwoTailErrorMass_eq_good_add_bad
    (N M : ℕ) (beta : ℝ) :
    nativeLambdaTwoTailErrorMass N M =
      nativeLambdaTwoGoodTailErrorMass N M beta +
        nativeLambdaTwoBadTailErrorMass N M beta := by
  classical
  unfold nativeLambdaTwoTailErrorMass nativeLambdaTwoGoodTailErrorMass
    nativeLambdaTwoBadTailErrorMass nativePNTSquarePrefixGoodTailFiberSet
    nativePNTSquarePrefixBadTailFiberSet
  symm
  apply Finset.sum_filter_add_sum_filter_not

/-- The complete second-Selberg error mass is tail plus finite quotient prefix. -/
theorem nativeLambdaTwoErrorMass_eq_tail_add_small
    (N M : ℕ) :
    nativeLambdaTwoErrorMass N =
      nativeLambdaTwoTailErrorMass N M +
        nativeLambdaTwoSmallQuotientErrorMass N M := by
  classical
  unfold nativeLambdaTwoErrorMass nativeLambdaTwoTailErrorMass
    nativeLambdaTwoSmallQuotientErrorMass nativePNTSquarePrefixTailFiberSet
    nativePNTSquarePrefixSmallQuotientFiberSet
  symm
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not
      (s := Finset.Icc 1 N)
      (p := fun n => M ≤ N / n)
      (f := fun n => nativeLambdaTwo n * |nativePNTError (N / n)|))

end RHLean.Analysis
