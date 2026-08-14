import Mathlib
import RHLean.Analysis.NativePNTRemainderProfileCompose
import RHLean.Analysis.NativePNTEvolvingTailCompensation

noncomputable section

namespace RHLean.Analysis

/-- Exact defect of the reciprocal LambdaTwo kernel from its log-square scale. -/
def nativeLambdaTwoRecipDefect (N : Nat) : Real :=
  nativeLambdaTwoRecipMass N - (Real.log (N : Real)) ^ 2

/-- Exact finite-prefix excess relative to the current tail slope. -/
def nativePNTSmallQuotientExcess (N M : Nat) (alpha : Real) : Real :=
  nativeLambdaTwoSmallQuotientErrorMass N M -
    alpha * (N : Real) * nativeLambdaTwoSmallQuotientRecipMass N M

/-- Total evolving cost in one tail contraction. -/
def nativePNTEvolvingTailCost
    (R : Nat -> Real) (N M : Nat) (alpha : Real) : Real :=
  alpha * (N : Real) * nativeLambdaTwoRecipDefect N +
    nativePNTSmallQuotientExcess N M alpha +
    nativePNTSecondRemainderFrom R N

/-- Constant-free compensated tail recurrence. -/
theorem nativePNTError_abs_log_sq_le_evolving_tail
    (R : Nat -> Real) (hR : NativePNTOneLogRemainderProfile R)
    (N M : Nat) (hN : 1 <= N)
    (alpha beta : Real) (halpha : 0 <= alpha)
    (htail : forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real)) :
    |nativePNTError N| * (Real.log (N : Real)) ^ 2 <=
      alpha * (N : Real) * (Real.log (N : Real)) ^ 2 -
        (alpha - beta) * (N : Real) *
          nativeLambdaTwoGoodTailRecipMass N M beta +
        nativePNTEvolvingTailCost R N M alpha := by
  have hsq := nativePNTError_abs_log_sq_le_lambdaTwo_profile R hR N hN
  have hcomp := nativeLambdaTwoErrorMass_tail_compensation_exactSmall
    N M alpha beta halpha htail
  have hsplit := nativeLambdaTwoTailRecipMass_add_small_eq N M
  have hrewrite :
      alpha * (N : Real) * nativeLambdaTwoTailRecipMass N M -
          (alpha - beta) * (N : Real) *
            nativeLambdaTwoGoodTailRecipMass N M beta +
          nativeLambdaTwoSmallQuotientErrorMass N M +
          nativePNTSecondRemainderFrom R N =
        alpha * (N : Real) * (Real.log (N : Real)) ^ 2 -
          (alpha - beta) * (N : Real) *
            nativeLambdaTwoGoodTailRecipMass N M beta +
          nativePNTEvolvingTailCost R N M alpha := by
    unfold nativePNTEvolvingTailCost nativePNTSmallQuotientExcess
      nativeLambdaTwoRecipDefect
    rw [hsplit.symm]
    ring
  calc
    |nativePNTError N| * (Real.log (N : Real)) ^ 2 <=
        nativeLambdaTwoErrorMass N + nativePNTSecondRemainderFrom R N := hsq
    _ <= (alpha * (N : Real) * nativeLambdaTwoTailRecipMass N M -
          (alpha - beta) * (N : Real) *
            nativeLambdaTwoGoodTailRecipMass N M beta +
          nativeLambdaTwoSmallQuotientErrorMass N M) +
          nativePNTSecondRemainderFrom R N := add_le_add_right hcomp _
    _ = alpha * (N : Real) * (Real.log (N : Real)) ^ 2 -
          (alpha - beta) * (N : Real) *
            nativeLambdaTwoGoodTailRecipMass N M beta +
          nativePNTEvolvingTailCost R N M alpha := hrewrite

end RHLean.Analysis
