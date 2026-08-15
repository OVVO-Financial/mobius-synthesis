import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixTailMass

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Error mass on good fibres in the contracted quotient tail. -/
def nativeLambdaTwoGoodTailErrorMass (N M : ℕ) (beta : ℝ) : ℝ :=
  ∑ n ∈ nativePNTSquarePrefixGoodTailFiberSet N M beta,
    nativeLambdaTwo n * |nativePNTError (N / n)|

/-- Good tail fibres pay exactly the smaller `beta` slope. -/
theorem nativeLambdaTwoGoodTailErrorMass_le
    (N M : ℕ) (beta : ℝ) :
    nativeLambdaTwoGoodTailErrorMass N M beta ≤
      beta * (N : ℝ) * nativeLambdaTwoGoodTailRecipMass N M beta := by
  classical
  unfold nativeLambdaTwoGoodTailErrorMass nativeLambdaTwoGoodTailRecipMass
  have hpoint :
      (∑ n ∈ nativePNTSquarePrefixGoodTailFiberSet N M beta,
        nativeLambdaTwo n * |nativePNTError (N / n)|) ≤
      ∑ n ∈ nativePNTSquarePrefixGoodTailFiberSet N M beta,
        nativeLambdaTwo n * (beta * ((N : ℝ) / (n : ℝ))) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnGood := Finset.mem_filter.mp hn
    have hnTail := hnGood.1
    have hnI : n ∈ Finset.Icc 1 N :=
      (Finset.mem_filter.mp hnTail).1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    exact mul_le_mul_of_nonneg_left hnGood.2
      (nativeLambdaTwo_nonneg n hn1)
  calc
    (∑ n ∈ nativePNTSquarePrefixGoodTailFiberSet N M beta,
      nativeLambdaTwo n * |nativePNTError (N / n)|) ≤
        ∑ n ∈ nativePNTSquarePrefixGoodTailFiberSet N M beta,
          nativeLambdaTwo n * (beta * ((N : ℝ) / (n : ℝ))) := hpoint
    _ = beta * (N : ℝ) *
        (∑ n ∈ nativePNTSquarePrefixGoodTailFiberSet N M beta,
          nativeLambdaTwo n / (n : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring

end RHLean.Analysis
