import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixCompensated

/-!
# Thresholded reciprocal masses for effective PNT contraction

This module keeps the finite quotient prefix separate instead of absorbing it
into the affine intercept used by the qualitative PNT proof.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Fibres whose reciprocal quotient has reached a previously contracted tail. -/
def nativePNTSquarePrefixTailFiberSet (N M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => M ≤ N / n

/-- Fibres whose reciprocal quotient is still in the finite prefix. -/
def nativePNTSquarePrefixSmallQuotientFiberSet (N M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => N / n < M

/-- Reciprocal second-Selberg mass on the contracted quotient tail. -/
def nativeLambdaTwoTailRecipMass (N M : ℕ) : ℝ :=
  ∑ n ∈ nativePNTSquarePrefixTailFiberSet N M,
    nativeLambdaTwo n / (n : ℝ)

/-- Reciprocal second-Selberg mass on the finite small-quotient prefix. -/
def nativeLambdaTwoSmallQuotientRecipMass (N M : ℕ) : ℝ :=
  ∑ n ∈ nativePNTSquarePrefixSmallQuotientFiberSet N M,
    nativeLambdaTwo n / (n : ℝ)

/-- Good reciprocal fibres restricted to quotients where the tail bound applies. -/
def nativePNTSquarePrefixGoodTailFiberSet
    (N M : ℕ) (beta : ℝ) : Finset ℕ :=
  (nativePNTSquarePrefixTailFiberSet N M).filter fun n =>
    |nativePNTError (N / n)| ≤ beta * ((N : ℝ) / (n : ℝ))

/-- Good reciprocal `Lambda_2` mass usable without any affine intercept. -/
def nativeLambdaTwoGoodTailRecipMass (N M : ℕ) (beta : ℝ) : ℝ :=
  ∑ n ∈ nativePNTSquarePrefixGoodTailFiberSet N M beta,
    nativeLambdaTwo n / (n : ℝ)

/-- Tail and finite-prefix reciprocal masses partition the total mass exactly. -/
theorem nativeLambdaTwoTailRecipMass_add_small_eq
    (N M : ℕ) :
    nativeLambdaTwoTailRecipMass N M +
      nativeLambdaTwoSmallQuotientRecipMass N M =
        nativeLambdaTwoRecipMass N := by
  classical
  unfold nativeLambdaTwoTailRecipMass nativeLambdaTwoSmallQuotientRecipMass
    nativePNTSquarePrefixTailFiberSet nativePNTSquarePrefixSmallQuotientFiberSet
    nativeLambdaTwoRecipMass
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not
      (s := Finset.Icc 1 N)
      (p := fun n => M ≤ N / n)
      (f := fun n => nativeLambdaTwo n / (n : ℝ)))

end RHLean.Analysis
