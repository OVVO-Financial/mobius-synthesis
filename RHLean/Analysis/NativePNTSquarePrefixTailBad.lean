import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixTailGood

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Contracted tail fibres which are not yet in the smaller `beta` tube. -/
def nativePNTSquarePrefixBadTailFiberSet
    (N M : ℕ) (beta : ℝ) : Finset ℕ :=
  (nativePNTSquarePrefixTailFiberSet N M).filter fun n =>
    ¬ |nativePNTError (N / n)| ≤ beta * ((N : ℝ) / (n : ℝ))

/-- Reciprocal second-Selberg mass on the bad part of the contracted tail. -/
def nativeLambdaTwoBadTailRecipMass (N M : ℕ) (beta : ℝ) : ℝ :=
  ∑ n ∈ nativePNTSquarePrefixBadTailFiberSet N M beta,
    nativeLambdaTwo n / (n : ℝ)

/-- Error mass on the bad part of the contracted tail. -/
def nativeLambdaTwoBadTailErrorMass (N M : ℕ) (beta : ℝ) : ℝ :=
  ∑ n ∈ nativePNTSquarePrefixBadTailFiberSet N M beta,
    nativeLambdaTwo n * |nativePNTError (N / n)|

/-- Good and bad fibres partition the reciprocal mass of the contracted tail. -/
theorem nativeLambdaTwoGoodTailRecipMass_add_bad_eq
    (N M : ℕ) (beta : ℝ) :
    nativeLambdaTwoGoodTailRecipMass N M beta +
      nativeLambdaTwoBadTailRecipMass N M beta =
        nativeLambdaTwoTailRecipMass N M := by
  classical
  unfold nativeLambdaTwoGoodTailRecipMass nativeLambdaTwoBadTailRecipMass
    nativeLambdaTwoTailRecipMass nativePNTSquarePrefixGoodTailFiberSet
    nativePNTSquarePrefixBadTailFiberSet
  apply Finset.sum_filter_add_sum_filter_not

/-- Once the quotient is beyond `M`, every non-good fibre pays only the
previously established pure slope `alpha`; no additive intercept is needed. -/
theorem nativeLambdaTwoBadTailErrorMass_le
    (N M : ℕ) (alpha beta : ℝ) (halpha : 0 ≤ alpha)
    (htail : ∀ q : ℕ, M ≤ q →
      |nativePNTError q| ≤ alpha * (q : ℝ)) :
    nativeLambdaTwoBadTailErrorMass N M beta ≤
      alpha * (N : ℝ) * nativeLambdaTwoBadTailRecipMass N M beta := by
  classical
  unfold nativeLambdaTwoBadTailErrorMass nativeLambdaTwoBadTailRecipMass
  have hpoint :
      (∑ n ∈ nativePNTSquarePrefixBadTailFiberSet N M beta,
        nativeLambdaTwo n * |nativePNTError (N / n)|) ≤
      ∑ n ∈ nativePNTSquarePrefixBadTailFiberSet N M beta,
        nativeLambdaTwo n * (alpha * ((N : ℝ) / (n : ℝ))) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnBad := Finset.mem_filter.mp hn
    have hnTail := hnBad.1
    have hnTF := Finset.mem_filter.mp hnTail
    have hnI : n ∈ Finset.Icc 1 N := hnTF.1
    have hqM : M ≤ N / n := hnTF.2
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    have hfloor : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hnpos]
      exact_mod_cast Nat.div_mul_le_self N n
    have herr := htail (N / n) hqM
    have hscale := mul_le_mul_of_nonneg_left hfloor halpha
    exact mul_le_mul_of_nonneg_left (herr.trans hscale)
      (nativeLambdaTwo_nonneg n hn1)
  calc
    (∑ n ∈ nativePNTSquarePrefixBadTailFiberSet N M beta,
      nativeLambdaTwo n * |nativePNTError (N / n)|) ≤
        ∑ n ∈ nativePNTSquarePrefixBadTailFiberSet N M beta,
          nativeLambdaTwo n * (alpha * ((N : ℝ) / (n : ℝ))) := hpoint
    _ = alpha * (N : ℝ) *
        (∑ n ∈ nativePNTSquarePrefixBadTailFiberSet N M beta,
          nativeLambdaTwo n / (n : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring

end RHLean.Analysis
