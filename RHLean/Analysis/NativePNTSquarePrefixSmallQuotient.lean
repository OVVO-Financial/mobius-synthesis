import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixTailBad

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Error mass on reciprocal fibres whose quotient is still below the tail cutoff. -/
def nativeLambdaTwoSmallQuotientErrorMass (N M : ℕ) : ℝ :=
  ∑ n ∈ nativePNTSquarePrefixSmallQuotientFiberSet N M,
    nativeLambdaTwo n * |nativePNTError (N / n)|

/-- The finite quotient prefix pays only the elementary Chebyshev slope six.
Crucially, its cost is proportional to its reciprocal `Lambda_2` mass, not to
a global affine intercept times the full summatory mass. -/
theorem nativeLambdaTwoSmallQuotientErrorMass_le
    (N M : ℕ) :
    nativeLambdaTwoSmallQuotientErrorMass N M ≤
      6 * (N : ℝ) * nativeLambdaTwoSmallQuotientRecipMass N M := by
  classical
  unfold nativeLambdaTwoSmallQuotientErrorMass
    nativeLambdaTwoSmallQuotientRecipMass
  have hC6 : Real.log 4 + 3 ≤ (6 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at h ⊢
    linarith
  have hpoint :
      (∑ n ∈ nativePNTSquarePrefixSmallQuotientFiberSet N M,
        nativeLambdaTwo n * |nativePNTError (N / n)|) ≤
      ∑ n ∈ nativePNTSquarePrefixSmallQuotientFiberSet N M,
        nativeLambdaTwo n * (6 * ((N : ℝ) / (n : ℝ))) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnS := Finset.mem_filter.mp hn
    have hnI : n ∈ Finset.Icc 1 N := hnS.1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    have hfloor : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hnpos]
      exact_mod_cast Nat.div_mul_le_self N n
    have herr := nativePNTError_abs_le_const_mul (N / n)
    have hq0 : (0 : ℝ) ≤ ((N / n : ℕ) : ℝ) := by positivity
    have hconst :
        (Real.log 4 + 3) * ((N / n : ℕ) : ℝ) ≤
          6 * ((N / n : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hC6 hq0
    have hscale :
        6 * ((N / n : ℕ) : ℝ) ≤ 6 * ((N : ℝ) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hfloor (by norm_num)
    exact mul_le_mul_of_nonneg_left (herr.trans (hconst.trans hscale))
      (nativeLambdaTwo_nonneg n hn1)
  calc
    (∑ n ∈ nativePNTSquarePrefixSmallQuotientFiberSet N M,
      nativeLambdaTwo n * |nativePNTError (N / n)|) ≤
        ∑ n ∈ nativePNTSquarePrefixSmallQuotientFiberSet N M,
          nativeLambdaTwo n * (6 * ((N : ℝ) / (n : ℝ))) := hpoint
    _ = 6 * (N : ℝ) *
        (∑ n ∈ nativePNTSquarePrefixSmallQuotientFiberSet N M,
          nativeLambdaTwo n / (n : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring

end RHLean.Analysis
