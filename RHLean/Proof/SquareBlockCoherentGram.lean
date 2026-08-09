import Mathlib
import RHLean.Proof.RealSquareBlockIncrements

/-!
# Coherent Gram identity for square-block increments

This module packages the cross-block same-sign mode as a rank-one Gram form.
For the real square-block increments `Delta_j`, the coherent all-ones Gram mass
through block `N` is

```text
sum_{i,j <= N} Delta_i Delta_j.
```

The main theorem proves that this is exactly the square of the cumulative
square-block discrepancy.  Consequently, any quantitative suppression of this
coherent Gram mass is immediately a quantitative cross-block cancellation
estimate.  No sign or asymptotic assumption is introduced here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- Rank-one Gram kernel of the real square-block increment sequence. -/
def squareBlockIncrementGramEntry (i j : ℕ) : ℝ :=
  realCanonicalTotalIncrement i * realCanonicalTotalIncrement j

/-- Coherent all-ones quadratic form of the square-block increment Gram kernel
through block `N`. -/
def squareBlockCoherentGramMass (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1),
    ∑ j ∈ Finset.range (N + 1), squareBlockIncrementGramEntry i j

/-- The coherent Gram mass is exactly the square of the cumulative square-block
discrepancy.  This is the precise algebraic bridge from a block Gram estimate to
cross-block cancellation. -/
theorem squareBlockCoherentGramMass_eq_prefix_sq (N : ℕ) :
    squareBlockCoherentGramMass N = (realCanonicalTotalPrefix N) ^ 2 := by
  unfold squareBlockCoherentGramMass squareBlockIncrementGramEntry
    realCanonicalTotalPrefix
  rw [← Finset.sum_mul_sum]
  ring

/-- The coherent square-block Gram mass is nonnegative. -/
theorem squareBlockCoherentGramMass_nonneg (N : ℕ) :
    0 ≤ squareBlockCoherentGramMass N := by
  rw [squareBlockCoherentGramMass_eq_prefix_sq]
  positivity

/-- A pointwise coherent-Gram upper bound immediately bounds the absolute
cumulative square-block discrepancy. -/
theorem abs_realCanonicalTotalPrefix_le_sqrt_of_coherentGram_le
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B)
    (hgram : squareBlockCoherentGramMass N ≤ B) :
    |realCanonicalTotalPrefix N| ≤ Real.sqrt B := by
  rw [squareBlockCoherentGramMass_eq_prefix_sq] at hgram
  have hsqrt : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hsqrtSq : (Real.sqrt B) ^ 2 = B := by
    exact Real.sq_sqrt hB
  nlinarith [sq_nonneg (|realCanonicalTotalPrefix N| - Real.sqrt B),
    sq_abs (realCanonicalTotalPrefix N)]

/-- Normalized coherent-Gram control transfers directly to normalized cumulative
block cancellation. -/
theorem normalized_prefix_sq_eq_normalized_coherentGram
    (N : ℕ) (hN : 0 < N) :
    (realCanonicalTotalPrefix N / (N : ℝ)) ^ 2 =
      squareBlockCoherentGramMass N / ((N : ℝ) ^ 2) := by
  rw [squareBlockCoherentGramMass_eq_prefix_sq]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp

end RHLean.Proof
