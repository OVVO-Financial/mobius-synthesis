import Mathlib
import RHLean.Proof.SquareRootLowPrimeQuantitativeEnergyReduction
import RHLean.Proof.SquareRootLowPrimeSignedResponseMatching

/-!
# Real deep-increment bound by the complete matched frontier

The complete signed response-child carrier has now undergone every available
fresh-prime matching.  This file closes the quantitative reduction from the
actual real running increments to the cardinality of that remaining frontier.

For `U<R`,

`|sum_{K<p<=U} Delta_p| <= #(OwnedResponseMatchingFrontier R K U)`.

No raw response weight and no number-of-fresh-primes factor remains.  A future
cardinality theorem at scale `R*sqrt(K)` would therefore give the desired deep
processed-response estimate immediately.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The real child-weight sum is the real cast of the integer Möbius sum. -/
theorem squareRootLowPrimeOwnedResponseChildren_realWeightSum_eq_intCast
    (R K U : ℕ) :
    (∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
      (canonicalMoebiusWeight n).re) =
      ((∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U, μ n : ℤ) : ℝ) := by
  unfold canonicalMoebiusWeight
  push_cast
  rfl

/-- Integer frontier control transferred to real scalars. -/
theorem abs_squareRootLowPrimeOwnedResponseChildren_realWeightSum_le_frontierCard
    (R K U : ℕ) :
    |∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
      (canonicalMoebiusWeight n).re| ≤
      ((squareRootLowPrimeOwnedResponseMatchingFrontier R K U).card : ℝ) := by
  rw [squareRootLowPrimeOwnedResponseChildren_realWeightSum_eq_intCast]
  exact_mod_cast
    abs_squareRootLowPrimeOwnedResponseChildren_moebiusSum_le_frontierCard
      R K U

/-- **Complete quantitative matching reduction.**  The absolute real increment
across the entire deep prime interval is bounded by the cardinality of the
single sequentially matched frontier. -/
theorem abs_squareRootLowPrimeFreshIncrementReal_sum_le_matchingFrontierCard
    {R K j U : ℕ} (hR : 2 ≤ R) (hUR : U < R) :
    |∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
      squareRootLowPrimeFreshIncrementReal R K j p| ≤
      ((squareRootLowPrimeOwnedResponseMatchingFrontier R K U).card : ℝ) := by
  rw [squareRootLowPrimeFreshIncrementReal_sum_eq_neg_ownedResponseChildrenMass
    hR hUR, abs_neg]
  exact
    abs_squareRootLowPrimeOwnedResponseChildren_realWeightSum_le_frontierCard
      R K U

/-- A cardinality estimate for the complete matched frontier transfers without
loss to the actual signed deep increment. -/
theorem abs_squareRootLowPrimeFreshIncrementReal_sum_le_of_frontierCard
    {R K j U : ℕ} (B : ℝ)
    (hR : 2 ≤ R) (hUR : U < R)
    (hfrontier :
      ((squareRootLowPrimeOwnedResponseMatchingFrontier R K U).card : ℝ) ≤ B) :
    |∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
      squareRootLowPrimeFreshIncrementReal R K j p| ≤ B := by
  exact
    (abs_squareRootLowPrimeFreshIncrementReal_sum_le_matchingFrontierCard
      (R := R) (K := K) (j := j) (U := U) hR hUR).trans hfrontier

end RHLean.Proof
