import Mathlib
import RHLean.Proof.FinitePartialMoments
import RHLean.Analysis.CanonicalHighSectorBridge

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Möbius weight as a real scalar. -/
def realCanonicalMoebiusWeight (m : ℕ) : ℝ :=
  ((μ m : ℤ) : ℝ)

/-- Complete real Möbius increment in square block `j`. -/
def realCanonicalTotalIncrement (j : ℕ) : ℝ :=
  ∑ m ∈ canonicalSquareBlock j, realCanonicalMoebiusWeight m

/-- Cumulative real square-block sum from the common origin. -/
def realCanonicalTotalPrefix (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), realCanonicalTotalIncrement j

/-- Total variation of the real square-block increments from the common origin. -/
def realCanonicalTotalVariation (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), |realCanonicalTotalIncrement j|

/-- The real Möbius weight casts to the existing complex canonical weight. -/
@[simp] theorem realCanonicalMoebiusWeight_cast (m : ℕ) :
    ((realCanonicalMoebiusWeight m : ℝ) : ℂ) = canonicalMoebiusWeight m := by
  rfl

/-- The real block increment casts exactly to the existing complex block
increment. -/
theorem realCanonicalTotalIncrement_cast (j : ℕ) :
    ((realCanonicalTotalIncrement j : ℝ) : ℂ) = canonicalTotalIncrement j := by
  classical
  simp [realCanonicalTotalIncrement, canonicalTotalIncrement]

/-- The cumulative real block sum casts exactly to the existing complex
canonical prefix. -/
theorem realCanonicalTotalPrefix_cast (n : ℕ) :
    ((realCanonicalTotalPrefix n : ℝ) : ℂ) = canonicalTotalPrefix n := by
  classical
  simp [realCanonicalTotalPrefix, canonicalTotalPrefix,
    realCanonicalTotalIncrement_cast]

/-- The cumulative real square-block sum casts to the concrete square-prefix
Mertens value at `X_n=(n+1)^2-1`. -/
theorem realCanonicalTotalPrefix_cast_eq_squarePrefixMertens (n : ℕ) :
    ((realCanonicalTotalPrefix n : ℝ) : ℂ) =
      RHLean.Analysis.squarePrefixMertens n := by
  rw [realCanonicalTotalPrefix_cast, canonicalTotalPrefix_eq_squarePrefixMertens]

/-- Every real Möbius weight has absolute value at most one. -/
theorem abs_realCanonicalMoebiusWeight_le_one (m : ℕ) :
    |realCanonicalMoebiusWeight m| ≤ 1 := by
  unfold realCanonicalMoebiusWeight
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)

/-- The exact cardinality of the square block `[j^2,(j+1)^2)`. -/
theorem card_canonicalSquareBlock (j : ℕ) :
    (canonicalSquareBlock j).card = 2 * j + 1 := by
  unfold canonicalSquareBlock
  rw [Nat.card_Ico]
  have hsq : (j + 1) ^ 2 = j ^ 2 + (2 * j + 1) := by ring
  rw [hsq]
  omega

/-- A block increment is bounded by the number of integers in its square
block. -/
theorem abs_realCanonicalTotalIncrement_le (j : ℕ) :
    |realCanonicalTotalIncrement j| ≤ (2 * j + 1 : ℕ) := by
  classical
  unfold realCanonicalTotalIncrement
  calc
    |∑ m ∈ canonicalSquareBlock j, realCanonicalMoebiusWeight m| ≤
        ∑ m ∈ canonicalSquareBlock j, |realCanonicalMoebiusWeight m| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le (canonicalSquareBlock j) realCanonicalMoebiusWeight)
    _ ≤ ∑ _m ∈ canonicalSquareBlock j, (1 : ℝ) := by
      exact Finset.sum_le_sum fun m _ => abs_realCanonicalMoebiusWeight_le_one m
    _ = ((canonicalSquareBlock j).card : ℝ) := by simp
    _ = (2 * j + 1 : ℕ) := by rw [card_canonicalSquareBlock]

/-- The finite sum of the first `N` odd numbers is `N^2`. -/
theorem sum_odd_range (N : ℕ) :
    (∑ j ∈ Finset.range N, ((2 * j + 1 : ℕ) : ℝ)) = (N : ℝ) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The total variation of all canonical square-block increments through block
`n` is bounded by the total number of integers through the endpoint
`(n+1)^2-1`. -/
theorem realCanonicalTotalVariation_le (n : ℕ) :
    realCanonicalTotalVariation n ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
  unfold realCanonicalTotalVariation
  calc
    (∑ j ∈ Finset.range (n + 1), |realCanonicalTotalIncrement j|) ≤
        ∑ j ∈ Finset.range (n + 1), ((2 * j + 1 : ℕ) : ℝ) := by
      exact Finset.sum_le_sum fun j _ => abs_realCanonicalTotalIncrement_le j
    _ = ((n + 1 : ℕ) : ℝ) ^ 2 := sum_odd_range (n + 1)

/-- The degree-one partial-moment absolute mass of the real canonical block
increments is exactly their total variation. -/
theorem finiteAbsoluteMass_realCanonicalTotalIncrement_eq_variation (n : ℕ) :
    RHLean.Analysis.finiteAbsoluteMass (Finset.range (n + 1))
      realCanonicalTotalIncrement = realCanonicalTotalVariation n := by
  rfl

/-- The degree-one partial-moment signed sum of the real canonical block
increments is exactly their cumulative real prefix. -/
theorem finiteSignedSum_realCanonicalTotalIncrement_eq_prefix (n : ℕ) :
    RHLean.Analysis.finiteSignedSum (Finset.range (n + 1))
      realCanonicalTotalIncrement = realCanonicalTotalPrefix n := by
  rfl

end RHLean.Proof
