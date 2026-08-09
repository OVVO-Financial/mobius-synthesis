import Mathlib

/-!
# Square-block prefix-comb sweep: blocks 1 through 10

There are two distinct block structures and they must not be conflated.

The seed parent blocks are

* parent block `1`: `[1,2) = {1}`;
* parent block `2`: `[2,4) = {2,3}`.

Their union is the initial seed parent reservoir `{1,2,3}`. Parent block `1`
contains no primes.

The generated target blocks are square shells `[n^2,(n+1)^2)`. The first target
shell generated from the complete seed parent reservoir is `[4,9)`.

A target block starts as dots and is filled by successively overlaying fresh-prime
combs from the fixed old prefix. The first-cover convention removes redundant
factorizations: a position is counted only for the least parent whose active comb
reaches it.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- The half-open square target shell `[n^2,(n+1)^2)`. -/
def prefixCombSquareBlock (n : ℕ) : Finset ℕ :=
  Finset.Icc (n ^ 2) ((n + 1) ^ 2 - 1)

/-- Seed parent block `1`, namely `[1,2) = {1}`. -/
def prefixCombSeedParentBlockOne : Finset ℕ :=
  Finset.Ico 1 2

/-- Seed parent block `2`, namely `[2,4) = {2,3}`. -/
def prefixCombSeedParentBlockTwo : Finset ℕ :=
  Finset.Ico 2 4

/-- The complete initial seed parent reservoir. -/
def prefixCombSeedParentBlock : Finset ℕ :=
  prefixCombSeedParentBlockOne ∪ prefixCombSeedParentBlockTwo

/-- Largest parent available to generate square shell `n`.

Shell `2`, namely `[4,9)`, is the first generated target shell and uses the full
seed parent reservoir `{1,2,3}`. From shell `3` onward, the half-prefix ceiling is
sufficient. -/
def prefixCombParentCeiling (n : ℕ) : ℕ :=
  if n = 2 then 3 else (n ^ 2 - 1) / 2

/-- An active fresh-prime comb tooth from parent `c` at position `x`. -/
def activeFreshPrimeCombHit (c x : ℕ) : Bool :=
  decide (0 < c ∧ μ c ≠ 0 ∧ c ∣ x ∧ Nat.Prime (x / c) ∧ ¬ x / c ∣ c)

/-- Position `x` is first covered by parent `c`: parent `c` hits it and no smaller
parent does. -/
def firstCoveredByPrefixComb (c x : ℕ) : Bool :=
  activeFreshPrimeCombHit c x &&
    !decide (∃ d ∈ Finset.range c, activeFreshPrimeCombHit d x = true)

/-- Genuinely new teeth contributed by parent `c` to square shell `n`. -/
def firstCoverTeeth (n c : ℕ) : Finset ℕ :=
  (prefixCombSquareBlock n).filter fun x => firstCoveredByPrefixComb c x

/-- Number of genuinely new positions filled by parent `c`. -/
def prefixCombNewCoverageCount (n c : ℕ) : ℕ :=
  (firstCoverTeeth n c).card

/-- Whether a nonzero shell position is reached by some available old-prefix parent. -/
def coveredByOldPrefix (n x : ℕ) : Bool :=
  decide (∃ i ∈ Finset.range (prefixCombParentCeiling n),
    activeFreshPrimeCombHit (i + 1) x = true)

/-- Nonzero Möbius positions not reached by the old-prefix comb sweep. -/
def uncoveredSquarefreePositions (n : ℕ) : Finset ℕ :=
  (prefixCombSquareBlock n).filter fun x =>
    decide (μ x ≠ 0) && !coveredByOldPrefix n x

/-- Running signed discrepancy after the first `r` parents have been processed. -/
def prefixCombSweepDiscrepancy (n r : ℕ) : ℤ :=
  (Finset.range r).sum fun i =>
    -(μ (i + 1)) * (prefixCombNewCoverageCount n (i + 1) : ℤ)

/-- The sweep has the exact one-parent recurrence. -/
theorem prefixCombSweepDiscrepancy_succ (n r : ℕ) :
    prefixCombSweepDiscrepancy n (r + 1) =
      prefixCombSweepDiscrepancy n r -
        μ (r + 1) * (prefixCombNewCoverageCount n (r + 1) : ℤ) := by
  unfold prefixCombSweepDiscrepancy
  rw [Finset.sum_range_succ]
  ring

/-- Actual Möbius increment of square shell `n`. -/
def prefixCombBlockIncrement (n : ℕ) : ℤ :=
  (prefixCombSquareBlock n).sum fun x => μ x

/-- Positive nonzero support of a square shell. -/
def prefixCombPositiveSupport (n : ℕ) : Finset ℕ :=
  (prefixCombSquareBlock n).filter fun x => decide (μ x = 1)

/-- Negative nonzero support of a square shell. -/
def prefixCombNegativeSupport (n : ℕ) : Finset ℕ :=
  (prefixCombSquareBlock n).filter fun x => decide (μ x = -1)

/-! ## Seed parent blocks -/

theorem prefixComb_seed_parent_block_one_exact :
    prefixCombSeedParentBlockOne = ({1} : Finset ℕ) := by
  native_decide

theorem prefixComb_seed_parent_block_one_has_no_primes :
    prefixCombSeedParentBlockOne.filter (fun x => decide (Nat.Prime x)) = ∅ := by
  native_decide

theorem prefixComb_seed_parent_block_two_exact :
    prefixCombSeedParentBlockTwo = ([2, 3] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_seed_parent_block_exact :
    prefixCombSeedParentBlock = ([1, 2, 3] : List ℕ).toFinset := by
  native_decide

/-! ## First generated target shell `[4,9)` -/

theorem prefixComb_first_generated_shell_trace :
    firstCoverTeeth 2 1 = ([5, 7] : List ℕ).toFinset ∧
    firstCoverTeeth 2 2 = ([6] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_first_generated_shell_complete :
    uncoveredSquarefreePositions 2 = ∅ ∧
      prefixCombSweepDiscrepancy 2 (prefixCombParentCeiling 2) =
        prefixCombBlockIncrement 2 := by
  native_decide

/-! ## Recovered first-cover traces for the following square shells -/

theorem prefixComb_shell_three_trace :
    firstCoverTeeth 3 1 = ([11, 13] : List ℕ).toFinset ∧
    firstCoverTeeth 3 2 = ([10, 14] : List ℕ).toFinset ∧
    firstCoverTeeth 3 3 = ([15] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_shell_four_trace :
    firstCoverTeeth 4 1 = ([17, 19, 23] : List ℕ).toFinset ∧
    firstCoverTeeth 4 2 = ([22] : List ℕ).toFinset ∧
    firstCoverTeeth 4 3 = ([21] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_shell_five_trace :
    firstCoverTeeth 5 1 = ([29, 31] : List ℕ).toFinset ∧
    firstCoverTeeth 5 2 = ([26, 34] : List ℕ).toFinset ∧
    firstCoverTeeth 5 3 = ([33] : List ℕ).toFinset ∧
    firstCoverTeeth 5 5 = ([35] : List ℕ).toFinset ∧
    firstCoverTeeth 5 6 = ([30] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_shell_six_trace :
    firstCoverTeeth 6 1 = ([37, 41, 43, 47] : List ℕ).toFinset ∧
    firstCoverTeeth 6 2 = ([38, 46] : List ℕ).toFinset ∧
    firstCoverTeeth 6 3 = ([39] : List ℕ).toFinset ∧
    firstCoverTeeth 6 6 = ([42] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_shell_seven_trace :
    firstCoverTeeth 7 1 = ([53, 59, 61] : List ℕ).toFinset ∧
    firstCoverTeeth 7 2 = ([58, 62] : List ℕ).toFinset ∧
    firstCoverTeeth 7 3 = ([51, 57] : List ℕ).toFinset ∧
    firstCoverTeeth 7 5 = ([55] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_shell_eight_trace :
    firstCoverTeeth 8 1 = ([67, 71, 73, 79] : List ℕ).toFinset ∧
    firstCoverTeeth 8 2 = ([74] : List ℕ).toFinset ∧
    firstCoverTeeth 8 3 = ([69] : List ℕ).toFinset ∧
    firstCoverTeeth 8 5 = ([65] : List ℕ).toFinset ∧
    firstCoverTeeth 8 6 = ([66, 78] : List ℕ).toFinset ∧
    firstCoverTeeth 8 7 = ([77] : List ℕ).toFinset ∧
    firstCoverTeeth 8 10 = ([70] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_shell_nine_trace :
    firstCoverTeeth 9 1 = ([83, 89, 97] : List ℕ).toFinset ∧
    firstCoverTeeth 9 2 = ([82, 86, 94] : List ℕ).toFinset ∧
    firstCoverTeeth 9 3 = ([87, 93] : List ℕ).toFinset ∧
    firstCoverTeeth 9 5 = ([85, 95] : List ℕ).toFinset ∧
    firstCoverTeeth 9 7 = ([91] : List ℕ).toFinset := by
  native_decide

theorem prefixComb_shell_ten_trace :
    firstCoverTeeth 10 1 = ([101, 103, 107, 109, 113] : List ℕ).toFinset ∧
    firstCoverTeeth 10 2 = ([106, 118] : List ℕ).toFinset ∧
    firstCoverTeeth 10 3 = ([111] : List ℕ).toFinset ∧
    firstCoverTeeth 10 5 = ([115] : List ℕ).toFinset ∧
    firstCoverTeeth 10 6 = ([102, 114] : List ℕ).toFinset ∧
    firstCoverTeeth 10 7 = ([119] : List ℕ).toFinset ∧
    firstCoverTeeth 10 10 = ([110] : List ℕ).toFinset ∧
    firstCoverTeeth 10 15 = ([105] : List ℕ).toFinset := by
  native_decide

/-! ## Exact completion for the first generated target shells -/

theorem prefixComb_generated_shells_two_to_nine_complete :
    uncoveredSquarefreePositions 2 = ∅ ∧
    uncoveredSquarefreePositions 3 = ∅ ∧
    uncoveredSquarefreePositions 4 = ∅ ∧
    uncoveredSquarefreePositions 5 = ∅ ∧
    uncoveredSquarefreePositions 6 = ∅ ∧
    uncoveredSquarefreePositions 7 = ∅ ∧
    uncoveredSquarefreePositions 8 = ∅ ∧
    uncoveredSquarefreePositions 9 = ∅ := by
  native_decide

theorem prefixComb_generated_shells_two_to_nine_exact_sweep :
    prefixCombSweepDiscrepancy 2 (prefixCombParentCeiling 2) = prefixCombBlockIncrement 2 ∧
    prefixCombSweepDiscrepancy 3 (prefixCombParentCeiling 3) = prefixCombBlockIncrement 3 ∧
    prefixCombSweepDiscrepancy 4 (prefixCombParentCeiling 4) = prefixCombBlockIncrement 4 ∧
    prefixCombSweepDiscrepancy 5 (prefixCombParentCeiling 5) = prefixCombBlockIncrement 5 ∧
    prefixCombSweepDiscrepancy 6 (prefixCombParentCeiling 6) = prefixCombBlockIncrement 6 ∧
    prefixCombSweepDiscrepancy 7 (prefixCombParentCeiling 7) = prefixCombBlockIncrement 7 ∧
    prefixCombSweepDiscrepancy 8 (prefixCombParentCeiling 8) = prefixCombBlockIncrement 8 ∧
    prefixCombSweepDiscrepancy 9 (prefixCombParentCeiling 9) = prefixCombBlockIncrement 9 := by
  native_decide

theorem prefixComb_square_shell_increments_zero_to_nine :
    prefixCombBlockIncrement 0 = 0 ∧
    prefixCombBlockIncrement 1 = -1 ∧
    prefixCombBlockIncrement 2 = -1 ∧
    prefixCombBlockIncrement 3 = 1 ∧
    prefixCombBlockIncrement 4 = -1 ∧
    prefixCombBlockIncrement 5 = 1 ∧
    prefixCombBlockIncrement 6 = -2 ∧
    prefixCombBlockIncrement 7 = 2 ∧
    prefixCombBlockIncrement 8 = -3 ∧
    prefixCombBlockIncrement 9 = 5 := by
  native_decide

theorem prefixComb_generated_shells_two_to_nine_mixed_sign :
    prefixCombPositiveSupport 2 ≠ ∅ ∧ prefixCombNegativeSupport 2 ≠ ∅ ∧
    prefixCombPositiveSupport 3 ≠ ∅ ∧ prefixCombNegativeSupport 3 ≠ ∅ ∧
    prefixCombPositiveSupport 4 ≠ ∅ ∧ prefixCombNegativeSupport 4 ≠ ∅ ∧
    prefixCombPositiveSupport 5 ≠ ∅ ∧ prefixCombNegativeSupport 5 ≠ ∅ ∧
    prefixCombPositiveSupport 6 ≠ ∅ ∧ prefixCombNegativeSupport 6 ≠ ∅ ∧
    prefixCombPositiveSupport 7 ≠ ∅ ∧ prefixCombNegativeSupport 7 ≠ ∅ ∧
    prefixCombPositiveSupport 8 ≠ ∅ ∧ prefixCombNegativeSupport 8 ≠ ∅ ∧
    prefixCombPositiveSupport 9 ≠ ∅ ∧ prefixCombNegativeSupport 9 ≠ ∅ := by
  native_decide

end RHLean.Arithmetic
