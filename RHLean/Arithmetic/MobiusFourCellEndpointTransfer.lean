import Mathlib
import RHLean.Arithmetic.FourSlotCell
import RHLean.Arithmetic.DyadicFrozenPrefix

/-!
# Four-cell endpoint transfer for the Möbius prefix

The three-slot route works at complete-cell endpoints `4K`.  This module
supplies the bounded endpoint transfer to arbitrary physical cutoffs `X`:

* the exact cell resummation
  `∑_{k<K} fourSlotCellSum k = moebiusPrefix (4K)`;
* the endpoint bound `|moebiusPrefix X − moebiusPrefix (4⌊X/4⌋)| ≤ 3`
  (at most three unit steps, each of Möbius size at most one);
* the transfer corollary
  `|moebiusPrefix X| ≤ |∑_{k<⌊X/4⌋} fourSlotCellSum k| + 3`.

Consequently a complete-cell estimate on the three-slot degree-one sum
controls the global Möbius prefix at every cutoff, up to an additive
constant `3` that is harmless at every exponent.  Everything is exact
arithmetic; no estimate beyond the trivial `|μ| ≤ 1` is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Arithmetic

/-- One-step unfolding of the integer Möbius prefix. -/
theorem moebiusPrefix_succ (n : ℕ) :
    moebiusPrefix (n + 1) = moebiusPrefix n + μ (n + 1) := by
  simp [moebiusPrefix, Finset.sum_range_succ]

/-- **Exact cell resummation.**  The sum of the first `K` complete four-slot
cells is the Möbius prefix at the complete-cell endpoint `4K`. -/
theorem sum_fourSlotCellSum_eq_moebiusPrefix (K : ℕ) :
    ∑ k ∈ Finset.range K, fourSlotCellSum k = moebiusPrefix (4 * K) := by
  induction K with
  | zero => simp [moebiusPrefix]
  | succ K ih =>
      have h4 : 4 * (K + 1) = 4 * K + 1 + 1 + 1 + 1 := by ring
      have e4 : 4 * K + 1 + 1 + 1 + 1 = 4 * K + 4 := by omega
      have e3 : 4 * K + 1 + 1 + 1 = 4 * K + 3 := by omega
      have e2 : 4 * K + 1 + 1 = 4 * K + 2 := by omega
      rw [Finset.sum_range_succ, ih, h4, moebiusPrefix_succ,
        moebiusPrefix_succ, moebiusPrefix_succ, moebiusPrefix_succ,
        e4, e3, e2]
      simp only [fourSlotCellSum]
      ring

/-- The Möbius function is bounded by one in absolute value. -/
theorem abs_moebius_le_one (n : ℕ) : |(μ n : ℤ)| ≤ 1 := by
  by_cases h : Squarefree n
  · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
    simp [abs_pow]
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]

/-- **Bounded endpoint transfer.**  The Möbius prefix moves by at most `3`
between an arbitrary cutoff `X` and its complete-cell endpoint `4⌊X/4⌋`. -/
theorem abs_moebiusPrefix_sub_fourCell_le (X : ℕ) :
    |moebiusPrefix X - moebiusPrefix (4 * (X / 4))| ≤ 3 := by
  have hle : 4 * (X / 4) + 1 ≤ X + 1 := by omega
  have hsub : moebiusPrefix X - moebiusPrefix (4 * (X / 4)) =
      ∑ n ∈ Finset.Ico (4 * (X / 4) + 1) (X + 1), μ n := by
    simp only [moebiusPrefix]
    rw [Finset.sum_Ico_eq_sub _ hle]
  rw [hsub]
  calc |∑ n ∈ Finset.Ico (4 * (X / 4) + 1) (X + 1), μ n|
      ≤ ∑ n ∈ Finset.Ico (4 * (X / 4) + 1) (X + 1), |(μ n : ℤ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Ico (4 * (X / 4) + 1) (X + 1), (1 : ℤ) :=
        Finset.sum_le_sum fun n _ => abs_moebius_le_one n
    _ = ((Finset.Ico (4 * (X / 4) + 1) (X + 1)).card : ℤ) := by
        simp
    _ ≤ 3 := by
        rw [Nat.card_Ico]
        have h3 : (X + 1) - (4 * (X / 4) + 1) ≤ 3 := by omega
        exact_mod_cast h3

/-- **Transfer corollary.**  A complete-cell bound on the three-slot cell sum
controls the Möbius prefix at every physical cutoff, at the cost of the
additive constant `3`. -/
theorem abs_moebiusPrefix_le_cellSum_add_three (X : ℕ) :
    |moebiusPrefix X| ≤
      |∑ k ∈ Finset.range (X / 4), fourSlotCellSum k| + 3 := by
  rw [sum_fourSlotCellSum_eq_moebiusPrefix]
  have h := abs_moebiusPrefix_sub_fourCell_le X
  have htri := abs_sub_abs_le_abs_sub (moebiusPrefix X)
    (moebiusPrefix (4 * (X / 4)))
  linarith

end RHLean.Arithmetic
