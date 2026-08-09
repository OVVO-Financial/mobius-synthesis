import Mathlib

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Total unsigned extension mass carried by a finite parent family. -/
def channelMass {ι : Type*} [DecidableEq ι]
    (parents : Finset ι) (mass : ι → ℝ) : ℝ :=
  ∑ c ∈ parents, mass c

/-- Total extension mass landing in a chosen phase window. -/
def phaseMass {ι : Type*} [DecidableEq ι]
    (parents : Finset ι) (phase : ι → ℝ) : ℝ :=
  ∑ c ∈ parents, phase c

/-- Normalized extension rate into a chosen phase window. -/
def channelRate {ι : Type*} [DecidableEq ι]
    (parents : Finset ι) (mass phase : ι → ℝ) : ℝ :=
  phaseMass parents phase / channelMass parents mass

/-- The `L¹` discrepancy from the target phase proportion `α`. -/
def channelDiscrepancy {ι : Type*} [DecidableEq ι]
    (parents : Finset ι) (mass phase : ι → ℝ) (α : ℝ) : ℝ :=
  ∑ c ∈ parents, |phase c - α * mass c|

/--
A summed channel-discrepancy bound controls the deviation of the aggregate
phase-extension rate from its target proportion.
-/
theorem abs_channelRate_sub_target_le
    {ι : Type*} [DecidableEq ι]
    (parents : Finset ι) (mass phase : ι → ℝ) (α : ℝ)
    (hpos : 0 < channelMass parents mass) :
    |channelRate parents mass phase - α| ≤
      channelDiscrepancy parents mass phase α / channelMass parents mass := by
  have hsum :
      |phaseMass parents phase - α * channelMass parents mass| ≤
        channelDiscrepancy parents mass phase α := by
    have habs :
        |∑ c ∈ parents, (phase c - α * mass c)| ≤
          ∑ c ∈ parents, |phase c - α * mass c| := by
      exact Finset.abs_sum_le_sum_abs _ _
    simpa [phaseMass, channelMass, channelDiscrepancy, Finset.mul_sum] using habs
  have hrate :
      channelRate parents mass phase - α =
        (phaseMass parents phase - α * channelMass parents mass) /
          channelMass parents mass := by
    unfold channelRate
    field_simp [ne_of_gt hpos]
  rw [hrate, abs_div, abs_of_pos hpos]
  exact div_le_div_of_nonneg_right hsum (le_of_lt hpos)

/--
If the positive- and negative-parent channel families each have small
relative phase discrepancy from the same target proportion, then their
aggregate extension rates are close.
-/
theorem abs_parity_channelRate_sub_le
    {ι : Type*} [DecidableEq ι]
    (parentsPlus parentsMinus : Finset ι)
    (mass phase : ι → ℝ) (α : ℝ)
    (hplus : 0 < channelMass parentsPlus mass)
    (hminus : 0 < channelMass parentsMinus mass) :
    |channelRate parentsPlus mass phase -
        channelRate parentsMinus mass phase| ≤
      channelDiscrepancy parentsPlus mass phase α /
          channelMass parentsPlus mass +
        channelDiscrepancy parentsMinus mass phase α /
          channelMass parentsMinus mass := by
  calc
    |channelRate parentsPlus mass phase -
        channelRate parentsMinus mass phase| =
        |(channelRate parentsPlus mass phase - α) +
          (α - channelRate parentsMinus mass phase)| := by
            congr 1
            ring
    _ ≤ |channelRate parentsPlus mass phase - α| +
          |α - channelRate parentsMinus mass phase| :=
      abs_add_le _ _
    _ = |channelRate parentsPlus mass phase - α| +
          |channelRate parentsMinus mass phase - α| := by
      rw [abs_sub_comm α (channelRate parentsMinus mass phase)]
    _ ≤ channelDiscrepancy parentsPlus mass phase α /
            channelMass parentsPlus mass +
          channelDiscrepancy parentsMinus mass phase α /
            channelMass parentsMinus mass :=
      add_le_add
        (abs_channelRate_sub_target_le parentsPlus mass phase α hplus)
        (abs_channelRate_sub_target_le parentsMinus mass phase α hminus)

/--
Quantitative growing-parent phase-uniformity bridge.

If each parent parity class has relative channel discrepancy at most
`εPlus` and `εMinus`, then the difference between its normalized phase
extension rates is at most `εPlus + εMinus`.
-/
theorem abs_parity_channelRate_sub_le_of_relative_discrepancy
    {ι : Type*} [DecidableEq ι]
    (parentsPlus parentsMinus : Finset ι)
    (mass phase : ι → ℝ) (α εPlus εMinus : ℝ)
    (hplus : 0 < channelMass parentsPlus mass)
    (hminus : 0 < channelMass parentsMinus mass)
    (hdiscPlus :
      channelDiscrepancy parentsPlus mass phase α ≤
        εPlus * channelMass parentsPlus mass)
    (hdiscMinus :
      channelDiscrepancy parentsMinus mass phase α ≤
        εMinus * channelMass parentsMinus mass) :
    |channelRate parentsPlus mass phase -
        channelRate parentsMinus mass phase| ≤ εPlus + εMinus := by
  have hratioPlus :
      channelDiscrepancy parentsPlus mass phase α /
          channelMass parentsPlus mass ≤ εPlus := by
    exact (div_le_iff₀ hplus).2 hdiscPlus
  have hratioMinus :
      channelDiscrepancy parentsMinus mass phase α /
          channelMass parentsMinus mass ≤ εMinus := by
    exact (div_le_iff₀ hminus).2 hdiscMinus
  exact
    (abs_parity_channelRate_sub_le
      parentsPlus parentsMinus mass phase α hplus hminus).trans
      (add_le_add hratioPlus hratioMinus)

/--
A common relative discrepancy bound `ε` gives the symmetric estimate `2ε`.
This is the finite form used before passing to an asymptotic statement with
`ε = ε N → 0`.
-/
theorem abs_parity_channelRate_sub_le_two_mul
    {ι : Type*} [DecidableEq ι]
    (parentsPlus parentsMinus : Finset ι)
    (mass phase : ι → ℝ) (α ε : ℝ)
    (hplus : 0 < channelMass parentsPlus mass)
    (hminus : 0 < channelMass parentsMinus mass)
    (hdiscPlus :
      channelDiscrepancy parentsPlus mass phase α ≤
        ε * channelMass parentsPlus mass)
    (hdiscMinus :
      channelDiscrepancy parentsMinus mass phase α ≤
        ε * channelMass parentsMinus mass) :
    |channelRate parentsPlus mass phase -
        channelRate parentsMinus mass phase| ≤ 2 * ε := by
  simpa [two_mul] using
    abs_parity_channelRate_sub_le_of_relative_discrepancy
      parentsPlus parentsMinus mass phase α ε ε
      hplus hminus hdiscPlus hdiscMinus

end RHLean.Analysis
