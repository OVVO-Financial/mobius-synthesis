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

/--
The fractional square-root phase attached to an integer.  If
`r = Nat.sqrt n`, then this is `sqrt(n) - r`; for a prime lying in the
square block `[r^2, (r+1)^2)` it is exactly the normalized root coordinate
used to discuss where that prime lies inside the block.
-/
def squareRootPrimePhase (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) - (Nat.sqrt n : ℝ)

/-- Number of primes in the closed integer range `[2, X]`. -/
def primeCountUpTo (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 2 X).filter Nat.Prime).card

/--
Number of primes `p ≤ X` whose square-root phase lies in the half-open
window `[a,b)`.
-/
def squareRootPrimePhaseWindowCount (X : ℕ) (a b : ℝ) : ℕ := by
  classical
  exact ((Finset.Icc 2 X).filter fun p =>
    Nat.Prime p ∧
      a ≤ squareRootPrimePhase p ∧
      squareRootPrimePhase p < b).card

/--
The classical square-root prime phase equidistribution statement, packaged in
an epsilon/counting form that is directly usable by the finite phase machinery
in this repository.

For every fixed phase window `[a,b) ⊆ [0,1]`, the number of primes in that
window is `(b-a) * pi(X)` up to relative error `ε * pi(X)` for all sufficiently
large `X`.

This declaration is deliberately a proposition, not a project axiom.  The
classical analytic theorem that `{sqrt p}` is uniformly distributed modulo one
is not presently formalized in Mathlib, so any theorem consuming this input
must receive a proof of this proposition as an explicit argument.  This keeps
the terminal axiom audit clean while fixing the exact theorem interface needed
for square-block prime-phase arguments.
-/
def SquareRootPrimePhaseEquidistributionStatement : Prop :=
  ∀ a b ε : ℝ,
    0 ≤ a →
    a ≤ b →
    b ≤ 1 →
    0 < ε →
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      |(squareRootPrimePhaseWindowCount X a b : ℝ) -
          (b - a) * (primeCountUpTo X : ℝ)| ≤
        ε * (primeCountUpTo X : ℝ)

/--
A square-root prime phase equidistribution input immediately gives the finite
two-sided count estimate for every fixed macroscopic phase window.  In
particular, no such window can carry a persistent positive proportion of
primes above its geometric length.
-/
theorem squareRootPrimePhaseWindowCount_two_sided
    (hphase : SquareRootPrimePhaseEquidistributionStatement)
    {a b ε : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b)
    (hb : b ≤ 1)
    (hε : 0 < ε) :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      (b - a - ε) * (primeCountUpTo X : ℝ) ≤
          (squareRootPrimePhaseWindowCount X a b : ℝ) ∧
        (squareRootPrimePhaseWindowCount X a b : ℝ) ≤
          (b - a + ε) * (primeCountUpTo X : ℝ) := by
  rcases hphase a b ε ha hab hb hε with ⟨X0, hX0⟩
  refine ⟨X0, ?_⟩
  intro X hX
  have hbound := hX0 X hX
  rcases (abs_le.mp hbound) with ⟨hlower, hupper⟩
  constructor <;> nlinarith

/--
Explicit no-bunching corollary: under square-root prime phase equidistribution,
every fixed phase window eventually contains at most its geometric proportion
plus an arbitrary positive tolerance.
-/
theorem squareRootPrimePhase_no_fixed_window_bunching
    (hphase : SquareRootPrimePhaseEquidistributionStatement)
    {a b ε : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b)
    (hb : b ≤ 1)
    (hε : 0 < ε) :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      (squareRootPrimePhaseWindowCount X a b : ℝ) ≤
        (b - a + ε) * (primeCountUpTo X : ℝ) := by
  rcases squareRootPrimePhaseWindowCount_two_sided
      hphase ha hab hb hε with ⟨X0, hX0⟩
  refine ⟨X0, ?_⟩
  intro X hX
  exact (hX0 X hX).2

end RHLean.Analysis
