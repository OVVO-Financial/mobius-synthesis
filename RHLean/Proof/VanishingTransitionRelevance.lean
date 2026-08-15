import Mathlib
import RHLean.Proof.MutableSupportBound

/-!
# Vanishing transition relevance

This module formalizes the final deterministic asymptotic transfer.  A transition
support `U n` is measured on the linear scale of the square block by

```text
card (U n) / n.
```

If the settled complement has zero Möbius mass, the mutable-support bound gives
`|Δ_n| <= card (U n)`. Dividing by `n` shows that vanishing transition relevance
forces the normalized square-block discrepancy to vanish as well.

The arithmetic construction of the genuine severed transition support, and the
proof that its relevance vanishes, remain separate inputs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators Topology
open Filter

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Transition relevance on the natural linear scale of the square block. -/
def transitionRelevance (U : ℕ → Finset ℕ) (n : ℕ) : ℝ :=
  ((U n).card : ℝ) / (n : ℝ)

/-- Absolute square-block discrepancy normalized by the same linear scale. -/
def normalizedSquareBlockDiscrepancy (n : ℕ) : ℝ :=
  |(squareBlockMoebius n : ℝ)| / (n : ℝ)

/-- Epsilon/eventually formulation of vanishing transition relevance. -/
def TransitionRelevanceVanishes (U : ℕ → Finset ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, transitionRelevance U n ≤ ε

/-- Epsilon/eventually formulation of `Δ_n = o(n)`. -/
def SquareBlockDiscrepancyVanishes : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, normalizedSquareBlockDiscrepancy n ≤ ε

/-- Pointwise transfer: the normalized block discrepancy is bounded by transition
relevance whenever the settled complement has zero Möbius mass. -/
theorem normalizedSquareBlockDiscrepancy_le_transitionRelevance
    (U : ℕ → Finset ℕ)
    (hU : ∀ n, U n ⊆ squareBlockInterval n)
    (hinterior : ∀ n, ∑ m ∈ squareBlockInterval n \ U n, μ m = 0)
    {n : ℕ} (hn : 0 < n) :
    normalizedSquareBlockDiscrepancy n ≤ transitionRelevance U n := by
  have hInt : |squareBlockMoebius n| ≤ ((U n).card : ℤ) :=
    abs_squareBlockMoebius_le_mutable_card (hU n) (hinterior n)
  have hReal : |(squareBlockMoebius n : ℝ)| ≤ ((U n).card : ℝ) := by
    exact_mod_cast hInt
  unfold normalizedSquareBlockDiscrepancy transitionRelevance
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  exact (div_le_div_iff_of_pos_right hnReal).2 hReal

/-- Vanishing transition relevance forces `Δ_n = o(n)` in epsilon/eventually
form.  No further cancellation estimate is used. -/
theorem squareBlockDiscrepancyVanishes_of_transitionRelevanceVanishes
    (U : ℕ → Finset ℕ)
    (hU : ∀ n, U n ⊆ squareBlockInterval n)
    (hinterior : ∀ n, ∑ m ∈ squareBlockInterval n \ U n, μ m = 0)
    (hvanish : TransitionRelevanceVanishes U) :
    SquareBlockDiscrepancyVanishes := by
  intro ε hε
  have hrel := hvanish ε hε
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    omega
  filter_upwards [hrel, hpos] with n hnRel hnPos
  exact le_trans
    (normalizedSquareBlockDiscrepancy_le_transitionRelevance U hU hinterior hnPos)
    hnRel

end RHLean.Proof
