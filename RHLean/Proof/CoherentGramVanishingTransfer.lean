import Mathlib
import RHLean.Proof.SquareBlockCoherentGram

/-!
# Vanishing coherent Gram transfer

This module converts decay of the coherent all-ones square-block Gram mode into
vanishing normalized cumulative square-block discrepancy.

The input is deliberately stated in epsilon/eventually form.  By the exact
identity from `SquareBlockCoherentGram`, the normalized coherent Gram mass is the
square of the normalized cumulative block prefix.  Hence an eventual `ε²` bound
on the Gram ratio gives an eventual `ε` bound on the absolute normalized prefix.

No arithmetic Gram estimate is asserted here.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace RHLean.Proof

/-- Absolute cumulative square-block discrepancy on the block-index scale. -/
def normalizedCumulativeSquareBlockDiscrepancy (N : ℕ) : ℝ :=
  |realCanonicalTotalPrefix N| / (N : ℝ)

/-- Coherent block-Gram mass normalized by the square of the block-index scale. -/
def normalizedSquareBlockCoherentGramMass (N : ℕ) : ℝ :=
  squareBlockCoherentGramMass N / ((N : ℝ) ^ 2)

/-- Epsilon/eventually formulation of coherent-mode Gram suppression. -/
def SquareBlockCoherentGramVanishes : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop,
      normalizedSquareBlockCoherentGramMass N ≤ ε ^ 2

/-- Epsilon/eventually formulation of vanishing normalized cumulative
square-block discrepancy. -/
def CumulativeSquareBlockDiscrepancyVanishes : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop,
      normalizedCumulativeSquareBlockDiscrepancy N ≤ ε

/-- Pointwise exact identity: the square of the normalized absolute cumulative
prefix is the normalized coherent Gram mass. -/
theorem normalizedCumulativeSquareBlockDiscrepancy_sq
    (N : ℕ) (hN : 0 < N) :
    (normalizedCumulativeSquareBlockDiscrepancy N) ^ 2 =
      normalizedSquareBlockCoherentGramMass N := by
  unfold normalizedCumulativeSquareBlockDiscrepancy
    normalizedSquareBlockCoherentGramMass
  simpa [div_pow, sq_abs] using
    normalized_prefix_sq_eq_normalized_coherentGram N hN

/-- Coherent all-ones Gram suppression forces vanishing normalized cumulative
square-block discrepancy. -/
theorem cumulativeSquareBlockDiscrepancyVanishes_of_coherentGramVanishes
    (hgram : SquareBlockCoherentGramVanishes) :
    CumulativeSquareBlockDiscrepancyVanishes := by
  intro ε hε
  have hgramEventually := hgram ε hε
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    omega
  filter_upwards [hgramEventually, hpos] with N hGN hN
  have hsq := normalizedCumulativeSquareBlockDiscrepancy_sq N hN
  have hnonneg : 0 ≤ normalizedCumulativeSquareBlockDiscrepancy N := by
    unfold normalizedCumulativeSquareBlockDiscrepancy
    positivity
  rw [← hsq] at hGN
  nlinarith

end RHLean.Proof
