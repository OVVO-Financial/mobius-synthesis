import RHLean.Proof.SquareRootMertensEndpointAmplification

/-!
# Parent-fibre expansion of the square-root ancestry successor

The open Gram estimate must retain the successor as the actual legal ancestry
state.  This module rewrites that successor one level below the scalar prefix:
each active nonroot child contributes the weight of its unique stripped parent.

The resulting double sum is indexed by the same canonical source universe as the
root.  It is therefore the natural interface for a direct signed cross-term
estimate and for the prime-wheel fixed-prime/cofactor fibres already present in
the repository.

Only exact finite identities are proved here.  No absolute-value estimate or
independence assertion is introduced.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge
open CanonicalGapAncestryEnergyBridge

/-- Parent-fibre expansion of the active successor.  The outer coordinate is a
candidate parent and the inner coordinate is a child whose deterministic parent
is that candidate. -/
def sourceSuccessorParentFiberMass (B x : ℕ) : ℤ :=
  ∑ p : SourceIndex B,
    ∑ s : SourceIndex B,
      if sourceClock B s ≤ x ∧ sourceParent s = some p then
        sourceWeight p
      else
        0

/-- The clock-pushed successor is exactly the sum of its active parent fibres. -/
theorem sourceSuccessorPrefix_eq_parentFiberMass (B x : ℕ) :
    sourceSuccessorPrefix B x = sourceSuccessorParentFiberMass B x := by
  classical
  unfold sourceSuccessorPrefix sourceSuccessorParentFiberMass clockPushforward
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hclock : sourceClock B s ≤ x
  · cases hparent : sourceParent s with
    | none =>
        simp [boundedSourceFlow, ParentFlow.successorOperator, hclock, hparent]
    | some p =>
        simp [boundedSourceFlow, ParentFlow.successorOperator, hclock, hparent]
  · simp [hclock]

/-- One parent fibre as a signed integer mass. -/
def sourceSuccessorParentFiber (B x : ℕ) (p : SourceIndex B) : ℤ :=
  ∑ s : SourceIndex B,
    if sourceClock B s ≤ x ∧ sourceParent s = some p then
      sourceWeight p
    else
      0

/-- Integer count of active legal children selecting a fixed parent. -/
def sourceActiveChildMultiplicityInt (B x : ℕ) (p : SourceIndex B) : ℤ :=
  ∑ s : SourceIndex B,
    if sourceClock B s ≤ x ∧ sourceParent s = some p then 1 else 0

/-- Every parent fibre is exactly its active-child multiplicity times the parent
Möbius weight. -/
theorem sourceSuccessorParentFiber_eq_multiplicity_mul_weight
    (B x : ℕ) (p : SourceIndex B) :
    sourceSuccessorParentFiber B x p =
      sourceActiveChildMultiplicityInt B x p * sourceWeight p := by
  classical
  unfold sourceSuccessorParentFiber sourceActiveChildMultiplicityInt
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hchild : sourceClock B s ≤ x ∧ sourceParent s = some p
  · simp [hchild]
  · simp [hchild]

/-- The complete successor is the exact sum of the individual parent fibres. -/
theorem sourceSuccessorPrefix_eq_sum_parentFibers (B x : ℕ) :
    sourceSuccessorPrefix B x =
      ∑ p : SourceIndex B, sourceSuccessorParentFiber B x p := by
  rw [sourceSuccessorPrefix_eq_parentFiberMass]
  rfl

/-- Weighted-parent form of the complete successor.  The arithmetic coefficient
of a parent is its actual number of active legal prime-extension children. -/
theorem sourceSuccessorPrefix_eq_sum_multiplicity_mul_weight (B x : ℕ) :
    sourceSuccessorPrefix B x =
      ∑ p : SourceIndex B,
        sourceActiveChildMultiplicityInt B x p * sourceWeight p := by
  rw [sourceSuccessorPrefix_eq_sum_parentFibers]
  apply Finset.sum_congr rfl
  intro p _hp
  exact sourceSuccessorParentFiber_eq_multiplicity_mul_weight B x p

/-- Signed root-by-parent-fibre cross ledger at a complete square endpoint.  No
term is discarded: the three finite coordinates are the active root, the parent
coordinate, and the active child selecting that parent. -/
def squareRootRootSuccessorCrossLedger (B R : ℕ) : ℤ :=
  ∑ u ∈ activeRootSourceSet B (R - 1),
    ∑ p : SourceIndex B,
      ∑ s : SourceIndex B,
        if sourceClock B s ≤ R - 1 ∧ sourceParent s = some p then
          sourceWeight u * sourceWeight p
        else
          0

/-- The source-level ledger is exactly the scalar root-successor cross term. -/
theorem squareRootRootSuccessorCrossLedger_eq_mul (B R : ℕ) :
    squareRootRootSuccessorCrossLedger B R =
      sourceRootPrefix B (R - 1) * sourceSuccessorPrefix B (R - 1) := by
  classical
  rw [sourceRootPrefix_eq_activeRoot_sum,
    sourceSuccessorPrefix_eq_sum_parentFibers]
  unfold squareRootRootSuccessorCrossLedger sourceSuccessorParentFiber
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hchild : sourceClock B s ≤ R - 1 ∧ sourceParent s = some p
  · simp [hchild]
  · simp [hchild]

/-- Cross-term form of the legal Gram defect using the explicit source ledger. -/
theorem squareRootLegalAncestryGramDefect_eq_sourceLedger
    (B R : ℕ) :
    squareRootLegalAncestryGramDefect B R =
      squareRootLegalRootReal B R ^ 2 +
        squareRootLegalSuccessorReal B R ^ 2 -
        2 * ((squareRootRootSuccessorCrossLedger B R : ℤ) : ℝ) := by
  rw [squareRootLegalAncestryGramDefect_eq_expanded,
    squareRootRootSuccessorCrossLedger_eq_mul]
  unfold squareRootLegalRootReal squareRootLegalSuccessorReal
  push_cast
  ring

end RHLean.Proof
