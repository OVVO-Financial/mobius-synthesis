import Mathlib
import RHLean.Proof.SquareRootLowPrimeCanonicalLiberty

/-!
# Exact raw canonical-liberty source/target partition

The canonical-liberty dichotomy is useful quantitatively only if the removed
population is retained as the two endpoints of the actual prime matchings.
This module records those endpoints across the complete chronological matching
list.

For every processed prime stage we keep

* the lower endpoint as a liberty source;
* the prime-extended endpoint as its liberty target; and
* the states surviving every stage as the raw no-liberty frontier.

The three populations are pairwise disjoint and partition the original carrier.
The source and target masses cancel exactly, so the raw frontier carries the
entire signed mass of the original carrier.

This raw frontier is deliberately **not** named as the final compressed liberty
boundary: several unit seats may still lie over one arithmetic root.  The final
boundary theorem must perform the additional alternating creation/response
rematching and prove at most one unmatched unit per canonical root before any
cardinality estimate is accepted.

No estimate, encoding, root box, terminal hypothesis, or frontier-cardinality
assumption appears here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Lower endpoints removed over an ordered prime list. -/
def squareRootLowPrimeLibertySourcePart :
    List ℕ → Finset SquareRootLowPrimeProcessedState →
      Finset SquareRootLowPrimeProcessedState
  | [], _S => ∅
  | p :: ps, S =>
      squareRootLowPrimeProcessedSeatPairLower S p ∪
        squareRootLowPrimeLibertySourcePart ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p)

/-- Upper endpoints removed over an ordered prime list. -/
def squareRootLowPrimeLibertyTargetPart :
    List ℕ → Finset SquareRootLowPrimeProcessedState →
      Finset SquareRootLowPrimeProcessedState
  | [], _S => ∅
  | p :: ps, S =>
      squareRootLowPrimeProcessedSeatPairUpper S p ∪
        squareRootLowPrimeLibertyTargetPart ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p)

/-- Every source endpoint comes from the original carrier. -/
theorem squareRootLowPrimeLibertySourcePart_subset
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeLibertySourcePart ps S ⊆ S := by
  induction ps generalizing S with
  | nil => simp [squareRootLowPrimeLibertySourcePart]
  | cons p ps ih =>
      intro x hx
      rcases Finset.mem_union.mp hx with hxLower | hxTail
      · exact squareRootLowPrimeProcessedSeatPairLower_subset S p hxLower
      · exact squareRootLowPrimeProcessedSeatFrontierStep_subset' S p
          (ih (S := squareRootLowPrimeProcessedSeatFrontierStep S p) hxTail)

/-- Every target endpoint comes from the original carrier. -/
theorem squareRootLowPrimeLibertyTargetPart_subset
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeLibertyTargetPart ps S ⊆ S := by
  induction ps generalizing S with
  | nil => simp [squareRootLowPrimeLibertyTargetPart]
  | cons p ps ih =>
      intro x hx
      rcases Finset.mem_union.mp hx with hxUpper | hxTail
      · exact squareRootLowPrimeProcessedSeatPairUpper_subset S p hxUpper
      · exact squareRootLowPrimeProcessedSeatFrontierStep_subset' S p
          (ih (S := squareRootLowPrimeProcessedSeatFrontierStep S p) hxTail)

/-- The raw no-liberty frontier is a subset of its original carrier. -/
theorem squareRootLowPrimeNoLibertyBoundary_subset
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeNoLibertyBoundary ps S ⊆ S := by
  unfold squareRootLowPrimeNoLibertyBoundary
  exact squareRootLowPrimeProcessedSeatMatchingFrontier_subset' ps S

/-- Lower endpoints removed at one prime are disjoint from the surviving
one-step frontier. -/
theorem squareRootLowPrimeProcessedSeatPairLower_disjoint_frontierStep
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Disjoint (squareRootLowPrimeProcessedSeatPairLower S p)
      (squareRootLowPrimeProcessedSeatFrontierStep S p) := by
  rw [Finset.disjoint_left]
  intro x hxLower hxFrontier
  exact (Finset.mem_sdiff.mp hxFrontier).2
    (Finset.mem_union.mpr (Or.inl hxLower))

/-- Upper endpoints removed at one prime are disjoint from the surviving
one-step frontier. -/
theorem squareRootLowPrimeProcessedSeatPairUpper_disjoint_frontierStep
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Disjoint (squareRootLowPrimeProcessedSeatPairUpper S p)
      (squareRootLowPrimeProcessedSeatFrontierStep S p) := by
  rw [Finset.disjoint_left]
  intro x hxUpper hxFrontier
  exact (Finset.mem_sdiff.mp hxFrontier).2
    (Finset.mem_union.mpr (Or.inr hxUpper))

/-- Liberty sources and targets are disjoint globally, not merely at one prime. -/
theorem squareRootLowPrimeLibertySourcePart_disjoint_targetPart
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    Disjoint (squareRootLowPrimeLibertySourcePart ps S)
      (squareRootLowPrimeLibertyTargetPart ps S) := by
  induction ps generalizing S with
  | nil => simp [squareRootLowPrimeLibertySourcePart,
      squareRootLowPrimeLibertyTargetPart]
  | cons p ps ih =>
      rw [Finset.disjoint_left]
      intro x hxSource hxTarget
      rcases Finset.mem_union.mp hxSource with hxLower | hxSourceTail
      · rcases Finset.mem_union.mp hxTarget with hxUpper | hxTargetTail
        · exact (Finset.disjoint_left.mp
            (squareRootLowPrimeProcessedSeatPairLower_disjoint_upper S p))
            hxLower hxUpper
        · have hxFrontier :=
            squareRootLowPrimeLibertyTargetPart_subset ps
              (squareRootLowPrimeProcessedSeatFrontierStep S p) hxTargetTail
          exact (Finset.disjoint_left.mp
            (squareRootLowPrimeProcessedSeatPairLower_disjoint_frontierStep S p))
            hxLower hxFrontier
      · rcases Finset.mem_union.mp hxTarget with hxUpper | hxTargetTail
        · have hxFrontier :=
            squareRootLowPrimeLibertySourcePart_subset ps
              (squareRootLowPrimeProcessedSeatFrontierStep S p) hxSourceTail
          exact (Finset.disjoint_left.mp
            (squareRootLowPrimeProcessedSeatPairUpper_disjoint_frontierStep S p))
            hxUpper hxFrontier
        · exact (Finset.disjoint_left.mp
            (ih (S := squareRootLowPrimeProcessedSeatFrontierStep S p)))
            hxSourceTail hxTargetTail

/-- Liberty sources are disjoint from the raw terminal no-liberty frontier. -/
theorem squareRootLowPrimeLibertySourcePart_disjoint_boundary
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    Disjoint (squareRootLowPrimeLibertySourcePart ps S)
      (squareRootLowPrimeNoLibertyBoundary ps S) := by
  induction ps generalizing S with
  | nil => simp [squareRootLowPrimeLibertySourcePart]
  | cons p ps ih =>
      rw [Finset.disjoint_left]
      intro x hxSource hxBoundary
      rcases Finset.mem_union.mp hxSource with hxLower | hxSourceTail
      · have hxFrontier :
            x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          squareRootLowPrimeProcessedSeatMatchingFrontier_subset' ps
            (squareRootLowPrimeProcessedSeatFrontierStep S p) hxBoundary
        exact (Finset.disjoint_left.mp
          (squareRootLowPrimeProcessedSeatPairLower_disjoint_frontierStep S p))
          hxLower hxFrontier
      · exact (Finset.disjoint_left.mp
          (ih (S := squareRootLowPrimeProcessedSeatFrontierStep S p)))
          hxSourceTail hxBoundary

/-- Liberty targets are disjoint from the raw terminal no-liberty frontier. -/
theorem squareRootLowPrimeLibertyTargetPart_disjoint_boundary
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    Disjoint (squareRootLowPrimeLibertyTargetPart ps S)
      (squareRootLowPrimeNoLibertyBoundary ps S) := by
  induction ps generalizing S with
  | nil => simp [squareRootLowPrimeLibertyTargetPart]
  | cons p ps ih =>
      rw [Finset.disjoint_left]
      intro x hxTarget hxBoundary
      rcases Finset.mem_union.mp hxTarget with hxUpper | hxTargetTail
      · have hxFrontier :
            x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          squareRootLowPrimeProcessedSeatMatchingFrontier_subset' ps
            (squareRootLowPrimeProcessedSeatFrontierStep S p) hxBoundary
        exact (Finset.disjoint_left.mp
          (squareRootLowPrimeProcessedSeatPairUpper_disjoint_frontierStep S p))
          hxUpper hxFrontier
      · exact (Finset.disjoint_left.mp
          (ih (S := squareRootLowPrimeProcessedSeatFrontierStep S p)))
          hxTargetTail hxBoundary

/-- The union of all removed source and target endpoints is disjoint from the
raw terminal frontier. -/
theorem squareRootLowPrimeLibertySourceTarget_disjoint_boundary
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    Disjoint
      (squareRootLowPrimeLibertySourcePart ps S ∪
        squareRootLowPrimeLibertyTargetPart ps S)
      (squareRootLowPrimeNoLibertyBoundary ps S) := by
  rw [Finset.disjoint_left]
  intro x hxST hxBoundary
  rcases Finset.mem_union.mp hxST with hxSource | hxTarget
  · exact (Finset.disjoint_left.mp
      (squareRootLowPrimeLibertySourcePart_disjoint_boundary ps S))
      hxSource hxBoundary
  · exact (Finset.disjoint_left.mp
      (squareRootLowPrimeLibertyTargetPart_disjoint_boundary ps S))
      hxTarget hxBoundary

/-- **Exact source/target/raw-frontier partition of an arbitrary processed carrier.** -/
theorem squareRootLowPrimeCanonicalLiberty_partition
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeLibertySourcePart ps S ∪
        squareRootLowPrimeLibertyTargetPart ps S ∪
        squareRootLowPrimeNoLibertyBoundary ps S = S := by
  induction ps generalizing S with
  | nil => simp [squareRootLowPrimeLibertySourcePart,
      squareRootLowPrimeLibertyTargetPart,
      squareRootLowPrimeNoLibertyBoundary,
      squareRootLowPrimeProcessedSeatMatchingFrontier]
  | cons p ps ih =>
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hxST | hxBoundary
        · rcases Finset.mem_union.mp hxST with hxSource | hxTarget
          · exact squareRootLowPrimeLibertySourcePart_subset (p :: ps) S hxSource
          · exact squareRootLowPrimeLibertyTargetPart_subset (p :: ps) S hxTarget
        · exact squareRootLowPrimeNoLibertyBoundary_subset (p :: ps) S hxBoundary
      · intro hxS
        by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatPaired S p
        · rcases Finset.mem_union.mp hxPaired with hxLower | hxUpper
          · apply Finset.mem_union.mpr
            left
            apply Finset.mem_union.mpr
            left
            exact Finset.mem_union.mpr (Or.inl hxLower)
          · apply Finset.mem_union.mpr
            left
            apply Finset.mem_union.mpr
            right
            exact Finset.mem_union.mpr (Or.inl hxUpper)
        · have hxFrontier :
              x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
            Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
          have hxTail :
              x ∈ squareRootLowPrimeLibertySourcePart ps
                    (squareRootLowPrimeProcessedSeatFrontierStep S p) ∪
                  squareRootLowPrimeLibertyTargetPart ps
                    (squareRootLowPrimeProcessedSeatFrontierStep S p) ∪
                  squareRootLowPrimeNoLibertyBoundary ps
                    (squareRootLowPrimeProcessedSeatFrontierStep S p) := by
            rw [ih]
            exact hxFrontier
          rcases Finset.mem_union.mp hxTail with hxTailST | hxBoundary
          · rcases Finset.mem_union.mp hxTailST with hxSourceTail | hxTargetTail
            · apply Finset.mem_union.mpr
              left
              apply Finset.mem_union.mpr
              left
              exact Finset.mem_union.mpr (Or.inr hxSourceTail)
            · apply Finset.mem_union.mpr
              left
              apply Finset.mem_union.mpr
              right
              exact Finset.mem_union.mpr (Or.inr hxTargetTail)
          · apply Finset.mem_union.mpr
            right
            exact hxBoundary

/-- The removed liberty sources and targets have zero total signed mass. -/
theorem squareRootLowPrimeLibertySource_add_target_weight_sum_eq_zero
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (hprime : ∀ p ∈ ps, p.Prime) :
    (∑ x ∈ squareRootLowPrimeLibertySourcePart ps S,
        squareRootLowPrimeProcessedSeatWeightReal x) +
      (∑ x ∈ squareRootLowPrimeLibertyTargetPart ps S,
        squareRootLowPrimeProcessedSeatWeightReal x) = 0 := by
  have hpart := squareRootLowPrimeCanonicalLiberty_partition ps S
  have hST := squareRootLowPrimeLibertySourcePart_disjoint_targetPart ps S
  have hBoundary := squareRootLowPrimeLibertySourceTarget_disjoint_boundary ps S
  have hdecomp :
      (∑ x ∈ S, squareRootLowPrimeProcessedSeatWeightReal x) =
        (∑ x ∈ squareRootLowPrimeLibertySourcePart ps S,
          squareRootLowPrimeProcessedSeatWeightReal x) +
        (∑ x ∈ squareRootLowPrimeLibertyTargetPart ps S,
          squareRootLowPrimeProcessedSeatWeightReal x) +
        ∑ x ∈ squareRootLowPrimeNoLibertyBoundary ps S,
          squareRootLowPrimeProcessedSeatWeightReal x := by
    calc
      (∑ x ∈ S, squareRootLowPrimeProcessedSeatWeightReal x) =
          ∑ x ∈
            (squareRootLowPrimeLibertySourcePart ps S ∪
              squareRootLowPrimeLibertyTargetPart ps S ∪
              squareRootLowPrimeNoLibertyBoundary ps S),
            squareRootLowPrimeProcessedSeatWeightReal x := by
        rw [hpart]
      _ =
          (∑ x ∈ squareRootLowPrimeLibertySourcePart ps S,
            squareRootLowPrimeProcessedSeatWeightReal x) +
          (∑ x ∈ squareRootLowPrimeLibertyTargetPart ps S,
            squareRootLowPrimeProcessedSeatWeightReal x) +
          ∑ x ∈ squareRootLowPrimeNoLibertyBoundary ps S,
            squareRootLowPrimeProcessedSeatWeightReal x := by
        rw [Finset.sum_union hBoundary, Finset.sum_union hST]
  have hmatch := squareRootLowPrimeProcessedSeat_weight_sum_eq_matchingFrontier
    ps S hprime
  have hmatch' :
      (∑ x ∈ S, squareRootLowPrimeProcessedSeatWeightReal x) =
        ∑ x ∈ squareRootLowPrimeNoLibertyBoundary ps S,
          squareRootLowPrimeProcessedSeatWeightReal x := by
    simpa [squareRootLowPrimeNoLibertyBoundary] using hmatch
  rw [hdecomp] at hmatch'
  linarith

/-- Canonical terminal cutoff used by the raw liberty partition. -/
def squareRootLowPrimeCanonicalLibertyCutoff (R : ℕ) : ℕ :=
  squareRootBornPostTailLowPrimeCutoff R

/-- Raw prime-matching source population at the canonical terminal cutoff. -/
def squareRootLowPrimeCanonicalRawLibertySources
    (R K j : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeLibertySourcePart
    (squareRootLowPrimeFreshPrimeList K
      (squareRootLowPrimeCanonicalLibertyCutoff R))
    (squareRootLowPrimeProcessedSeatCarrier R K j
      (squareRootLowPrimeCanonicalLibertyCutoff R))

/-- Raw prime-matching target population at the canonical terminal cutoff. -/
def squareRootLowPrimeCanonicalRawLibertyTargets
    (R K j : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeLibertyTargetPart
    (squareRootLowPrimeFreshPrimeList K
      (squareRootLowPrimeCanonicalLibertyCutoff R))
    (squareRootLowPrimeProcessedSeatCarrier R K j
      (squareRootLowPrimeCanonicalLibertyCutoff R))

/-- Raw no-liberty frontier before alternating-component compression. -/
def squareRootLowPrimeCanonicalRawNoLibertyFrontier
    (R K j : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeNoLibertyBoundary
    (squareRootLowPrimeFreshPrimeList K
      (squareRootLowPrimeCanonicalLibertyCutoff R))
    (squareRootLowPrimeProcessedSeatCarrier R K j
      (squareRootLowPrimeCanonicalLibertyCutoff R))

/-- **Canonical terminal raw source/target/frontier decomposition.** -/
theorem squareRootLowPrimeCanonicalRawLiberty_decomposition
    (R K j : ℕ) :
    squareRootLowPrimeCanonicalRawLibertySources R K j ∪
        squareRootLowPrimeCanonicalRawLibertyTargets R K j ∪
        squareRootLowPrimeCanonicalRawNoLibertyFrontier R K j =
      squareRootLowPrimeProcessedSeatCarrier R K j
        (squareRootLowPrimeCanonicalLibertyCutoff R) := by
  exact squareRootLowPrimeCanonicalLiberty_partition _ _

/-- The raw terminal source/target pieces are disjoint. -/
theorem squareRootLowPrimeCanonicalRawLiberty_sources_disjoint_targets
    (R K j : ℕ) :
    Disjoint (squareRootLowPrimeCanonicalRawLibertySources R K j)
      (squareRootLowPrimeCanonicalRawLibertyTargets R K j) :=
  squareRootLowPrimeLibertySourcePart_disjoint_targetPart _ _

/-- The raw paired interior is disjoint from the raw exposed frontier. -/
theorem squareRootLowPrimeCanonicalRawLiberty_interior_disjoint_frontier
    (R K j : ℕ) :
    Disjoint
      (squareRootLowPrimeCanonicalRawLibertySources R K j ∪
        squareRootLowPrimeCanonicalRawLibertyTargets R K j)
      (squareRootLowPrimeCanonicalRawNoLibertyFrontier R K j) :=
  squareRootLowPrimeLibertySourceTarget_disjoint_boundary _ _

/-- **Exact raw frontier mass identity at the canonical terminal cutoff.**
This is the entry point for the still-required alternating-component
compression; it is not a cardinality theorem. -/
theorem squareRootLowPrimeCanonicalRawNoLibertyFrontier_weight_sum_eq_terminal
    {R K j : ℕ} (hR : 2 ≤ R) :
    (∑ x ∈ squareRootLowPrimeCanonicalRawNoLibertyFrontier R K j,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootLowPrimeCanonicalLibertyCutoff R) := by
  unfold squareRootLowPrimeCanonicalRawNoLibertyFrontier
    squareRootLowPrimeCanonicalLibertyCutoff
    squareRootLowPrimeNoLibertyBoundary
  simpa [squareRootLowPrimeProcessedSeatTerminalFrontier] using
    (squareRootLowPrimeProcessedSeatTerminalFrontier_weight_sum
      (R := R) (K := K) (j := j)
      (U := squareRootBornPostTailLowPrimeCutoff R) hR)

end RHLean.Proof
