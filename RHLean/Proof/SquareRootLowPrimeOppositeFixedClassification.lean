import Mathlib
import RHLean.Proof.FiniteOthelloMatching
import RHLean.Proof.SquareRootLowPrimeProcessedMatchingInvolution
import RHLean.Proof.SquareRootLowPrimeDescendingPivotStability
import RHLean.Proof.SquareRootLowPrimeNoLibertyBoundaryHome

/-!
# Opposite processed-seat Othello matching

The second matching lives on the exact processed-seat carrier.  We play the
already-kernel-checked processed prime matching in descending fresh-prime order.
The arithmetic endpoint compression to the four tagged no-liberty classes is
proved below this legality layer.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The opposite-order Othello matching on the true processed-seat carrier. -/
noncomputable def squareRootLowPrimeProcessedSeatNoLibertyMate
    (R K j U : ℕ) :
    SquareRootLowPrimeProcessedState → SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeProcessedSeatMatchingInvolution
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)

/-- The second matching preserves the exact processed carrier. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyMate_mem
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedSeatNoLibertyMate R K j U x ∈
      squareRootLowPrimeProcessedSeatCarrier R K j U := by
  exact squareRootLowPrimeProcessedSeatMatchingInvolution_mem
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U) hx

/-- The second matching is involutive on the exact processed carrier. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyMate_involutive
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedSeatNoLibertyMate R K j U
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U x) = x := by
  apply squareRootLowPrimeProcessedSeatMatchingInvolution_involutive
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)
  · intro p hp
    exact (prime_of_mem_squareRootLowPrimeFreshPrimeListDescending hp).pos
  · exact hx

/-- Every moved processed seat reverses its native sign. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyMate_weight_neg
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hne : squareRootLowPrimeProcessedSeatNoLibertyMate R K j U x ≠ x) :
    squareRootLowPrimeProcessedSeatWeightReal
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U x) =
      -squareRootLowPrimeProcessedSeatWeightReal x := by
  apply squareRootLowPrimeProcessedSeatMatchingInvolution_weight_neg
    (squareRootLowPrimeFreshPrimeListDescending K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)
  · intro p hp
    exact prime_of_mem_squareRootLowPrimeFreshPrimeListDescending hp
  · exact hx
  · exact hne

/-- The legality layer's fixed set is the descending processed frontier. -/
theorem finiteOthelloStablePart_processedSeatNoLibertyMate_eq_descendingFrontier
    (R K j U : ℕ) :
    finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U) =
      squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U := by
  classical
  ext x
  have h := Finset.ext_iff.mp
    (signMatchingFixedPart_processedSeatMatching_eq_frontier
      (squareRootLowPrimeFreshPrimeListDescending K U)
      (squareRootLowPrimeProcessedSeatCarrier R K j U)
      (fun p hp =>
        (prime_of_mem_squareRootLowPrimeFreshPrimeListDescending hp).pos)) x
  simpa [finiteOthelloStablePart, signMatchingFixedPart,
    squareRootLowPrimeProcessedSeatNoLibertyMate,
    squareRootLowPrimeProcessedSeatDescendingTerminalFrontier] using h

/-- Finite cancellation identifies the stable mass with the running imbalance. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyMate_stableMass_eq_runningImbalance
    {R K j U : ℕ} (hR : 2 ≤ R) :
    (∑ x ∈ finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeRunningImbalanceReal R K j U := by
  calc
    (∑ x ∈ finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x :=
        (sum_finiteOthelloRegion_eq_stable
          (squareRootLowPrimeProcessedSeatCarrier R K j U)
          (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U)
          squareRootLowPrimeProcessedSeatWeightReal
          (fun x hx => squareRootLowPrimeProcessedSeatNoLibertyMate_mem hx)
          (fun x hx => squareRootLowPrimeProcessedSeatNoLibertyMate_involutive hx)
          (fun x hx hne =>
            squareRootLowPrimeProcessedSeatNoLibertyMate_weight_neg hx hne)).symm
    _ = squareRootLowPrimeRunningImbalanceReal R K j U :=
      squareRootLowPrimeProcessedSeatCarrier_mass_eq_runningImbalanceReal hR

end RHLean.Proof
