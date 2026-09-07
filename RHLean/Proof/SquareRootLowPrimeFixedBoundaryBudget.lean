import Mathlib
import RHLean.Proof.SquareRootLowPrimeFixedPartialPacketResidual
import RHLean.Proof.SquareRootLowPrimeNoLibertyBoundaryHome

/-!
# Sharper fixed-depth no-liberty boundary budget

At the certified fixed reciprocal depth `K = 18349`, the first crossing packet
has residual cardinality strictly below `21`.  Combining that exact finite fact
with the already-proved endpoint budgets gives

* Head: `1`;
* Partial: at most `20`;
* BornExit: at most `2*R`;
* RootEquality: at most `R` by the Go parent projection.

Hence the actual tagged no-liberty boundary has cardinality at most
`3*R + 21`.

This is only a target-side improvement.  It does not assume or manufacture the
still-open source-to-boundary classifier.
-/

noncomputable section

namespace RHLean.Proof

/-- Fixed-depth packet cardinality under the actual nonnegative residual bound. -/
theorem squareRootLowPrimePartialPacketBoundary18349_card_lt_twentyOne
    {R j : ℕ}
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j)
    (hV21 : squareRootCrossingLayerPartialPacketInt R 18349 j < 21) :
    (squareRootLowPrimePartialPacketBoundary R 18349 j).card < 21 := by
  rw [squareRootLowPrimePartialPacketBoundary_card]
  have hcast :
      (Int.toNat (squareRootCrossingLayerPartialPacketInt R 18349 j) : ℤ) =
        squareRootCrossingLayerPartialPacketInt R 18349 j :=
    Int.toNat_of_nonneg hV0
  have hltZ :
      (Int.toNat (squareRootCrossingLayerPartialPacketInt R 18349 j) : ℤ) < 21 := by
    rw [hcast]
    exact hV21
  exact_mod_cast hltZ

/-- **Fixed crossing target-home budget.** -/
theorem squareRootLowPrimeNoLibertyBoundaryHomeSpace18349_card_le_three_root_add_twentyOne
    {R j : ℕ} (hR : 1 ≤ R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j)
    (hV21 : squareRootCrossingLayerPartialPacketInt R 18349 j < 21) :
    (squareRootLowPrimeNoLibertyBoundaryHomeSpace R 18349 j).card ≤
      3 * R + 21 := by
  have hpacket :=
    squareRootLowPrimePartialPacketBoundary18349_card_lt_twentyOne hV0 hV21
  have hborn :=
    squareRootLowPrimeBornNoSuccessorAtoms_card_le_two_root R 18349 hR
  rw [card_squareRootLowPrimeNoLibertyBoundaryHomeSpace]
  omega

/-- **The actual fixed-depth tagged boundary has the sharper budget directly.**
The four tags are disjoint by construction, so no home-map unfolding is needed:
use the packet bound, the born-exit bound, and the existing injective Go
root-equality carrier bound separately. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyBoundary18349_card_le_three_root_add_twentyOne
    {R j : ℕ} (hR : 1 ≤ R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j)
    (hV21 : squareRootCrossingLayerPartialPacketInt R 18349 j < 21) :
    (squareRootLowPrimeProcessedSeatNoLibertyBoundary
      R 18349 j (squareRootBornPostTailLowPrimeCutoff R)).card ≤
      3 * R + 21 := by
  have hpacket :=
    squareRootLowPrimePartialPacketBoundary18349_card_lt_twentyOne hV0 hV21
  have hborn :=
    squareRootLowPrimeBornNoSuccessorAtoms_card_le_two_root R 18349 hR
  have hroot := squareRootLowPrimeGoRootEqualityDefectCarrier_card_le_root R
  simp only [squareRootLowPrimeProcessedSeatNoLibertyBoundary,
    Finset.card_disjSum, Finset.card_singleton]
  omega

/-- A genuine fixed crossing supplies a concrete layer index with the sharper
`3*R+21` target-side budget. -/
theorem squareRootPacketCrossing18349_exists_noLibertyBoundary_card_le_three_root_add_twentyOne
    {R : ℕ} (hR : 1 ≤ R) (hcross : SquareRootPacketCrossesAt R 18349) :
    ∃ j : ℕ,
      j ≤ squareRootReciprocalPrimeLayerCard R 18349 ∧
        0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j ∧
        squareRootCrossingLayerPartialPacketInt R 18349 j < 21 ∧
        (squareRootLowPrimeProcessedSeatNoLibertyBoundary
          R 18349 j (squareRootBornPostTailLowPrimeCutoff R)).card ≤
          3 * R + 21 := by
  rcases squareRootPacketCrossing18349_exists_partial_residual_lt_twentyOne
      hcross with ⟨j, hj, hV0, hV21⟩
  exact ⟨j, hj, hV0, hV21,
    squareRootLowPrimeProcessedSeatNoLibertyBoundary18349_card_le_three_root_add_twentyOne
      hR hV0 hV21⟩

end RHLean.Proof
