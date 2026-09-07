import Mathlib
import RHLean.Analysis.SquareRootFixedCrossing18349
import RHLean.Proof.SquareRootLowPrimePartialPacketBoundary

/-!
# Exact fixed-depth size of the partial crossing residual

At the certified fixed crossing depth `K = 18349`, the finite Mertens prefix is
exactly `-21`.  The first crossing prime therefore advances the reciprocal
packet in steps of size `21`.

The existing first-crossing theorem already proves that the nonnegative
overshoot is strictly smaller than one such step.  Hence the compressed partial
packet has fewer than `21` unit cells, uniformly in `R`.

This is a finite exact certificate only.  No asymptotic estimate, PNT input, or
new analytic hypothesis enters here.
-/

noncomputable section

namespace RHLean.Proof

/-- Exact finite Mertens prefix at the fixed reciprocal crossing depth. -/
theorem squareRootMertensInt_18349 :
    squareRootMertensInt 18349 = -21 := by
  native_decide

/-- **Fixed-depth overshoot is smaller than 21.**  At a genuine crossing at
`18349`, the first admitted prime which makes the packet nonnegative leaves a
residual in `[0,21)`. -/
theorem squareRootPacketCrossing18349_exists_partial_residual_lt_twentyOne
    {R : ℕ} (hcross : SquareRootPacketCrossesAt R 18349) :
    ∃ j : ℕ,
      j ≤ squareRootReciprocalPrimeLayerCard R 18349 ∧
        0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j ∧
          squareRootCrossingLayerPartialPacketInt R 18349 j < 21 := by
  rcases squareRootPacketCrossing_exists_partial_residual hcross with
    ⟨j, hj, hV0, hVstep⟩
  rw [squareRootMertensInt_18349] at hVstep
  norm_num at hVstep
  exact ⟨j, hj, hV0, hVstep⟩

/-- Cardinality form: the literal compressed packet attached to that first
crossing has fewer than 21 cells. -/
theorem squareRootPacketCrossing18349_exists_partialBoundary_card_lt_twentyOne
    {R : ℕ} (hcross : SquareRootPacketCrossesAt R 18349) :
    ∃ j : ℕ,
      j ≤ squareRootReciprocalPrimeLayerCard R 18349 ∧
        0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j ∧
        squareRootCrossingLayerPartialPacketInt R 18349 j < 21 ∧
        (squareRootLowPrimePartialPacketBoundary R 18349 j).card < 21 := by
  rcases squareRootPacketCrossing18349_exists_partial_residual_lt_twentyOne
      hcross with ⟨j, hj, hV0, hV21⟩
  refine ⟨j, hj, hV0, hV21, ?_⟩
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

end RHLean.Proof
