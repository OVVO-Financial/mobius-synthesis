import Mathlib
import RHLean.Proof.LargePrimeTerminalFlipLayers

/-!
# Partial crossing packet as an explicit unit boundary

The shallow reciprocal prime population must be combined before any boundary
cardinality is taken.  At a packet crossing, the repository supplies the
ordered residual

`V(R,K,j) = squareRootCrossingLayerPartialPacketInt R K j`

with `0 <= V < K`.  This file represents that already-combined scalar by `V`
positive unit cells.  Thus the entire shallow packet contributes fewer than
`K` boundary cells, independently of the number of primes in its reciprocal
layers.
-/

noncomputable section

namespace RHLean.Proof

/-- Unit carrier of the nonnegative partial packet residual. -/
def squareRootLowPrimePartialPacketBoundary
    (R K j : ℕ) : Finset ℕ :=
  Finset.range
    (Int.toNat (squareRootCrossingLayerPartialPacketInt R K j))

/-- Every compressed packet cell has unit weight. -/
def squareRootLowPrimePartialPacketBoundaryWeight (_s : ℕ) : ℤ := 1

@[simp] theorem squareRootLowPrimePartialPacketBoundary_card
    (R K j : ℕ) :
    (squareRootLowPrimePartialPacketBoundary R K j).card =
      Int.toNat (squareRootCrossingLayerPartialPacketInt R K j) := by
  simp [squareRootLowPrimePartialPacketBoundary]

/-- The compressed unit carrier has exactly the signed mass of the nonnegative
partial packet residual. -/
theorem squareRootLowPrimePartialPacketBoundary_weight_sum
    {R K j : ℕ}
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j) :
    (∑ s ∈ squareRootLowPrimePartialPacketBoundary R K j,
      squareRootLowPrimePartialPacketBoundaryWeight s) =
      squareRootCrossingLayerPartialPacketInt R K j := by
  calc
    (∑ s ∈ squareRootLowPrimePartialPacketBoundary R K j,
      squareRootLowPrimePartialPacketBoundaryWeight s) =
        (Int.toNat
          (squareRootCrossingLayerPartialPacketInt R K j) : ℤ) := by
      simp [squareRootLowPrimePartialPacketBoundary,
        squareRootLowPrimePartialPacketBoundaryWeight]
    _ = squareRootCrossingLayerPartialPacketInt R K j :=
      Int.toNat_of_nonneg hV0

/-- **The entire compressed shallow packet has fewer than `K` cells.** -/
theorem squareRootLowPrimePartialPacketBoundary_card_lt_depth
    {R K j : ℕ}
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    (squareRootLowPrimePartialPacketBoundary R K j).card < K := by
  rw [squareRootLowPrimePartialPacketBoundary_card]
  have hcast :
      (Int.toNat (squareRootCrossingLayerPartialPacketInt R K j) : ℤ) =
        squareRootCrossingLayerPartialPacketInt R K j :=
    Int.toNat_of_nonneg hV0
  have hltZ :
      (Int.toNat (squareRootCrossingLayerPartialPacketInt R K j) : ℤ) < (K : ℤ) := by
    rw [hcast]
    exact hVK
  exact_mod_cast hltZ

end RHLean.Proof
