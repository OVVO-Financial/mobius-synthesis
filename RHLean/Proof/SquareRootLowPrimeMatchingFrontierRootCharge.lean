import Mathlib
import RHLean.Proof.SquareRootLowPrimeMatchingFrontierSaturation
import RHLean.Proof.SquareRootLowPrimeMatchedFrontierBound

/-!
# Root-seat charge for the complete matched response frontier

The repository already carries arithmetic states from their cofactor coordinate
to a root-scale coordinate.  Once a bounded seat index is supplied, the final
combinatorial step is purely finite: an injective map from the complete matched
frontier into

`{1,...,R} x {0,...,B-1}`

bounds the frontier by `R*B`.  Combined with the preceding signed matching
reduction, this immediately bounds the actual deep increment by `R*B`.

This file isolates that transfer so the remaining arithmetic theorem can focus
only on constructing the root/seat encoding from the existing cofactor-to-root
map and the fresh-prime saturation property.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Finite root coordinate paired with a bounded local seat. -/
def squareRootLowPrimeRootSeatBox (R B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 R).product (Finset.range B)

/-- The root-seat box has exactly `R*B` states. -/
theorem card_squareRootLowPrimeRootSeatBox (R B : ℕ) :
    (squareRootLowPrimeRootSeatBox R B).card = R * B := by
  simp [squareRootLowPrimeRootSeatBox]

/-- An injective root-seat encoding gives the desired frontier-cardinality
bound. -/
theorem squareRootLowPrimeMatchingFrontier_card_le_root_mul_seats
    {R K U B : ℕ} (encode : ℕ → ℕ × ℕ)
    (hinj : Set.InjOn encode
      (squareRootLowPrimeOwnedResponseMatchingFrontier R K U))
    (hbox : ∀ n ∈ squareRootLowPrimeOwnedResponseMatchingFrontier R K U,
      encode n ∈ squareRootLowPrimeRootSeatBox R B) :
    (squareRootLowPrimeOwnedResponseMatchingFrontier R K U).card ≤ R * B := by
  have himage :
      (squareRootLowPrimeOwnedResponseMatchingFrontier R K U).image encode ⊆
        squareRootLowPrimeRootSeatBox R B := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
    exact hbox n hn
  have hcard :
      ((squareRootLowPrimeOwnedResponseMatchingFrontier R K U).image encode).card =
        (squareRootLowPrimeOwnedResponseMatchingFrontier R K U).card :=
    Finset.card_image_iff.mpr hinj
  rw [← hcard, ← card_squareRootLowPrimeRootSeatBox R B]
  exact Finset.card_le_card himage

/-- **Quantitative root-seat transfer.**  Once the complete matching frontier
has an injective `R`-by-`B` encoding, the actual real deep increment is bounded
by `R*B`, with no further loss. -/
theorem abs_squareRootLowPrimeFreshIncrementReal_sum_le_root_mul_seats
    {R K j U B : ℕ} (encode : ℕ → ℕ × ℕ)
    (hR : 2 ≤ R) (hUR : U < R)
    (hinj : Set.InjOn encode
      (squareRootLowPrimeOwnedResponseMatchingFrontier R K U))
    (hbox : ∀ n ∈ squareRootLowPrimeOwnedResponseMatchingFrontier R K U,
      encode n ∈ squareRootLowPrimeRootSeatBox R B) :
    |∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
      squareRootLowPrimeFreshIncrementReal R K j p| ≤
      (R * B : ℕ) := by
  have hfrontier :=
    squareRootLowPrimeMatchingFrontier_card_le_root_mul_seats
      encode hinj hbox
  exact
    (abs_squareRootLowPrimeFreshIncrementReal_sum_le_matchingFrontierCard
      (R := R) (K := K) (j := j) (U := U) hR hUR).trans
      (by exact_mod_cast hfrontier)

end RHLean.Proof
