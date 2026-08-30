import Mathlib
import RHLean.Proof.SquareRootLowPrimeMatchedFrontierBound
import RHLean.Proof.SquareRootLowPrimeMatchingFrontierRootCharge
import RHLean.Proof.SquareRootLowPrimeRoughBaseResidual

/-!
# Quantitative transfer from rough-base residuals

The complete signed child mass is now compressed to nonzero residuals on the
rough-base coordinate.  This file transfers that compression to the actual real
fresh-prime increment and packages the final root-seat counting theorem.

If every nonzero rough-base residual has magnitude at most one and those bases
inject into an `R`-by-`B` root-seat box, then

`|sum_{K<p<=U} Delta_p| <= R*B`.

For `B` of order `sqrt(K)`, this is the desired quantitative scale.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Unit rough-base residuals bound the actual real deep increment by the number
of nonzero rough bases. -/
theorem abs_squareRootLowPrimeFreshIncrementReal_sum_le_nonzeroRoughBaseCard
    {R K j U : ℕ} (hR : 2 ≤ R) (hUR : U < R)
    (hunit : ∀ b ∈ squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U,
      |squareRootLowPrimeOwnedResponseRoughBaseResidual R K U b| ≤ 1) :
    |∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
      squareRootLowPrimeFreshIncrementReal R K j p| ≤
      ((squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U).card : ℝ) := by
  rw [squareRootLowPrimeFreshIncrementReal_sum_eq_neg_ownedResponseChildrenMass
    hR hUR, abs_neg,
    squareRootLowPrimeOwnedResponseChildren_realWeightSum_eq_intCast]
  exact_mod_cast
    abs_squareRootLowPrimeOwnedResponseChildren_moebiusSum_le_nonzeroRoughBaseCard
      R K U hunit

/-- An injective root-seat encoding of nonzero rough bases bounds their
population by `R*B`. -/
theorem squareRootLowPrimeNonzeroRoughBases_card_le_root_mul_seats
    {R K U B : ℕ} (encode : ℕ → ℕ × ℕ)
    (hinj : Set.InjOn encode
      (squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U))
    (hbox : ∀ b ∈ squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U,
      encode b ∈ squareRootLowPrimeRootSeatBox R B) :
    (squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U).card ≤ R * B := by
  have himage :
      (squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U).image encode ⊆
        squareRootLowPrimeRootSeatBox R B := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨b, hb, rfl⟩
    exact hbox b hb
  have hcard :
      ((squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U).image encode).card =
        (squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U).card :=
    Finset.card_image_iff.mpr hinj
  rw [← hcard, ← card_squareRootLowPrimeRootSeatBox R B]
  exact Finset.card_le_card himage

/-- **Rough-base quantitative gate.** -/
theorem abs_squareRootLowPrimeFreshIncrementReal_sum_le_root_mul_seats_of_roughBase
    {R K j U B : ℕ} (encode : ℕ → ℕ × ℕ)
    (hR : 2 ≤ R) (hUR : U < R)
    (hunit : ∀ b ∈ squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U,
      |squareRootLowPrimeOwnedResponseRoughBaseResidual R K U b| ≤ 1)
    (hinj : Set.InjOn encode
      (squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U))
    (hbox : ∀ b ∈ squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U,
      encode b ∈ squareRootLowPrimeRootSeatBox R B) :
    |∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
      squareRootLowPrimeFreshIncrementReal R K j p| ≤
      (R * B : ℕ) := by
  have hmass :=
    abs_squareRootLowPrimeFreshIncrementReal_sum_le_nonzeroRoughBaseCard
      (R := R) (K := K) (j := j) (U := U) hR hUR hunit
  have hcard := squareRootLowPrimeNonzeroRoughBases_card_le_root_mul_seats
    encode hinj hbox
  exact hmass.trans (by exact_mod_cast hcard)

end RHLean.Proof
