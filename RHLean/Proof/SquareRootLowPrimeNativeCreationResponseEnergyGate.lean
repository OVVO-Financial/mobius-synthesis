import Mathlib
import RHLean.Proof.SquareRootLowPrimeChannelCreationCarrier
import RHLean.Proof.SquareRootLowPrimeRunningTelescope
import RHLean.Proof.SquareRootLowPrimeMatchingFrontierRootCharge

/-!
# Native creation-to-response energy gate

The source and target masses are now discharged by the literal repository
carriers:

* `squareRootLowPrimeCreationCarrierExact R K j` has mass `T(K)`;
* `squareRootLowPrimeOwnedResponseAtoms R K U` has mass
  `-sum_{K<p<=U} Delta_p`.

The running telescope therefore identifies their total mass with `T(U)`.
This module specializes the abstract creation-to-response cancellation theorem
so that the only remaining inputs are the actual map, its matched domain, and a
root-seat encoding of the two unmatched complements.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The native creation and response carriers reconstruct the terminal real
state exactly. -/
theorem squareRootLowPrimeRunningImbalanceReal_eq_nativeCreation_add_response
    {R K j U : ℕ} (hR : 2 ≤ R) (hK : 1 ≤ K)
    (hKU : K ≤ U) (hUR : U < R) :
    squareRootLowPrimeRunningImbalanceReal R K j U =
      (∑ x ∈ squareRootLowPrimeCreationCarrierExact R K j,
        squareRootLowPrimeCreationWeightReal x) +
      ∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
        squareRootLowPrimeResponseAtomWeightReal z := by
  have htelescope :=
    squareRootLowPrimeRunningImbalanceReal_sub_eq_freshIncrement_sum
      (R := R) (K := K) (j := j) (U := U) hK hKU
  have hcreation :=
    squareRootLowPrimeCreationCarrierExact_realWeight_sum R K j
  have hresponse :=
    squareRootLowPrimeOwnedResponseAtoms_realWeight_sum
      (R := R) (K := K) (j := j) (U := U) hR hUR
  linarith

/-- Exact native terminal state on the two unmatched frontiers produced by a
creation-to-response map. -/
theorem squareRootLowPrimeRunningImbalanceReal_eq_nativeUnmatchedFrontiers
    {R K j U : ℕ}
    (M : Finset SquareRootLowPrimeCreationState)
    (φ : SquareRootLowPrimeCreationState → ℕ × ℕ)
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) (hUR : U < R)
    (hMC : M ⊆ squareRootLowPrimeCreationCarrierExact R K j)
    (hmap : ∀ x ∈ M, φ x ∈ squareRootLowPrimeOwnedResponseAtoms R K U)
    (hinj : Set.InjOn φ M)
    (hcancel : ∀ x ∈ M,
      squareRootLowPrimeCreationWeightReal x +
        squareRootLowPrimeResponseAtomWeightReal (φ x) = 0) :
    squareRootLowPrimeRunningImbalanceReal R K j U =
      (∑ x ∈ squareRootLowPrimeCreationCarrierExact R K j \ M,
        squareRootLowPrimeCreationWeightReal x) +
      ∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U \
          creationResponseMatchedImage M φ,
        squareRootLowPrimeResponseAtomWeightReal z := by
  rw [squareRootLowPrimeRunningImbalanceReal_eq_nativeCreation_add_response
    hR hK hKU hUR]
  exact creationResponse_sum_eq_unmatchedFrontiers
    (squareRootLowPrimeCreationCarrierExact R K j) M
    (squareRootLowPrimeOwnedResponseAtoms R K U)
    φ squareRootLowPrimeCreationWeightReal
    squareRootLowPrimeResponseAtomWeightReal
    hMC hmap hinj hcancel

/-- The native terminal state is bounded by the two unmatched populations. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_nativeUnmatchedCards
    {R K j U : ℕ}
    (M : Finset SquareRootLowPrimeCreationState)
    (φ : SquareRootLowPrimeCreationState → ℕ × ℕ)
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) (hUR : U < R)
    (hMC : M ⊆ squareRootLowPrimeCreationCarrierExact R K j)
    (hmap : ∀ x ∈ M, φ x ∈ squareRootLowPrimeOwnedResponseAtoms R K U)
    (hinj : Set.InjOn φ M)
    (hcancel : ∀ x ∈ M,
      squareRootLowPrimeCreationWeightReal x +
        squareRootLowPrimeResponseAtomWeightReal (φ x) = 0) :
    |squareRootLowPrimeRunningImbalanceReal R K j U| ≤
      (((squareRootLowPrimeCreationCarrierExact R K j \ M).card +
        (squareRootLowPrimeOwnedResponseAtoms R K U \
          creationResponseMatchedImage M φ).card : ℕ) : ℝ) := by
  rw [squareRootLowPrimeRunningImbalanceReal_eq_nativeCreation_add_response
    hR hK hKU hUR]
  exact abs_creationResponse_realSum_le_unmatchedCards
    (squareRootLowPrimeCreationCarrierExact R K j) M
    (squareRootLowPrimeOwnedResponseAtoms R K U)
    φ squareRootLowPrimeCreationWeightReal
    squareRootLowPrimeResponseAtomWeightReal
    hMC hmap hinj hcancel
    (fun x _hx => abs_squareRootLowPrimeCreationWeightReal_le_one x)
    (fun z _hz => abs_squareRootLowPrimeResponseAtomWeightReal_le_one z)

/-- **Native root-seat terminal bound.** -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_root_mul_seats_native
    {R K j U B : ℕ}
    (M : Finset SquareRootLowPrimeCreationState)
    (φ : SquareRootLowPrimeCreationState → ℕ × ℕ)
    (encode : Sum SquareRootLowPrimeCreationState (ℕ × ℕ) → ℕ × ℕ)
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) (hUR : U < R)
    (hMC : M ⊆ squareRootLowPrimeCreationCarrierExact R K j)
    (hmap : ∀ x ∈ M, φ x ∈ squareRootLowPrimeOwnedResponseAtoms R K U)
    (hinj : Set.InjOn φ M)
    (hcancel : ∀ x ∈ M,
      squareRootLowPrimeCreationWeightReal x +
        squareRootLowPrimeResponseAtomWeightReal (φ x) = 0)
    (hencodeInj : Set.InjOn encode
      (creationResponseTaggedFrontier
        (squareRootLowPrimeCreationCarrierExact R K j) M
        (squareRootLowPrimeOwnedResponseAtoms R K U) φ))
    (hbox : ∀ y ∈ creationResponseTaggedFrontier
      (squareRootLowPrimeCreationCarrierExact R K j) M
      (squareRootLowPrimeOwnedResponseAtoms R K U) φ,
      encode y ∈ squareRootLowPrimeRootSeatBox R B) :
    |squareRootLowPrimeRunningImbalanceReal R K j U| ≤
      (R * B : ℕ) := by
  rw [squareRootLowPrimeRunningImbalanceReal_eq_nativeCreation_add_response
    hR hK hKU hUR]
  have hbound := abs_creationResponse_realSum_le_boxCard
    (squareRootLowPrimeCreationCarrierExact R K j) M
    (squareRootLowPrimeOwnedResponseAtoms R K U)
    φ squareRootLowPrimeCreationWeightReal
    squareRootLowPrimeResponseAtomWeightReal
    (squareRootLowPrimeRootSeatBox R B) encode
    hMC hmap hinj hcancel
    (fun x _hx => abs_squareRootLowPrimeCreationWeightReal_le_one x)
    (fun z _hz => abs_squareRootLowPrimeResponseAtomWeightReal_le_one z)
    hencodeInj hbox
  simpa [card_squareRootLowPrimeRootSeatBox] using hbound

/-- Native squared terminal estimate. -/
theorem squareRootLowPrimeRunningImbalanceReal_sq_le_root_sq_mul_seats_sq_native
    {R K j U B : ℕ}
    (M : Finset SquareRootLowPrimeCreationState)
    (φ : SquareRootLowPrimeCreationState → ℕ × ℕ)
    (encode : Sum SquareRootLowPrimeCreationState (ℕ × ℕ) → ℕ × ℕ)
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) (hUR : U < R)
    (hMC : M ⊆ squareRootLowPrimeCreationCarrierExact R K j)
    (hmap : ∀ x ∈ M, φ x ∈ squareRootLowPrimeOwnedResponseAtoms R K U)
    (hinj : Set.InjOn φ M)
    (hcancel : ∀ x ∈ M,
      squareRootLowPrimeCreationWeightReal x +
        squareRootLowPrimeResponseAtomWeightReal (φ x) = 0)
    (hencodeInj : Set.InjOn encode
      (creationResponseTaggedFrontier
        (squareRootLowPrimeCreationCarrierExact R K j) M
        (squareRootLowPrimeOwnedResponseAtoms R K U) φ))
    (hbox : ∀ y ∈ creationResponseTaggedFrontier
      (squareRootLowPrimeCreationCarrierExact R K j) M
      (squareRootLowPrimeOwnedResponseAtoms R K U) φ,
      encode y ∈ squareRootLowPrimeRootSeatBox R B) :
    squareRootLowPrimeRunningImbalanceReal R K j U ^ 2 ≤
      ((R * B : ℕ) : ℝ) ^ 2 := by
  have habs := abs_squareRootLowPrimeRunningImbalanceReal_le_root_mul_seats_native
    M φ encode hR hK hKU hUR hMC hmap hinj hcancel hencodeInj hbox
  have hnonneg : (0 : ℝ) ≤ (R * B : ℕ) := by positivity
  rcases abs_le.mp habs with ⟨hlow, hupp⟩
  nlinarith

/-- **Native creation-response energy decrement.** -/
theorem squareRootLowPrimeCreationResponse_energyDecrement_ge_native
    {R K j U B : ℕ}
    (M : Finset SquareRootLowPrimeCreationState)
    (φ : SquareRootLowPrimeCreationState → ℕ × ℕ)
    (encode : Sum SquareRootLowPrimeCreationState (ℕ × ℕ) → ℕ × ℕ)
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) (hUR : U < R)
    (hMC : M ⊆ squareRootLowPrimeCreationCarrierExact R K j)
    (hmap : ∀ x ∈ M, φ x ∈ squareRootLowPrimeOwnedResponseAtoms R K U)
    (hinj : Set.InjOn φ M)
    (hcancel : ∀ x ∈ M,
      squareRootLowPrimeCreationWeightReal x +
        squareRootLowPrimeResponseAtomWeightReal (φ x) = 0)
    (hencodeInj : Set.InjOn encode
      (creationResponseTaggedFrontier
        (squareRootLowPrimeCreationCarrierExact R K j) M
        (squareRootLowPrimeOwnedResponseAtoms R K U) φ))
    (hbox : ∀ y ∈ creationResponseTaggedFrontier
      (squareRootLowPrimeCreationCarrierExact R K j) M
      (squareRootLowPrimeOwnedResponseAtoms R K U) φ,
      encode y ∈ squareRootLowPrimeRootSeatBox R B) :
    squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        squareRootLowPrimeRunningImbalanceReal R K j U ^ 2 ≥
      squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        ((R * B : ℕ) : ℝ) ^ 2 := by
  have hterminal :=
    squareRootLowPrimeRunningImbalanceReal_sq_le_root_sq_mul_seats_sq_native
      M φ encode hR hK hKU hUR hMC hmap hinj hcancel hencodeInj hbox
  linarith

end RHLean.Proof
