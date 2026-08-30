import Mathlib
import RHLean.Proof.SquareRootLowPrimeResponseSeatCarrier
import RHLean.Proof.SquareRootLowPrimeRunningTelescope
import RHLean.Proof.SquareRootLowPrimeMatchingFrontierRootCharge

/-!
# Eulerian creation-to-response energy gate

The creation-to-response map is now fixed to the repository's only genuine
lever: add one fresh prime to the cofactor while preserving the response seat.

For an owner-prime function `p(x)`,

`phi(x) = (p(x) * cofactor(x), absoluteSeat(x))`.

Freshness reverses the Möbius sign automatically.  The remaining hypotheses are
exactly the combinatorial content still required from the native `C -> R` map:

* every matched source is non-head;
* its owner is prime and fresh;
* the resulting seat belongs to the deep response carrier;
* the map is injective;
* the tagged unmatched frontiers inject into an `R`-by-`B` root-seat box.

Under these hypotheses the terminal energy has the required `R^2 * B^2`
remainder.  Specializing `B = O(sqrt K)` is the quantitative acceptance gate.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The literal creation and combined response-seat carriers reconstruct the
terminal state. -/
theorem squareRootLowPrimeRunningImbalanceReal_eq_creation_add_responseSeats
    {R K j U : ℕ} (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) :
    squareRootLowPrimeRunningImbalanceReal R K j U =
      (∑ x ∈ squareRootLowPrimeCreationCarrierExact R K j,
        squareRootLowPrimeCreationWeightReal x) +
      ∑ z ∈ squareRootLowPrimeOwnedResponseSeatCarrier R K j U,
        squareRootLowPrimeResponseSeatWeightReal z := by
  have htelescope :=
    squareRootLowPrimeRunningImbalanceReal_sub_eq_freshIncrement_sum
      (R := R) (K := K) (j := j) (U := U) hK hKU
  have hcreation :=
    squareRootLowPrimeCreationCarrierExact_realWeight_sum R K j
  have hresponse :=
    squareRootLowPrimeOwnedResponseSeatCarrier_weight_sum
      (R := R) (K := K) (j := j) (U := U) hR
  linarith

/-- **Eulerian root-seat terminal bound.** -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_root_mul_seats_euler
    {R K j U B : ℕ}
    (M : Finset SquareRootLowPrimeCreationState)
    (ownerPrime : SquareRootLowPrimeCreationState → ℕ)
    (encode : Sum SquareRootLowPrimeCreationState (ℕ × ℕ) → ℕ × ℕ)
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    (hMC : M ⊆ squareRootLowPrimeCreationCarrierExact R K j)
    (hnonhead : ∀ x ∈ M, x ≠ none)
    (hprime : ∀ x ∈ M, (ownerPrime x).Prime)
    (hfresh : ∀ x ∈ M,
      ¬ ownerPrime x ∣ squareRootLowPrimeCreationStateCofactor x)
    (hmap : ∀ x ∈ M,
      squareRootLowPrimeCreationToResponseSeat R ownerPrime x ∈
        squareRootLowPrimeOwnedResponseSeatCarrier R K j U)
    (hinj : Set.InjOn
      (squareRootLowPrimeCreationToResponseSeat R ownerPrime) M)
    (hencodeInj : Set.InjOn encode
      (creationResponseTaggedFrontier
        (squareRootLowPrimeCreationCarrierExact R K j) M
        (squareRootLowPrimeOwnedResponseSeatCarrier R K j U)
        (squareRootLowPrimeCreationToResponseSeat R ownerPrime)))
    (hbox : ∀ y ∈ creationResponseTaggedFrontier
      (squareRootLowPrimeCreationCarrierExact R K j) M
      (squareRootLowPrimeOwnedResponseSeatCarrier R K j U)
      (squareRootLowPrimeCreationToResponseSeat R ownerPrime),
      encode y ∈ squareRootLowPrimeRootSeatBox R B) :
    |squareRootLowPrimeRunningImbalanceReal R K j U| ≤
      (R * B : ℕ) := by
  rw [squareRootLowPrimeRunningImbalanceReal_eq_creation_add_responseSeats
    hR hK hKU]
  have hcancel : ∀ x ∈ M,
      squareRootLowPrimeCreationWeightReal x +
        squareRootLowPrimeResponseSeatWeightReal
          (squareRootLowPrimeCreationToResponseSeat R ownerPrime x) = 0 := by
    intro x hx
    exact squareRootLowPrimeCreationToResponseSeat_weight_cancel
      (hnonhead x hx) (hprime x hx) (hfresh x hx)
  have hbound := abs_creationResponse_realSum_le_boxCard
    (squareRootLowPrimeCreationCarrierExact R K j) M
    (squareRootLowPrimeOwnedResponseSeatCarrier R K j U)
    (squareRootLowPrimeCreationToResponseSeat R ownerPrime)
    squareRootLowPrimeCreationWeightReal
    squareRootLowPrimeResponseSeatWeightReal
    (squareRootLowPrimeRootSeatBox R B) encode
    hMC hmap hinj hcancel
    (fun x _hx => abs_squareRootLowPrimeCreationWeightReal_le_one x)
    (fun z _hz => abs_squareRootLowPrimeResponseSeatWeightReal_le_one z)
    hencodeInj hbox
  simpa [card_squareRootLowPrimeRootSeatBox] using hbound

/-- Squared terminal bound from the Eulerian map. -/
theorem squareRootLowPrimeRunningImbalanceReal_sq_le_root_sq_mul_seats_sq_euler
    {R K j U B : ℕ}
    (M : Finset SquareRootLowPrimeCreationState)
    (ownerPrime : SquareRootLowPrimeCreationState → ℕ)
    (encode : Sum SquareRootLowPrimeCreationState (ℕ × ℕ) → ℕ × ℕ)
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    (hMC : M ⊆ squareRootLowPrimeCreationCarrierExact R K j)
    (hnonhead : ∀ x ∈ M, x ≠ none)
    (hprime : ∀ x ∈ M, (ownerPrime x).Prime)
    (hfresh : ∀ x ∈ M,
      ¬ ownerPrime x ∣ squareRootLowPrimeCreationStateCofactor x)
    (hmap : ∀ x ∈ M,
      squareRootLowPrimeCreationToResponseSeat R ownerPrime x ∈
        squareRootLowPrimeOwnedResponseSeatCarrier R K j U)
    (hinj : Set.InjOn
      (squareRootLowPrimeCreationToResponseSeat R ownerPrime) M)
    (hencodeInj : Set.InjOn encode
      (creationResponseTaggedFrontier
        (squareRootLowPrimeCreationCarrierExact R K j) M
        (squareRootLowPrimeOwnedResponseSeatCarrier R K j U)
        (squareRootLowPrimeCreationToResponseSeat R ownerPrime)))
    (hbox : ∀ y ∈ creationResponseTaggedFrontier
      (squareRootLowPrimeCreationCarrierExact R K j) M
      (squareRootLowPrimeOwnedResponseSeatCarrier R K j U)
      (squareRootLowPrimeCreationToResponseSeat R ownerPrime),
      encode y ∈ squareRootLowPrimeRootSeatBox R B) :
    squareRootLowPrimeRunningImbalanceReal R K j U ^ 2 ≤
      ((R * B : ℕ) : ℝ) ^ 2 := by
  have habs :=
    abs_squareRootLowPrimeRunningImbalanceReal_le_root_mul_seats_euler
      M ownerPrime encode hR hK hKU hMC hnonhead hprime hfresh
      hmap hinj hencodeInj hbox
  have hnonneg : (0 : ℝ) ≤ (R * B : ℕ) := by positivity
  rcases abs_le.mp habs with ⟨hlow, hupp⟩
  nlinarith

/-- **Eulerian energy-decrement acceptance gate.** -/
theorem squareRootLowPrimeCreationResponse_energyDecrement_ge_euler
    {R K j U B : ℕ}
    (M : Finset SquareRootLowPrimeCreationState)
    (ownerPrime : SquareRootLowPrimeCreationState → ℕ)
    (encode : Sum SquareRootLowPrimeCreationState (ℕ × ℕ) → ℕ × ℕ)
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    (hMC : M ⊆ squareRootLowPrimeCreationCarrierExact R K j)
    (hnonhead : ∀ x ∈ M, x ≠ none)
    (hprime : ∀ x ∈ M, (ownerPrime x).Prime)
    (hfresh : ∀ x ∈ M,
      ¬ ownerPrime x ∣ squareRootLowPrimeCreationStateCofactor x)
    (hmap : ∀ x ∈ M,
      squareRootLowPrimeCreationToResponseSeat R ownerPrime x ∈
        squareRootLowPrimeOwnedResponseSeatCarrier R K j U)
    (hinj : Set.InjOn
      (squareRootLowPrimeCreationToResponseSeat R ownerPrime) M)
    (hencodeInj : Set.InjOn encode
      (creationResponseTaggedFrontier
        (squareRootLowPrimeCreationCarrierExact R K j) M
        (squareRootLowPrimeOwnedResponseSeatCarrier R K j U)
        (squareRootLowPrimeCreationToResponseSeat R ownerPrime)))
    (hbox : ∀ y ∈ creationResponseTaggedFrontier
      (squareRootLowPrimeCreationCarrierExact R K j) M
      (squareRootLowPrimeOwnedResponseSeatCarrier R K j U)
      (squareRootLowPrimeCreationToResponseSeat R ownerPrime),
      encode y ∈ squareRootLowPrimeRootSeatBox R B) :
    squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        squareRootLowPrimeRunningImbalanceReal R K j U ^ 2 ≥
      squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        ((R * B : ℕ) : ℝ) ^ 2 := by
  have hterminal :=
    squareRootLowPrimeRunningImbalanceReal_sq_le_root_sq_mul_seats_sq_euler
      M ownerPrime encode hR hK hKU hMC hnonhead hprime hfresh
      hmap hinj hencodeInj hbox
  linarith

end RHLean.Proof
