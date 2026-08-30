import Mathlib
import RHLean.Proof.CreationResponseFrontierCancellation
import RHLean.Proof.SquareRootLowPrimeRunningTelescope
import RHLean.Proof.SquareRootLowPrimeMatchingFrontierRootCharge

/-!
# Creation-to-response energy gate for low-prime dissipation

The deep response is deliberately large: it must remove the shallow excursion.
The quantitative object is therefore the sum of

* the shallow creation carrier, representing `T(K)`; and
* the signed deep response carrier, representing `-sum Delta_p`.

By the real running telescope this sum is exactly the terminal state `T(U)`.
After inserting an injective sign-reversing map from matched creation states to
response states, only the two unmatched frontiers remain.

An injective encoding of their tagged union into an `R`-by-`B` box gives

`|T(U)| <= R*B`

and therefore

`T(K)^2 - T(U)^2 >= T(K)^2 - R^2*B^2`.

Thus `B = O(sqrt K)` is precisely the required energy-decrement scale.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Real cast of an integer-valued finite mass. -/
def intMassReal {α : Type*} [DecidableEq α]
    (S : Finset α) (w : α → ℤ) : ℝ :=
  ((∑ x ∈ S, w x : ℤ) : ℝ)

/-- The shallow creation and signed response representations reconstruct the
terminal state exactly. -/
theorem squareRootLowPrimeRunningImbalanceReal_eq_creation_add_response
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {R K j U : ℕ}
    (C : Finset α) (Resp : Finset β)
    (wC : α → ℤ) (wR : β → ℤ)
    (hK : 1 ≤ K) (hKU : K ≤ U)
    (hcreation :
      squareRootLowPrimeRunningImbalanceReal R K j K =
        intMassReal C wC)
    (hresponse :
      -(∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p) =
        intMassReal Resp wR) :
    squareRootLowPrimeRunningImbalanceReal R K j U =
      intMassReal C wC + intMassReal Resp wR := by
  have htelescope :=
    squareRootLowPrimeRunningImbalanceReal_sub_eq_freshIncrement_sum
      (R := R) (K := K) (j := j) (U := U) hK hKU
  rw [hcreation] at htelescope
  linarith [hresponse]

/-- Exact terminal reconstruction on the unmatched creation/response
frontiers. -/
theorem squareRootLowPrimeRunningImbalanceReal_eq_unmatchedCreationResponse
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {R K j U : ℕ}
    (C M : Finset α) (Resp : Finset β)
    (φ : α → β) (wC : α → ℤ) (wR : β → ℤ)
    (hK : 1 ≤ K) (hKU : K ≤ U)
    (hcreation :
      squareRootLowPrimeRunningImbalanceReal R K j K =
        intMassReal C wC)
    (hresponse :
      -(∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p) =
        intMassReal Resp wR)
    (hMC : M ⊆ C)
    (hmap : ∀ c ∈ M, φ c ∈ Resp)
    (hinj : Set.InjOn φ M)
    (hcancel : ∀ c ∈ M, wC c + wR (φ c) = 0) :
    squareRootLowPrimeRunningImbalanceReal R K j U =
      intMassReal (C \ M) wC +
        intMassReal
          (Resp \ creationResponseMatchedImage M φ) wR := by
  have hterminal :=
    squareRootLowPrimeRunningImbalanceReal_eq_creation_add_response
      C Resp wC wR hK hKU hcreation hresponse
  have hcancelInt := creationResponse_sum_eq_unmatchedFrontiers
    C M Resp φ wC wR hMC hmap hinj hcancel
  calc
    squareRootLowPrimeRunningImbalanceReal R K j U =
        intMassReal C wC + intMassReal Resp wR := hterminal
    _ = intMassReal (C \ M) wC +
        intMassReal
          (Resp \ creationResponseMatchedImage M φ) wR := by
      unfold intMassReal
      exact_mod_cast hcancelInt

/-- Unit weights bound the terminal state by the total unmatched population. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_unmatchedCreationResponseCards
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {R K j U : ℕ}
    (C M : Finset α) (Resp : Finset β)
    (φ : α → β) (wC : α → ℤ) (wR : β → ℤ)
    (hK : 1 ≤ K) (hKU : K ≤ U)
    (hcreation :
      squareRootLowPrimeRunningImbalanceReal R K j K =
        intMassReal C wC)
    (hresponse :
      -(∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p) =
        intMassReal Resp wR)
    (hMC : M ⊆ C)
    (hmap : ∀ c ∈ M, φ c ∈ Resp)
    (hinj : Set.InjOn φ M)
    (hcancel : ∀ c ∈ M, wC c + wR (φ c) = 0)
    (hCunit : ∀ c ∈ C, |wC c| ≤ 1)
    (hRunit : ∀ r ∈ Resp, |wR r| ≤ 1) :
    |squareRootLowPrimeRunningImbalanceReal R K j U| ≤
      (((C \ M).card +
        (Resp \ creationResponseMatchedImage M φ).card : ℕ) : ℝ) := by
  have hterminal :=
    squareRootLowPrimeRunningImbalanceReal_eq_creation_add_response
      C Resp wC wR hK hKU hcreation hresponse
  have hbound := abs_creationResponse_sum_le_unmatchedCards
    C M Resp φ wC wR hMC hmap hinj hcancel hCunit hRunit
  unfold intMassReal at hterminal
  rw [hterminal]
  exact_mod_cast hbound

/-- **Root-seat quantitative gate.**  If the tagged unmatched frontier injects
into the repository's root-seat box, the terminal state is bounded by `R*B`. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_root_mul_seats_of_creationResponse
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {R K j U B : ℕ}
    (C M : Finset α) (Resp : Finset β)
    (φ : α → β) (wC : α → ℤ) (wR : β → ℤ)
    (encode : Sum α β → ℕ × ℕ)
    (hK : 1 ≤ K) (hKU : K ≤ U)
    (hcreation :
      squareRootLowPrimeRunningImbalanceReal R K j K =
        intMassReal C wC)
    (hresponse :
      -(∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p) =
        intMassReal Resp wR)
    (hMC : M ⊆ C)
    (hmap : ∀ c ∈ M, φ c ∈ Resp)
    (hinj : Set.InjOn φ M)
    (hcancel : ∀ c ∈ M, wC c + wR (φ c) = 0)
    (hCunit : ∀ c ∈ C, |wC c| ≤ 1)
    (hRunit : ∀ r ∈ Resp, |wR r| ≤ 1)
    (hencodeInj : Set.InjOn encode
      (creationResponseTaggedFrontier C M Resp φ))
    (hbox : ∀ z ∈ creationResponseTaggedFrontier C M Resp φ,
      encode z ∈ squareRootLowPrimeRootSeatBox R B) :
    |squareRootLowPrimeRunningImbalanceReal R K j U| ≤
      (R * B : ℕ) := by
  have hterminal :=
    squareRootLowPrimeRunningImbalanceReal_eq_creation_add_response
      C Resp wC wR hK hKU hcreation hresponse
  have hbound := abs_creationResponse_sum_le_boxCard
    C M Resp φ wC wR
      (squareRootLowPrimeRootSeatBox R B) encode
      hMC hmap hinj hcancel hCunit hRunit hencodeInj hbox
  unfold intMassReal at hterminal
  rw [hterminal]
  rw [card_squareRootLowPrimeRootSeatBox] at hbound
  exact_mod_cast hbound

/-- Squared terminal bound supplied by the root-seat creation/response map. -/
theorem squareRootLowPrimeRunningImbalanceReal_sq_le_root_sq_mul_seats_sq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {R K j U B : ℕ}
    (C M : Finset α) (Resp : Finset β)
    (φ : α → β) (wC : α → ℤ) (wR : β → ℤ)
    (encode : Sum α β → ℕ × ℕ)
    (hK : 1 ≤ K) (hKU : K ≤ U)
    (hcreation :
      squareRootLowPrimeRunningImbalanceReal R K j K =
        intMassReal C wC)
    (hresponse :
      -(∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p) =
        intMassReal Resp wR)
    (hMC : M ⊆ C)
    (hmap : ∀ c ∈ M, φ c ∈ Resp)
    (hinj : Set.InjOn φ M)
    (hcancel : ∀ c ∈ M, wC c + wR (φ c) = 0)
    (hCunit : ∀ c ∈ C, |wC c| ≤ 1)
    (hRunit : ∀ r ∈ Resp, |wR r| ≤ 1)
    (hencodeInj : Set.InjOn encode
      (creationResponseTaggedFrontier C M Resp φ))
    (hbox : ∀ z ∈ creationResponseTaggedFrontier C M Resp φ,
      encode z ∈ squareRootLowPrimeRootSeatBox R B) :
    squareRootLowPrimeRunningImbalanceReal R K j U ^ 2 ≤
      ((R * B : ℕ) : ℝ) ^ 2 := by
  have habs :=
    abs_squareRootLowPrimeRunningImbalanceReal_le_root_mul_seats_of_creationResponse
      C M Resp φ wC wR encode hK hKU hcreation hresponse
      hMC hmap hinj hcancel hCunit hRunit hencodeInj hbox
  have hnonneg : (0 : ℝ) ≤ (R * B : ℕ) := by positivity
  rcases abs_le.mp habs with ⟨hlow, hupp⟩
  nlinarith

/-- **Energy-decrement acceptance gate.** -/
theorem squareRootLowPrimeCreationResponse_energyDecrement_ge
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {R K j U B : ℕ}
    (C M : Finset α) (Resp : Finset β)
    (φ : α → β) (wC : α → ℤ) (wR : β → ℤ)
    (encode : Sum α β → ℕ × ℕ)
    (hK : 1 ≤ K) (hKU : K ≤ U)
    (hcreation :
      squareRootLowPrimeRunningImbalanceReal R K j K =
        intMassReal C wC)
    (hresponse :
      -(∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p) =
        intMassReal Resp wR)
    (hMC : M ⊆ C)
    (hmap : ∀ c ∈ M, φ c ∈ Resp)
    (hinj : Set.InjOn φ M)
    (hcancel : ∀ c ∈ M, wC c + wR (φ c) = 0)
    (hCunit : ∀ c ∈ C, |wC c| ≤ 1)
    (hRunit : ∀ r ∈ Resp, |wR r| ≤ 1)
    (hencodeInj : Set.InjOn encode
      (creationResponseTaggedFrontier C M Resp φ))
    (hbox : ∀ z ∈ creationResponseTaggedFrontier C M Resp φ,
      encode z ∈ squareRootLowPrimeRootSeatBox R B) :
    squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        squareRootLowPrimeRunningImbalanceReal R K j U ^ 2 ≥
      squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        ((R * B : ℕ) : ℝ) ^ 2 := by
  have hterminal :=
    squareRootLowPrimeRunningImbalanceReal_sq_le_root_sq_mul_seats_sq
      C M Resp φ wC wR encode hK hKU hcreation hresponse
      hMC hmap hinj hcancel hCunit hRunit hencodeInj hbox
  linarith

end RHLean.Proof
