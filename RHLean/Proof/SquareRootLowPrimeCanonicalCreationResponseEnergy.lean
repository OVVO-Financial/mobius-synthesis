import Mathlib
import RHLean.Proof.SquareRootLowPrimeCanonicalCreationResponseMap

/-!
# Canonical creation-response energy reduction

The canonical map now discharges every qualitative hypothesis of the Eulerian
energy gate.  The matched domain is the full set of non-head shallow creation
states admitting at least one fresh-prime extension into the deep response
carrier; the least eligible prime owns each state.

Consequently the final quantitative theorem requires only an injective encoding
of the tagged unmatched creation and response frontiers into an `R`-by-`B`
box.  For `B = O(sqrt K)`, the desired `O(R^2 K)` terminal energy bound follows
immediately.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Tagged unmatched frontier for the canonical creation-to-response map. -/
def squareRootLowPrimeCanonicalCreationResponseFrontier
    (R K j U : ℕ) :
    Finset (Sum SquareRootLowPrimeCreationState (ℕ × ℕ)) :=
  creationResponseTaggedFrontier
    (squareRootLowPrimeCreationCarrierExact R K j)
    (squareRootLowPrimeMatchedCreationStates R K j U)
    (squareRootLowPrimeOwnedResponseSeatCarrier R K j U)
    (squareRootLowPrimeCanonicalCreationToResponse R K j U)

/-- **Canonical terminal bound from one unmatched-frontier owner map.** -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_root_mul_seats_canonical
    {R K j U B : ℕ}
    (encode : Sum SquareRootLowPrimeCreationState (ℕ × ℕ) → ℕ × ℕ)
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    (hencodeInj : Set.InjOn encode
      (squareRootLowPrimeCanonicalCreationResponseFrontier R K j U))
    (hbox : ∀ y ∈ squareRootLowPrimeCanonicalCreationResponseFrontier R K j U,
      encode y ∈ squareRootLowPrimeRootSeatBox R B) :
    |squareRootLowPrimeRunningImbalanceReal R K j U| ≤
      (R * B : ℕ) := by
  apply abs_squareRootLowPrimeRunningImbalanceReal_le_root_mul_seats_euler
    (squareRootLowPrimeMatchedCreationStates R K j U)
    (squareRootLowPrimeCanonicalResponseOwner R K j U)
    encode hR hK hKU
  · intro x hx
    exact (mem_squareRootLowPrimeMatchedCreationStates.mp hx).1
  · intro x hx
    exact (mem_squareRootLowPrimeMatchedCreationStates.mp hx).2.1
  · intro x hx
    exact (squareRootLowPrimeCanonicalResponseOwner_data hx).2.2
  · intro x hx
    exact squareRootLowPrimeCanonicalResponseOwner_fresh hx
  · intro x hx
    exact squareRootLowPrimeCanonicalCreationToResponse_mem hx
  · exact squareRootLowPrimeCanonicalCreationToResponse_injOn
  · simpa [squareRootLowPrimeCanonicalCreationResponseFrontier,
      squareRootLowPrimeCanonicalCreationToResponse] using hencodeInj
  · simpa [squareRootLowPrimeCanonicalCreationResponseFrontier,
      squareRootLowPrimeCanonicalCreationToResponse] using hbox

/-- Canonical squared terminal estimate. -/
theorem squareRootLowPrimeRunningImbalanceReal_sq_le_root_sq_mul_seats_sq_canonical
    {R K j U B : ℕ}
    (encode : Sum SquareRootLowPrimeCreationState (ℕ × ℕ) → ℕ × ℕ)
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    (hencodeInj : Set.InjOn encode
      (squareRootLowPrimeCanonicalCreationResponseFrontier R K j U))
    (hbox : ∀ y ∈ squareRootLowPrimeCanonicalCreationResponseFrontier R K j U,
      encode y ∈ squareRootLowPrimeRootSeatBox R B) :
    squareRootLowPrimeRunningImbalanceReal R K j U ^ 2 ≤
      ((R * B : ℕ) : ℝ) ^ 2 := by
  have habs :=
    abs_squareRootLowPrimeRunningImbalanceReal_le_root_mul_seats_canonical
      encode hR hK hKU hencodeInj hbox
  have hnonneg : (0 : ℝ) ≤ (R * B : ℕ) := by positivity
  rcases abs_le.mp habs with ⟨hlow, hupp⟩
  nlinarith

/-- **Canonical energy-decrement acceptance gate.** -/
theorem squareRootLowPrimeCreationResponse_energyDecrement_ge_canonical
    {R K j U B : ℕ}
    (encode : Sum SquareRootLowPrimeCreationState (ℕ × ℕ) → ℕ × ℕ)
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    (hencodeInj : Set.InjOn encode
      (squareRootLowPrimeCanonicalCreationResponseFrontier R K j U))
    (hbox : ∀ y ∈ squareRootLowPrimeCanonicalCreationResponseFrontier R K j U,
      encode y ∈ squareRootLowPrimeRootSeatBox R B) :
    squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        squareRootLowPrimeRunningImbalanceReal R K j U ^ 2 ≥
      squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        ((R * B : ℕ) : ℝ) ^ 2 := by
  have hterminal :=
    squareRootLowPrimeRunningImbalanceReal_sq_le_root_sq_mul_seats_sq_canonical
      encode hR hK hKU hencodeInj hbox
  linarith

end RHLean.Proof
