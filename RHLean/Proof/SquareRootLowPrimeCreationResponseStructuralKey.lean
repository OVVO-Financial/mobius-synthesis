import Mathlib
import RHLean.Proof.SquareRootLowPrimeProcessedCreationResponseInvolution

/-!
# Common structural key for both processed-carrier Othello matchings

The creation-response mate and the descending processed-prime mate are built
from the same elementary operation: add or remove one fresh prime strictly above
`K` while preserving the absolute seat.  Consequently both preserve the same
canonical key

`(gcd(cofactor,K!), absoluteSeat)`.

This file proves the creation-response half.  Together with
`squareRootLowPrimeProcessedSeatNoLibertyMate_structuralKey`, every alternating
component of the two carrier-wide Othello involutions lies in one structural
key fibre.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Structural key expressed in the tagged head/creation/response coordinates. -/
def squareRootLowPrimeProcessedCreationResponseTaggedStructuralKey
    (R K : ℕ) :
    SquareRootLowPrimeProcessedCreationResponseState → ℕ × ℕ
  | .inl _ => (squareRootLowPrimeShallowBase K 1, 0)
  | .inr (.inl c) =>
      (squareRootLowPrimeShallowBase K
          (squareRootLowPrimeCreationStateCofactor c),
        squareRootLowPrimeCreationStateAbsoluteSeat R c)
  | .inr (.inr z) =>
      (squareRootLowPrimeShallowBase K z.1, z.2)

/-- One matched creation edge preserves the tagged structural key. -/
theorem squareRootLowPrimeCanonicalCreationToResponse_structuralKey
    {R K j U : ℕ} {c : SquareRootLowPrimeCreationState}
    (hc : c ∈ squareRootLowPrimeMatchedCreationStates R K j U) :
    squareRootLowPrimeProcessedCreationResponseTaggedStructuralKey R K
        (.inr (.inr
          (squareRootLowPrimeCanonicalCreationToResponse R K j U c))) =
      squareRootLowPrimeProcessedCreationResponseTaggedStructuralKey R K
        (.inr (.inl c)) := by
  have hpData := squareRootLowPrimeCanonicalResponseOwner_data hc
  unfold squareRootLowPrimeProcessedCreationResponseTaggedStructuralKey
    squareRootLowPrimeCanonicalCreationToResponse
    squareRootLowPrimeCreationToResponseSeat
  dsimp
  rw [squareRootLowPrimeShallowBase_mul_fresh_prime hpData.2.2 hpData.1]

/-- The tagged creation-response Othello mate preserves the common structural
key, in both the creation-to-response and response-to-creation directions. -/
theorem squareRootLowPrimeProcessedCreationResponseTaggedMate_structuralKey
    (R K j U : ℕ)
    (y : SquareRootLowPrimeProcessedCreationResponseState) :
    squareRootLowPrimeProcessedCreationResponseTaggedStructuralKey R K
        (squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U y) =
      squareRootLowPrimeProcessedCreationResponseTaggedStructuralKey R K y := by
  rcases y with u | y
  · rfl
  · rcases y with c | z
    · by_cases hc : c ∈ squareRootLowPrimeMatchedCreationStates R K j U
      · simp only [squareRootLowPrimeProcessedCreationResponseTaggedMate,
          creationResponseOthelloMate, hc, if_true]
        exact squareRootLowPrimeCanonicalCreationToResponse_structuralKey hc
      · simp [squareRootLowPrimeProcessedCreationResponseTaggedMate,
          creationResponseOthelloMate, hc]
    · by_cases hpre :
        ∃ c ∈ squareRootLowPrimeMatchedCreationStates R K j U,
          squareRootLowPrimeCanonicalCreationToResponse R K j U c = z
      · -- `simp` cannot be used to select this branch: it rewrites membership in
        -- `squareRootLowPrimeMatchedCreationStates` inside the `dite` condition,
        -- after which `hpre` no longer matches it.  Select the branch with
        -- `dif_pos` directly.
        have hmate :
            squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U
                (Sum.inr (Sum.inr z)) =
              Sum.inr (Sum.inl (creationResponseOthelloPreimage
                (squareRootLowPrimeMatchedCreationStates R K j U)
                (squareRootLowPrimeCanonicalCreationToResponse R K j U)
                z hpre)) := by
          dsimp only [squareRootLowPrimeProcessedCreationResponseTaggedMate,
            creationResponseOthelloMate]
          rw [dif_pos hpre]
        have hc :
            creationResponseOthelloPreimage
                (squareRootLowPrimeMatchedCreationStates R K j U)
                (squareRootLowPrimeCanonicalCreationToResponse R K j U) z hpre ∈
              squareRootLowPrimeMatchedCreationStates R K j U ∧
              squareRootLowPrimeCanonicalCreationToResponse R K j U
                (creationResponseOthelloPreimage
                  (squareRootLowPrimeMatchedCreationStates R K j U)
                  (squareRootLowPrimeCanonicalCreationToResponse R K j U)
                  z hpre) = z := by
          dsimp only [creationResponseOthelloPreimage]
          exact Classical.choose_spec hpre
        have hkey := squareRootLowPrimeCanonicalCreationToResponse_structuralKey
          hc.1
        rw [hc.2] at hkey
        rw [hmate]
        exact hkey.symm
      · have hmate :
            squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U
                (Sum.inr (Sum.inr z)) = Sum.inr (Sum.inr z) := by
          dsimp only [squareRootLowPrimeProcessedCreationResponseTaggedMate,
            creationResponseOthelloMate]
          rw [dif_neg hpre]
        rw [hmate]

/-- Encoding the exact processed carrier does not change the common structural
key. -/
theorem squareRootLowPrimeProcessedCreationResponseEncode_structuralKey
    {R K j U : ℕ} (_hR : 1 ≤ R) (_hK : 1 ≤ K) (_hKU : K ≤ U)
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedCreationResponseTaggedStructuralKey R K
        (squareRootLowPrimeProcessedCreationResponseEncode R K x) =
      squareRootLowPrimeProcessedSeatStructuralKey K x := by
  rcases x with _ | z
  · rfl
  · have hzAtom : z ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
      simpa [squareRootLowPrimeProcessedSeatCarrier] using hx
    by_cases hshallow : canonicalLargestPrimeFactor z.1 ≤ K
    · have hzShallow :
          z ∈ squareRootLowPrimeProcessedShallowSeatAtoms R K j U :=
        mem_squareRootLowPrimeProcessedShallowSeatAtoms.mpr
          ⟨hzAtom, hshallow⟩
      rcases z with ⟨c, s⟩
      by_cases hsBorn : s < squareRootBornPartnerCount R c
      · simp [squareRootLowPrimeProcessedCreationResponseEncode, hshallow,
          squareRootLowPrimeProcessedCreationResponseTaggedStructuralKey,
          squareRootLowPrimeProcessedShallowSeatToCreation, hsBorn,
          squareRootLowPrimeCreationStateCofactor,
          squareRootLowPrimeCreationStateAbsoluteSeat,
          squareRootLowPrimeProcessedSeatStructuralKey,
          squareRootLowPrimeProcessedStateCofactor,
          squareRootLowPrimeProcessedSeatIndex]
      · have hsCombined :=
          (mem_squareRootLowPrimeProcessedSeatAtoms.mp hzAtom).2
        simp [squareRootLowPrimeProcessedCreationResponseEncode, hshallow,
          squareRootLowPrimeProcessedCreationResponseTaggedStructuralKey,
          squareRootLowPrimeProcessedShallowSeatToCreation, hsBorn,
          squareRootLowPrimeCreationStateCofactor,
          squareRootLowPrimeCreationStateAbsoluteSeat,
          squareRootLowPrimeProcessedSeatStructuralKey,
          squareRootLowPrimeProcessedStateCofactor,
          squareRootLowPrimeProcessedSeatIndex]
        omega
    · simp [squareRootLowPrimeProcessedCreationResponseEncode, hshallow,
        squareRootLowPrimeProcessedCreationResponseTaggedStructuralKey,
        squareRootLowPrimeProcessedSeatStructuralKey,
        squareRootLowPrimeProcessedStateCofactor,
        squareRootLowPrimeProcessedSeatIndex]

/-- **Common-key theorem for the first carrier-wide Othello mate.** -/
theorem squareRootLowPrimeProcessedSeatCreationResponseMate_structuralKey
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedSeatStructuralKey K
        (squareRootLowPrimeProcessedSeatCreationResponseMate R K j U x) =
      squareRootLowPrimeProcessedSeatStructuralKey K x := by
  let y := squareRootLowPrimeProcessedCreationResponseEncode R K x
  let z := squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U y
  have hy : y ∈ squareRootLowPrimeProcessedCreationResponseTaggedCarrier R K j U :=
    squareRootLowPrimeProcessedCreationResponseEncode_mem hR hK hKU hx
  have hz : z ∈ squareRootLowPrimeProcessedCreationResponseTaggedCarrier R K j U :=
    squareRootLowPrimeProcessedCreationResponseTaggedMate_mem hy
  have hxMate :
      squareRootLowPrimeProcessedSeatCreationResponseMate R K j U x ∈
        squareRootLowPrimeProcessedSeatCarrier R K j U :=
    squareRootLowPrimeProcessedSeatCreationResponseMate_mem hR hK hKU hx
  have hencMate :
      squareRootLowPrimeProcessedCreationResponseEncode R K
          (squareRootLowPrimeProcessedSeatCreationResponseMate R K j U x) = z := by
    change squareRootLowPrimeProcessedCreationResponseEncode R K
      (squareRootLowPrimeProcessedCreationResponseDecode R z) = z
    exact squareRootLowPrimeProcessedCreationResponseEncode_decode hR hK hKU hz
  have hleft := squareRootLowPrimeProcessedCreationResponseEncode_structuralKey
    hR hK hKU hxMate
  rw [hencMate] at hleft
  have hright := squareRootLowPrimeProcessedCreationResponseEncode_structuralKey
    hR hK hKU hx
  have htag :=
    squareRootLowPrimeProcessedCreationResponseTaggedMate_structuralKey
      R K j U y
  change squareRootLowPrimeProcessedCreationResponseTaggedStructuralKey R K z =
    squareRootLowPrimeProcessedCreationResponseTaggedStructuralKey R K y at htag
  exact hleft.symm.trans (htag.trans hright)

end RHLean.Proof
