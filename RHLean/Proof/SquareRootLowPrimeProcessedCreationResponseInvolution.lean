import Mathlib
import RHLean.Proof.CreationResponseOthelloInvolution
import RHLean.Proof.SquareRootLowPrimeShallowProcessedCreationEquiv
import RHLean.Proof.SquareRootLowPrimeDeepProcessedSeatBridge

/-!
# Creation-response Othello involution on the exact processed-seat carrier

The processed carrier is already the common arithmetic universe needed by the
final alternating classifier.  Its non-head states split canonically into:

* shallow seats, which are literally the tagged creation carrier; and
* deep seats, which are literally the owned response-seat carrier.

Using those two proved coordinate equivalences, this file conjugates the
existing canonical creation-to-response matching onto the exact processed-seat
universe.  The distinguished head remains fixed.

Thus the first Othello move and the descending processed-prime move now act on
the same carrier.  No cardinality equivalence, arbitrary encoding, or new
arithmetic matching is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Tagged coordinates used only to expose the already-existing shallow/deep
split of one processed state. -/
abbrev SquareRootLowPrimeProcessedCreationResponseState :=
  Sum Unit (Sum SquareRootLowPrimeCreationState (ℕ × ℕ))

/-- Encode a processed state as head, shallow creation, or deep response. -/
def squareRootLowPrimeProcessedCreationResponseEncode
    (R K : ℕ) :
    SquareRootLowPrimeProcessedState →
      SquareRootLowPrimeProcessedCreationResponseState
  | none => .inl ()
  | some z =>
      if canonicalLargestPrimeFactor z.1 ≤ K then
        .inr (.inl (squareRootLowPrimeProcessedShallowSeatToCreation R z))
      else
        .inr (.inr z)

/-- Forget the tagged shallow/deep coordinates back to the exact processed
state. -/
def squareRootLowPrimeProcessedCreationResponseDecode
    (R : ℕ) :
    SquareRootLowPrimeProcessedCreationResponseState →
      SquareRootLowPrimeProcessedState
  | .inl _ => none
  | .inr (.inl x) =>
      some (squareRootLowPrimeCreationToProcessedShallowSeat R x)
  | .inr (.inr z) => some z

/-- Head plus the generic creation-response tagged carrier. -/
def squareRootLowPrimeProcessedCreationResponseTaggedCarrier
    (R K j U : ℕ) :
    Finset SquareRootLowPrimeProcessedCreationResponseState :=
  ({()} : Finset Unit).disjSum
    (creationResponseOthelloCarrier
      ((squareRootLowPrimeCreationCarrierExact R K j).erase none)
      (squareRootLowPrimeOwnedResponseSeatCarrier R K j U))

private theorem squareRootLowPrimeMatchedCreationStates_subset_nonheadCreation
    (R K j U : ℕ) :
    squareRootLowPrimeMatchedCreationStates R K j U ⊆
      (squareRootLowPrimeCreationCarrierExact R K j).erase none := by
  intro x hx
  have hxData := mem_squareRootLowPrimeMatchedCreationStates.mp hx
  exact Finset.mem_erase.mpr ⟨hxData.2.1, hxData.1⟩

/-- Every processed carrier state has one of the tagged coordinates above. -/
theorem squareRootLowPrimeProcessedCreationResponseEncode_mem
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedCreationResponseEncode R K x ∈
      squareRootLowPrimeProcessedCreationResponseTaggedCarrier R K j U := by
  rcases x with _ | z
  · simp [squareRootLowPrimeProcessedCreationResponseEncode,
      squareRootLowPrimeProcessedCreationResponseTaggedCarrier]
  · have hzAtom : z ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
      simpa [squareRootLowPrimeProcessedSeatCarrier] using hx
    by_cases hshallow : canonicalLargestPrimeFactor z.1 ≤ K
    · have hzShallow :
          z ∈ squareRootLowPrimeProcessedShallowSeatAtoms R K j U :=
        mem_squareRootLowPrimeProcessedShallowSeatAtoms.mpr
          ⟨hzAtom, hshallow⟩
      have hcreation :=
        squareRootLowPrimeProcessedShallowSeatToCreation_mem hR hKU hzShallow
      simpa [squareRootLowPrimeProcessedCreationResponseEncode, hshallow,
        squareRootLowPrimeProcessedCreationResponseTaggedCarrier,
        creationResponseOthelloCarrier] using
          (Finset.mem_erase.mp hcreation)
    · have hdeep : K < canonicalLargestPrimeFactor z.1 := by omega
      have hresponse :
          z ∈ squareRootLowPrimeOwnedResponseSeatCarrier R K j U :=
        squareRootLowPrimeProcessedSeat_mem_ownedResponseSeatCarrier_of_deep
          hK hx hdeep
      simp [squareRootLowPrimeProcessedCreationResponseEncode, hshallow,
        squareRootLowPrimeProcessedCreationResponseTaggedCarrier,
        creationResponseOthelloCarrier, hresponse]

/-- Every tagged carrier state decodes back into the exact processed carrier. -/
theorem squareRootLowPrimeProcessedCreationResponseDecode_mem
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    {y : SquareRootLowPrimeProcessedCreationResponseState}
    (hy : y ∈ squareRootLowPrimeProcessedCreationResponseTaggedCarrier R K j U) :
    squareRootLowPrimeProcessedCreationResponseDecode R y ∈
      squareRootLowPrimeProcessedSeatCarrier R K j U := by
  rcases y with u | y
  · simp [squareRootLowPrimeProcessedCreationResponseDecode,
      squareRootLowPrimeProcessedSeatCarrier]
  · rcases y with c | z
    · have hc :
          c ∈ (squareRootLowPrimeCreationCarrierExact R K j).erase none := by
        simpa [squareRootLowPrimeProcessedCreationResponseTaggedCarrier,
          creationResponseOthelloCarrier] using hy
      have hz :=
        squareRootLowPrimeCreationToProcessedShallowSeat_mem hR hKU hc
      have hzAtom :=
        (mem_squareRootLowPrimeProcessedShallowSeatAtoms.mp hz).1
      simpa [squareRootLowPrimeProcessedCreationResponseDecode,
        squareRootLowPrimeProcessedSeatCarrier] using hzAtom
    · have hzResponse :
          z ∈ squareRootLowPrimeOwnedResponseSeatCarrier R K j U := by
        simpa [squareRootLowPrimeProcessedCreationResponseTaggedCarrier,
          creationResponseOthelloCarrier] using hy
      have hzDeep :
          z ∈ squareRootLowPrimeProcessedDeepSeatAtoms R K j U := by
        rw [squareRootLowPrimeProcessedDeepSeatAtoms_eq_ownedResponseSeatCarrier hK]
        exact hzResponse
      have hzAtom :=
        (mem_squareRootLowPrimeProcessedDeepSeatAtoms.mp hzDeep).1
      simpa [squareRootLowPrimeProcessedCreationResponseDecode,
        squareRootLowPrimeProcessedSeatCarrier] using hzAtom

/-- Decode after encode is literally the identity on the processed carrier. -/
theorem squareRootLowPrimeProcessedCreationResponseDecode_encode
    {R K j U : ℕ} (hR : 1 ≤ R) (_hK : 1 ≤ K) (hKU : K ≤ U)
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedCreationResponseDecode R
        (squareRootLowPrimeProcessedCreationResponseEncode R K x) = x := by
  rcases x with _ | z
  · rfl
  · have hzAtom : z ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
      simpa [squareRootLowPrimeProcessedSeatCarrier] using hx
    by_cases hshallow : canonicalLargestPrimeFactor z.1 ≤ K
    · have hzShallow :
          z ∈ squareRootLowPrimeProcessedShallowSeatAtoms R K j U :=
        mem_squareRootLowPrimeProcessedShallowSeatAtoms.mpr
          ⟨hzAtom, hshallow⟩
      simp only [squareRootLowPrimeProcessedCreationResponseEncode, hshallow,
        if_true, squareRootLowPrimeProcessedCreationResponseDecode]
      apply congrArg some
      exact squareRootLowPrimeCreationToProcessedShallowSeat_toCreation
        hR hKU hzShallow
    · simp [squareRootLowPrimeProcessedCreationResponseEncode, hshallow,
        squareRootLowPrimeProcessedCreationResponseDecode]

/-- Encode after decode is the identity on the tagged carrier. -/
theorem squareRootLowPrimeProcessedCreationResponseEncode_decode
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    {y : SquareRootLowPrimeProcessedCreationResponseState}
    (hy : y ∈ squareRootLowPrimeProcessedCreationResponseTaggedCarrier R K j U) :
    squareRootLowPrimeProcessedCreationResponseEncode R K
        (squareRootLowPrimeProcessedCreationResponseDecode R y) = y := by
  rcases y with u | y
  · cases u
    rfl
  · rcases y with c | z
    · have hc :
          c ∈ (squareRootLowPrimeCreationCarrierExact R K j).erase none := by
        simpa [squareRootLowPrimeProcessedCreationResponseTaggedCarrier,
          creationResponseOthelloCarrier] using hy
      have hz :=
        squareRootLowPrimeCreationToProcessedShallowSeat_mem hR hKU hc
      have hshallow :=
        (mem_squareRootLowPrimeProcessedShallowSeatAtoms.mp hz).2
      simp only [squareRootLowPrimeProcessedCreationResponseDecode,
        squareRootLowPrimeProcessedCreationResponseEncode, hshallow, if_true]
      congr 2
      exact squareRootLowPrimeProcessedShallowSeatToCreation_fromCreation
        hR hKU hc
    · have hzResponse :
          z ∈ squareRootLowPrimeOwnedResponseSeatCarrier R K j U := by
        simpa [squareRootLowPrimeProcessedCreationResponseTaggedCarrier,
          creationResponseOthelloCarrier] using hy
      have hzDeep :
          z ∈ squareRootLowPrimeProcessedDeepSeatAtoms R K j U := by
        rw [squareRootLowPrimeProcessedDeepSeatAtoms_eq_ownedResponseSeatCarrier hK]
        exact hzResponse
      have hdeep :=
        (mem_squareRootLowPrimeProcessedDeepSeatAtoms.mp hzDeep).2
      have hnot : ¬ canonicalLargestPrimeFactor z.1 ≤ K := by omega
      simp [squareRootLowPrimeProcessedCreationResponseDecode,
        squareRootLowPrimeProcessedCreationResponseEncode, hnot]

/-- Generic creation-response mate, with the processed head fixed. -/
noncomputable def squareRootLowPrimeProcessedCreationResponseTaggedMate
    (R K j U : ℕ) :
    SquareRootLowPrimeProcessedCreationResponseState →
      SquareRootLowPrimeProcessedCreationResponseState
  | .inl u => .inl u
  | .inr y => .inr <|
      creationResponseOthelloMate
        (squareRootLowPrimeMatchedCreationStates R K j U)
        (squareRootLowPrimeCanonicalCreationToResponse R K j U) y

/-- The tagged mate preserves the tagged carrier. -/
theorem squareRootLowPrimeProcessedCreationResponseTaggedMate_mem
    {R K j U : ℕ}
    {y : SquareRootLowPrimeProcessedCreationResponseState}
    (hy : y ∈ squareRootLowPrimeProcessedCreationResponseTaggedCarrier R K j U) :
    squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U y ∈
      squareRootLowPrimeProcessedCreationResponseTaggedCarrier R K j U := by
  rcases y with u | y
  · simp [squareRootLowPrimeProcessedCreationResponseTaggedMate,
      squareRootLowPrimeProcessedCreationResponseTaggedCarrier]
  · have hyCR :
      y ∈ creationResponseOthelloCarrier
        ((squareRootLowPrimeCreationCarrierExact R K j).erase none)
        (squareRootLowPrimeOwnedResponseSeatCarrier R K j U) := by
      simpa [squareRootLowPrimeProcessedCreationResponseTaggedCarrier] using hy
    have hmate := creationResponseOthelloMate_mem
      ((squareRootLowPrimeCreationCarrierExact R K j).erase none)
      (squareRootLowPrimeMatchedCreationStates R K j U)
      (squareRootLowPrimeOwnedResponseSeatCarrier R K j U)
      (squareRootLowPrimeCanonicalCreationToResponse R K j U)
      (squareRootLowPrimeMatchedCreationStates_subset_nonheadCreation R K j U)
      (fun c hc => squareRootLowPrimeCanonicalCreationToResponse_mem hc)
      hyCR
    simpa [squareRootLowPrimeProcessedCreationResponseTaggedMate,
      squareRootLowPrimeProcessedCreationResponseTaggedCarrier] using hmate

/-- The tagged mate is involutive. -/
theorem squareRootLowPrimeProcessedCreationResponseTaggedMate_involutive
    (R K j U : ℕ)
    (y : SquareRootLowPrimeProcessedCreationResponseState) :
    squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U
        (squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U y) = y := by
  rcases y with u | y
  · rfl
  · simp only [squareRootLowPrimeProcessedCreationResponseTaggedMate]
    congr 1
    exact creationResponseOthelloMate_involutive
      (squareRootLowPrimeMatchedCreationStates R K j U)
      (squareRootLowPrimeCanonicalCreationToResponse R K j U)
      squareRootLowPrimeCanonicalCreationToResponse_injOn y

/-- Native tagged real weight before conjugating back to the processed carrier. -/
def squareRootLowPrimeProcessedCreationResponseTaggedWeight :
    SquareRootLowPrimeProcessedCreationResponseState → ℝ
  | .inl _ => 1
  | .inr (.inl c) => squareRootLowPrimeCreationWeightReal c
  | .inr (.inr z) => squareRootLowPrimeResponseSeatWeightReal z

/-- The encoding preserves native processed-seat weight. -/
theorem squareRootLowPrimeProcessedCreationResponseEncode_weight
    {R K j U : ℕ} (hR : 1 ≤ R) (_hK : 1 ≤ K) (hKU : K ≤ U)
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedCreationResponseTaggedWeight
        (squareRootLowPrimeProcessedCreationResponseEncode R K x) =
      squareRootLowPrimeProcessedSeatWeightReal x := by
  rcases x with _ | z
  · rfl
  · have hzAtom : z ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
      simpa [squareRootLowPrimeProcessedSeatCarrier] using hx
    by_cases hshallow : canonicalLargestPrimeFactor z.1 ≤ K
    · have hzShallow :
          z ∈ squareRootLowPrimeProcessedShallowSeatAtoms R K j U :=
        mem_squareRootLowPrimeProcessedShallowSeatAtoms.mpr
          ⟨hzAtom, hshallow⟩
      let zs : ↥(squareRootLowPrimeProcessedShallowSeatAtoms R K j U) :=
        ⟨z, hzShallow⟩
      have hw := squareRootLowPrimeProcessedShallowSeatCreationEquiv_weight_eq
        hR hKU zs
      simpa [squareRootLowPrimeProcessedCreationResponseEncode, hshallow,
        squareRootLowPrimeProcessedCreationResponseTaggedWeight,
        squareRootLowPrimeProcessedShallowSeatCreationEquiv, zs] using hw
    · simp [squareRootLowPrimeProcessedCreationResponseEncode, hshallow,
        squareRootLowPrimeProcessedCreationResponseTaggedWeight,
        squareRootLowPrimeResponseSeatWeightReal,
        squareRootLowPrimeProcessedSeatWeightReal]

/-- On the non-head tag the tagged weight is literally the generic
creation-response Othello weight.  The nested match in the definition does not
reduce for a variable `y`, so this has to be proved by cases rather than used
definitionally. -/
theorem squareRootLowPrimeProcessedCreationResponseTaggedWeight_inr
    (y : Sum SquareRootLowPrimeCreationState (ℕ × ℕ)) :
    squareRootLowPrimeProcessedCreationResponseTaggedWeight (Sum.inr y) =
      creationResponseOthelloWeight
        squareRootLowPrimeCreationWeightReal
        squareRootLowPrimeResponseSeatWeightReal y := by
  cases y with
  | inl c => rfl
  | inr z => rfl

/-- Every moved tagged creation-response state reverses its native weight. -/
theorem squareRootLowPrimeProcessedCreationResponseTaggedMate_weight_neg
    (R K j U : ℕ)
    (y : SquareRootLowPrimeProcessedCreationResponseState)
    (hne : squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U y ≠ y) :
    squareRootLowPrimeProcessedCreationResponseTaggedWeight
        (squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U y) =
      -squareRootLowPrimeProcessedCreationResponseTaggedWeight y := by
  rcases y with u | y
  · exact (hne rfl).elim
  · have hne' :
      creationResponseOthelloMate
          (squareRootLowPrimeMatchedCreationStates R K j U)
          (squareRootLowPrimeCanonicalCreationToResponse R K j U) y ≠ y := by
      simpa [squareRootLowPrimeProcessedCreationResponseTaggedMate] using hne
    have h := creationResponseOthelloMate_weight_neg
      (squareRootLowPrimeMatchedCreationStates R K j U)
      (squareRootLowPrimeCanonicalCreationToResponse R K j U)
      squareRootLowPrimeCreationWeightReal
      squareRootLowPrimeResponseSeatWeightReal
      squareRootLowPrimeCanonicalCreationToResponse_injOn
      (fun c hc => squareRootLowPrimeCanonicalCreationToResponse_weight_cancel hc)
      y hne'
    have hmate :
        squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U
            (Sum.inr y) =
          Sum.inr (creationResponseOthelloMate
            (squareRootLowPrimeMatchedCreationStates R K j U)
            (squareRootLowPrimeCanonicalCreationToResponse R K j U) y) := rfl
    rw [hmate, squareRootLowPrimeProcessedCreationResponseTaggedWeight_inr,
      squareRootLowPrimeProcessedCreationResponseTaggedWeight_inr]
    exact h

/-- **First Othello mate on the exact processed-seat universe.** -/
noncomputable def squareRootLowPrimeProcessedSeatCreationResponseMate
    (R K j U : ℕ) :
    SquareRootLowPrimeProcessedState → SquareRootLowPrimeProcessedState :=
  fun x =>
    squareRootLowPrimeProcessedCreationResponseDecode R
      (squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U
        (squareRootLowPrimeProcessedCreationResponseEncode R K x))

/-- The first Othello mate preserves the exact processed carrier. -/
theorem squareRootLowPrimeProcessedSeatCreationResponseMate_mem
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedSeatCreationResponseMate R K j U x ∈
      squareRootLowPrimeProcessedSeatCarrier R K j U := by
  apply squareRootLowPrimeProcessedCreationResponseDecode_mem hR hK hKU
  apply squareRootLowPrimeProcessedCreationResponseTaggedMate_mem
  exact squareRootLowPrimeProcessedCreationResponseEncode_mem hR hK hKU hx

/-- The first Othello mate is involutive on the processed carrier. -/
theorem squareRootLowPrimeProcessedSeatCreationResponseMate_involutive
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedSeatCreationResponseMate R K j U
        (squareRootLowPrimeProcessedSeatCreationResponseMate R K j U x) = x := by
  let y := squareRootLowPrimeProcessedCreationResponseEncode R K x
  let z := squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U y
  have hy : y ∈ squareRootLowPrimeProcessedCreationResponseTaggedCarrier R K j U :=
    squareRootLowPrimeProcessedCreationResponseEncode_mem hR hK hKU hx
  have hz : z ∈ squareRootLowPrimeProcessedCreationResponseTaggedCarrier R K j U :=
    squareRootLowPrimeProcessedCreationResponseTaggedMate_mem hy
  have hencdec :
      squareRootLowPrimeProcessedCreationResponseEncode R K
          (squareRootLowPrimeProcessedCreationResponseDecode R z) = z :=
    squareRootLowPrimeProcessedCreationResponseEncode_decode hR hK hKU hz
  change squareRootLowPrimeProcessedCreationResponseDecode R
      (squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U
        (squareRootLowPrimeProcessedCreationResponseEncode R K
          (squareRootLowPrimeProcessedCreationResponseDecode R z))) = x
  rw [hencdec]
  have hinv :=
    squareRootLowPrimeProcessedCreationResponseTaggedMate_involutive
      R K j U y
  change squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U z = y
    at hinv
  rw [hinv]
  exact squareRootLowPrimeProcessedCreationResponseDecode_encode hR hK hKU hx

/-- Every moved state of the first processed-carrier Othello mate reverses the
native processed-seat weight. -/
theorem squareRootLowPrimeProcessedSeatCreationResponseMate_weight_neg
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hne : squareRootLowPrimeProcessedSeatCreationResponseMate R K j U x ≠ x) :
    squareRootLowPrimeProcessedSeatWeightReal
        (squareRootLowPrimeProcessedSeatCreationResponseMate R K j U x) =
      -squareRootLowPrimeProcessedSeatWeightReal x := by
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
  have hmoveTagged :
      squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U y ≠ y := by
    intro hfix
    apply hne
    change squareRootLowPrimeProcessedCreationResponseDecode R z = x
    rw [show z = y by exact hfix]
    exact squareRootLowPrimeProcessedCreationResponseDecode_encode hR hK hKU hx
  have hneg :=
    squareRootLowPrimeProcessedCreationResponseTaggedMate_weight_neg
      R K j U y hmoveTagged
  have hleft := squareRootLowPrimeProcessedCreationResponseEncode_weight
    hR hK hKU hxMate
  rw [hencMate] at hleft
  have hright := squareRootLowPrimeProcessedCreationResponseEncode_weight
    hR hK hKU hx
  change squareRootLowPrimeProcessedCreationResponseTaggedWeight z =
    -squareRootLowPrimeProcessedCreationResponseTaggedWeight y at hneg
  linarith

end RHLean.Proof
