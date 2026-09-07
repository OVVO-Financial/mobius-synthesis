import Mathlib
import RHLean.Proof.SquareRootLowPrimeProcessedCreationResponseInvolution

/-!
# Fixed-state classification for the first processed Othello mate

The carrier-wide creation-response involution has only three kinds of fixed
states:

* the distinguished head;
* shallow processed seats whose corresponding creation state has no admitted
  response owner;
* deep processed seats not occupied by the matched creation image.

This is the exact source-side partition to be refined by the final endpoint
classifier.  The shallow residual feeds Partial or the root fallback; the deep
residual feeds BornExit or the same root fallback.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- On the processed carrier, being fixed after conjugation is equivalent to
being fixed in the tagged creation/response coordinates. -/
theorem squareRootLowPrimeProcessedSeatCreationResponseMate_eq_self_iff_tagged
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedSeatCreationResponseMate R K j U x = x ↔
      squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U
          (squareRootLowPrimeProcessedCreationResponseEncode R K x) =
        squareRootLowPrimeProcessedCreationResponseEncode R K x := by
  constructor
  · intro hfix
    have hy := squareRootLowPrimeProcessedCreationResponseEncode_mem
      hR hK hKU hx
    have hz := squareRootLowPrimeProcessedCreationResponseTaggedMate_mem hy
    have hencdec := squareRootLowPrimeProcessedCreationResponseEncode_decode
      hR hK hKU hz
    have henc := congrArg
      (squareRootLowPrimeProcessedCreationResponseEncode R K) hfix
    change squareRootLowPrimeProcessedCreationResponseEncode R K
        (squareRootLowPrimeProcessedCreationResponseDecode R
          (squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U
            (squareRootLowPrimeProcessedCreationResponseEncode R K x))) =
      squareRootLowPrimeProcessedCreationResponseEncode R K x at henc
    rw [hencdec] at henc
    exact henc
  · intro hfix
    change squareRootLowPrimeProcessedCreationResponseDecode R
        (squareRootLowPrimeProcessedCreationResponseTaggedMate R K j U
          (squareRootLowPrimeProcessedCreationResponseEncode R K x)) = x
    rw [hfix]
    exact squareRootLowPrimeProcessedCreationResponseDecode_encode
      hR hK hKU hx

/-- The processed head is fixed by the first Othello mate. -/
@[simp] theorem squareRootLowPrimeProcessedSeatCreationResponseMate_head
    (R K j U : ℕ) :
    squareRootLowPrimeProcessedSeatCreationResponseMate R K j U none = none := by
  rfl

/-- **Shallow fixed-state classification.**  A shallow processed seat is fixed
exactly when its literal tagged creation state has no eligible response owner. -/
theorem squareRootLowPrimeProcessedSeatCreationResponseMate_shallow_eq_self_iff
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    {z : ℕ × ℕ}
    (hz : some z ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hshallow : canonicalLargestPrimeFactor z.1 ≤ K) :
    squareRootLowPrimeProcessedSeatCreationResponseMate R K j U (some z) =
        some z ↔
      squareRootLowPrimeProcessedShallowSeatToCreation R z ∉
        squareRootLowPrimeMatchedCreationStates R K j U := by
  rw [squareRootLowPrimeProcessedSeatCreationResponseMate_eq_self_iff_tagged
    hR hK hKU hz]
  simp [squareRootLowPrimeProcessedCreationResponseEncode, hshallow,
    squareRootLowPrimeProcessedCreationResponseTaggedMate,
    creationResponseOthelloMate]

/-- **Deep fixed-state classification.**  A deep processed seat is fixed exactly
when no matched shallow creation state maps to that response seat. -/
theorem squareRootLowPrimeProcessedSeatCreationResponseMate_deep_eq_self_iff
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    {z : ℕ × ℕ}
    (hz : some z ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hdeep : K < canonicalLargestPrimeFactor z.1) :
    squareRootLowPrimeProcessedSeatCreationResponseMate R K j U (some z) =
        some z ↔
      ¬ ∃ c ∈ squareRootLowPrimeMatchedCreationStates R K j U,
        squareRootLowPrimeCanonicalCreationToResponse R K j U c = z := by
  have hnot : ¬ canonicalLargestPrimeFactor z.1 ≤ K := by omega
  rw [squareRootLowPrimeProcessedSeatCreationResponseMate_eq_self_iff_tagged
    hR hK hKU hz]
  simp [squareRootLowPrimeProcessedCreationResponseEncode, hnot,
    squareRootLowPrimeProcessedCreationResponseTaggedMate,
    creationResponseOthelloMate]

/-- Equivalent finite-set form of the deep residual. -/
theorem squareRootLowPrimeProcessedSeatCreationResponseMate_deep_eq_self_iff_not_mem_image
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    {z : ℕ × ℕ}
    (hz : some z ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hdeep : K < canonicalLargestPrimeFactor z.1) :
    squareRootLowPrimeProcessedSeatCreationResponseMate R K j U (some z) =
        some z ↔
      z ∉ creationResponseMatchedImage
        (squareRootLowPrimeMatchedCreationStates R K j U)
        (squareRootLowPrimeCanonicalCreationToResponse R K j U) := by
  rw [squareRootLowPrimeProcessedSeatCreationResponseMate_deep_eq_self_iff
    hR hK hKU hz hdeep]
  simp [creationResponseMatchedImage]

end RHLean.Proof
