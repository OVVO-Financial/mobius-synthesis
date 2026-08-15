import Mathlib
import RHLean.Analysis.ThreeSlotMertensDegreeOneProjection
import RHLean.Analysis.PrimeSievePNTCentering
import RHLean.Analysis.SquareRootTransportRealization

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-!
# Three-slot degree-one synthesis checkpoint

This module records a compact exact checkpoint connecting the three-slot
Möbius degree-one projection to the two established square-sensitive views of
the same Mertens object.

No quantitative cancellation estimate is asserted here.  The theorem below
packages three kernel-checked identities:

* the complete-cell Mertens value is the three-slot signed `R - 2H` field;
* the square-prefix Mertens quantity has its positive-smooth plus matched
  transport decomposition;
* the canonical nonzero square-wheel response is the exact zero-mode centering
  of the Mertens summatory function.

This makes the remaining problem explicit: prove RH-scale cancellation for the
signed degree-one field without destroying its cancellations by estimating the
raw and smooth pieces separately.
-/

/-- Exact cross-track checkpoint for the signed degree-one Mertens object. -/
theorem threeSlotDegreeOne_crossTrackCheckpoint
    (K R k n : ℕ)
    (hR : 1 ≤ R)
    (hlower : primorialBlockLower k < squarePrefixEndpoint n)
    (hupper : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    (mertensSummatory (4 * K) =
      (((threeSlotSignedFieldPrefix 1 K +
          threeSlotSignedFieldPrefix 2 K +
          threeSlotSignedFieldPrefix 3 K : ℤ)) : ℂ)) ∧
    (squarePrefixMertens (R - 1) =
      squareRootPositiveSmoothMass R +
        squareRootMatchedBornSmoothTransport R) ∧
    (squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n =
      primorialSquareZeroModeCenter k n mertensSummatory) := by
  refine ⟨mertensSummatory_four_mul_eq_signedField K, ?_, ?_⟩
  · exact RHLean.Proof.squarePrefixMertens_eq_positiveSmooth_add_matched R hR
  · exact primorialMinimalSquareWheelNonzeroResponse_eq_mertensCenter
      k n hlower hupper

end RHLean.Analysis
