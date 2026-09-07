import Mathlib
import RHLean.Proof.SquareRootLowPrimeNoLibertyBoundaryHome
import RHLean.Proof.SquareRootLowPrimeProcessedSeatCarrier

/-!
# Literal Head branch of the no-liberty classifier

The distinguished processed head is already a literal unit endpoint.  No
arithmetic classification is required: `none` is sent to the `Head` summand of
the final tagged boundary.  This file records the branch membership and exact
weight equality used by the final classifier.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Distinguished head tag in the final no-liberty boundary. -/
def squareRootLowPrimeHeadBoundaryTag :
    SquareRootLowPrimeProcessedSeatNoLibertyState :=
  .inl ()

/-- The head tag is present in every final boundary. -/
theorem squareRootLowPrimeHeadBoundaryTag_mem
    (R K j U : ℕ) :
    squareRootLowPrimeHeadBoundaryTag ∈
      squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U := by
  simp [squareRootLowPrimeHeadBoundaryTag,
    squareRootLowPrimeProcessedSeatNoLibertyBoundary]

/-- Head orientation agrees exactly with the processed-seat head weight. -/
theorem squareRootLowPrimeHeadBoundaryTag_weight_eq :
    squareRootLowPrimeNoLibertyBoundaryWeight
        squareRootLowPrimeHeadBoundaryTag =
      squareRootLowPrimeProcessedSeatWeightReal none := by
  rfl

/-- The Head constructor is disjoint from every non-head boundary constructor.
This is definitional `Sum`-tag separation and will discharge cross-branch
injectivity in the final classifier. -/
theorem squareRootLowPrimeHeadBoundaryTag_ne_inr
    (x : Sum ℕ (Sum (ℕ × ℕ) ((ℕ × ℕ) × ℕ))) :
    squareRootLowPrimeHeadBoundaryTag ≠ .inr x := by
  simp [squareRootLowPrimeHeadBoundaryTag]

end RHLean.Proof
