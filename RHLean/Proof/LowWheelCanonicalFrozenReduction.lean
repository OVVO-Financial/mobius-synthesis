import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedParentClassification

/-!
# Frozen canonical downcross carrier

The original version of this file also claimed a full exact reduction of the
canonical downcross ledger to the frozen carrier.  That proof depended on an
older face/tail transport API and on the retired
`sum_lowWheelCanonicalRepeatedMovablePart_eq_zero` theorem.  Once this module
was made reachable from `RHLean.lean`, those stale dependencies were exposed by
the clean root build.

The durable object used by the current first-failure geometry is the frozen
carrier itself.  We keep that definition here and deliberately do not restate
the obsolete global cancellation theorem.  Exact movable cancellation is now
carried by the maintained Othello modules; identifying that cancellation with
this older canonical carrier is a genuine seam rather than hidden compiled
state.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Frozen first-crossing states in the complete tagged downcross carrier. -/
def lowWheelCanonicalFrozenDowncrossPart (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalTaggedDowncrossCarrier R).filter
    LowWheelDowncrossFrozenShape

end RHLean.Proof
