import RHLean.Proof.LowWheelCanonicalRepeatedParentClassification
import RHLean.Proof.LowWheelOthelloRepeatedInvolution

/-!
# Retired canonical repeated-mass reduction experiment

The former declarations in this module reduced the older canonical
repeated-parent ledger by invoking
`sum_lowWheelCanonicalRepeatedMovablePart_eq_zero`.  That theorem belonged to a
superseded movable-toggle API and disappeared when the maintained Othello
involution replaced it.  The file had remained checked in only because it was
absent from `RHLean.lean` and therefore was never compiled by the root build.

The maintained ingredients are now explicit imports above:

* `LowWheelCanonicalRepeatedParentClassification` contains the current
  canonical repeated/frozen classification; and
* `LowWheelOthelloRepeatedInvolution` contains the compiled exact cancellation
  on the lightweight Othello carrier.

A bridge identifying those two carriers is an open synthesis seam.  We do not
preserve an obsolete theorem under a green manifest merely by leaving it
unreachable.
-/
