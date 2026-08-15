import RHLean.Analysis.NativePNTMertensBoundContraction
import RHLean.Analysis.NativePNTLowSlopeContraction

/-!
# Quantitative contraction retained from the native PNT proof

This aggregator exposes the bound-level improvements extracted from the PNT
proof already in the repository:

* reciprocal-square growth for the exact cubic recurrence, yielding an
  `eta^(-2)` iteration budget on both native PNT paths;
* finite normalized Mertens bounds retaining the contracted PNT slope after
  the Axer transfer;
* a `32/5` improvement of the low-slope one-step cubic coefficient.

No new analytic premise is introduced.
-/
