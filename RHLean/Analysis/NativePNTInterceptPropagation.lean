import RHLean.Analysis.NativePNTInterceptMildUpdates

/-!
# Native PNT intercept propagation

This module is the public entry point for the explicit affine-intercept
recurrence attached to the native PNT cubic contraction.

It exposes:

* the specified affine-envelope predicate `NativePNTAffineEnvelopeAt`;
* the canonical one-step onset `nativePNTCubicStepOnset`;
* the canonical propagated intercept `nativePNTCubicIntercept`;
* the exact update `D_(n+1) = D_n + C a_n^3 M_n`;
* the current exponential onset obstruction;
* the precise onset-scale hypotheses that would imply linear or quadratic
  intercept updates.
-/
