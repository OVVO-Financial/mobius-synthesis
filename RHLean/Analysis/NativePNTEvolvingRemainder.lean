import RHLean.Analysis.NativePNTRemainderProfileCore
import RHLean.Analysis.NativePNTRemainderProfileCompose
import RHLean.Analysis.NativePNTSignedWheelRemainder
import RHLean.Analysis.NativePNTEvolvingTailCompensation
import RHLean.Analysis.NativePNTEvolvingTailState
import RHLean.Analysis.NativePNTEvolvingTailStep

/-!
# Evolving native PNT remainder engine

This module collects the constant-free quantitative architecture:

* exact scale-dependent first and second Selberg remainder profiles;
* exact signed prime-wheel resolved and unresolved reciprocal masses;
* exact wheel-cutoff update with no additive constant;
* exact small-quotient excess and reciprocal-kernel defect;
* one-step tail contraction driven only by the current evolving cost.

Numerical constants remain available only through separate majorant theorems.
-/
