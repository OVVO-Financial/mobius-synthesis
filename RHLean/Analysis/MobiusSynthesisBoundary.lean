import Mathlib
import RHLean.Analysis.SquareWheelQuantitativeBridge

/-!
# Möbius synthesis quantitative boundary contract

This module defines the strict quantitative lane of the synthesis PR gate. A
pull request that claims analytic improvement of the remaining nonzero response
must prove a stronger instance of the pointwise power-bound predicate below, or
prove the full RH-scale predicate.

This is no longer the only accepted research lane. Exact theorems may also be
accepted by the separate cross-track synthesis policy when they genuinely invoke
both square-block and prime-wheel machinery in synthesis form.

The quantitative object remains the already isolated nonzero square-wheel
response `H_{k,n}` represented by `squareWheelNonzeroSampleResponse`.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

namespace MobiusSynthesisBoundary

/-- A uniform pointwise power bound for the canonical nonzero response on every
complete square sample in every synchronized primorial block from `k >= 2`.

A theorem of this type is a quantitative statement about the existing boundary
object itself; changing coordinates or proving an equivalent decomposition does
not inhabit this predicate unless it also yields the stated bound. -/
def NonzeroResponsePowerBound (r : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (k n : ℕ),
      2 ≤ k →
      primorialBlockLower k < squarePrefixEndpoint n →
      squarePrefixEndpoint n ≤ primorialBlockUpper k →
      ‖squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n‖ ≤
        K * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) r

/-- The exact synthesis target: for every positive epsilon, the canonical
nonzero response has a pointwise bound at exponent `1/2 + epsilon`, uniformly
on the synchronized complete-square samples. -/
def NonzeroResponseRHScale : Prop :=
  ∀ ε : ℝ, 0 < ε →
    NonzeroResponsePowerBound ((1 : ℝ) / 2 + ε)

end MobiusSynthesisBoundary

end RHLean.Analysis
