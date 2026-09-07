import Mathlib
import RHLean.Proof.SquareRootMertensMiddleTracking
import RHLean.Proof.SquareRootMertensPositiveTracking

/-!
# Ancestral tracking is the matched channel, with no strip loss

`SquareRootMertensPositiveTracking` (stated in `SquareRootMertensMiddleTracking`)
is the terminal obstruction in ancestral coordinates,

`|M(R^2 - 1) + sum_{q <= R prime} M(q - 1)| <= C * R`.

Its bridges to `SquareRootMertensMiddleTracking` cost `7` in the constant, since
the middle population carries the seven-coordinate near-prime strip.

This file records the sharper fact: because
`squarePrefixMertens_eq_positiveSmooth_add_matched` is exact,
`M(R^2-1) - A_pos R` is *literally* the matched channel, so the ancestral
proposition coincides with `SquareRootMertensPositiveTrackingReal` on the nose —
no constant loss — and composes to the terminal imbalance at `C*R + R + K`
rather than `(C+8)*R + K`.  The strip is never traversed on this route.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- **Ancestral coordinates are exactly the matched real form.**  No constant
loss: the two propositions are the same statement. -/
theorem squareRootMertensPositiveTracking_iff_positiveTrackingReal
    {C : ℝ} {R : ℕ} (hR : 1 ≤ R) :
    SquareRootMertensPositiveTracking C R ↔
      SquareRootMertensPositiveTrackingReal C R := by
  unfold SquareRootMertensPositiveTracking
    SquareRootMertensPositiveTrackingReal
  have hre :
      (RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
          squareRootPositiveSmoothMass R).re =
        (squareRootMertensInt (squareRootEndpoint R) : ℝ) +
          (squareRootPositiveSmoothPrimeMertensTransform R).re := by
    rw [Complex.sub_re, mertensSummatory_squareRootEndpoint_re,
      squareRootPositiveSmoothMass_eq_neg_primeMertensTransform R hR]
    simp
  rw [hre]

/-- **The branch from ancestral tracking, without the seven-strip loss.** -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_of_ancestralTracking
    {C : ℝ} {R K j : ℕ} (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (h : SquareRootMertensPositiveTracking C R) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤
      C * (R : ℝ) + (R : ℝ) + (K : ℝ) :=
  abs_squareRootLowPrimeRunningImbalanceReal_le_of_mertensPositiveTracking
    hR hK hKR hj hV0 hVK
    ((squareRootMertensPositiveTracking_iff_positiveTrackingReal
      (by omega)).mp h)

end RHLean.Proof
