import Mathlib
import RHLean.Proof.SquareRootLowPrimeMatchedCoreMertensObstruction

/-!
# Mertens/positive tracking: the terminal seam in its shortest form

`squarePrefixMertens_eq_positiveSmooth_add_matched` is an exact repository
identity:

`M(R^2 - 1) = A_pos R + matched R`.

So the difference `M(R^2-1) - A_pos R` is **exactly** the matched born/transport
channel — there is no error term, and no reindexing is left to do.

Two consequences worth recording.

* The proposed identity `core R = M(R^2-1) - A_pos R` is off by the
  seven-coordinate near-prime strip.  The exact statement is
  `core R = M(R^2-1) - A_pos R + near R`, since `matched = core - near`.
* Therefore the tracking hypothesis `|M(R^2-1) - A_pos R| ≤ C * R` is literally
  the matched-channel bound.  Routing through it rather than through the core
  is also cheaper: it reaches the terminal imbalance at `C*R + R + K` instead of
  `(C+8)*R + K`, because the strip is never traversed.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- **The square-prefix Mertens value minus the positive orientation is exactly
the matched channel.** -/
theorem mertens_sub_positiveSmooth_eq_matched
    (R : ℕ) (hR : 1 ≤ R) :
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
        squareRootPositiveSmoothMass R =
      squareRootMatchedBornSmoothTransport R := by
  rw [← squarePrefixMertens_pred_eq_mertens_squareRootEndpoint R hR,
    squarePrefixMertens_eq_positiveSmooth_add_matched R hR]
  ring

/-- **Corrected core identity.**  The core exceeds `M - A_pos` by exactly the
seven-coordinate near-prime strip. -/
theorem squareRootLowPrimeMatchedCore_eq_mertens_sub_positiveSmooth_add_near
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootLowPrimeMatchedCore R =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
          squareRootPositiveSmoothMass R +
        squareRootNearPrimeTransport R := by
  rw [mertens_sub_positiveSmooth_eq_matched R (by omega),
    squareRootMatchedBornSmoothTransport_eq_core_sub_near R hR]
  ring

/-- Norm form of the matched-channel target.  The ancestral proposition
`SquareRootMertensPositiveTracking` lives in `SquareRootMertensMiddleTracking`;
this is the stronger complex-norm variant against `squareRootPositiveSmoothMass`. -/
def SquareRootMertensMatchedNormTracking (C : ℝ) (R : ℕ) : Prop :=
  ‖RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
      squareRootPositiveSmoothMass R‖ ≤ C * (R : ℝ)

/-- **The terminal open proposition**, real form.  This is the minimal
hypothesis the terminal real imbalance consumes. -/
def SquareRootMertensPositiveTrackingReal (C : ℝ) (R : ℕ) : Prop :=
  |(RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
      squareRootPositiveSmoothMass R).re| ≤ C * (R : ℝ)

/-- The tracking hypothesis is literally the matched-channel norm bound. -/
theorem squareRootMertensMatchedNormTracking_iff_matched_norm
    {C : ℝ} {R : ℕ} (hR : 1 ≤ R) :
    SquareRootMertensMatchedNormTracking C R ↔
      ‖squareRootMatchedBornSmoothTransport R‖ ≤ C * (R : ℝ) := by
  unfold SquareRootMertensMatchedNormTracking
  rw [mertens_sub_positiveSmooth_eq_matched R hR]

/-- The real form is literally the matched-channel real bound. -/
theorem squareRootMertensPositiveTrackingReal_iff_matched_re
    {C : ℝ} {R : ℕ} (hR : 1 ≤ R) :
    SquareRootMertensPositiveTrackingReal C R ↔
      |(squareRootMatchedBornSmoothTransport R).re| ≤ C * (R : ℝ) := by
  unfold SquareRootMertensPositiveTrackingReal
  rw [mertens_sub_positiveSmooth_eq_matched R hR]

/-- The norm form supplies the real form. -/
theorem squareRootMertensPositiveTrackingReal_of_norm
    {C : ℝ} {R : ℕ}
    (htrack : SquareRootMertensMatchedNormTracking C R) :
    SquareRootMertensPositiveTrackingReal C R := by
  unfold SquareRootMertensMatchedNormTracking at htrack
  unfold SquareRootMertensPositiveTrackingReal
  exact (Complex.abs_re_le_norm _).trans htrack

/-- **The whole low-prime branch from the tracking hypothesis, without the
seven-strip loss.**  Routing through the matched channel directly gives
`C*R + R + K`, where routing through the core would give `(C+8)*R + K`. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_of_mertensPositiveTracking
    {C : ℝ} {R K j : ℕ} (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (htrack : SquareRootMertensPositiveTrackingReal C R) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤
      C * (R : ℝ) + (R : ℝ) + (K : ℝ) :=
  abs_squareRootLowPrimeRunningImbalanceReal_le_of_matched_re_bound
    hR hK hKR hj hV0 hVK
    ((squareRootMertensPositiveTrackingReal_iff_matched_re (by omega)).mp htrack)

end RHLean.Proof
