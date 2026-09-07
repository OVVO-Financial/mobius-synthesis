import Mathlib
import RHLean.Proof.SquareRootLowPrimeNearRootRemainder
import RHLean.Proof.MatchedFarSurvivorBridge

/-!
# The branch target with no fixed constant

The far-survivor bridge localizes the matched born/transport channel to the
signed core

`core R = bornSmooth R + survivorSixteenFarUpperPrimeMass (R-1)`,

up to the seven-coordinate near-prime strip, whose norm is at most `7R` by the
triangle inequality alone.  Nothing downstream consumes a specific constant, so
the branch target is stated here with the constant left free.

Two interfaces are exposed:

* `SquareRootLowPrimeMatchedCoreBound C R` asks for the full complex norm;
* `SquareRootLowPrimeMatchedCoreRealBound C R` asks only for the real part.

The second is the genuinely minimal hypothesis for the terminal real imbalance.
Either form gives

`|runningImbalanceReal| <= (C + 8) * R + K`.

Note the indexing: the far-upper survivor enters at stage `R - 1`, not `R`.

Everything below is pure bookkeeping around that one hypothesis.  The seven-term
strip is handled by the triangle inequality throughout -- it never needs to
cancel once the core is `O(R)`.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- The signed core to which the far-survivor bridge localizes the matched
channel. -/
def squareRootLowPrimeMatchedCore (R : ℕ) : ℂ :=
  squareRootBornSmoothMass R + survivorSixteenFarUpperPrimeMass (R - 1)

/-- Full complex-norm version of the remaining open bound. -/
def SquareRootLowPrimeMatchedCoreBound (C : ℝ) (R : ℕ) : Prop :=
  ‖squareRootLowPrimeMatchedCore R‖ ≤ C * (R : ℝ)

/-- Minimal real-coordinate version of the remaining open bound.  This is all
that the terminal real imbalance actually consumes. -/
def SquareRootLowPrimeMatchedCoreRealBound (C : ℝ) (R : ℕ) : Prop :=
  |(squareRootLowPrimeMatchedCore R).re| ≤ C * (R : ℝ)

/-- A complex-norm core bound automatically supplies the weaker real bound. -/
theorem squareRootLowPrimeMatchedCoreRealBound_of_normBound
    {C : ℝ} {R : ℕ}
    (hcore : SquareRootLowPrimeMatchedCoreBound C R) :
    SquareRootLowPrimeMatchedCoreRealBound C R := by
  unfold SquareRootLowPrimeMatchedCoreBound at hcore
  unfold SquareRootLowPrimeMatchedCoreRealBound
  exact (Complex.abs_re_le_norm _).trans hcore

/-- The matched channel is the core minus the near-prime strip. -/
theorem squareRootMatchedBornSmoothTransport_eq_core_sub_near
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootMatchedBornSmoothTransport R =
      squareRootLowPrimeMatchedCore R - squareRootNearPrimeTransport R := by
  unfold squareRootLowPrimeMatchedCore
  rw [squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_farSurvivor_sub_near
    R hR]

/-- A core norm bound gives a matched norm bound, with the elementary
seven-strip loss. -/
theorem norm_squareRootMatchedBornSmoothTransport_le_of_coreBound
    {C : ℝ} {R : ℕ} (hR : 56 ≤ R)
    (hcore : SquareRootLowPrimeMatchedCoreBound C R) :
    ‖squareRootMatchedBornSmoothTransport R‖ ≤ (C + 7) * (R : ℝ) := by
  unfold SquareRootLowPrimeMatchedCoreBound at hcore
  have hnear := norm_squareRootNearPrimeTransport_le R hR
  rw [squareRootMatchedBornSmoothTransport_eq_core_sub_near R hR]
  calc
    ‖squareRootLowPrimeMatchedCore R - squareRootNearPrimeTransport R‖ ≤
        ‖squareRootLowPrimeMatchedCore R‖ +
          ‖squareRootNearPrimeTransport R‖ := norm_sub_le _ _
    _ ≤ C * (R : ℝ) + 7 * (R : ℝ) := add_le_add hcore hnear
    _ = (C + 7) * (R : ℝ) := by ring

/-- A real-part core bound already gives the only matched estimate needed by the
terminal real imbalance.  No imaginary-coordinate control is used. -/
theorem abs_squareRootMatchedBornSmoothTransport_re_le_of_coreRealBound
    {C : ℝ} {R : ℕ} (hR : 56 ≤ R)
    (hcore : SquareRootLowPrimeMatchedCoreRealBound C R) :
    |(squareRootMatchedBornSmoothTransport R).re| ≤
      (C + 7) * (R : ℝ) := by
  unfold SquareRootLowPrimeMatchedCoreRealBound at hcore
  have hnearNorm := norm_squareRootNearPrimeTransport_le R hR
  have hnearRe :
      |(squareRootNearPrimeTransport R).re| ≤ 7 * (R : ℝ) :=
    (Complex.abs_re_le_norm _).trans hnearNorm
  have heq := congrArg Complex.re
    (squareRootMatchedBornSmoothTransport_eq_core_sub_near R hR)
  have hre :
      (squareRootMatchedBornSmoothTransport R).re =
        (squareRootLowPrimeMatchedCore R).re -
          (squareRootNearPrimeTransport R).re := by
    simpa using heq
  rw [hre]
  have htri :
      |(squareRootLowPrimeMatchedCore R).re -
          (squareRootNearPrimeTransport R).re| ≤
        |(squareRootLowPrimeMatchedCore R).re| +
          |(squareRootNearPrimeTransport R).re| := by
    simpa [sub_eq_add_neg, abs_neg] using
      (abs_add_le (squareRootLowPrimeMatchedCore R).re
        (-(squareRootNearPrimeTransport R).re))
  calc
    |(squareRootLowPrimeMatchedCore R).re -
        (squareRootNearPrimeTransport R).re| ≤
      |(squareRootLowPrimeMatchedCore R).re| +
        |(squareRootNearPrimeTransport R).re| := htri
    _ ≤ C * (R : ℝ) + 7 * (R : ℝ) := add_le_add hcore hnearRe
    _ = (C + 7) * (R : ℝ) := by ring

/-- **Parameterized running-imbalance bound.**  Any bound on the real part of
the matched channel transfers, with the already-proved `R + K` proximity. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_of_matched_re_bound
    {R K j : ℕ} {B : ℝ} (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (hmatched : |(squareRootMatchedBornSmoothTransport R).re| ≤ B) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤ B + (R : ℝ) + (K : ℝ) := by
  have hnorm :=
    norm_squareRootLowPrimeRunningImbalance_sub_matched_le_root_add_depth
      R K j hR hK hKR hj hV0 hVK
  have hre :
      |(squareRootLowPrimeRunningImbalance R K j
            (squareRootBornPostTailLowPrimeCutoff R) -
          squareRootMatchedBornSmoothTransport R).re| ≤ (R : ℝ) + (K : ℝ) :=
    le_trans (Complex.abs_re_le_norm _) hnorm
  have hsplit :
      (squareRootLowPrimeRunningImbalance R K j
            (squareRootBornPostTailLowPrimeCutoff R) -
          squareRootMatchedBornSmoothTransport R).re =
        squareRootLowPrimeRunningImbalanceReal R K j
            (squareRootBornPostTailLowPrimeCutoff R) -
          (squareRootMatchedBornSmoothTransport R).re := by
    unfold squareRootLowPrimeRunningImbalanceReal
    simp
  rw [hsplit] at hre
  have h1 := abs_le.mp hre
  have h2 := abs_le.mp hmatched
  rw [abs_le]
  constructor <;> linarith

/-- The branch target from the stronger complex-norm core hypothesis. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_of_matchedCoreBound
    {C : ℝ} {R K j : ℕ} (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (hcore : SquareRootLowPrimeMatchedCoreBound C R) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤
      (C + 8) * (R : ℝ) + (K : ℝ) := by
  have hmatchedNorm :=
    norm_squareRootMatchedBornSmoothTransport_le_of_coreBound hR hcore
  have hmatchedRe :
      |(squareRootMatchedBornSmoothTransport R).re| ≤ (C + 7) * (R : ℝ) :=
    le_trans (Complex.abs_re_le_norm _) hmatchedNorm
  have hmain :=
    abs_squareRootLowPrimeRunningImbalanceReal_le_of_matched_re_bound
      hR hK hKR hj hV0 hVK hmatchedRe
  calc
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤
        (C + 7) * (R : ℝ) + (R : ℝ) + (K : ℝ) := hmain
    _ = (C + 8) * (R : ℝ) + (K : ℝ) := by ring

/-- The same terminal bound from the minimal real-part core hypothesis. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_of_matchedCoreRealBound
    {C : ℝ} {R K j : ℕ} (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (hcore : SquareRootLowPrimeMatchedCoreRealBound C R) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤
      (C + 8) * (R : ℝ) + (K : ℝ) := by
  have hmatchedRe :=
    abs_squareRootMatchedBornSmoothTransport_re_le_of_coreRealBound hR hcore
  have hmain :=
    abs_squareRootLowPrimeRunningImbalanceReal_le_of_matched_re_bound
      hR hK hKR hj hV0 hVK hmatchedRe
  calc
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤
        (C + 7) * (R : ℝ) + (R : ℝ) + (K : ℝ) := hmain
    _ = (C + 8) * (R : ℝ) + (K : ℝ) := by ring

end RHLean.Proof
