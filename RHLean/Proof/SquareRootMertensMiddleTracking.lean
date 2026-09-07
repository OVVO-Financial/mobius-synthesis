import Mathlib
import RHLean.Proof.SquareRootLowPrimeMatchedCoreMertensObstruction

/-!
# Terminal obstruction: Mertens/middle tracking

The structural development ends here.

`squareRootLowPrimeMatchedCore_eq_mertens_sub_middleMertensMass` gives the exact
identity

`core R = M(R^2 - 1) - Middle R`,

so the entire low-prime branch rests on a single open proposition: that the
signed middle population tracks the square-prefix Mertens value to within a
constant multiple of `R`.

This file states that proposition in literal real/integer coordinates — the
square-prefix Mertens value is an integer, so no complex coordinate survives —
and composes it, in one theorem, all the way to the terminal real imbalance.

Nothing here bounds `M(R^2 - 1)` or `Middle R` separately.  That would not help:
since `core = M - Middle`, a separate `O(R)` bound on `Middle` together with an
`O(R)` bound on `core` would force `M(R^2-1) = O(R)`, i.e. `M(x) = O(sqrt x)`.
The content is entirely in the correlation between the two terms.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- **The terminal open proposition.**

`|M(R^2 - 1) - Middle R| <= C * R`, in real/integer coordinates. -/
def SquareRootMertensMiddleTracking (C : ℝ) (R : ℕ) : Prop :=
  |(squareRootMertensInt (squareRootEndpoint R) : ℝ) -
      (squareRootLowPrimeMiddleMertensMass R).re| ≤ C * (R : ℝ)

/-- The integer square-prefix Mertens value is the real coordinate of the
complex Mertens sample. -/
theorem mertensSummatory_squareRootEndpoint_re
    (R : ℕ) :
    (RHLean.Analysis.mertensSummatory (squareRootEndpoint R)).re =
      (squareRootMertensInt (squareRootEndpoint R) : ℝ) := by
  rw [← squareRootMertensInt_cast_complex]
  simp

/-- **Clean ancestral form of the terminal open proposition.**

The positive orientation has already collapsed exactly to the negative
prime-indexed ancestral Mertens transform.  This therefore states the remaining
question in its most readable coordinates:

`|M(R^2 - 1) + sum_{q <= R, q prime} M(q - 1)| <= C * R`.

The existing complex transform is real-valued, but the terminal theorem only
consumes its real coordinate, so the proposition is stated directly in `ℝ`. -/
def SquareRootMertensPositiveTracking (C : ℝ) (R : ℕ) : Prop :=
  |(squareRootMertensInt (squareRootEndpoint R) : ℝ) +
      (squareRootPositiveSmoothPrimeMertensTransform R).re| ≤
    C * (R : ℝ)

/-- The middle population differs from the negative ancestral transform only by
the seven-coordinate near-prime strip. -/
private theorem squareRootLowPrimeMiddleMertensMass_re_eq_neg_primeTransform_sub_near
    (R : ℕ) (hR : 1 ≤ R) :
    (squareRootLowPrimeMiddleMertensMass R).re =
      -(squareRootPositiveSmoothPrimeMertensTransform R).re -
        (squareRootNearPrimeTransport R).re := by
  unfold squareRootLowPrimeMiddleMertensMass
  rw [squareRootPositiveSmoothMass_eq_neg_primeMertensTransform R hR]
  simp

/-- Clean ancestral tracking implies the existing middle-tracking proposition,
losing only the already-proved `7R` near-prime strip. -/
theorem squareRootMertensMiddleTracking_of_positiveTracking
    {C : ℝ} {R : ℕ} (hR : 56 ≤ R)
    (htrack : SquareRootMertensPositiveTracking C R) :
    SquareRootMertensMiddleTracking (C + 7) R := by
  unfold SquareRootMertensPositiveTracking at htrack
  unfold SquareRootMertensMiddleTracking
  have hmiddle :=
    squareRootLowPrimeMiddleMertensMass_re_eq_neg_primeTransform_sub_near
      R (by omega)
  have hnearNorm := norm_squareRootNearPrimeTransport_le R hR
  have hnearRe :
      |(squareRootNearPrimeTransport R).re| ≤ 7 * (R : ℝ) :=
    (Complex.abs_re_le_norm _).trans hnearNorm
  rw [hmiddle]
  have hsplit :
      (squareRootMertensInt (squareRootEndpoint R) : ℝ) -
          (-(squareRootPositiveSmoothPrimeMertensTransform R).re -
            (squareRootNearPrimeTransport R).re) =
        ((squareRootMertensInt (squareRootEndpoint R) : ℝ) +
            (squareRootPositiveSmoothPrimeMertensTransform R).re) +
          (squareRootNearPrimeTransport R).re := by
    ring
  rw [hsplit]
  calc
    |((squareRootMertensInt (squareRootEndpoint R) : ℝ) +
          (squareRootPositiveSmoothPrimeMertensTransform R).re) +
        (squareRootNearPrimeTransport R).re| ≤
      |(squareRootMertensInt (squareRootEndpoint R) : ℝ) +
          (squareRootPositiveSmoothPrimeMertensTransform R).re| +
        |(squareRootNearPrimeTransport R).re| := abs_add_le _ _
    _ ≤ C * (R : ℝ) + 7 * (R : ℝ) := add_le_add htrack hnearRe
    _ = (C + 7) * (R : ℝ) := by ring

/-- Conversely, the existing middle-tracking proposition implies the clean
ancestral form with the same `7R` constant loss.  Thus the two formulations are
asymptotically identical and differ only by the harmless fixed-width strip. -/
theorem squareRootMertensPositiveTracking_of_middleTracking
    {C : ℝ} {R : ℕ} (hR : 56 ≤ R)
    (htrack : SquareRootMertensMiddleTracking C R) :
    SquareRootMertensPositiveTracking (C + 7) R := by
  unfold SquareRootMertensMiddleTracking at htrack
  unfold SquareRootMertensPositiveTracking
  have hmiddle :=
    squareRootLowPrimeMiddleMertensMass_re_eq_neg_primeTransform_sub_near
      R (by omega)
  have hnearNorm := norm_squareRootNearPrimeTransport_le R hR
  have hnearRe :
      |(squareRootNearPrimeTransport R).re| ≤ 7 * (R : ℝ) :=
    (Complex.abs_re_le_norm _).trans hnearNorm
  rw [hmiddle] at htrack
  have hsplit :
      (squareRootMertensInt (squareRootEndpoint R) : ℝ) +
          (squareRootPositiveSmoothPrimeMertensTransform R).re =
        ((squareRootMertensInt (squareRootEndpoint R) : ℝ) -
            (-(squareRootPositiveSmoothPrimeMertensTransform R).re -
              (squareRootNearPrimeTransport R).re)) -
          (squareRootNearPrimeTransport R).re := by
    ring
  rw [hsplit]
  calc
    |((squareRootMertensInt (squareRootEndpoint R) : ℝ) -
          (-(squareRootPositiveSmoothPrimeMertensTransform R).re -
            (squareRootNearPrimeTransport R).re)) -
        (squareRootNearPrimeTransport R).re| ≤
      |(squareRootMertensInt (squareRootEndpoint R) : ℝ) -
          (-(squareRootPositiveSmoothPrimeMertensTransform R).re -
            (squareRootNearPrimeTransport R).re)| +
        |(squareRootNearPrimeTransport R).re| := by
          simpa [sub_eq_add_neg, abs_neg] using
            (abs_add_le
              ((squareRootMertensInt (squareRootEndpoint R) : ℝ) -
                (-(squareRootPositiveSmoothPrimeMertensTransform R).re -
                  (squareRootNearPrimeTransport R).re))
              (-(squareRootNearPrimeTransport R).re))
    _ ≤ C * (R : ℝ) + 7 * (R : ℝ) := add_le_add htrack hnearRe
    _ = (C + 7) * (R : ℝ) := by ring

/-- The terminal proposition is exactly the real-coordinate Mertens-minus-middle
bound already isolated by the obstruction module. -/
theorem squareRootMertensMiddleTracking_iff_mertensMiddleRealBound
    {C : ℝ} {R : ℕ} :
    SquareRootMertensMiddleTracking C R ↔
      SquareRootLowPrimeMertensMiddleRealBound C R := by
  unfold SquareRootMertensMiddleTracking
    SquareRootLowPrimeMertensMiddleRealBound
  have hre :
      (RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
          squareRootLowPrimeMiddleMertensMass R).re =
        (squareRootMertensInt (squareRootEndpoint R) : ℝ) -
          (squareRootLowPrimeMiddleMertensMass R).re := by
    rw [Complex.sub_re, mertensSummatory_squareRootEndpoint_re]
  rw [hre]

/-- The terminal proposition supplies the minimal matched-core real bound. -/
theorem squareRootLowPrimeMatchedCoreRealBound_of_mertensMiddleTracking
    {C : ℝ} {R : ℕ} (hR : 56 ≤ R)
    (htrack : SquareRootMertensMiddleTracking C R) :
    SquareRootLowPrimeMatchedCoreRealBound C R :=
  (squareRootLowPrimeMatchedCoreRealBound_iff_mertensMiddleRealBound hR).mpr
    (squareRootMertensMiddleTracking_iff_mertensMiddleRealBound.mp htrack)

/-- **The whole low-prime branch, from one open proposition.**

Every structural reduction on the branch — the compressed packet, the four-class
boundary, the classifier, the near-root remainder, the far-survivor bridge and
the seven-coordinate strip — is discharged.  What remains is exactly
`SquareRootMertensMiddleTracking`. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_of_mertensMiddleTracking
    {C : ℝ} {R K j : ℕ} (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (htrack : SquareRootMertensMiddleTracking C R) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤
      (C + 8) * (R : ℝ) + (K : ℝ) :=
  abs_squareRootLowPrimeRunningImbalanceReal_le_of_matchedCoreRealBound
    hR hK hKR hj hV0 hVK
    (squareRootLowPrimeMatchedCoreRealBound_of_mertensMiddleTracking hR htrack)

end RHLean.Proof
