import Mathlib
import RHLean.Proof.SquareRootLowPrimeSequentialDissipationOwnership
import RHLean.Proof.SquareRootLowPrimeDeepResponseAtoms
import RHLean.Proof.LowWheelCanonicalDefectReduction
import RHLean.Analysis.SquareRootPositiveSmoothCollapse
import RHLean.Proof.MatchedFarSurvivorBridge

/-!
# Full low-prime response as a canonical signed frontier

The sequential dissipation modules split every actual fresh-prime increment as

`Delta_p = -D_p + F_p`

and assign the complete positive-orientation response mass to its unique
largest-prime owner.  That support theorem does not make the response weight of
one cofactor small.  The correct next operation is to retain the signed response
and connect it to the repository's atom-level cancellation coordinates.

This file makes two exact terminal connections at

`P_R = R - floor(sqrt R)`.

First, it synthesizes:

* the low-prime collapse of `BornPostTail`;
* `BornPostTail = matched born/transport - partial crossing packet`;
* the positive-smooth prime-Mertens collapse;
* the canonical transport involution
  `M(R^2-1) = M(R) - canonicalDowncross`.

This identifies the complete processed response, and therefore the final
running imbalance, with the canonical adjacent root-downcross ledger plus only
explicit lower-scale terms, the partial crossing packet, and the near-root
remainder.

Second, the far-upper rigidity bridge rewrites the same complete terminal state
as

`bornSmooth + farSurvivor`

minus only the seven-coordinate root strip, the partial crossing packet, and
the near-root rectangle.  Under the usual crossing-residual hypotheses, the
entire discrepancy from that one signed pair is at most `8*R + K`.

Thus the transition-seat shell is not declared to be the complete bad
frontier, and the raw positive mass `F_p` is not estimated separately.  The
remaining hard object is one signed born-smooth / far-survivor interaction.

No bound on that hard pair, no energy decrement, no PNT estimate, no Mertens
hypothesis, and no RH implication is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- The lower-scale and canonical-frontier core of the terminal running
imbalance.  The only omitted term is the positive near-root remainder. -/
def squareRootLowPrimeCanonicalTerminalCore
    (R K j : ℕ) : ℂ :=
  mertensSummatory R - lowWheelCanonicalDowncrossLedger R +
    squareRootPositiveSmoothPrimeMertensTransform R -
      ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)

/-- **Full processed-response / canonical-frontier bridge.**

The entire low-prime processed response—not merely the transition-seat
component—is the canonical root-downcross ledger together with explicit
lower-scale terms and the already-controlled near-root remainder. -/
theorem squareRootBornPostTailLowPrimeProcessedResponse_eq_canonicalFrontier
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootBornPostTailLowPrimeProcessedResponse R K j =
      1 - mertensSummatory R + lowWheelCanonicalDowncrossLedger R -
        squareRootPositiveSmoothPrimeMertensTransform R +
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) +
        squareRootBornPostTailNearRootRemainder R K j := by
  have hcollapse :=
    squareRootBornPostTail_eq_one_sub_lowPrimeProcessedResponse_add_nearRootRemainder
      R K j hR hK hKR hj
  have hmatched :=
    squareRootBornPostTail_eq_matched_sub_partial R K j (by omega)
  have hpositive :=
    squarePrefixMertens_eq_neg_positivePrimeTransform_add_matched
      R (by omega)
  have hdowncross :=
    squarePrefixMertens_eq_mertens_sub_canonicalDowncross R (by omega)
  linear_combination hcollapse - hmatched + hpositive - hdowncross

/-- Terminal running imbalance in the exact canonical-frontier coordinates. -/
theorem squareRootLowPrimeRunningImbalance_at_cutoff_eq_canonicalFrontier
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) =
      squareRootLowPrimeCanonicalTerminalCore R K j -
        squareRootBornPostTailNearRootRemainder R K j := by
  unfold squareRootLowPrimeRunningImbalance
    squareRootLowPrimeCanonicalTerminalCore
  rw [squareRootBornPostTailRunningLowPrimeResponse_at_cutoff]
  rw [squareRootBornPostTailLowPrimeProcessedResponse_eq_canonicalFrontier
    R K j hR hK hKR hj]
  ring

/-- **Quantitative canonical-frontier reduction.**  After the complete signed
low-prime response is synthesized with the canonical involution, the discrepancy
from the explicit canonical core is at most `R`.  This does not estimate the
canonical downcross ledger itself. -/
theorem squareRootLowPrimeRunningImbalance_sub_canonicalCore_norm_le_root
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    ‖squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
      squareRootLowPrimeCanonicalTerminalCore R K j‖ ≤ (R : ℝ) := by
  rw [squareRootLowPrimeRunningImbalance_at_cutoff_eq_canonicalFrontier
    R K j hR hK hKR hj]
  have hnear := squareRootBornPostTailNearRootRemainder_norm_le_root
    R K j hR hK hKR hj
  simpa using hnear

/-! ## The same complete terminal response in far-survivor coordinates -/

/-- The one signed interaction left after the far-upper transport rigidity
cancels every upper-prime coordinate except the bounded root strip. -/
def squareRootLowPrimeFarSurvivorTerminalCore (R : ℕ) : ℂ :=
  squareRootBornSmoothMass R +
    survivorSixteenFarUpperPrimeMass (R - 1)

/-- **Exact full-response localization.**  The terminal running imbalance is
the born-smooth / far-survivor signed pair minus only three explicit boundaries:
the seven-coordinate near-prime strip, the partial crossing packet, and the
near-root low-prime remainder. -/
theorem squareRootLowPrimeRunningImbalance_at_cutoff_eq_farSurvivorCore_sub_boundaries
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) =
      squareRootLowPrimeFarSurvivorTerminalCore R -
        squareRootNearPrimeTransport R -
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) -
        squareRootBornPostTailNearRootRemainder R K j := by
  unfold squareRootLowPrimeRunningImbalance
    squareRootLowPrimeFarSurvivorTerminalCore
  rw [squareRootBornPostTailRunningLowPrimeResponse_at_cutoff]
  have hcollapse :=
    squareRootBornPostTail_eq_one_sub_lowPrimeProcessedResponse_add_nearRootRemainder
      R K j (by omega) hK hKR hj
  have hmatched :=
    squareRootBornPostTail_eq_matched_sub_partial R K j (by omega)
  have hfar :=
    squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_farSurvivor_sub_near
      R hR
  linear_combination -hcollapse + hmatched + hfar

private theorem squareRootCrossingLayerPartialPacket_norm_le_depth
    {R K j : ℕ}
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ ≤
      (K : ℝ) := by
  rw [Complex.norm_intCast, abs_of_nonneg]
  · exact_mod_cast Int.le_of_lt hVK
  · exact_mod_cast hV0

/-- **Quantitative localization of the complete terminal response.**  Under the
actual crossing-residual inequalities, everything outside the one signed
born-smooth / far-survivor pair has norm at most `8*R + K`.

This is a bound on all explicit boundaries after signed synthesis.  It is not a
bound on the remaining hard pair. -/
theorem squareRootLowPrimeRunningImbalance_sub_farSurvivorCore_norm_le
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    ‖squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
      squareRootLowPrimeFarSurvivorTerminalCore R‖ ≤
        8 * (R : ℝ) + (K : ℝ) := by
  rw [squareRootLowPrimeRunningImbalance_at_cutoff_eq_farSurvivorCore_sub_boundaries
    R K j hR hK hKR hj]
  have htransport := norm_squareRootNearPrimeTransport_le R hR
  have hpartial := squareRootCrossingLayerPartialPacket_norm_le_depth hV0 hVK
  have hnear := squareRootBornPostTailNearRootRemainder_norm_le_root
    R K j (by omega) hK hKR hj
  have hfirst :
      ‖-squareRootNearPrimeTransport R -
          ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ ≤
        ‖squareRootNearPrimeTransport R‖ +
          ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ := by
    simpa only [norm_neg] using
      norm_sub_le (-squareRootNearPrimeTransport R)
        (((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ))
  calc
    ‖(squareRootLowPrimeFarSurvivorTerminalCore R -
          squareRootNearPrimeTransport R -
          ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) -
          squareRootBornPostTailNearRootRemainder R K j) -
        squareRootLowPrimeFarSurvivorTerminalCore R‖ =
      ‖(-squareRootNearPrimeTransport R -
          ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)) -
        squareRootBornPostTailNearRootRemainder R K j‖ := by
          congr 1
          ring
    _ ≤ ‖-squareRootNearPrimeTransport R -
          ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ +
        ‖squareRootBornPostTailNearRootRemainder R K j‖ :=
      norm_sub_le _ _
    _ ≤ (‖squareRootNearPrimeTransport R‖ +
          ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖) +
        ‖squareRootBornPostTailNearRootRemainder R K j‖ :=
      add_le_add_right hfirst _
    _ ≤ (7 * (R : ℝ) + (K : ℝ)) + (R : ℝ) :=
      add_le_add (add_le_add htransport hpartial) hnear
    _ = 8 * (R : ℝ) + (K : ℝ) := by ring

end RHLean.Proof
