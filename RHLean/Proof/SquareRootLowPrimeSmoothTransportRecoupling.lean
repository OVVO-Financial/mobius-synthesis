import Mathlib
import RHLean.Proof.SquareRootLowPrimeTerminalHighPrimeIntegration
import RHLean.Proof.SquareRootLowPrimeGlobalEnergyTelescope
import RHLean.Proof.SquareRootLowPrimeDefectThresholdBridge
import RHLean.Proof.SquareRootLowPrimeGoWallPartnerReassembly
import RHLean.Proof.SquareRootLowPrimeGoCrossingMateLedger
import RHLean.Proof.SquareRootLowPrimeGoRootEqualityBoundary

/-!
# Recouple the terminal low-prime state to the original smooth/transport residual

The historical square-root architecture is

`S_R = A_R - T_R`,

where `S_R = M(R^2-1)`, `A_R` is the complete smooth mass, and `T_R` is the
upper-prime transport.  The later low-prime sequential construction is a finite
coordinate system for the same signed interaction; it must not create a new
independent low-prime analytic obligation.

An earlier layer already proves that the terminal running imbalance is the matched
born-smooth/transport core minus only the partial crossing packet and the
near-root response rectangle.  This module closes the dictionary back to the
original `A-T` identity and records the quantitative consequence.

At `P_R = R - floor(sqrt R)` we prove exactly

`terminal = M(R^2-1) - PositiveSmooth_R - Packet - NearRoot`,

or, after the positive-orientation collapse,

`terminal = M(R^2-1) + sum_{q <= R prime} M(q-1) - Packet - NearRoot`.

Thus the only non-elementary amplitude left in the terminal state is the old
matched `A-T` core.  The two terminal boundary terms have total norm at most
`R+K`.  Consequently a bound

`||Matched_R|| <= 3 R sqrt(K)`

implies the exact endpoint estimate

`T(P_R)^2 <= 25 R^2 K`,

and hence, through the already-proved exact global telescope, the desired
signed response-child energy decrement.

The final two theorems are conditional on the displayed matched-core bound.
They do not assert that bound and therefore do not claim the remaining
arithmetic cancellation is solved.  Their purpose is to make rigorous that the
remaining quantitative input is the historical signed smooth/transport
correlation, not a separate low-prime frontier estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- The only two terminal terms left outside the historical matched
born-smooth/transport core. -/
def squareRootLowPrimeTerminalShallowBoundary
    (R K j : ℕ) : ℂ :=
  (((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)) +
    squareRootBornPostTailNearRootRemainder R K j

/-- The terminal identity with the two elementary terms packaged as one
shallow boundary. -/
theorem squareRootLowPrimeRunningImbalance_at_cutoff_eq_matched_sub_shallowBoundary
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) =
      squareRootMatchedBornSmoothTransport R -
        squareRootLowPrimeTerminalShallowBoundary R K j := by
  rw [squareRootLowPrimeRunningImbalance_at_cutoff_eq_matched_sub_boundaries
    R K j hR hK hKR hj]
  unfold squareRootLowPrimeTerminalShallowBoundary
  ring

/-- **Recoupling to the original `S=A-T` architecture.**

The terminal low-prime state is the complete square-prefix Mertens residual
minus the positive-orientation smooth contribution and the two already-exposed
shallow boundary terms.  No independent low-prime hard core remains. -/
theorem squareRootLowPrimeRunningImbalance_at_cutoff_eq_squarePrefixMertens_sub_positiveSmooth_sub_boundary
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) =
      RHLean.Analysis.squarePrefixMertens (R - 1) -
        squareRootPositiveSmoothMass R -
        squareRootLowPrimeTerminalShallowBoundary R K j := by
  rw [squareRootLowPrimeRunningImbalance_at_cutoff_eq_matched_sub_shallowBoundary
      R K j hR hK hKR hj,
    squarePrefixMertens_eq_positiveSmooth_add_matched R (by omega)]
  ring

/-- The same recoupling after collapsing the positive orientation to its exact
prime-indexed lower-scale Mertens transform. -/
theorem squareRootLowPrimeRunningImbalance_at_cutoff_eq_squarePrefixMertens_add_positivePrimeTransform_sub_boundary
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) =
      RHLean.Analysis.squarePrefixMertens (R - 1) +
        squareRootPositiveSmoothPrimeMertensTransform R -
        squareRootLowPrimeTerminalShallowBoundary R K j := by
  rw [squareRootLowPrimeRunningImbalance_at_cutoff_eq_squarePrefixMertens_sub_positiveSmooth_sub_boundary
      R K j hR hK hKR hj,
    squareRootPositiveSmoothMass_eq_neg_primeMertensTransform R (by omega)]
  ring

private theorem squareRootCrossingLayerPartialPacket_norm_le_depth_recoupled
    {R K j : ℕ}
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ ≤
      (K : ℝ) := by
  rw [Complex.norm_intCast, abs_of_nonneg]
  · exact_mod_cast Int.le_of_lt hVK
  · exact_mod_cast hV0

/-- The recoupled terminal boundary is elementary: packet `< K` plus the
near-root rectangle `<= R`. -/
theorem norm_squareRootLowPrimeTerminalShallowBoundary_le_root_add_depth
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    ‖squareRootLowPrimeTerminalShallowBoundary R K j‖ ≤
      (R : ℝ) + (K : ℝ) := by
  unfold squareRootLowPrimeTerminalShallowBoundary
  have hpacket :=
    squareRootCrossingLayerPartialPacket_norm_le_depth_recoupled hV0 hVK
  have hnear := squareRootBornPostTailNearRootRemainder_norm_le_root
    R K j (by omega) hK hKR hj
  calc
    ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) +
        squareRootBornPostTailNearRootRemainder R K j‖ ≤
      ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ +
        ‖squareRootBornPostTailNearRootRemainder R K j‖ :=
      norm_add_le _ _
    _ ≤ (K : ℝ) + (R : ℝ) := add_le_add hpacket hnear
    _ = (R : ℝ) + (K : ℝ) := by ring

/-- Quantitative form of the recoupling: the terminal state differs from the
old matched `A-T` core by at most `R+K`. -/
theorem norm_squareRootLowPrimeRunningImbalance_sub_matched_le_root_add_depth
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    ‖squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
      squareRootMatchedBornSmoothTransport R‖ ≤
        (R : ℝ) + (K : ℝ) := by
  rw [squareRootLowPrimeRunningImbalance_at_cutoff_eq_matched_sub_shallowBoundary
    R K j hR hK hKR hj]
  have hboundary :=
    norm_squareRootLowPrimeTerminalShallowBoundary_le_root_add_depth
      R K j hR hK hKR hj hV0 hVK
  have hEq :
      (squareRootMatchedBornSmoothTransport R -
          squareRootLowPrimeTerminalShallowBoundary R K j) -
        squareRootMatchedBornSmoothTransport R =
      -squareRootLowPrimeTerminalShallowBoundary R K j := by
    ring
  rw [hEq, norm_neg]
  exact hboundary

/-- The terminal amplitude is controlled by the historical matched core plus
only the elementary `R+K` boundary. -/
theorem norm_squareRootLowPrimeRunningImbalance_le_matched_add_root_add_depth
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    ‖squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R)‖ ≤
      ‖squareRootMatchedBornSmoothTransport R‖ +
        ((R : ℝ) + (K : ℝ)) := by
  have hdiff :=
    norm_squareRootLowPrimeRunningImbalance_sub_matched_le_root_add_depth
      R K j hR hK hKR hj hV0 hVK
  calc
    ‖squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R)‖ =
      ‖(squareRootLowPrimeRunningImbalance R K j
          (squareRootBornPostTailLowPrimeCutoff R) -
          squareRootMatchedBornSmoothTransport R) +
        squareRootMatchedBornSmoothTransport R‖ := by
      congr 1
      ring
    _ ≤ ‖squareRootLowPrimeRunningImbalance R K j
          (squareRootBornPostTailLowPrimeCutoff R) -
          squareRootMatchedBornSmoothTransport R‖ +
        ‖squareRootMatchedBornSmoothTransport R‖ := norm_add_le _ _
    _ ≤ ((R : ℝ) + (K : ℝ)) +
        ‖squareRootMatchedBornSmoothTransport R‖ :=
      add_le_add_right hdiff _
    _ = ‖squareRootMatchedBornSmoothTransport R‖ +
        ((R : ℝ) + (K : ℝ)) := by ring

/-- A `3 R sqrt(K)` estimate for the old signed matched core is already enough
for the `5 R sqrt(K)` terminal amplitude required by the `25 R^2 K` energy
remainder.  This is a sufficient-condition theorem, not a proof of the matched
estimate. -/
theorem norm_squareRootLowPrimeRunningImbalance_le_five_root_sqrt_depth_of_matched
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (hmatched : ‖squareRootMatchedBornSmoothTransport R‖ ≤
      3 * (R : ℝ) * Real.sqrt (K : ℝ)) :
    ‖squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R)‖ ≤
      5 * (R : ℝ) * Real.sqrt (K : ℝ) := by
  have hterminal :=
    norm_squareRootLowPrimeRunningImbalance_le_matched_add_root_add_depth
      R K j hR hK hKR hj hV0 hVK
  have hKreal : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKRreal : (K : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hKR)
  have hsqrt0 : 0 ≤ Real.sqrt (K : ℝ) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (K : ℝ)) ^ 2 = (K : ℝ) := by
    rw [Real.sq_sqrt (by positivity)]
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (K : ℝ) := by
    nlinarith
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
  have hRsqrt : (R : ℝ) ≤ (R : ℝ) * Real.sqrt (K : ℝ) := by
    nlinarith [mul_nonneg hR0 (sub_nonneg.mpr hsqrt1)]
  have hboundaryScale :
      (R : ℝ) + (K : ℝ) ≤
        2 * (R : ℝ) * Real.sqrt (K : ℝ) := by
    nlinarith
  linarith

/-- **Terminal square reduction to the old `A-T` core.**  Under the same
matched-core input, the actual terminal running state has precisely the
`25 R^2 K` square bound used by the signed-energy target. -/
theorem squareRootLowPrimeRunningImbalanceReal_sq_le_twentyfive_root_sq_depth_of_matched
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (hmatched : ‖squareRootMatchedBornSmoothTransport R‖ ≤
      3 * (R : ℝ) * Real.sqrt (K : ℝ)) :
    squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) ^ 2 ≤
      25 * (R : ℝ) ^ 2 * (K : ℝ) := by
  have hnorm :=
    norm_squareRootLowPrimeRunningImbalance_le_five_root_sqrt_depth_of_matched
      R K j hR hK hKR hj hV0 hVK hmatched
  have hre := Complex.abs_re_le_norm
    (squareRootLowPrimeRunningImbalance R K j
      (squareRootBornPostTailLowPrimeCutoff R))
  have habs :
      |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤
        5 * (R : ℝ) * Real.sqrt (K : ℝ) := by
    exact hre.trans hnorm
  have hsqrtSq : (Real.sqrt (K : ℝ)) ^ 2 = (K : ℝ) := by
    rw [Real.sq_sqrt (by positivity)]
  have hright : 0 ≤ 5 * (R : ℝ) * Real.sqrt (K : ℝ) := by positivity
  have hsquare :
      |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ^ 2 ≤
        (5 * (R : ℝ) * Real.sqrt (K : ℝ)) ^ 2 := by
    nlinarith [abs_nonneg
      (squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R))]
  calc
    squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) ^ 2 =
      |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ^ 2 := by
      simp [sq_abs]
    _ ≤ (5 * (R : ℝ) * Real.sqrt (K : ℝ)) ^ 2 := hsquare
    _ = 25 * (R : ℝ) ^ 2 * (K : ℝ) := by
      rw [mul_pow, mul_pow, hsqrtSq]
      ring

/-- **Signed response-child energy reduction to the old smooth/transport
correlation.**  Once the historical matched `A-T` core satisfies the displayed
`3 R sqrt(K)` bound, the desired sequential energy decrement follows with the
exact `25 R^2 K` remainder.  There is no additional low-prime analytic premise. -/
theorem squareRootLowPrimeSignedResponseEnergy_decrement_ge_of_matched
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hKU : K ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (hmatched : ‖squareRootMatchedBornSmoothTransport R‖ ≤
      3 * (R : ℝ) * Real.sqrt (K : ℝ)) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet K
        (squareRootBornPostTailLowPrimeCutoff R),
      (2 * squareRootLowPrimeRunningImbalanceReal R K j (p - 1) *
          squareRootLowPrimeFreshIncrementReal R K j p -
        squareRootLowPrimeFreshIncrementReal R K j p ^ 2)) ≥
      squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        25 * (R : ℝ) ^ 2 * (K : ℝ) := by
  have hterminal :=
    squareRootLowPrimeRunningImbalanceReal_sq_le_twentyfive_root_sq_depth_of_matched
      R K j hR hK hKR hj hV0 hVK hmatched
  exact squareRootLowPrimeGlobalEnergyDecrement_ge_of_terminal_sq_le
    (R := R) (K := K) (j := j)
    (U := squareRootBornPostTailLowPrimeCutoff R)
    (25 * (R : ℝ) ^ 2 * (K : ℝ)) hK hKU hterminal

/-! ## Cross-coordinate square-root intertwiner -/

/-- The literal canonical processed-seat terminal frontier and the historical
matched smooth/transport coordinate are the same signed state after removing
only the already-exposed shallow boundary.  This is the occurrence-level
Othello-to-`A-T` edge of the cross-coordinate diagram. -/
theorem squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier_weight_sum_eq_matched_sub_shallowBoundary_re
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier
        R K j (squareRootBornPostTailLowPrimeCutoff R),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      (squareRootMatchedBornSmoothTransport R -
        squareRootLowPrimeTerminalShallowBoundary R K j).re := by
  calc
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier
        R K j (squareRootBornPostTailLowPrimeCutoff R),
      squareRootLowPrimeProcessedSeatWeightReal x) =
        squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) :=
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier_weight_sum
        (R := R) (K := K) (j := j)
        (U := squareRootBornPostTailLowPrimeCutoff R) (by omega)
    _ = (squareRootMatchedBornSmoothTransport R -
          squareRootLowPrimeTerminalShallowBoundary R K j).re := by
      have h := congrArg Complex.re
        (squareRootLowPrimeRunningImbalance_at_cutoff_eq_matched_sub_shallowBoundary
          R K j hR hK hKR hj)
      simpa [squareRootLowPrimeRunningImbalanceReal] using h

/-- A single proposition carrying all exact maps needed to identify the
square-root obstruction across the Born/high, processed-seat, literal Go-wall,
and tagged transport coordinates.

The fixed prime `p` is the fresh wall coordinate used by the literal
first-owner wall carrier. -/
structure SquareRootLowPrimeCrossCoordinateIntertwiner
    (R K j p : ℕ) : Prop where
  postRootThreshold :
    ∀ a r : ℕ,
      r ∈ squareRootPostRootPrimePartnerProductBoundary R a (p * a) ↔
        r ∈ squareRootPostRootPrimePartnerSet R a ∧
          squareRootLowPrimeThresholdCrosses p (squareRootEndpoint R / r) a
  bornThreshold :
    ∀ a r : ℕ,
      r ∈ squareRootBornPartnerBirthBoundary R a (p * a) ↔
        r ∈ squareRootBornPartnerSet R (p * a) ∧
          squareRootLowPrimeThresholdCrosses p (r - 1) a
  processedTerminalToMatched :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier
        R K j (squareRootBornPostTailLowPrimeCutoff R),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      (squareRootMatchedBornSmoothTransport R -
        squareRootLowPrimeTerminalShallowBoundary R K j).re
  terminalToMatched :
    squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) =
      squareRootMatchedBornSmoothTransport R -
        squareRootLowPrimeTerminalShallowBoundary R K j
  literalWallCarrier :
    squareRootLowPrimeWallPairCarrierCofactorFirst R K p =
      squareRootLowPrimeWallPairCarrierOldPrimeFirst R K p
  literalWallReassembly :
    squareRootLowPrimeLiteralWallFalloutMass R K p =
      squareRootLowPrimeLiteralWallResidualFalloutMass R K +
        squareRootLowPrimeLiteralWallPartnerFalloutMass R K p
  goSourceInjective :
    Function.Injective squareRootLowPrimeGoStrictCrossingSourceTag
  goMateInjective :
    Set.InjOn squareRootLowPrimeGoStrictCrossingMateTag
      (squareRootLowPrimeGoStrictCrossingCarrier R)
  goSourceInTransport :
    squareRootLowPrimeGoStrictCrossingSourceImage R ⊆
      lowWheelCanonicalTaggedPhysicalCarrier R
  goMateInTransport :
    squareRootLowPrimeGoStrictCrossingMateImage R ⊆
      lowWheelCanonicalTaggedPhysicalCarrier R
  goImagesDisjoint :
    Disjoint
      (squareRootLowPrimeGoStrictCrossingSourceImage R)
      (squareRootLowPrimeGoStrictCrossingMateImage R)
  goStrictCancellation :
    ((squareRootLowPrimeGoStrictCrossingSourceMass R : ℤ) : ℂ) +
      squareRootLowPrimeGoStrictCrossingMateLedger R = 0
  goRootEqualityCard :
    (squareRootLowPrimeGoRootEqualityDefectCarrier R).card ≤ R
  goRootEqualityMass :
    |squareRootLowPrimeGoRootEqualityDefectMass R| ≤ (R : ℤ)
  shallowBoundaryBound :
    ‖squareRootLowPrimeTerminalShallowBoundary R K j‖ ≤
      (R : ℝ) + (K : ℝ)

/-- **Cross-coordinate square-root intertwiner.**

Under the native terminal packet hypotheses and one fresh wall prime
`K < p < R`, every structural edge in the diagram above is simultaneously
realized.  The old high response has not disappeared while a new low
obstruction appeared: both sides have been transported to the same
threshold/first-owner/Go coordinates, while the terminal signed state remains
exactly the historical matched `A-T` core modulo the explicit shallow boundary.
-/
theorem squareRootLowPrime_crossCoordinateIntertwiner
    (R K j p : ℕ)
    (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hp : p.Prime) (hKp : K < p) (hpR : p < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    SquareRootLowPrimeCrossCoordinateIntertwiner R K j p := by
  have hR2 : 2 ≤ R := by omega
  refine
    { postRootThreshold := ?_
      bornThreshold := ?_
      processedTerminalToMatched := ?_
      terminalToMatched := ?_
      literalWallCarrier := ?_
      literalWallReassembly := ?_
      goSourceInjective := ?_
      goMateInjective := ?_
      goSourceInTransport := ?_
      goMateInTransport := ?_
      goImagesDisjoint := ?_
      goStrictCancellation := ?_
      goRootEqualityCard := ?_
      goRootEqualityMass := ?_
      shallowBoundaryBound := ?_ }
  · intro a r
    exact mem_squareRootPostRootPrimePartnerProductBoundary_iff_thresholdCrosses
  · intro a r
    exact mem_squareRootBornPartnerBirthBoundary_iff_thresholdCrosses
  · exact
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier_weight_sum_eq_matched_sub_shallowBoundary_re
        R K j hR hK hKR hj
  · exact
      squareRootLowPrimeRunningImbalance_at_cutoff_eq_matched_sub_shallowBoundary
        R K j hR hK hKR hj
  · exact
      squareRootLowPrimeWallPairCarrierCofactorFirst_eq_oldPrimeFirst
        hR2 hp hKp hpR
  · exact
      squareRootLowPrimeLiteralWallFalloutMass_eq_residual_add_partner
        hR2 hp hKp hpR
  · exact squareRootLowPrimeGoStrictCrossingSourceTag_injective
  · exact squareRootLowPrimeGoStrictCrossingMateTag_injOn R
  · exact squareRootLowPrimeGoStrictCrossingSourceImage_subset_transport hR2
  · exact squareRootLowPrimeGoStrictCrossingMateImage_subset_transport hR2
  · exact squareRootLowPrimeGoStrictCrossingImages_disjoint R
  · exact squareRootLowPrimeGoStrictCrossingMass_add_existingMate_eq_zero hR2
  · exact squareRootLowPrimeGoRootEqualityDefectCarrier_card_le_root R
  · exact abs_squareRootLowPrimeGoRootEqualityDefectMass_le_root R
  · exact
      norm_squareRootLowPrimeTerminalShallowBoundary_le_root_add_depth
        R K j hR hK hKR hj hV0 hVK

end RHLean.Proof
