import Mathlib
import RHLean.Proof.SquareRootLowPrimeQuantitativeEnergyReduction
import RHLean.Proof.SquareRootLowPrimeCanonicalLiberty
import RHLean.Proof.LowWheelExternalTerminalEightRootBound

/-!
# Integrate the external high-prime closure into the terminal processed state

The terminal processed-state bridge already localizes the running imbalance at

`P_R = R - floor(sqrt R)`

to the signed pair

`BornSmooth_R + FarSurvivor_R`

minus three explicit boundaries: the seven-coordinate near-prime strip, the
partial crossing packet, and the near-root response rectangle.

The external high-prime theorem now gives more than a stand-alone `8R` bound.
On the very same high-prime carrier it proves the exact parent split

`T_R = ERuniq_R + ERrep_R`

and the signed recombination

`ERrep_R + FarSurvivor_R = Near_R - ERuniq_R`.

At the terminal processed state the `Near_R` term is already present with the
opposite sign.  Therefore the entire integrated external boundary is exactly
`-ERuniq_R`, whose norm is at most `R`.  No second charge for the near strip is
needed.

Consequently the terminal running state differs from the single integrated core

`BornSmooth_R - ERrep_R`

by only

* the unique-parent external mass, bounded by `R`;
* the already-shallow partial packet, bounded by `K` under its native range
  hypotheses; and
* the near-root response rectangle, bounded by `R`.

Thus the full terminal discrepancy is at most `2R + K`.  The same statement is
proved below directly on the canonical terminal processed frontier, not merely
on an abstract analytic coordinate.

Finally, the integrated core is shown to be the repository's old matched
born-smooth/transport core plus `ERuniq`.  This is an audit theorem: the
integration introduces no new hard population.  It does **not** prove the final
signed energy inequality.  In particular, the endpoint-transfer lemmas below
are bookkeeping consequences only; they must not be substituted for an
independent signed dissipation estimate.

No PNT input, asymptotic estimate, further Euler descent, or independent norm of
an already-cancelled population is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- The signed core left after the external repeated-parent high-prime mass is
inserted into the terminal processed identity. -/
def squareRootLowPrimeIntegratedTerminalCore (R : ℕ) : ℂ :=
  squareRootBornSmoothMass R - squareRootERrep R

/-- Real coordinate of the integrated terminal core. -/
def squareRootLowPrimeIntegratedTerminalCoreReal (R : ℕ) : ℝ :=
  (squareRootLowPrimeIntegratedTerminalCore R).re

/-- The external repeated/far-survivor combination cancels the near-prime strip
already present in the terminal identity.  The whole inserted high-prime
boundary is therefore exactly the negative unique-parent mass. -/
theorem squareRootERrep_add_farSurvivor_sub_near_eq_neg_ERuniq
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootERrep R + survivorSixteenFarUpperPrimeMass (R - 1) -
        squareRootNearPrimeTransport R =
      -squareRootERuniq R := by
  rw [squareRootERrep_add_farSurvivor_eq_near_sub_ERuniq R hR]
  ring

/-- Quantitative form of the integrated high-prime boundary.  In the terminal
processed state the new high-prime closure costs only the already-owned unique
parent budget `R`. -/
theorem norm_squareRootERrep_add_farSurvivor_sub_near_le_root
    (R : ℕ) (hR : 56 ≤ R) :
    ‖squareRootERrep R + survivorSixteenFarUpperPrimeMass (R - 1) -
        squareRootNearPrimeTransport R‖ ≤ (R : ℝ) := by
  rw [squareRootERrep_add_farSurvivor_sub_near_eq_neg_ERuniq R hR, norm_neg]
  exact norm_squareRootERuniq_le_root R

/-- **Exact terminal high-prime integration.**

After the `ERrep + FarSurvivor` recombination is inserted into the already
localized terminal processed state, the seven-coordinate near strip disappears
exactly.  What remains is the signed core `BornSmooth - ERrep`, followed only by
the unique-parent mass, the partial crossing packet, and the near-root
remainder. -/
theorem squareRootLowPrimeRunningImbalance_at_cutoff_eq_integratedCore_sub_boundaries
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) =
      squareRootLowPrimeIntegratedTerminalCore R -
        squareRootERuniq R -
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) -
        squareRootBornPostTailNearRootRemainder R K j := by
  have hterminal :=
    squareRootLowPrimeRunningImbalance_at_cutoff_eq_farSurvivorCore_sub_boundaries
      R K j hR hK hKR hj
  have hhigh :=
    squareRootERrep_add_farSurvivor_eq_near_sub_ERuniq R hR
  unfold squareRootLowPrimeFarSurvivorTerminalCore at hterminal
  unfold squareRootLowPrimeIntegratedTerminalCore
  linear_combination hterminal + hhigh

/-- **No-new-core audit.**  The integrated core is exactly the historical
matched born-smooth/transport object plus the already-owned unique-parent
external mass.  Thus the high-prime integration changes the bookkeeping, not
the underlying hard signed population. -/
theorem squareRootLowPrimeIntegratedTerminalCore_eq_matched_add_ERuniq
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootLowPrimeIntegratedTerminalCore R =
      squareRootMatchedBornSmoothTransport R + squareRootERuniq R := by
  unfold squareRootLowPrimeIntegratedTerminalCore
  rw [squareRootMatchedBornSmoothTransport_eq_bornSmooth_sub_transport,
    squareRootTransport_eq_ERuniq_add_ERrep R hR]
  ring

/-- After the ownership term is cancelled in the full terminal identity, the
same state is the old matched signed core minus only the shallow partial packet
and the near-root rectangle.  This theorem is included to certify that the
integration has not hidden or duplicated a population. -/
theorem squareRootLowPrimeRunningImbalance_at_cutoff_eq_matched_sub_boundaries
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) =
      squareRootMatchedBornSmoothTransport R -
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) -
        squareRootBornPostTailNearRootRemainder R K j := by
  rw [squareRootLowPrimeRunningImbalance_at_cutoff_eq_integratedCore_sub_boundaries
      R K j hR hK hKR hj,
    squareRootLowPrimeIntegratedTerminalCore_eq_matched_add_ERuniq R (by omega)]
  ring

private theorem squareRootCrossingLayerPartialPacket_norm_le_depth_integrated
    {R K j : ℕ}
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ ≤
      (K : ℝ) := by
  rw [Complex.norm_intCast, abs_of_nonneg]
  · exact_mod_cast Int.le_of_lt hVK
  · exact_mod_cast hV0

/-- **Quantitative terminal integration.**  Everything outside the one signed
core `BornSmooth - ERrep` is now elementary root scale.  The former `8R` high
prime closure and the pre-existing near strip combine before any norm is taken,
leaving only one `R` unique-parent charge. -/
theorem squareRootLowPrimeRunningImbalance_sub_integratedCore_norm_le
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    ‖squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
      squareRootLowPrimeIntegratedTerminalCore R‖ ≤
        2 * (R : ℝ) + (K : ℝ) := by
  rw [squareRootLowPrimeRunningImbalance_at_cutoff_eq_integratedCore_sub_boundaries
    R K j hR hK hKR hj]
  have huniq := norm_squareRootERuniq_le_root R
  have hpartial :=
    squareRootCrossingLayerPartialPacket_norm_le_depth_integrated hV0 hVK
  have hnear := squareRootBornPostTailNearRootRemainder_norm_le_root
    R K j (by omega) hK hKR hj
  have hfirst :
      ‖-squareRootERuniq R -
          ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ ≤
        ‖squareRootERuniq R‖ +
          ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ := by
    simpa only [norm_neg] using
      norm_sub_le (-squareRootERuniq R)
        (((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ))
  calc
    ‖(squareRootLowPrimeIntegratedTerminalCore R -
          squareRootERuniq R -
          ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) -
          squareRootBornPostTailNearRootRemainder R K j) -
        squareRootLowPrimeIntegratedTerminalCore R‖ =
      ‖(-squareRootERuniq R -
          ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)) -
        squareRootBornPostTailNearRootRemainder R K j‖ := by
          congr 1
          ring
    _ ≤ ‖-squareRootERuniq R -
          ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ +
        ‖squareRootBornPostTailNearRootRemainder R K j‖ :=
      norm_sub_le _ _
    _ ≤ (‖squareRootERuniq R‖ +
          ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖) +
        ‖squareRootBornPostTailNearRootRemainder R K j‖ :=
      add_le_add_right hfirst _
    _ ≤ ((R : ℝ) + (K : ℝ)) + (R : ℝ) :=
      add_le_add (add_le_add huniq hpartial) hnear
    _ = 2 * (R : ℝ) + (K : ℝ) := by ring

private theorem abs_re_sub_le_norm_sub_integrated (z w : ℂ) :
    |z.re - w.re| ≤ ‖z - w‖ := by
  have h := Complex.abs_re_le_norm (z - w)
  simpa using h

/-- Real terminal state differs from the integrated signed core by at most
`2R + K`. -/
theorem squareRootLowPrimeRunningImbalanceReal_sub_integratedCore_abs_le
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
      squareRootLowPrimeIntegratedTerminalCoreReal R| ≤
        2 * (R : ℝ) + (K : ℝ) := by
  exact (abs_re_sub_le_norm_sub_integrated
    (squareRootLowPrimeRunningImbalance R K j
      (squareRootBornPostTailLowPrimeCutoff R))
    (squareRootLowPrimeIntegratedTerminalCore R)).trans
      (squareRootLowPrimeRunningImbalance_sub_integratedCore_norm_le
        R K j hR hK hKR hj hV0 hVK)

/-- **Integration on the literal canonical terminal processed carrier.**  Its
signed mass is the integrated core plus only the three explicit boundary terms.
This is the finite processed-state form needed by the subsequent signed-energy
argument. -/
theorem squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier_weight_sum_eq_integrated
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier
        R K j (squareRootBornPostTailLowPrimeCutoff R),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeIntegratedTerminalCoreReal R -
        (squareRootERuniq R).re -
        (((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)).re -
        (squareRootBornPostTailNearRootRemainder R K j).re := by
  calc
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier
        R K j (squareRootBornPostTailLowPrimeCutoff R),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) :=
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier_weight_sum
        (R := R) (K := K) (j := j)
        (U := squareRootBornPostTailLowPrimeCutoff R) (by omega)
    _ = squareRootLowPrimeIntegratedTerminalCoreReal R -
        (squareRootERuniq R).re -
        (((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)).re -
        (squareRootBornPostTailNearRootRemainder R K j).re := by
      have h := congrArg Complex.re
        (squareRootLowPrimeRunningImbalance_at_cutoff_eq_integratedCore_sub_boundaries
          R K j hR hK hKR hj)
      simpa [squareRootLowPrimeRunningImbalanceReal,
        squareRootLowPrimeIntegratedTerminalCoreReal] using h

/-- The literal canonical terminal processed frontier is within `2R + K` of the
single integrated signed core.  This is the quantitative integration theorem on
the actual finite carrier. -/
theorem abs_squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier_sub_integratedCore_le
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    |(∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier
          R K j (squareRootBornPostTailLowPrimeCutoff R),
        squareRootLowPrimeProcessedSeatWeightReal x) -
      squareRootLowPrimeIntegratedTerminalCoreReal R| ≤
        2 * (R : ℝ) + (K : ℝ) := by
  rw [squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier_weight_sum
    (R := R) (K := K) (j := j)
    (U := squareRootBornPostTailLowPrimeCutoff R) (by omega)]
  exact squareRootLowPrimeRunningImbalanceReal_sub_integratedCore_abs_le
    R K j hR hK hKR hj hV0 hVK

/-- Any absolute bound for the integrated signed core transfers immediately to
the full terminal processed state.  This is a terminal transfer lemma only, not
the final independent signed-energy inequality. -/
theorem squareRootLowPrimeRunningImbalanceReal_abs_le_of_integratedCore
    (R K j : ℕ) (B : ℝ)
    (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (hcore : |squareRootLowPrimeIntegratedTerminalCoreReal R| ≤ B) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤
      B + (2 * (R : ℝ) + (K : ℝ)) := by
  have hdiff :=
    squareRootLowPrimeRunningImbalanceReal_sub_integratedCore_abs_le
      R K j hR hK hKR hj hV0 hVK
  calc
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| =
      |(squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) -
        squareRootLowPrimeIntegratedTerminalCoreReal R) +
        squareRootLowPrimeIntegratedTerminalCoreReal R| := by ring_nf
    _ ≤ |squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) -
        squareRootLowPrimeIntegratedTerminalCoreReal R| +
          |squareRootLowPrimeIntegratedTerminalCoreReal R| :=
      abs_add_le _ _
    _ ≤ (2 * (R : ℝ) + (K : ℝ)) +
          |squareRootLowPrimeIntegratedTerminalCoreReal R| :=
      add_le_add_right hdiff _
    _ ≤ (2 * (R : ℝ) + (K : ℝ)) + B :=
      add_le_add_left hcore _
    _ = B + (2 * (R : ℝ) + (K : ℝ)) := by ring

/-- Squared terminal-state transfer.  This is again only endpoint bookkeeping:
the independent global signed-energy decrement remains the next theorem to be
proved. -/
theorem squareRootLowPrimeRunningImbalanceReal_sq_le_of_integratedCore
    (R K j : ℕ) (B : ℝ)
    (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (hB : 0 ≤ B)
    (hcore : |squareRootLowPrimeIntegratedTerminalCoreReal R| ≤ B) :
    squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) ^ 2 ≤
      (B + (2 * (R : ℝ) + (K : ℝ))) ^ 2 := by
  have habs :=
    squareRootLowPrimeRunningImbalanceReal_abs_le_of_integratedCore
      R K j B hR hK hKR hj hV0 hVK hcore
  have hright : 0 ≤ B + (2 * (R : ℝ) + (K : ℝ)) := by positivity
  have hsquare :
      |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ^ 2 ≤
        (B + (2 * (R : ℝ) + (K : ℝ))) ^ 2 := by
    nlinarith [abs_nonneg
      (squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R))]
  simpa [sq_abs] using hsquare

end RHLean.Proof
