import Mathlib
import RHLean.Proof.SquareRootLowPrimeTerminalHighPrimeIntegration
import RHLean.Proof.SquareRootLowPrimeGlobalEnergyTelescope

/-!
# Recouple the terminal low-prime energy to the original smooth-minus-transport core

The terminal processed identity is already

`T(P_R) = Matched_R - Partial_{K,j} - NearRoot_{R,K,j}`,

where

`Matched_R = BornSmooth_R - Transport_R`.

Thus the low-prime terminal machinery is not a new arithmetic obstruction.
Under the native packet hypotheses, the partial packet has magnitude `< K < R`,
and the near-root rectangle has norm at most `R`.  Consequently the complete
terminal square is controlled by the historical smooth/transport cancellation:

`T(P_R)^2 <= 2 * ||Matched_R||^2 + 8 * R^2`.

Combining this *quantitative* terminal reduction with the exact global energy
telescope gives the unconditional one-sided response-child energy inequality

`Energy >= T(K)^2 - 2 * ||Matched_R||^2 - 8 * R^2`.

This does not assume or prove an RH-scale estimate for `Matched_R`.  Its purpose
is to prove rigorously that all remaining low-prime packet/root geometry costs
only root scale, and that the sole non-root-scale arithmetic term in the energy
gate is exactly the old `A - T` matched smooth/transport core.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

private theorem abs_partialPacket_re_lt_root
    {R K j : ℕ}
    (hKR : K < R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    |(((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)).re| <
      (R : ℝ) := by
  have hnonneg :
      0 ≤ (((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)).re := by
    exact_mod_cast hV0
  rw [abs_of_nonneg hnonneg]
  have hltK :
      (((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)).re <
        (K : ℝ) := by
    exact_mod_cast hVK
  exact hltK.trans (by exact_mod_cast hKR)

/-- The two genuine low-prime boundary terms in the matched terminal identity
have total real magnitude strictly below `2R`. -/
theorem abs_squareRootLowPrimeMatchedTerminalBoundary_lt_two_root
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    |(((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)).re +
        (squareRootBornPostTailNearRootRemainder R K j).re| <
      2 * (R : ℝ) := by
  have hpacket := abs_partialPacket_re_lt_root hKR hV0 hVK
  have hnearNorm := squareRootBornPostTailNearRootRemainder_norm_le_root
    R K j (by omega) hK hKR hj
  have hnear :
      |(squareRootBornPostTailNearRootRemainder R K j).re| ≤ (R : ℝ) :=
    (Complex.abs_re_le_norm _).trans hnearNorm
  calc
    |(((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)).re +
        (squareRootBornPostTailNearRootRemainder R K j).re| ≤
      |(((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)).re| +
        |(squareRootBornPostTailNearRootRemainder R K j).re| := abs_add_le _ _
    _ < (R : ℝ) + (R : ℝ) := add_lt_add_of_lt_of_le hpacket hnear
    _ = 2 * (R : ℝ) := by ring

/-- **Quantitative recoupling to the historical `A - T` core.**

At the canonical terminal cutoff, every low-prime boundary contribution is
root-scale.  The only potentially larger term is the old matched
born-smooth/transport difference itself. -/
theorem squareRootLowPrimeTerminal_sq_le_two_matched_sq_add_eight_root_sq
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) ^ 2 ≤
      2 * ‖squareRootMatchedBornSmoothTransport R‖ ^ 2 +
        8 * (R : ℝ) ^ 2 := by
  have hterminalC :=
    squareRootLowPrimeRunningImbalance_at_cutoff_eq_matched_sub_boundaries
      R K j hR hK hKR hj
  have hterminalR := congrArg Complex.re hterminalC
  have hterminal :
      squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) =
        (squareRootMatchedBornSmoothTransport R).re -
          (((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)).re -
          (squareRootBornPostTailNearRootRemainder R K j).re := by
    simpa [squareRootLowPrimeRunningImbalanceReal] using hterminalR
  have hboundary :=
    abs_squareRootLowPrimeMatchedTerminalBoundary_lt_two_root
      R K j hR hK hKR hj hV0 hVK
  have hmatched :
      |(squareRootMatchedBornSmoothTransport R).re| ≤
        ‖squareRootMatchedBornSmoothTransport R‖ :=
    Complex.abs_re_le_norm _
  have htermAbs :
      |squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R)| ≤
        ‖squareRootMatchedBornSmoothTransport R‖ + 2 * (R : ℝ) := by
    rw [hterminal]
    calc
      |(squareRootMatchedBornSmoothTransport R).re -
          (((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)).re -
          (squareRootBornPostTailNearRootRemainder R K j).re| =
        |(squareRootMatchedBornSmoothTransport R).re -
          ((((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)).re +
            (squareRootBornPostTailNearRootRemainder R K j).re)| := by
          congr 1
          ring
      _ ≤ |(squareRootMatchedBornSmoothTransport R).re| +
          |(((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)).re +
            (squareRootBornPostTailNearRootRemainder R K j).re| := abs_sub _ _
      _ ≤ ‖squareRootMatchedBornSmoothTransport R‖ + 2 * (R : ℝ) :=
        add_le_add hmatched (le_of_lt hboundary)
  have hright :
      0 ≤ ‖squareRootMatchedBornSmoothTransport R‖ + 2 * (R : ℝ) := by
    positivity
  have hsquare :
      |squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R)| ^ 2 ≤
        (‖squareRootMatchedBornSmoothTransport R‖ + 2 * (R : ℝ)) ^ 2 := by
    nlinarith [abs_nonneg
      (squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R))]
  have htermSq :
      squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) ^ 2 ≤
        (‖squareRootMatchedBornSmoothTransport R‖ + 2 * (R : ℝ)) ^ 2 := by
    simpa [sq_abs] using hsquare
  have hsplit :
      (‖squareRootMatchedBornSmoothTransport R‖ + 2 * (R : ℝ)) ^ 2 ≤
        2 * ‖squareRootMatchedBornSmoothTransport R‖ ^ 2 +
          8 * (R : ℝ) ^ 2 := by
    nlinarith [sq_nonneg
      (‖squareRootMatchedBornSmoothTransport R‖ - 2 * (R : ℝ))]
  exact htermSq.trans hsplit

/-- **Signed response-child energy recoupled to `A - T`.**

The complete sequential energy decrement loses only a root-scale `8R^2` term
outside the original matched smooth/transport core.  In particular, there is no
independent low-prime analytic obstruction left in this formulation. -/
theorem squareRootLowPrimeSignedResponseEnergy_ge_initial_sub_matched
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K)
    (hKU : K ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet K
        (squareRootBornPostTailLowPrimeCutoff R),
      (2 * squareRootLowPrimeRunningImbalanceReal R K j (p - 1) *
          squareRootLowPrimeFreshIncrementReal R K j p -
        squareRootLowPrimeFreshIncrementReal R K j p ^ 2)) ≥
      squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        (2 * ‖squareRootMatchedBornSmoothTransport R‖ ^ 2 +
          8 * (R : ℝ) ^ 2) := by
  rw [squareRootLowPrimeGlobalEnergyTelescope hK hKU]
  have hterminal :=
    squareRootLowPrimeTerminal_sq_le_two_matched_sq_add_eight_root_sq
      R K j hR hK hKR hj hV0 hVK
  linarith

end RHLean.Proof
