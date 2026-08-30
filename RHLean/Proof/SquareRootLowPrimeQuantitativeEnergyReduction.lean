import Mathlib
import RHLean.Proof.SquareRootLowPrimeSignedResponseChildren
import RHLean.Proof.SquareRootLowPrimeCanonicalFrontierBridge

/-!
# Real quantitative reductions for the low-prime sequential state

The running low-prime state is represented in `ℂ` only so that it composes with
the repository's other signed finite sums.  Every coefficient is real.  For
ordered estimates we therefore pass through the real-part map and keep the
exact chronological convention

`Delta_p = T(p - 1) - T(p)`.

This file packages three reductions needed by the quantitative endgame.

* The exact prime step and its quadratic energy identity are transferred to
  `ℝ`.
* The complete signed-child identity is transferred to one real restricted
  Möbius mass.
* The existing canonical-core and far-survivor bridges are converted into
  explicit absolute-value and square-energy transfer inequalities.

The strongest bridge loses only `R` beyond the real canonical terminal core.
The geometrically simpler born-smooth / far-survivor core loses `8*R + K`.
Thus any square bound for either real core immediately produces a square bound
for the actual terminal low-prime state, with no additional prime-count factor.

No estimate for either hard core is assumed or proved here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Real coordinate of the chronological running imbalance. -/
def squareRootLowPrimeRunningImbalanceReal
    (R K j p : ℕ) : ℝ :=
  (squareRootLowPrimeRunningImbalance R K j p).re

/-- Real coordinate of one exact fresh-prime increment. -/
def squareRootLowPrimeFreshIncrementReal
    (R K j p : ℕ) : ℝ :=
  (squareRootLowPrimeFreshIncrement R K j p).re

/-- Real coordinate of the exact canonical terminal core. -/
def squareRootLowPrimeCanonicalTerminalCoreReal
    (R K j : ℕ) : ℝ :=
  (squareRootLowPrimeCanonicalTerminalCore R K j).re

/-- Real coordinate of the born-smooth / far-survivor terminal core. -/
def squareRootLowPrimeFarSurvivorTerminalCoreReal
    (R : ℕ) : ℝ :=
  (squareRootLowPrimeFarSurvivorTerminalCore R).re

/-- The accepted chronological prime step in ordered real coordinates. -/
theorem squareRootLowPrimeRunningImbalanceReal_step_eq_freshIncrementReal
    (R K j p : ℕ) (hp : p.Prime) :
    squareRootLowPrimeRunningImbalanceReal R K j (p - 1) -
        squareRootLowPrimeRunningImbalanceReal R K j p =
      squareRootLowPrimeFreshIncrementReal R K j p := by
  have h := congrArg Complex.re
    (squareRootLowPrimeRunningImbalance_step_eq_freshIncrement
      R K j p hp)
  simpa [squareRootLowPrimeRunningImbalanceReal,
    squareRootLowPrimeFreshIncrementReal] using h

/-- Exact real quadratic energy decrement at one fresh prime. -/
theorem squareRootLowPrimeRunningEnergyReal_step
    (R K j p : ℕ) (hp : p.Prime) :
    squareRootLowPrimeRunningImbalanceReal R K j (p - 1) ^ 2 -
        squareRootLowPrimeRunningImbalanceReal R K j p ^ 2 =
      2 * squareRootLowPrimeRunningImbalanceReal R K j (p - 1) *
          squareRootLowPrimeFreshIncrementReal R K j p -
        squareRootLowPrimeFreshIncrementReal R K j p ^ 2 := by
  have hstep :=
    squareRootLowPrimeRunningImbalanceReal_step_eq_freshIncrementReal
      R K j p hp
  rw [← hstep]
  ring

/-- The complete deep signed-child identity in real coordinates.  The response
weights and both Möbius orientations have already been reunited before this
map is applied. -/
theorem squareRootLowPrimeFreshIncrementReal_sum_eq_neg_ownedResponseChildrenMass
    {R K j U : ℕ} (hR : 2 ≤ R) (hUR : U < R) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
      squareRootLowPrimeFreshIncrementReal R K j p) =
      -∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
        (canonicalMoebiusWeight n).re := by
  have h := congrArg Complex.re
    (squareRootLowPrimeFreshIncrement_sum_eq_neg_ownedResponseChildrenMass
      (R := R) (K := K) (j := j) (U := U) hR hUR)
  simpa [squareRootLowPrimeFreshIncrementReal] using h

/-- Taking real parts of a complex difference costs at most its complex norm. -/
private theorem abs_re_sub_le_norm_sub (z w : ℂ) :
    |z.re - w.re| ≤ ‖z - w‖ := by
  have h := Complex.abs_re_le_norm (z - w)
  simpa using h

/-- **Canonical-core real reduction.**  The actual terminal real state differs
from the explicit canonical core by at most `R`. -/
theorem squareRootLowPrimeRunningImbalanceReal_sub_canonicalCore_abs_le_root
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
      squareRootLowPrimeCanonicalTerminalCoreReal R K j| ≤ (R : ℝ) := by
  exact (abs_re_sub_le_norm_sub
    (squareRootLowPrimeRunningImbalance R K j
      (squareRootBornPostTailLowPrimeCutoff R))
    (squareRootLowPrimeCanonicalTerminalCore R K j)).trans
      (squareRootLowPrimeRunningImbalance_sub_canonicalCore_norm_le_root
        R K j hR hK hKR hj)

/-- Terminal absolute value transferred from the canonical real core. -/
theorem squareRootLowPrimeRunningImbalanceReal_abs_le_canonicalCore_add_root
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤
      |squareRootLowPrimeCanonicalTerminalCoreReal R K j| + (R : ℝ) := by
  have hdiff :=
    squareRootLowPrimeRunningImbalanceReal_sub_canonicalCore_abs_le_root
      R K j hR hK hKR hj
  calc
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| =
      |(squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) -
        squareRootLowPrimeCanonicalTerminalCoreReal R K j) +
        squareRootLowPrimeCanonicalTerminalCoreReal R K j| := by ring_nf
    _ ≤ |squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) -
        squareRootLowPrimeCanonicalTerminalCoreReal R K j| +
          |squareRootLowPrimeCanonicalTerminalCoreReal R K j| :=
      abs_add_le _ _
    _ ≤ (R : ℝ) +
          |squareRootLowPrimeCanonicalTerminalCoreReal R K j| :=
      add_le_add_right hdiff _
    _ = |squareRootLowPrimeCanonicalTerminalCoreReal R K j| +
          (R : ℝ) := by ring

/-- A bound for the canonical real core transfers directly to the terminal
state, with only the already-proved root-scale loss. -/
theorem squareRootLowPrimeRunningImbalanceReal_abs_le_of_canonicalCore
    (R K j : ℕ) (B : ℝ)
    (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hcore : |squareRootLowPrimeCanonicalTerminalCoreReal R K j| ≤ B) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤ B + (R : ℝ) := by
  exact
    (squareRootLowPrimeRunningImbalanceReal_abs_le_canonicalCore_add_root
      R K j hR hK hKR hj).trans
      (add_le_add_right hcore _)

/-- Squared terminal bound transferred from a canonical-core absolute bound. -/
theorem squareRootLowPrimeRunningImbalanceReal_sq_le_of_canonicalCore
    (R K j : ℕ) (B : ℝ)
    (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hB : 0 ≤ B)
    (hcore : |squareRootLowPrimeCanonicalTerminalCoreReal R K j| ≤ B) :
    squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) ^ 2 ≤
      (B + (R : ℝ)) ^ 2 := by
  have habs :=
    squareRootLowPrimeRunningImbalanceReal_abs_le_of_canonicalCore
      R K j B hR hK hKR hj hcore
  have hright : 0 ≤ B + (R : ℝ) := by positivity
  have hsquare :
      |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ^ 2 ≤
        (B + (R : ℝ)) ^ 2 := by
    nlinarith [abs_nonneg
      (squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R))]
  simpa [sq_abs] using hsquare

/-- The corresponding endpoint energy decrement lower bound. -/
theorem squareRootLowPrimeEndpointEnergyReal_ge_of_canonicalCore
    (R K j : ℕ) (B : ℝ)
    (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hB : 0 ≤ B)
    (hcore : |squareRootLowPrimeCanonicalTerminalCoreReal R K j| ≤ B) :
    squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) ^ 2 ≥
      squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        (B + (R : ℝ)) ^ 2 := by
  have hterminal :=
    squareRootLowPrimeRunningImbalanceReal_sq_le_of_canonicalCore
      R K j B hR hK hKR hj hB hcore
  linarith

/-- **Far-survivor real reduction.**  The geometrically transparent hard pair
loses only the already-proved boundary `8*R + K`. -/
theorem squareRootLowPrimeRunningImbalanceReal_sub_farSurvivorCore_abs_le
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
      squareRootLowPrimeFarSurvivorTerminalCoreReal R| ≤
        8 * (R : ℝ) + (K : ℝ) := by
  exact (abs_re_sub_le_norm_sub
    (squareRootLowPrimeRunningImbalance R K j
      (squareRootBornPostTailLowPrimeCutoff R))
    (squareRootLowPrimeFarSurvivorTerminalCore R)).trans
      (squareRootLowPrimeRunningImbalance_sub_farSurvivorCore_norm_le
        R K j hR hK hKR hj hV0 hVK)

/-- Terminal absolute value transferred from the born-smooth / far-survivor
real core. -/
theorem squareRootLowPrimeRunningImbalanceReal_abs_le_farSurvivorCore_add_boundary
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤
      |squareRootLowPrimeFarSurvivorTerminalCoreReal R| +
        (8 * (R : ℝ) + (K : ℝ)) := by
  have hdiff :=
    squareRootLowPrimeRunningImbalanceReal_sub_farSurvivorCore_abs_le
      R K j hR hK hKR hj hV0 hVK
  calc
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| =
      |(squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) -
        squareRootLowPrimeFarSurvivorTerminalCoreReal R) +
        squareRootLowPrimeFarSurvivorTerminalCoreReal R| := by ring_nf
    _ ≤ |squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) -
        squareRootLowPrimeFarSurvivorTerminalCoreReal R| +
          |squareRootLowPrimeFarSurvivorTerminalCoreReal R| :=
      abs_add_le _ _
    _ ≤ (8 * (R : ℝ) + (K : ℝ)) +
          |squareRootLowPrimeFarSurvivorTerminalCoreReal R| :=
      add_le_add_right hdiff _
    _ = |squareRootLowPrimeFarSurvivorTerminalCoreReal R| +
          (8 * (R : ℝ) + (K : ℝ)) := by ring

end RHLean.Proof
