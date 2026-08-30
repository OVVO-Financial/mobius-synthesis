import Mathlib
import RHLean.Proof.SquareRootLowPrimeRunningTelescope
import RHLean.Proof.SquareRootLowPrimeCanonicalFrontierBridge
import RHLean.Proof.SquareRootLowPrimeRoughBaseBound

/-!
# Signed response children to the canonical root core

The complete signed response-child mass and the canonical terminal core are two
coordinates for the same processed response.  This file makes that connection
exact.

At the terminal low-prime cutoff `P_R`,

`ChildMass = T(P_R) - T(K)`

by the real running telescope.  The existing canonical-frontier bridge gives

`T(P_R) = CanonicalCore - NearRoot`,

with `|NearRoot| <= R`.  Hence

`ChildMass = CanonicalCore - T(K) - NearRoot`.

The analogous far-survivor identity loses only the already-proved boundary
`8*R+K`.  Therefore every matched-frontier or rough-base estimate is now a
quantitative estimate for the canonical root geometry, up to explicit
root-scale terms.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Real cast of the complete signed response-child Möbius mass. -/
def squareRootLowPrimeOwnedResponseChildMassReal
    (R K U : ℕ) : ℝ :=
  ((∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U, μ n : ℤ) : ℝ)

/-- Real coordinate of the near-root terminal remainder. -/
def squareRootLowPrimeNearRootRemainderReal
    (R K j : ℕ) : ℝ :=
  (squareRootBornPostTailNearRootRemainder R K j).re

/-- The complete signed child mass is exactly terminal state minus shallow
state. -/
theorem squareRootLowPrimeOwnedResponseChildMassReal_eq_terminal_sub_shallow
    {R K j U : ℕ} (hR : 2 ≤ R) (hK : 1 ≤ K)
    (hKU : K ≤ U) (hUR : U < R) :
    squareRootLowPrimeOwnedResponseChildMassReal R K U =
      squareRootLowPrimeRunningImbalanceReal R K j U -
        squareRootLowPrimeRunningImbalanceReal R K j K := by
  have htelescope :=
    squareRootLowPrimeRunningImbalanceReal_sub_eq_freshIncrement_sum
      (R := R) (K := K) (j := j) (U := U) hK hKU
  have hchildren :=
    squareRootLowPrimeFreshIncrementReal_sum_eq_neg_ownedResponseChildrenMass
      (R := R) (K := K) (j := j) (U := U) hR hUR
  rw [squareRootLowPrimeOwnedResponseChildren_realWeightSum_eq_intCast]
    at hchildren
  unfold squareRootLowPrimeOwnedResponseChildMassReal
  linarith

/-- Real form of the exact terminal canonical-frontier identity. -/
theorem squareRootLowPrimeRunningImbalanceReal_at_cutoff_eq_canonicalCore_sub_nearRoot
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) =
      squareRootLowPrimeCanonicalTerminalCoreReal R K j -
        squareRootLowPrimeNearRootRemainderReal R K j := by
  have h := congrArg Complex.re
    (squareRootLowPrimeRunningImbalance_at_cutoff_eq_canonicalFrontier
      R K j hR hK hKR hj)
  simpa [squareRootLowPrimeRunningImbalanceReal,
    squareRootLowPrimeCanonicalTerminalCoreReal,
    squareRootLowPrimeNearRootRemainderReal] using h

/-- **Exact child-to-root map.** -/
theorem squareRootLowPrimeOwnedResponseChildMassReal_eq_canonicalCore_sub_shallow_sub_nearRoot
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hKU : K ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hUR : squareRootBornPostTailLowPrimeCutoff R < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeOwnedResponseChildMassReal R K
        (squareRootBornPostTailLowPrimeCutoff R) =
      squareRootLowPrimeCanonicalTerminalCoreReal R K j -
        squareRootLowPrimeRunningImbalanceReal R K j K -
          squareRootLowPrimeNearRootRemainderReal R K j := by
  rw [squareRootLowPrimeOwnedResponseChildMassReal_eq_terminal_sub_shallow
      (R := R) (K := K) (j := j)
      (U := squareRootBornPostTailLowPrimeCutoff R)
      (by omega) hK hKU hUR,
    squareRootLowPrimeRunningImbalanceReal_at_cutoff_eq_canonicalCore_sub_nearRoot
      R K j hR hK hKR hj]
  ring

/-- The child mass differs from `CanonicalCore - T(K)` by at most `R`. -/
theorem abs_squareRootLowPrimeOwnedResponseChildMassReal_sub_canonicalCore_sub_shallow_le_root
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hKU : K ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hUR : squareRootBornPostTailLowPrimeCutoff R < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    |squareRootLowPrimeOwnedResponseChildMassReal R K
        (squareRootBornPostTailLowPrimeCutoff R) -
      (squareRootLowPrimeCanonicalTerminalCoreReal R K j -
        squareRootLowPrimeRunningImbalanceReal R K j K)| ≤ (R : ℝ) := by
  rw [squareRootLowPrimeOwnedResponseChildMassReal_eq_canonicalCore_sub_shallow_sub_nearRoot
    R K j hR hK hKR hKU hUR hj]
  have hre :
      |squareRootLowPrimeNearRootRemainderReal R K j| ≤
        ‖squareRootBornPostTailNearRootRemainder R K j‖ := by
    exact Complex.abs_re_le_norm _
  have hnear := squareRootBornPostTailNearRootRemainder_norm_le_root
    R K j hR hK hKR hj
  have hbound := hre.trans hnear
  simpa [squareRootLowPrimeNearRootRemainderReal] using hbound

/-- The canonical core-minus-shallow state is controlled by any child-mass
bound plus the root remainder. -/
theorem abs_canonicalCore_sub_shallow_le_childMass_add_root
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hKU : K ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hUR : squareRootBornPostTailLowPrimeCutoff R < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    |squareRootLowPrimeCanonicalTerminalCoreReal R K j -
        squareRootLowPrimeRunningImbalanceReal R K j K| ≤
      |squareRootLowPrimeOwnedResponseChildMassReal R K
        (squareRootBornPostTailLowPrimeCutoff R)| + (R : ℝ) := by
  have hdiff :=
    abs_squareRootLowPrimeOwnedResponseChildMassReal_sub_canonicalCore_sub_shallow_le_root
      R K j hR hK hKR hKU hUR hj
  rw [show squareRootLowPrimeCanonicalTerminalCoreReal R K j -
      squareRootLowPrimeRunningImbalanceReal R K j K =
      squareRootLowPrimeOwnedResponseChildMassReal R K
          (squareRootBornPostTailLowPrimeCutoff R) -
        (squareRootLowPrimeOwnedResponseChildMassReal R K
          (squareRootBornPostTailLowPrimeCutoff R) -
          (squareRootLowPrimeCanonicalTerminalCoreReal R K j -
            squareRootLowPrimeRunningImbalanceReal R K j K)) by ring]
  calc
    |squareRootLowPrimeOwnedResponseChildMassReal R K
        (squareRootBornPostTailLowPrimeCutoff R) -
      (squareRootLowPrimeOwnedResponseChildMassReal R K
        (squareRootBornPostTailLowPrimeCutoff R) -
        (squareRootLowPrimeCanonicalTerminalCoreReal R K j -
          squareRootLowPrimeRunningImbalanceReal R K j K))| ≤
      |squareRootLowPrimeOwnedResponseChildMassReal R K
        (squareRootBornPostTailLowPrimeCutoff R)| +
      |squareRootLowPrimeOwnedResponseChildMassReal R K
        (squareRootBornPostTailLowPrimeCutoff R) -
        (squareRootLowPrimeCanonicalTerminalCoreReal R K j -
          squareRootLowPrimeRunningImbalanceReal R K j K)| := by
            simpa only [abs_neg] using abs_sub
              (squareRootLowPrimeOwnedResponseChildMassReal R K
                (squareRootBornPostTailLowPrimeCutoff R))
              (squareRootLowPrimeOwnedResponseChildMassReal R K
                (squareRootBornPostTailLowPrimeCutoff R) -
                (squareRootLowPrimeCanonicalTerminalCoreReal R K j -
                  squareRootLowPrimeRunningImbalanceReal R K j K))
    _ ≤ |squareRootLowPrimeOwnedResponseChildMassReal R K
          (squareRootBornPostTailLowPrimeCutoff R)| + (R : ℝ) :=
      add_le_add_left hdiff _

/-- The child-to-far-survivor discrepancy is bounded by `8R+K`. -/
theorem abs_squareRootLowPrimeOwnedResponseChildMassReal_sub_farSurvivorCore_sub_shallow_le
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hKU : K ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hUR : squareRootBornPostTailLowPrimeCutoff R < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    |squareRootLowPrimeOwnedResponseChildMassReal R K
        (squareRootBornPostTailLowPrimeCutoff R) -
      (squareRootLowPrimeFarSurvivorTerminalCoreReal R -
        squareRootLowPrimeRunningImbalanceReal R K j K)| ≤
      8 * (R : ℝ) + (K : ℝ) := by
  rw [squareRootLowPrimeOwnedResponseChildMassReal_eq_terminal_sub_shallow
    (R := R) (K := K) (j := j)
    (U := squareRootBornPostTailLowPrimeCutoff R)
    (by omega) hK hKU hUR]
  have hfar :=
    squareRootLowPrimeRunningImbalanceReal_sub_farSurvivorCore_abs_le
      R K j hR hK hKR hj hV0 hVK
  convert hfar using 1
  all_goals ring_nf

end RHLean.Proof
