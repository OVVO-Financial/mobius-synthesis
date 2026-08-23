import Mathlib
import RHLean.Analysis.SquareRootMiddleSequentialCoherence
import RHLean.Proof.LowWheelSequentialSmoothRoughBoundary
import RHLean.Proof.RecursivePrimeReplacement

/-!
# Predecessor-prime cells in the square-root reciprocal corridor

The completed one-prime frontier is killed by full divisor-fibre Möbius
inversion. This module keeps one chronological low-prime coordinate visible.
For a prime `p` and reciprocal label `k`, define

`A_p(k) = F_{<p}(floor(k/p))`,

where `F_{<p}` is the truncated Boolean-cube mass on primes strictly below `p`.
On squarefree support this is exactly the signed mass

`sum_{d <= k/p, P+(d) < p} mu(d)`.

The exact identities below separate the genuinely additive fresh-prime state
from the cumulative state, identify the reciprocal `k`-cells of the existing
double-cube/window fold, record the primorial deletion of completed old cubes,
and expose the cross-root cancellation against the terminal prime fibre.

The final algebra is also recorded explicitly: once the predecessor chronology
is completed, the cross-root derivative is not a new signed Mertens state. It
collapses to `terminal primes - all unresolved integers`, i.e. minus the
composite population of the reciprocal fibre. If the future composite channel
is further split by its first-hit prime `r`, completing the predecessor primes
below `r` gives coefficient `-1` on every such first-hit composite. Thus merely
unsumming the first-hit coordinate does not escape the collapse.

No analytic estimate, asymptotic, PNT input, or RH hypothesis is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Signed predecessor-prime mass at reciprocal label `k`.

This is the frozen old-prime cube strictly before `p`, evaluated at the child
cutoff `floor(k/p)`. -/
def predecessorPrimeMass (p k : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo (p - 1)) (k / p)

/-- Literal Boolean-face form of `A_p(k)`. -/
theorem predecessorPrimeMass_eq_faceSum (p k : ℕ) :
    predecessorPrimeMass p k =
      ∑ t ∈ (primesUpTo (p - 1)).powerset,
        if primeFaceProduct t ≤ k / p then booleanCubeSign t else 0 := by
  unfold predecessorPrimeMass
  exact frozenPrimeUniverseMass_eq_cutoffSum _ _

/-- **Fresh-prime decrement.** Admitting a prime `p` to the frozen lower-scale
cube subtracts exactly `A_p(k)`. -/
theorem frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor
    (p k : ℕ) (hp : p.Prime) :
    frozenPrimeUniverseMass (primesUpTo p) k =
      frozenPrimeUniverseMass (primesUpTo (p - 1)) k -
        predecessorPrimeMass p k := by
  rw [primesUpTo_eq_insert_pred_of_prime hp]
  rw [frozenPrimeUniverseMass_insert
    (freshPrime_not_mem_primesUpTo_pred hp) hp]
  rfl

/-- The sequential smooth-face shell is exactly the frozen lower-scale state
after the fresh prime `p` has been processed. -/
theorem lowWheelSmoothFaceShellMass_eq_frozenPrimeUniverseMass
    (p k : ℕ) (hp : p.Prime) :
    lowWheelSmoothFaceShellMass p k =
      frozenPrimeUniverseMass (primesUpTo p) k := by
  rw [lowWheelSmoothFaceShellMass_eq_truncatedCubeDiff]
  change
    frozenPrimeUniverseMass (primesUpTo (p - 1)) k -
        frozenPrimeUniverseMass (primesUpTo (p - 1)) (k / p) =
      frozenPrimeUniverseMass (primesUpTo p) k
  rw [frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor p k hp]
  rfl

/-- Unresolved integers in one reciprocal quotient fibre which survive every
prime coordinate through `p`. -/
def lowWheelPKReciprocalSurvivorSet (p R k : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter fun q =>
    squareRootEndpoint R / q = k ∧ lowWheelHighSurvivor p q

/-- The literal cumulative `(p,k)` cell obtained by retaining only the quotient
fibre `floor(X_R/q)=k` in the q-first smooth/rough form of the double-cube state
through prime `p`. -/
def lowWheelPKCumulativeCell (p R k : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
    if squareRootEndpoint R / q = k then
      if lowWheelHighSurvivor p q then
        ((lowWheelSmoothFaceShellMass p k : ℤ) : ℂ)
      else 0
    else 0

/-- **Exact factorization of one reciprocal cell.** Once the quotient label `k`
is fixed, the old smooth-face coefficient is constant across the fibre, so the
literal double-cube/window cell is the product of that coefficient and the
through-`p` survivor population in the same fibre. -/
theorem lowWheelPKCumulativeCell_eq_shell_mul_survivorCard
    (p R k : ℕ) :
    lowWheelPKCumulativeCell p R k =
      ((lowWheelSmoothFaceShellMass p k : ℤ) : ℂ) *
        ((lowWheelPKReciprocalSurvivorSet p R k).card : ℂ) := by
  classical
  unfold lowWheelPKCumulativeCell lowWheelPKReciprocalSurvivorSet
  calc
    (∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
      if squareRootEndpoint R / q = k then
        if lowWheelHighSurvivor p q then
          ((lowWheelSmoothFaceShellMass p k : ℤ) : ℂ)
        else 0
      else 0) =
      ∑ q ∈ (Finset.Ioc R (squareRootEndpoint R)).filter (fun q =>
          squareRootEndpoint R / q = k ∧ lowWheelHighSurvivor p q),
        ((lowWheelSmoothFaceShellMass p k : ℤ) : ℂ) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro q _hq
          by_cases hqk : squareRootEndpoint R / q = k <;>
            by_cases hsurv : lowWheelHighSurvivor p q <;>
              simp [hqk, hsurv]
    _ = ((lowWheelSmoothFaceShellMass p k : ℤ) : ℂ) *
        (((Finset.Ioc R (squareRootEndpoint R)).filter (fun q =>
          squareRootEndpoint R / q = k ∧ lowWheelHighSurvivor p q)).card : ℂ) := by
          simp [mul_comm]

/-- In frozen-cube notation the literal reciprocal cell is exactly
`C_{<=p}(k) * Q_{<=p}(k)`. -/
theorem lowWheelPKCumulativeCell_eq_frozen_mul_survivorCard
    (p R k : ℕ) (hp : p.Prime) :
    lowWheelPKCumulativeCell p R k =
      ((frozenPrimeUniverseMass (primesUpTo p) k : ℤ) : ℂ) *
        ((lowWheelPKReciprocalSurvivorSet p R k).card : ℂ) := by
  rw [lowWheelPKCumulativeCell_eq_shell_mul_survivorCard,
    lowWheelSmoothFaceShellMass_eq_frozenPrimeUniverseMass p k hp]

/-- **The full cumulative double-cube state is the sum of its reciprocal
`(p,k)` cells.** Every unresolved `q>R` has quotient strictly below `R`, so the
finite family `k<R` is exhaustive. -/
theorem lowWheelDoubleCubePrimePrefix_step_eq_sum_pkCumulativeCells
    (R p : ℕ) (hR : 2 ≤ R) (hp : p.Prime) :
    lowWheelDoubleCubeSetTransportLedger R (primesUpTo p) =
      ∑ k ∈ Finset.range R, lowWheelPKCumulativeCell p R k := by
  rw [lowWheelDoubleCubePrimePrefix_step_eq_smoothRoughShellMass R p hp]
  unfold lowWheelPKCumulativeCell
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  have hqR : R ≤ q := by
    have := (Finset.mem_Ioc.mp hq).1
    omega
  have hklt : squareRootEndpoint R / q < R :=
    squareRootEndpoint_div_lt_root_of_root_le hR hqR
  have hkmem : squareRootEndpoint R / q ∈ Finset.range R :=
    Finset.mem_range.mpr hklt
  by_cases hsurv : lowWheelHighSurvivor p q
  · simp [hsurv, hkmem]
  · simp [hsurv]

/-- **Cumulative-state guardrail.** Adding `A_p(k)` back to the already-
processed smooth-shell coefficient reconstructs the old parent prefix exactly.
Therefore this pair by itself is not an independent cancellation mechanism. -/
theorem lowWheelSmoothFaceShellMass_add_predecessor_eq_parentPrefix
    (p k : ℕ) (hp : p.Prime) :
    lowWheelSmoothFaceShellMass p k + predecessorPrimeMass p k =
      frozenPrimeUniverseMass (primesUpTo (p - 1)) k := by
  rw [lowWheelSmoothFaceShellMass_eq_frozenPrimeUniverseMass p k hp]
  rw [frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor p k hp]
  ring

/-- **Primorial deletion.** If `k/p` already contains the complete Boolean cube
on all primes below `p`, then `A_p(k)` vanishes exactly. -/
theorem predecessorPrimeMass_eq_zero_of_predPrimeCube_complete
    {p k : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hfit : p * primeFaceProduct (primesUpTo (p - 1)) ≤ k) :
    predecessorPrimeMass p k = 0 := by
  unfold predecessorPrimeMass
  apply frozenPrimeUniverseMass_eq_zero_of_complete_old_cube
  · refine ⟨2, mem_primesUpTo_of_prime_le Nat.prime_two ?_⟩
    omega
  · intro q hq
    exact prime_of_mem_primesUpTo hq
  · apply (Nat.le_div_iff_mul_le hp.pos).2
    simpa [Nat.mul_comm] using hfit

/-- The first predecessor-prime channel at `k=2` has unit mass. -/
theorem predecessorPrimeMass_two_two : predecessorPrimeMass 2 2 = 1 := by
  have hS : primesUpTo (2 - 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqData := mem_primesUpTo.mp hq
    have hq2 : 2 ≤ q := hqData.1.two_le
    omega
  unfold predecessorPrimeMass
  rw [hS]
  simp [frozenPrimeUniverseMass, truncatedCubeAlternatingSum,
    primeProductAdmissible, primeFaceProduct, booleanCubeSign]

/-- **Prime edge plus `p=2` cancellation in the `k=2` fibre.** -/
theorem edge_prime_plus_p2_cancel_of_k2 :
    (-1 : ℤ) + predecessorPrimeMass 2 2 = 0 := by
  rw [predecessorPrimeMass_two_two]
  norm_num

/-- Algebra of one additive fresh-prime `(p,k)` cell. If `C` and `Q` are the
cofactor and unresolved-quotient states before `p`, while `A` and `H` are their
respective fresh-`p` deletions, then the four-corner update has the exact two
component form used by the finite gate. -/
theorem freshPrimePKCell_eq_cofactorDeletion_add_hitDeletion
    (C A Q H : ℤ) :
    (C - A) * (Q - H) - C * Q =
      -A * (Q - H) - C * H := by
  ring

/-- **Exact cross-root cancellation for the additive step.** Add the terminal-
prime predecessor mass `N*A` to the change across the fresh prime. The terminal
prime part cancels algebraically, leaving only future composite hits and the
current hit. -/
theorem freshPrimePKCrossRoot_eq_futureHitResidual
    (C A Q H N : ℤ) :
    ((C - A) * (Q - H) - C * Q) + N * A =
      -A * ((Q - H) - N) - C * H := by
  ring

/-- **Literal cumulative-cell decomposition.** If the low term is the state
*through* `p`, as in the cumulative double-cube/window fold, then adding the
terminal predecessor term does not equal only the new cross-root residual: it
also retains the entire inherited parent product `C*Q`. This identity is the
exact distinction between the literal cumulative gate and the additive gate. -/
theorem cumulativePKCrossRoot_eq_parent_add_futureHitResidual
    (C A Q H N : ℤ) :
    (C - A) * (Q - H) + N * A =
      C * Q + (-A * ((Q - H) - N) - C * H) := by
  ring

/-- Replacing the evolving survivor population by the terminal prime population
necessarily drops the future-hit channel. This is the residual term exposed by
the preceding cross-root identities. -/
theorem predecessorPrime_terminalProjection_exposes_futureHits
    (A N future : ℤ) :
    -A * (N + future) = -A * N - A * future := by
  ring

/-- **Completed predecessor chronology collapses to composite count.** If the
additive low state has telescoped from the initial cell `J` to terminal value
`M*N`, while the predecessor decrements telescope from `1` to `M`, then adding
all terminal-prime corrections leaves exactly `N-J`. In the reciprocal corridor
this is minus the number of composites in the fibre. -/
theorem completedPKCrossRoot_endpointCollapse
    (M J N : ℤ) :
    (M * N - J) + N * (1 - M) = N - J := by
  ring

/-- **First-hit refinement also completes to one sign.** For a fixed later
first-hit prime `r`, the future terms from predecessor primes below `r` have
total coefficient `1-C`, while the current-hit term has coefficient `C`.
Completing the predecessor coordinate therefore gives coefficient `-1` on each
first-hit composite. -/
theorem completedPredecessorFirstHit_eq_neg_hitCount
    (C H : ℤ) :
    -(1 - C) * H - C * H = -H := by
  ring

/-- **Two-thirds support law.** In a reciprocal cell `k = floor(X_R/q)` with
`p <= k`, any unresolved composite `q` whose least prime factor is at least `p`
forces `p^3 < R^2`. Hence above the `R^(2/3)` predecessor scale the supported
additive cross-root residual has no current or future composite hit. -/
theorem reciprocalMiddle_composite_survivor_forces_predCube_lt_square
    {R p k q : ℕ}
    (hR : 2 ≤ R) (_hp : 1 ≤ p) (hRq : R < q)
    (hqk : squareRootEndpoint R / q = k)
    (hpk : p ≤ k) (hqPrime : ¬ q.Prime)
    (hpMin : p ≤ q.minFac) :
    p ^ 3 < R ^ 2 := by
  have hqpos : 0 < q := by omega
  have hminSq : q.minFac ^ 2 ≤ q :=
    Nat.minFac_sq_le_self hqpos hqPrime
  have hpSq : p ^ 2 ≤ q.minFac ^ 2 :=
    Nat.pow_le_pow_left hpMin 2
  have hpSqQ : p ^ 2 ≤ q := hpSq.trans hminSq
  have hkq : k * q ≤ squareRootEndpoint R := by
    rw [← hqk]
    exact Nat.div_mul_le_self (squareRootEndpoint R) q
  have hpq : p * q ≤ squareRootEndpoint R := by
    exact (Nat.mul_le_mul_right q hpk).trans hkq
  have hpCube : p ^ 3 ≤ squareRootEndpoint R := by
    calc
      p ^ 3 = p * p ^ 2 := by ring
      _ ≤ p * q := Nat.mul_le_mul_left p hpSqQ
      _ ≤ squareRootEndpoint R := hpq
  have hXlt : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hsqpos : 0 < R ^ 2 := by positivity
    omega
  exact hpCube.trans_lt hXlt

/-- Contrapositive form of the two-thirds support law. -/
theorem no_reciprocalMiddle_composite_survivor_of_square_le_predCube
    {R p k q : ℕ}
    (hR : 2 ≤ R) (hp : 1 ≤ p) (hRq : R < q)
    (hqk : squareRootEndpoint R / q = k)
    (hpk : p ≤ k) (hqPrime : ¬ q.Prime)
    (hpMin : p ≤ q.minFac) (hcube : R ^ 2 ≤ p ^ 3) :
    False := by
  exact (Nat.not_lt_of_ge hcube)
    (reciprocalMiddle_composite_survivor_forces_predCube_lt_square
      hR hp hRq hqk hpk hqPrime hpMin)

/-- The already-formalized exact middle corridor, displayed in reciprocal
coordinates. The quotient label `k` is the only surviving large-prime label
after primes `q` in the same fibre are counted. -/
theorem squareRootMiddle_exact_reciprocalLayers
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleMertensTail R =
      ∑ k ∈ Finset.Icc 2 (R - 1),
        primeSieveReciprocalPrimeCount R (squareRootEndpoint R) k *
          mertensSummatory k :=
  squareRootMiddleMertensTail_eq_reciprocalPrimeLayers R hR

/-- The `k=2` reciprocal band is identically zero, not merely small. -/
theorem squareRootMiddle_k2_band_exact_zero (R : ℕ) :
    (∑ q ∈ Finset.Ioc (squareRootEndpoint R / 3) (squareRootEndpoint R / 2),
      if q.Prime then mertensSummatory (squareRootEndpoint R / q) else 0) = 0 :=
  squareRootMiddleHarmonicBand_two_eq_zero R

end RHLean.Proof
