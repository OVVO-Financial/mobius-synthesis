import Mathlib
import RHLean.Arithmetic.PrimorialTruncatedWheelBoundary
import RHLean.Proof.MutableSupportBound
import RHLean.Analysis.SquareRootPrimeCountGap
import RHLean.Proof.LowWheelDoubleCubeTransport
import RHLean.Proof.PrimeCombReciprocalBandCancellation
import RHLean.Proof.TerminalAxiomAudit

/-!
# Vanishing transition relevance

This module formalizes the final deterministic asymptotic transfer.  A transition
support `U n` is measured on the linear scale of the square block by

```text
card (U n) / n.
```

If the settled complement has zero Möbius mass, an earlier layer gives
`|Δ_n| <= card (U n)`.  Dividing by `n` shows that vanishing transition relevance
forces the normalized square-block discrepancy to vanish as well.

The arithmetic construction of the genuine severed transition support, and the
proof that its relevance vanishes, remain separate inputs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators Topology
open Filter

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership

/-- Transition relevance on the natural linear scale of the square block. -/
def transitionRelevance (U : ℕ → Finset ℕ) (n : ℕ) : ℝ :=
  ((U n).card : ℝ) / (n : ℝ)

/-- Absolute square-block discrepancy normalized by the same linear scale. -/
def normalizedSquareBlockDiscrepancy (n : ℕ) : ℝ :=
  |(squareBlockMoebius n : ℝ)| / (n : ℝ)

/-- Epsilon/eventually formulation of vanishing transition relevance. -/
def TransitionRelevanceVanishes (U : ℕ → Finset ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, transitionRelevance U n ≤ ε

/-- Epsilon/eventually formulation of `Δ_n = o(n)`. -/
def SquareBlockDiscrepancyVanishes : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, normalizedSquareBlockDiscrepancy n ≤ ε

/-- Pointwise transfer: the normalized block discrepancy is bounded by transition
relevance whenever the settled complement has zero Möbius mass. -/
theorem normalizedSquareBlockDiscrepancy_le_transitionRelevance
    (U : ℕ → Finset ℕ)
    (hU : ∀ n, U n ⊆ squareBlockInterval n)
    (hinterior : ∀ n, ∑ m ∈ squareBlockInterval n \ U n, μ m = 0)
    {n : ℕ} (hn : 0 < n) :
    normalizedSquareBlockDiscrepancy n ≤ transitionRelevance U n := by
  have hInt : |squareBlockMoebius n| ≤ ((U n).card : ℤ) :=
    abs_squareBlockMoebius_le_mutable_card (hU n) (hinterior n)
  have hReal : |(squareBlockMoebius n : ℝ)| ≤ ((U n).card : ℝ) := by
    exact_mod_cast hInt
  unfold normalizedSquareBlockDiscrepancy transitionRelevance
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  exact (div_le_div_iff_of_pos_right hnReal).2 hReal

/-- Vanishing transition relevance forces `Δ_n = o(n)` in epsilon/eventually
form.  No further cancellation estimate is used. -/
theorem squareBlockDiscrepancyVanishes_of_transitionRelevanceVanishes
    (U : ℕ → Finset ℕ)
    (hU : ∀ n, U n ⊆ squareBlockInterval n)
    (hinterior : ∀ n, ∑ m ∈ squareBlockInterval n \ U n, μ m = 0)
    (hvanish : TransitionRelevanceVanishes U) :
    SquareBlockDiscrepancyVanishes := by
  intro ε hε
  have hrel := hvanish ε hε
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    omega
  filter_upwards [hrel, hpos] with n hnRel hnPos
  exact le_trans
    (normalizedSquareBlockDiscrepancy_le_transitionRelevance U hU hinterior hnPos)
    hnRel

/-! ## Ordered prime replication as deterministic Möbius transport

The fixed lower Möbius prefix is not resampled by post-root primes.  This
section identifies the user's cofactor-first response with the repository's
existing high transport and therefore with its exact dyadic compression.
-/

/-- Complete signed replication response of the fixed prefix at the square
endpoint `X_R = R^2 - 1`. -/
def orderedPrimeReplicationResponse (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    canonicalMoebiusWeight c *
      ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
        (Nat.primeCounting R : ℂ))

/-- The `c=1,2` channels cancel everything except the inert top-prime block. -/
theorem orderedPrimeReplication_firstTwo_eq_topCard
    (R : ℕ) :
    (∑ c ∈ ({1, 2} : Finset ℕ),
      canonicalMoebiusWeight c *
        ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
          (Nat.primeCounting R : ℂ))) =
      ((squareRootTopFibrePrimes R).card : ℂ) := by
  have hmu1 : canonicalMoebiusWeight 1 = 1 := by
    simp [canonicalMoebiusWeight]
  have hmu2 : canonicalMoebiusWeight 2 = -1 := by
    unfold canonicalMoebiusWeight
    rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num
  have htop := squareRootTopFibrePrimes_card_add_primeCounting_half R
  have htopC :
      ((squareRootTopFibrePrimes R).card : ℂ) +
          (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) =
        (Nat.primeCounting (squareRootEndpoint R) : ℂ) := by
    exact_mod_cast htop
  have htopDiff :
      (Nat.primeCounting (squareRootEndpoint R) : ℂ) -
          (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) =
        ((squareRootTopFibrePrimes R).card : ℂ) := by
    symm
    exact (eq_sub_iff_add_eq).2 htopC
  calc
    (∑ c ∈ ({1, 2} : Finset ℕ),
      canonicalMoebiusWeight c *
        ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
          (Nat.primeCounting R : ℂ))) =
        (Nat.primeCounting (squareRootEndpoint R) : ℂ) -
          (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) := by
      simp [hmu1, hmu2]
    _ = ((squareRootTopFibrePrimes R).card : ℂ) := htopDiff

/-- **Exact global identification.**  The full ordered replication response is
exactly the existing cofactor-first transport.  No iid or probabilistic input
appears. -/
theorem orderedPrimeReplicationResponse_eq_transport
    (R : ℕ) (hR : 3 ≤ R) :
    orderedPrimeReplicationResponse R = squareRootTransportCofactorFirst R := by
  classical
  let lowC : Finset ℕ := Finset.Icc 3 (R - 1)
  have hset :
      Finset.Ico 1 R = ({1, 2} : Finset ℕ) ∪ lowC := by
    ext c
    simp only [lowC, Finset.mem_Ico, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hdisj : Disjoint ({1, 2} : Finset ℕ) lowC := by
    rw [Finset.disjoint_left]
    intro c hc12 hclow
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc12
    rcases Finset.mem_Icc.mp hclow with ⟨hc3, _hcTop⟩
    omega
  have hmiddle := squareRootMiddleMertensTail_eq_swappedPrimeCounting R hR
  unfold orderedPrimeReplicationResponse
  rw [hset, Finset.sum_union hdisj,
    orderedPrimeReplication_firstTwo_eq_topCard R]
  change ((squareRootTopFibrePrimes R).card : ℂ) +
      (∑ c ∈ Finset.Icc 3 (R - 1),
        canonicalMoebiusWeight c *
          ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
            (Nat.primeCounting R : ℂ))) = squareRootTransportCofactorFirst R
  rw [← hmiddle, squareRootTransportCofactorFirst_eq_primeFirst,
    squareRootTransportPrimeFirst_eq_middleMertensTail_add_topCard R hR]
  ring

/-- **Global deterministic non-iid compression.**  The whole ordered prime
replication of the fixed Möbius prefix is exactly the repository's odd dyadic
boundary mass. -/
theorem orderedPrimeReplicationResponse_eq_dyadicBoundaryMass
    (R : ℕ) (hR : 3 ≤ R) :
    orderedPrimeReplicationResponse R =
      squareRootDyadicTransportBoundaryMass R := by
  rw [orderedPrimeReplicationResponse_eq_transport R hR,
    squareRootTransportCofactorFirst_eq_dyadicBoundaryMass]

/-! ## Iterated fresh-prime Euler finite differences

The post-root response is now reindexed through the *entire* deterministic
Möbius dependence of the fixed prefix.  In reciprocal coordinates a fresh
prime acts by `W(X) - W(X/p)`.  The cutoff travels with the shift, so no raw
seat outside the surviving Boolean face is introduced.
-/

/-- Prime-count response field above the fixed root cutoff. -/
def orderedPrimeWindowWeight (R x : ℕ) : ℂ :=
  (Nat.primeCounting x : ℂ) - (Nat.primeCounting R : ℂ)

/-- Truncated Boolean Euler finite difference in the reciprocal endpoint
coordinate. -/
def eulerFiniteDifferenceResponse
    (P : Finset ℕ) (B X : ℕ) (W : ℕ → ℂ) : ℂ :=
  ∑ t ∈ P.powerset,
    if primeFaceProduct t ≤ B then
      (booleanCubeSign t : ℂ) * W (X / primeFaceProduct t)
    else
      0

/-- **One fresh prime is one exact Boolean difference.** -/
theorem eulerFiniteDifferenceResponse_insert
    {P : Finset ℕ} {p B X : ℕ} (W : ℕ → ℂ)
    (hp : p ∉ P) (hpPrime : p.Prime) :
    eulerFiniteDifferenceResponse (insert p P) B X W =
      eulerFiniteDifferenceResponse P B X W -
        eulerFiniteDifferenceResponse P (B / p) (X / p) W := by
  classical
  unfold eulerFiniteDifferenceResponse
  rw [Finset.sum_powerset_insert hp]
  have hsecond :
      (∑ t ∈ P.powerset,
        if primeFaceProduct (insert p t) ≤ B then
          (booleanCubeSign (insert p t) : ℂ) *
            W (X / primeFaceProduct (insert p t))
        else 0) =
        -(∑ t ∈ P.powerset,
          if primeFaceProduct t ≤ B / p then
            (booleanCubeSign t : ℂ) *
              W ((X / p) / primeFaceProduct t)
          else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hpt : p ∉ t :=
      Finset.notMem_of_mem_powerset_of_notMem ht hp
    have hprod :
        primeFaceProduct (insert p t) = p * primeFaceProduct t := by
      simp [primeFaceProduct, hpt]
    have hsign :
        (booleanCubeSign (insert p t) : ℂ) =
          -(booleanCubeSign t : ℂ) := by
      unfold booleanCubeSign
      rw [Finset.card_insert_of_notMem hpt, pow_succ]
      push_cast
      ring
    have hcut :
        primeFaceProduct (insert p t) ≤ B ↔
          primeFaceProduct t ≤ B / p := by
      rw [hprod]
      constructor
      · intro hle
        apply (Nat.le_div_iff_mul_le hpPrime.pos).2
        simpa [Nat.mul_comm] using hle
      · intro hle
        have hmul := (Nat.le_div_iff_mul_le hpPrime.pos).1 hle
        simpa [Nat.mul_comm] using hmul
    have hdiv :
        X / primeFaceProduct (insert p t) =
          (X / p) / primeFaceProduct t := by
      rw [hprod, Nat.div_div_eq_div_mul]
    by_cases hle : primeFaceProduct t ≤ B / p
    · have hchild : primeFaceProduct (insert p t) ≤ B := hcut.mpr hle
      simp only [hchild, hle, if_true]
      rw [hsign, hdiv]
      ring
    · have hchild : ¬primeFaceProduct (insert p t) ≤ B := by
        intro h
        exact hle (hcut.mp h)
      simp [hchild, hle]
  rw [hsecond]
  ring

/-- The complete fixed-prefix ordered response as one truncated Euler cube. -/
def orderedPrimeReplicationEulerResponse (R : ℕ) : ℂ :=
  eulerFiniteDifferenceResponse
    (primesUpTo R) (R - 1) (squareRootEndpoint R)
    (orderedPrimeWindowWeight R)

/-- **No iid surrogate remains:** the lower Möbius prefix is literally one
truncated Boolean prime cube for the actual prime-count response weight. -/
theorem orderedPrimeReplicationResponse_eq_eulerFiniteDifference
    (R : ℕ) (hR : 1 ≤ R) :
    orderedPrimeReplicationResponse R =
      orderedPrimeReplicationEulerResponse R := by
  classical
  unfold orderedPrimeReplicationResponse orderedPrimeReplicationEulerResponse
  rw [canonicalMoebiusWeighted_Ico_eq_admissibleFaceSum
    R hR (fun c =>
      (Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
        (Nat.primeCounting R : ℂ))]
  rw [admissiblePrimeFaces_pred_eq_lowCube_filter_product_lt R hR]
  unfold eulerFiniteDifferenceResponse
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases hlt : primeFaceProduct t < R
  · have hle : primeFaceProduct t ≤ R - 1 := by omega
    simp [hlt, hle, orderedPrimeWindowWeight]
  · have hnle : ¬primeFaceProduct t ≤ R - 1 := by omega
    simp [hlt, hnle]

/-- The finite-difference cube is exactly the existing high transport. -/
theorem orderedPrimeReplicationEulerResponse_eq_transport
    (R : ℕ) (hR : 3 ≤ R) :
    orderedPrimeReplicationEulerResponse R =
      squareRootTransportCofactorFirst R := by
  rw [← orderedPrimeReplicationResponse_eq_eulerFiniteDifference R (by omega)]
  exact orderedPrimeReplicationResponse_eq_transport R hR

/-- And therefore exactly the compiled dyadic boundary compression. -/
theorem orderedPrimeReplicationEulerResponse_eq_dyadicBoundaryMass
    (R : ℕ) (hR : 3 ≤ R) :
    orderedPrimeReplicationEulerResponse R =
      squareRootDyadicTransportBoundaryMass R := by
  rw [orderedPrimeReplicationEulerResponse_eq_transport R hR,
    squareRootTransportCofactorFirst_eq_dyadicBoundaryMass]

/-- The dual reciprocal-weighted convention is already native in the repo and
satisfies the exact `1 - (1/p) S_p` recurrence. -/
theorem reciprocalWeightedEulerFiniteDifference_insert
    {P : Finset ℕ} {p X : ℕ}
    (hp : p ∉ P) (hpPrime : p.Prime) :
    primorialTruncatedSignedReciprocalCube (insert p P) X =
      primorialTruncatedSignedReciprocalCube P X -
        (1 / (p : ℝ)) *
          primorialTruncatedSignedReciprocalCube P (X / p) :=
  primorialTruncatedSignedReciprocalCube_insert hp hpPrime

/-! ## Exact post-cancellation live exposure

The first-jump fibre below is *after* the predecessor-dense cube has already
collapsed to the smaller square-root universe.  Thus the exposure counts only
the exact first-failure boundary; it is not a generic remaining-seat count.
-/

/-- Signed first-jump aggregate with all state signs intact. -/
def signedLiveFirstJumpAggregate (R : ℕ) : ℂ :=
  ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
    lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x

/-- Nonnegative live cancellation exposure.  The norm is taken only after each
exact first-failure predecessor fibre has been formed. -/
def liveCancellationExposure (R : ℕ) : ℝ :=
  ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
    ‖lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x‖

/-- Signed live mass is dominated by the post-cancellation exposure. -/
theorem norm_signedLiveFirstJumpAggregate_le_liveCancellationExposure
    (R : ℕ) :
    ‖signedLiveFirstJumpAggregate R‖ ≤ liveCancellationExposure R := by
  unfold signedLiveFirstJumpAggregate liveCancellationExposure
  exact norm_sum_le _ _

/-- **Exact remaining live-exposure theorem.**  This is stated on the compiled
first-failure carrier, not on Mertens and not on raw prime seats. -/
def LiveCancellationExposureBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      liveCancellationExposure R ≤
        C * (R : ℝ) * (Real.log (R : ℝ) + 1)

/-- The exposure theorem immediately controls the signed first-jump aggregate. -/
theorem signedLiveFirstJumpAggregate_polylog_of_liveExposure
    (h : LiveCancellationExposureBound) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 3 ≤ R →
        ‖signedLiveFirstJumpAggregate R‖ ≤
          C * (R : ℝ) * (Real.log (R : ℝ) + 1) := by
  rcases h with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro R hR
  exact (norm_signedLiveFirstJumpAggregate_le_liveCancellationExposure R).trans
    (hbound R hR)

/-- The exact square-root predecessor contraction isolates this signed live
aggregate as the only first-jump part of the oriented ledger. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sqrtDense_add_signedLive
    (R : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger R =
      (∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre R x) +
        signedLiveFirstJumpAggregate R := by
  simpa [signedLiveFirstJumpAggregate] using
    lowWheelCanonicalDowncrossOrientedLedger_eq_sqrtDense_add_firstJump R

end RHLean.Proof
