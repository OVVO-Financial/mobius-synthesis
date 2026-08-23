import Mathlib
import RHLean.Analysis.PrimeDilateCofactorPrimeWindows
import RHLean.Analysis.PrimeSieveAbelIdentity
import RHLean.Analysis.SquareRootPrimeCountGap
import RHLean.Arithmetic.TruncatedCubeMertensPrefix
import RHLean.Proof.PrimeCombVisualizationRecurrence

/-!
# Sequential coherence of the square-root middle section

The square-root middle section now has several exact coordinate systems in the
repository.  They are useful only if their distinct mechanisms remain visible.
This module composes the existing interfaces without replacing any of them:

* the harmonic quotient layers from `SquareRootPrimeCountGap`;
* the older reciprocal quotient fibres and prime-count/Li discrepancies from
  `PrimeSieveQuotientPNTError`;
* the Abel telescope from `PrimeSieveAbelIdentity`;
* the complete-square prime-dilate cofactor windows from
  `PrimeDilateCofactorPrimeWindows`;
* the finite frozen-prime universe and its fresh-prime recurrence from
  `PrimeCombVisualizationDynamics`;
* the local fresh-prime parent/child law and literal kill/flip recurrence from
  `PrimeCombVisualizationRecurrence`.

The resulting statements are all finite exact identities.  In particular:

* the `d = 2` harmonic layer is the already-existing reciprocal quotient fibre
  `(X/3,X/2]`, and its Mertens weight is exactly zero;
* the whole middle is the old reciprocal-prime-tail with only the inert `d = 1`
  top fibre removed;
* the swapped `mu(c) pi(X/c)` hyperbola exposes the exact
  `-pi(R) M(R-1)` edge, but this reindexing is not itself a contraction;
* the Abel discrepancy and the prime-dilate cofactor-window discrepancy are two
  exact coordinates of the same centered error;
* the weighted-middle bias from the unit model recombines exactly into full
  transport minus the smooth mass, and equivalently into the harmonic layers
  `d >= 2` plus the inert top minus the smooth mass;
* the finite frozen universe at primes `<= R` is exactly the square-root smooth
  mass, and after that stopping point every fresh prime `q > R` subtracts the
  already-complete ordinary Mertens value at `floor(X_R/q)`;
* the aggregate middle/top readouts do not replace the sequential mechanism:
  a fresh prime still acts parent by parent, with first-hit and reachable-parent
  channels kept separate before any sum is taken.

The finite frozen universe is deliberately kept distinct from the separate
all-plus visualization state used by `PrimeSievePostSqrtGap`.  The internal
cofactor-prefix cancellation `mu(1)+mu(2)=0` is also deliberately not identified
with the distinct source pairing `q <-> 2q`.  No interval-PNT estimate,
averaging claim, recursive square-root hierarchy, or RH-scale saving is
introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- At the complete-square endpoint the generic quotient support ends exactly
at `R-1`:

`floor((R^2-1)/(R+1)) = R-1`.
-/
theorem squareRootQuotientSupportTop_eq_pred
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootEndpoint R / (R + 1) = R - 1 := by
  unfold squareRootEndpoint
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel hR
  have hsq1 : 1 ≤ R ^ 2 := by nlinarith
  have hsqpred : R ^ 2 - 1 + 1 = R ^ 2 := Nat.sub_add_cancel hsq1
  have hfactor : (R + 1) * (R - 1) = R ^ 2 - 1 := by
    nlinarith
  rw [← hfactor]
  exact Nat.mul_div_right (R - 1) (by omega : 0 < R + 1)

/-- The harmonic tail at `j=2` is literally the middle Mertens tail from the
three-section decomposition. -/
@[simp] theorem squareRootMiddleHarmonicTail_two_eq_middle
    (R : ℕ) :
    squareRootMiddleHarmonicTail R 2 = squareRootMiddleMertensTail R := by
  rfl

/-- The new harmonic layer is not a second interval construction: it is exactly
the repository's pre-existing reciprocal quotient interval, with the prime
predicate applied. -/
theorem squareRootMiddleHarmonicLayerPrimes_eq_reciprocalInterval
    (R j : ℕ) :
    squareRootMiddleHarmonicLayerPrimes R j =
      (primeSieveReciprocalInterval R (squareRootEndpoint R) j).filter Nat.Prime := by
  classical
  ext q
  simp [squareRootMiddleHarmonicLayerPrimes,
    primeSieveReciprocalInterval, primeSieveReciprocalLower,
    primeSieveReciprocalUpper]
  omega

/-- Equivalently, for positive quotient index `j`, the harmonic layer is the
prime subset of the older literal quotient fibre `floor(X_R/q)=j`. -/
theorem squareRootMiddleHarmonicLayerPrimes_eq_quotientFiber
    (R j : ℕ) (hj : 0 < j) :
    squareRootMiddleHarmonicLayerPrimes R j =
      (primeSieveQuotientFiber R (squareRootEndpoint R) j).filter Nat.Prime := by
  rw [primeSieveQuotientFiber_eq_reciprocalInterval
    R (squareRootEndpoint R) j hj]
  exact squareRootMiddleHarmonicLayerPrimes_eq_reciprocalInterval R j

/-- The layer cardinality used by the harmonic peel is exactly the older
reciprocal-interval prime-count object. -/
theorem squareRootMiddleHarmonicLayer_card_eq_reciprocalPrimeCount
    (R j : ℕ) :
    ((squareRootMiddleHarmonicLayerPrimes R j).card : ℂ) =
      primeSieveReciprocalPrimeCount R (squareRootEndpoint R) j := by
  rw [squareRootMiddleHarmonicLayerPrimes_eq_reciprocalInterval,
    primeSieveReciprocalPrimeCount_eq_card]

/-- The one-layer peel written directly in the pre-existing quotient-fibre
language.  This is the same recurrence, not a new decomposition. -/
theorem squareRootMiddleHarmonicTail_peel_reciprocal
    (R j : ℕ) (hj : 2 ≤ j) (hjR : j < R) :
    squareRootMiddleHarmonicTail R j =
      mertensSummatory j *
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) j +
        squareRootMiddleHarmonicTail R (j + 1) := by
  rw [squareRootMiddleHarmonicTail_peel R j hj hjR,
    squareRootMiddleHarmonicLayer_card_eq_reciprocalPrimeCount]

/-- The reciprocal quotient fibre `d=1` is exactly the inert top-prime block. -/
theorem squareRootReciprocalPrimeCount_one_eq_topCard
    (R : ℕ) (hR : 3 ≤ R) :
    primeSieveReciprocalPrimeCount R (squareRootEndpoint R) 1 =
      ((squareRootTopFibrePrimes R).card : ℂ) := by
  have hpow : R ^ 2 = R * R := by ring
  have hge : 3 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
  have hmul : R * 2 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hhalf : R ≤ squareRootEndpoint R / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 hmul
  have hinterval :
      primeSieveReciprocalInterval R (squareRootEndpoint R) 1 =
        Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R) := by
    unfold primeSieveReciprocalInterval primeSieveReciprocalLower
      primeSieveReciprocalUpper
    simp [max_eq_right hhalf]
  unfold squareRootTopFibrePrimes
  rw [primeSieveReciprocalPrimeCount_eq_card, hinterval]

/-- **The whole middle in the old quotient-fibre coordinates.**  The complete
reciprocal prime tail has quotient support `1,...,R-1`; removing the inert
`d=1` fibre leaves exactly the middle layers `2,...,R-1`.

Thus the harmonic peel from the merged middle theorem is an interface to the
older quotient-fibre machinery, not a competing hierarchy.
-/
theorem squareRootMiddleMertensTail_eq_reciprocalPrimeLayers
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleMertensTail R =
      ∑ d ∈ Finset.Icc 2 (R - 1),
        primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
          mertensSummatory d := by
  classical
  have hsupport :
      squareRootEndpoint R / (R + 1) = R - 1 :=
    squareRootQuotientSupportTop_eq_pred R (by omega)
  have htransportRecip :
      squareRootTransportPrimeFirst R =
        primeSieveReciprocalPrimeTail R (squareRootEndpoint R) := by
    rw [squareRootTransportPrimeFirst_eq_mertensTransform R (by omega)]
    rw [← primeSieveMertensPrimeTail_squareRootEndpoint R]
    exact primeSieveMertensPrimeTail_eq_reciprocalPrimeTail
      R (squareRootEndpoint R)
  unfold primeSieveReciprocalPrimeTail primeSieveQuotientSupport at htransportRecip
  rw [hsupport] at htransportRecip
  have hset :
      Finset.Icc 1 (R - 1) =
        ({1} : Finset ℕ) ∪ Finset.Icc 2 (R - 1) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({1} : Finset ℕ) (Finset.Icc 2 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro d hd1 hdrest
    rw [Finset.mem_singleton] at hd1
    rcases Finset.mem_Icc.mp hdrest with ⟨hd2, _⟩
    omega
  rw [hset, Finset.sum_union hdisj] at htransportRecip
  simp [squareRootReciprocalPrimeCount_one_eq_topCard R hR] at htransportRecip
  have hsplit :=
    squareRootTransportPrimeFirst_eq_middleMertensTail_add_topCard R hR
  calc
    squareRootMiddleMertensTail R =
        squareRootTransportPrimeFirst R -
          ((squareRootTopFibrePrimes R).card : ℂ) := by
      rw [hsplit]
      ring
    _ = ∑ d ∈ Finset.Icc 2 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d := by
      rw [htransportRecip]
      ring

private theorem sum_canonicalMoebiusWeight_three_to_pred_eq_mertens
    (R : ℕ) (hR : 3 ≤ R) :
    (∑ c ∈ Finset.Icc 3 (R - 1), canonicalMoebiusWeight c) =
      mertensSummatory (R - 1) := by
  classical
  have hset :
      Finset.Icc 1 (R - 1) =
        ({1, 2} : Finset ℕ) ∪ Finset.Icc 3 (R - 1) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({1, 2} : Finset ℕ) (Finset.Icc 3 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro c hc12 hcrest
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc12
    rcases Finset.mem_Icc.mp hcrest with ⟨hc3, _⟩
    omega
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
  unfold cofactorMobiusPrefixMass
  rw [hset, Finset.sum_union hdisj]
  have h12 :
      (∑ c ∈ ({1, 2} : Finset ℕ), canonicalMoebiusWeight c) = 0 := by
    simp [canonicalMoebiusWeight,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  rw [h12, zero_add]

/-- The swapped hyperbola with the inert-style root edge made explicit:

`T_mid = sum_{3<=c<R} mu(c) pi(floor(X_R/c)) - pi(R) M(R-1)`.

This is exact bookkeeping.  The `c<R` support and the hyperbola reindexing do
not by themselves provide an analytic saving.
-/
theorem squareRootMiddleMertensTail_eq_swappedPrimeCounting_sub_rootEdge
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleMertensTail R =
      (∑ c ∈ Finset.Icc 3 (R - 1),
        canonicalMoebiusWeight c *
          (Nat.primeCounting (squareRootEndpoint R / c) : ℂ)) -
        (Nat.primeCounting R : ℂ) * mertensSummatory (R - 1) := by
  rw [squareRootMiddleMertensTail_eq_swappedPrimeCounting R hR]
  have hsum := sum_canonicalMoebiusWeight_three_to_pred_eq_mertens R hR
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hsecond :
      (∑ c ∈ Finset.Icc 3 (R - 1),
        canonicalMoebiusWeight c * (Nat.primeCounting R : ℂ)) =
        (Nat.primeCounting R : ℂ) * mertensSummatory (R - 1) := by
    rw [← Finset.sum_mul, hsum]
    ring
  rw [hsecond]

/-- **Middle as the complete-square prime-dilate windows minus the inert top.**
For any fixed prime `p`, the older prime-dilate compression removes every
recursive Mertens weight from the full upper-prime transport.  Subtracting the
known `d=1` top block gives the present middle target exactly.
-/
theorem squareRootMiddleMertensTail_eq_primeDilateWindows_sub_topCard
    (p R : ℕ) (hp : p.Prime) (hR : 3 ≤ R) :
    squareRootMiddleMertensTail R =
      squarePrimeDilateCofactorPrimeCountTransform p R -
        ((squareRootTopFibrePrimes R).card : ℂ) := by
  calc
    squareRootMiddleMertensTail R =
        squareRootTransportPrimeFirst R -
          ((squareRootTopFibrePrimes R).card : ℂ) := by
      rw [squareRootTransportPrimeFirst_eq_middleMertensTail_add_topCard R hR]
      ring
    _ = squarePrimeDilateCofactorPrimeCountTransform p R -
          ((squareRootTopFibrePrimes R).card : ℂ) := by
      rw [squareRootTransportPrimeFirst_eq_squarePrimeDilateCofactorPrimeCountTransform
        p R hp (by omega)]

/-- **Weighted-bias closure in the old prime-dilate coordinates.**  Once the
population gap and unit model from the weighted-middle target are expanded, the
entire centered bias is exactly full upper-prime transport minus the smooth
mass.  Thus the PNT-scale middle/top population mismatch is a bookkeeping bias
to be absorbed by the sequential transport; it is not a saving term. -/
theorem squareRootMiddleBiasResidual_eq_primeDilateWindows_sub_smooth
    (p R : ℕ) (hp : p.Prime) (hR : 3 ≤ R) :
    squareRootMiddleBiasResidual R =
      squarePrimeDilateCofactorPrimeCountTransform p R -
        squareRootSmoothMass (R - 1) := by
  unfold squareRootMiddleBiasResidual squareRootMiddleUnitModelDefect
    squareRootOrientedMiddleThrowMass squareRootMiddleTopPrimeCountGapMass
  rw [squareRootMiddleMertensTail_eq_primeDilateWindows_sub_topCard p R hp hR]
  ring

/-- The same weighted-bias target in harmonic coordinates.  This is the exact
interface for peeling known long reciprocal fibres while leaving a later short
fibre tail untouched.  No interval estimate is used here. -/
theorem squareRootMiddleBiasResidual_eq_reciprocalLayers_add_top_sub_smooth
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleBiasResidual R =
      (∑ d ∈ Finset.Icc 2 (R - 1),
        primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
          mertensSummatory d) +
        ((squareRootTopFibrePrimes R).card : ℂ) -
          squareRootSmoothMass (R - 1) := by
  unfold squareRootMiddleBiasResidual squareRootMiddleUnitModelDefect
    squareRootOrientedMiddleThrowMass squareRootMiddleTopPrimeCountGapMass
  rw [squareRootMiddleMertensTail_eq_reciprocalPrimeLayers R hR]
  ring

/-- **Abel and prime-dilate coherence.**  At the square endpoint, the older Abel
coordinate and the older parent/child cofactor-window coordinate are exactly
the same centered PNT error.  This is an identity between two prior interfaces,
not an estimate on either one.
-/
theorem squareRootAbelDiscrepancy_eq_primeDilateWindowDiscrepancy
    (p R : ℕ) (hp : p.Prime) (hR : 1 ≤ R) :
    primeSieveMoebiusDiscrepancySum R (squareRootEndpoint R) -
        primeSieveAbelBoundary R (squareRootEndpoint R) =
      squarePrimeDilateCofactorDiscrepancyTransform p R := by
  calc
    primeSieveMoebiusDiscrepancySum R (squareRootEndpoint R) -
        primeSieveAbelBoundary R (squareRootEndpoint R) =
      primeSievePNTError R (squareRootEndpoint R) :=
        (primeSievePNTError_eq_moebiusDiscrepancySum_sub_abelBoundary
          R (squareRootEndpoint R)).symm
    _ = squarePrimeDilateCofactorDiscrepancyTransform p R :=
      primeSievePNTError_squareRootEndpoint_eq_squarePrimeDilateCofactorDiscrepancyTransform
        p R hp (by omega)

/-! ## Frozen-universe chronology at the square root -/

/-- Once the ambient prime set contains every prime through the numerical
cutoff, adding still larger prime coordinates cannot change the frozen mass.
Any face that actually fits below `X` already uses only primes at most `X`. -/
private theorem frozenPrimeUniverseMass_primesUpTo_saturates
    {X Y : ℕ} (hXY : X ≤ Y) :
    frozenPrimeUniverseMass (primesUpTo Y) X =
      frozenPrimeUniverseMass (primesUpTo X) X := by
  classical
  rw [frozenPrimeUniverseMass_eq_cutoffSum,
    frozenPrimeUniverseMass_eq_cutoffSum]
  have hsub : (primesUpTo X).powerset ⊆ (primesUpTo Y).powerset := by
    intro t ht
    apply Finset.mem_powerset.mpr
    intro p hp
    have hpX := mem_primesUpTo.mp ((Finset.mem_powerset.mp ht) hp)
    exact mem_primesUpTo.mpr ⟨hpX.1, hpX.2.trans hXY⟩
  symm
  apply Finset.sum_subset hsub
  intro t htY htNotX
  have htSubY := Finset.mem_powerset.mp htY
  by_cases hfit : primeFaceProduct t ≤ X
  · have htX : t ∈ (primesUpTo X).powerset := by
      apply Finset.mem_powerset.mpr
      intro p hp
      have hpY := mem_primesUpTo.mp (htSubY hp)
      have hprodPos : 0 < primeFaceProduct t := by
        unfold primeFaceProduct
        exact Finset.prod_pos fun q hq =>
          (prime_of_mem_primesUpTo (htSubY hq)).pos
      have hpdiv : p ∣ primeFaceProduct t := by
        unfold primeFaceProduct
        exact Finset.dvd_prod_of_mem id hp
      have hpLeProd : p ≤ primeFaceProduct t := Nat.le_of_dvd hprodPos hpdiv
      exact mem_primesUpTo.mpr ⟨hpY.1, hpLeProd.trans hfit⟩
    exact (htNotX htX).elim
  · simp [hfit]

/-- Saturated frozen prime universes are ordinary Mertens prefixes.  This is the
precise reason that every post-root fresh prime reads an already-completed
lower-scale Mertens value rather than another provisional frozen value. -/
theorem frozenPrimeUniverseMass_primesUpTo_cast_eq_mertens
    {X Y : ℕ} (hXY : X ≤ Y) :
    ((frozenPrimeUniverseMass (primesUpTo Y) X : ℤ) : ℂ) =
      mertensSummatory X := by
  rw [frozenPrimeUniverseMass_primesUpTo_saturates hXY]
  unfold frozenPrimeUniverseMass
  rw [truncatedPrimeCube_eq_moebiusPrefix]
  unfold mertensSummatory
  push_cast
  rfl

/-- Every reciprocal cutoff seen by a fresh prime strictly above the square-root
stop lies strictly below `R`.  No upper-half hypothesis is needed. -/
theorem squareRootEndpoint_div_lt_root_of_postRoot
    {R q : ℕ} (hR : 1 ≤ R) (hRq : R < q) :
    squareRootEndpoint R / q < R := by
  have hqpos : 0 < q := by omega
  apply (Nat.div_lt_iff_lt_mul hqpos).2
  have hRRlt : R * R < R * q :=
    Nat.mul_lt_mul_of_pos_left hRq (by omega)
  have hRRpos : 0 < R * R := by positivity
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    rw [show R ^ 2 = R * R by ring]
    omega
  exact hXlt.trans hRRlt

/-- **Completed-parent bridge.**  Immediately before a fresh prime `q > R`
acts, its parent cutoff `floor(X_R/q)` is below `R`, hence below `q`.  The old
prime universe therefore already contains every prime relevant to that cutoff,
so its frozen parent mass is exactly ordinary `M(floor(X_R/q))`. -/
theorem squareRootFrozenParentMass_eq_mertens
    {R q : ℕ} (hR : 1 ≤ R) (hRq : R < q) :
    ((frozenPrimeUniverseMass (primesUpTo (q - 1))
        (squareRootEndpoint R / q) : ℤ) : ℂ) =
      mertensSummatory (squareRootEndpoint R / q) := by
  apply frozenPrimeUniverseMass_primesUpTo_cast_eq_mertens
  have hcut := squareRootEndpoint_div_lt_root_of_postRoot hR hRq
  omega

/-- **Literal post-root fresh-prime step.**  This is the frozen-universe game in
its exact square-root chronology.  After the stop at `R`, admitting a fresh
prime `q` changes the full `X_R` state by subtracting the already-completed
ordinary lower-scale value `M(floor(X_R/q))`.

This theorem is about the finite frozen cube, not the separate all-plus comb. -/
theorem squareRootFrozenPrimeUniverse_primesUpTo_step
    (R q : ℕ) (hR : 1 ≤ R) (hq : q.Prime) (hRq : R < q) :
    ((frozenPrimeUniverseMass (primesUpTo q) (squareRootEndpoint R) : ℤ) : ℂ) =
      ((frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R) : ℤ) : ℂ) -
        mertensSummatory (squareRootEndpoint R / q) := by
  have hqNot : q ∉ primesUpTo (q - 1) := by
    simp only [mem_primesUpTo, not_and]
    intro _hqPrime
    omega
  have hraw :
      frozenPrimeUniverseMass (primesUpTo q) (squareRootEndpoint R) =
        frozenPrimeUniverseMass (primesUpTo (q - 1)) (squareRootEndpoint R) -
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / q) := by
    rw [primesUpTo_eq_insert_pred_of_prime hq]
    exact frozenPrimeUniverseMass_insert hqNot hq
  have hcast := congrArg (fun z : ℤ => (z : ℂ)) hraw
  push_cast at hcast
  rw [squareRootFrozenParentMass_eq_mertens hR hRq] at hcast
  exact hcast

private theorem primesUpTo_succ_eq_of_not_prime
    (n : ℕ) (hnot : ¬ (n + 1).Prime) :
    primesUpTo (n + 1) = primesUpTo n := by
  ext p
  simp only [mem_primesUpTo]
  constructor
  · rintro ⟨hpPrime, hple⟩
    refine ⟨hpPrime, ?_⟩
    have hpne : p ≠ n + 1 := by
      intro hpeq
      subst p
      exact hnot hpPrime
    omega
  · rintro ⟨hpPrime, hple⟩
    exact ⟨hpPrime, by omega⟩

/-- **Sequential frozen-universe telescope.**  Starting from the prime universe
frozen at `R`, admit the later primes in increasing order through `y`.  The
state after those admissions is the frozen root state minus exactly the sum of
the lower-scale Mertens probes produced by the fresh-prime recurrence.

No aggregate identity is used to define the sequence: this is obtained by
iterating the one-prime update above, with composite integers producing no
state change. -/
theorem squareRootFrozenPrimeUniverse_sequence
    (R y : ℕ) (hR : 1 ≤ R) (hRy : R ≤ y) :
    ((frozenPrimeUniverseMass (primesUpTo y) (squareRootEndpoint R) : ℤ) : ℂ) =
      ((frozenPrimeUniverseMass (primesUpTo R) (squareRootEndpoint R) : ℤ) : ℂ) -
        ∑ q ∈ Finset.Ioc R y,
          if q.Prime then mertensSummatory (squareRootEndpoint R / q) else 0 := by
  induction y, hRy using Nat.le_induction with
  | base => simp
  | succ y hRy ih =>
      rw [Finset.sum_Ioc_succ_top hRy]
      by_cases hprime : (y + 1).Prime
      · have hRq : R < y + 1 := by omega
        have hstep :=
          squareRootFrozenPrimeUniverse_primesUpTo_step R (y + 1) hR hprime hRq
        have hpred : y + 1 - 1 = y := by omega
        rw [hpred] at hstep
        rw [if_pos hprime, hstep, ih]
        ring
      · have hsame := primesUpTo_succ_eq_of_not_prime y hprime
        rw [if_neg hprime, add_zero, hsame, ih]

/-- **The square-root stopping state is exactly the smooth/low edge.**  The
finite frozen cube with precisely the primes `<= R` is not the all-plus comb
state.  It is exactly

`sum_{n <= X_R, P+(n) <= R} mu(n) = squareRootSmoothMass (R-1)`.

The proof identifies it by continuing the same frozen-prime sequence to the
fully saturated universe and comparing with the already-proved exact
`smooth - transport` decomposition. -/
theorem squareRootFrozenPrimeUniverseMass_eq_smooth
    (R : ℕ) (hR : 3 ≤ R) :
    ((frozenPrimeUniverseMass (primesUpTo R) (squareRootEndpoint R) : ℤ) : ℂ) =
      squareRootSmoothMass (R - 1) := by
  have hRX : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hRR : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  have hseq :=
    squareRootFrozenPrimeUniverse_sequence R (squareRootEndpoint R) (by omega) hRX
  have hfinal :
      ((frozenPrimeUniverseMass (primesUpTo (squareRootEndpoint R))
          (squareRootEndpoint R) : ℤ) : ℂ) =
        mertensSummatory (squareRootEndpoint R) :=
    frozenPrimeUniverseMass_primesUpTo_cast_eq_mertens (le_refl _)
  rw [hfinal] at hseq
  rw [← squareRootTransportPrimeFirst_eq_mertensTransform R (by omega)] at hseq
  have hclock :
      mertensSummatory (squareRootEndpoint R) = squarePrefixMertens (R - 1) := by
    unfold squarePrefixMertens squarePrefixEndpoint squareRootEndpoint
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R)]
  rw [hclock] at hseq
  have hdecomp :
      squarePrefixMertens (R - 1) =
        squareRootSmoothMass (R - 1) - squareRootTransportPrimeFirst R := by
    rw [squarePrefixMertens_eq_squareRootSmooth_sub_transport]
    rw [squareRootTransportMass_pred_eq_cofactorFirst R (by omega),
      squareRootTransportCofactorFirst_eq_primeFirst]
  calc
    ((frozenPrimeUniverseMass (primesUpTo R) (squareRootEndpoint R) : ℤ) : ℂ) =
        squarePrefixMertens (R - 1) + squareRootTransportPrimeFirst R := by
      calc
        ((frozenPrimeUniverseMass (primesUpTo R) (squareRootEndpoint R) : ℤ) : ℂ) =
            (((frozenPrimeUniverseMass (primesUpTo R)
                (squareRootEndpoint R) : ℤ) : ℂ) -
              squareRootTransportPrimeFirst R) + squareRootTransportPrimeFirst R := by
                ring
        _ = squarePrefixMertens (R - 1) + squareRootTransportPrimeFirst R := by
          rw [← hseq]
    _ = squareRootSmoothMass (R - 1) := by
      rw [hdecomp]
      ring

/-- After all middle primes have acted, but before the inert top primes act, the
frozen-universe state is exactly `smooth - middle`.  This is a chronological
statement, not a new harmonic coordinate. -/
theorem squareRootFrozenPrimeUniverse_after_middle
    (R : ℕ) (hR : 3 ≤ R) :
    ((frozenPrimeUniverseMass (primesUpTo (squareRootEndpoint R / 2))
        (squareRootEndpoint R) : ℤ) : ℂ) =
      squareRootSmoothMass (R - 1) - squareRootMiddleMertensTail R := by
  have hmul : R * 2 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    rw [show R ^ 2 = R * R by ring]
    have hge : 3 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
    omega
  have hhalf : R ≤ squareRootEndpoint R / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 hmul
  have hseq :=
    squareRootFrozenPrimeUniverse_sequence R (squareRootEndpoint R / 2)
      (by omega) hhalf
  rw [squareRootFrozenPrimeUniverseMass_eq_smooth R hR] at hseq
  simpa [squareRootMiddleMertensTail] using hseq

/-- A middle fresh prime performs the same one-prime frozen update, and its
ordinary Mertens probe lies exactly in the completed lower interval `[2,R)`. -/
theorem squareRootFrozenPrimeUniverse_middle_step
    {R q : ℕ} (hR : 3 ≤ R) (hqPrime : q.Prime)
    (hq : q ∈ Finset.Ioc R (squareRootEndpoint R / 2)) :
    ((frozenPrimeUniverseMass (primesUpTo q) (squareRootEndpoint R) : ℤ) : ℂ) =
      ((frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R) : ℤ) : ℂ) -
        mertensSummatory (squareRootEndpoint R / q) ∧
      2 ≤ squareRootEndpoint R / q ∧ squareRootEndpoint R / q < R := by
  refine ⟨?_, squareRootMiddleQuotient_range (by omega) hq⟩
  exact squareRootFrozenPrimeUniverse_primesUpTo_step
    R q (by omega) hqPrime (Finset.mem_Ioc.mp hq).1

/-- A top fresh prime performs the same one-prime update, but now its completed
parent probe is the constant atom `M(1)=1`; hence each such prime subtracts
exactly one unit from the frozen state. -/
theorem squareRootFrozenPrimeUniverse_top_step_eq_sub_one
    {R q : ℕ} (hR : 3 ≤ R) (hqPrime : q.Prime)
    (hq : q ∈ Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R)) :
    ((frozenPrimeUniverseMass (primesUpTo q) (squareRootEndpoint R) : ℤ) : ℂ) =
      ((frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R) : ℤ) : ℂ) - 1 := by
  rcases Finset.mem_Ioc.mp hq with ⟨hqHalf, hqX⟩
  have hmul : R * 2 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    rw [show R ^ 2 = R * R by ring]
    have hge : 3 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
    omega
  have hhalf : R ≤ squareRootEndpoint R / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 hmul
  have hRq : R < q := hhalf.trans_lt hqHalf
  rw [squareRootFrozenPrimeUniverse_primesUpTo_step R q (by omega) hqPrime hRq]
  have hdiv : squareRootEndpoint R / q = 1 :=
    squareRootEndpoint_div_eq_one_of_top_fibre hqPrime.pos (by omega) hqX
  rw [hdiv]
  have hM1 : mertensSummatory 1 = 1 := by
    rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
    simp [cofactorMobiusPrefixMass, canonicalMoebiusWeight]
  rw [hM1]

/-- At the fully saturated endpoint the frozen universe is ordinary Mertens.
Together with the root, middle, and top theorems above this closes the exact
chronology

`frozen smooth -> middle probes -> unit top probes -> ordinary Mertens`.
-/
theorem squareRootFrozenPrimeUniverse_at_endpoint_eq_mertens
    (R : ℕ) :
    ((frozenPrimeUniverseMass (primesUpTo (squareRootEndpoint R))
        (squareRootEndpoint R) : ℤ) : ℂ) =
      mertensSummatory (squareRootEndpoint R) :=
  frozenPrimeUniverseMass_primesUpTo_cast_eq_mertens (le_refl _)

/-! ## Sequential mechanism retained underneath the readouts -/

/-- **Separate all-plus visualization state.**  This is not the frozen smooth
mass above.  The all-plus comb keeps unresolved high-prime sources with
provisional signs, so before the upper primes act it equals `smooth + transport`.
Its gap to final Mertens is therefore twice the middle-plus-top transport. -/
theorem allPlusSquareRootPrimeCombMass_sub_mertens_eq_two_middle_add_topCard
    (R : ℕ) (hR : 3 ≤ R) :
    allPlusSquareRootPrimeCombMass R - squarePrefixMertens (R - 1) =
      2 * (squareRootMiddleMertensTail R +
        ((squareRootTopFibrePrimes R).card : ℂ)) := by
  rw [allPlusSquareRootPrimeCombMass_sub_mertens_eq_two_transport R (by omega)]
  rw [squareRootTransportMass_pred_eq_cofactorFirst R (by omega)]
  rw [squareRootTransportCofactorFirst_eq_primeFirst]
  rw [squareRootTransportPrimeFirst_eq_middleMertensTail_add_topCard R hR]

/-- Square-endpoint specialization of the local parentwise fresh-prime law.
The first-hit seat and the opposite-signed reachable parent remain separate
before any frame sum is taken. -/
theorem squareRootFreshPrimeChildContribution_eq_firstHit_sub_reachableParent
    {S t : Finset ℕ} {p R : ℕ}
    (hp : p ∉ S) (ht : t ∈ S.powerset) :
    frozenFreshPrimeChildContribution p (squareRootEndpoint R) t =
      frozenFreshPrimeFirstHitContribution p (squareRootEndpoint R) t -
        frozenFreshPrimeReachableParentContribution p (squareRootEndpoint R) t := by
  exact frozenFreshPrimeChildContribution_eq_firstHit_sub_reachableParent hp ht

/-- Square-endpoint specialization of the sequential fresh-prime state update.
This retains the old state, reachable proper-parent mass, and first-hit boundary
as three visible channels. -/
theorem squareRootFrozenPrimeUniverseMass_insert_eq_sequential_channels
    {S : Finset ℕ} {p R : ℕ} (hp : p ∉ S) :
    frozenPrimeUniverseMass (insert p S) (squareRootEndpoint R) =
      frozenPrimeUniverseMass S (squareRootEndpoint R) -
        frozenPrimeUniverseReachableProperParentMass S p (squareRootEndpoint R) +
          frozenPrimeUniverseFirstHitBoundaryMass p (squareRootEndpoint R) := by
  exact frozenPrimeUniverseMass_insert_eq_old_sub_reachableParent_add_firstHit hp

/-- The literal increasing-prime animation at the square endpoint: square
collisions delete old mass and later touches reverse old mass, producing the
factor `2` on the flip channel.  This remains the primitive step when the
harmonic layers are later accumulated. -/
theorem squareRootPrimeCombFramePrefixMass_primesUpTo_step
    (R p : ℕ) (hp : p.Prime) :
    primeCombFramePrefixMass (primesUpTo p) (squareRootEndpoint R) =
      primeCombFramePrefixMass (primesUpTo (p - 1)) (squareRootEndpoint R) -
        primeCombFrameKillChannelMass (primesUpTo (p - 1)) p
          (squareRootEndpoint R) -
          2 * primeCombFrameFlipChannelMass (primesUpTo (p - 1)) p
            (squareRootEndpoint R) := by
  exact primeCombFramePrefixMass_primesUpTo_step p (squareRootEndpoint R) hp

end RHLean.Proof