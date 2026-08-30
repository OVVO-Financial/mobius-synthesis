import Mathlib
import RHLean.Proof.LowPrimeCompletedPartnerWindowFold

/-!
# Combined born/high finite differences at one fresh low prime

The high parent/child response from `LowPrimeParentChildWindowDifference` has
three exact cases.  The important empirical correction is that the middle case
`a <= K < p*a` carries substantial mass, so the born and high channels must be
kept together before any estimate.

This module makes that combination literal.

First, for every cofactor `c < R`, all auxiliary cutoffs in the born partner
set are automatic: a prime partner lies exactly in

`P+(c) < q <= c`.

Consequently, on every old parent whose fresh child remains below `R`, the born
parent/child finite difference is an explicit difference of two prime
intervals.  We then add this signed born difference to the high response and
retain the complete three-way geometry:

* `p*a <= K`: only the born interval difference remains;
* `a <= K < p*a`: the born interval difference stays attached to the explicit
  high transition difference;
* `K < a`: the born interval difference stays attached to the completed
  `window - p*window` partner fold proved in
  `LowPrimeCompletedPartnerWindowFold`.

The theorem is pointwise on the chronological old Boolean face, so it can be
summed without changing signs.  It is an exact representation theorem only:
no norm, absolute value, PNT estimate, Mertens bound, RH input, or dissipation
claim appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Prime sites in a finite open/closed interval `(L,U]`. -/
def squareRootPrimeIntervalSet (L U : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter Nat.Prime

/-- Cardinality of the prime interval `(L,U]`. -/
def squareRootPrimeIntervalCount (L U : ℕ) : ℕ :=
  (squareRootPrimeIntervalSet L U).card

/-- Below the root, the born partner set is exactly the prime interval
`(P+(c),c]`.  Both the displayed root cutoff and the product cutoff are
automatic consequences of `q <= c < R`. -/
theorem squareRootBornPartnerSet_eq_primeInterval_of_lt_root
    {R c : ℕ} (hcR : c < R) :
    squareRootBornPartnerSet R c =
      squareRootPrimeIntervalSet (canonicalLargestPrimeFactor c) c := by
  classical
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with
      ⟨hqRange, hqPrime, hrough, hqc, _hproduct⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hrough, hqc⟩, hqPrime⟩
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqIoc, hqPrime⟩
    rcases Finset.mem_Ioc.mp hqIoc with ⟨hrough, hqc⟩
    have hqR : q ≤ R := hqc.trans (Nat.le_of_lt hcR)
    have hcq : c * q ≤ c * c := Nat.mul_le_mul_left c hqc
    have hcc : c * c < R * R := by nlinarith
    have hproductLt : c * q < R ^ 2 := by
      calc
        c * q ≤ c * c := hcq
        _ < R * R := hcc
        _ = R ^ 2 := by ring
    have hproduct : c * q ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hqPrime.two_le, hqR⟩,
        hqPrime, hrough, hqc, hproduct⟩

/-- Cardinality form of the exact born-prime interval identification. -/
theorem squareRootBornPartnerCount_eq_primeIntervalCount_of_lt_root
    {R c : ℕ} (hcR : c < R) :
    squareRootBornPartnerCount R c =
      squareRootPrimeIntervalCount (canonicalLargestPrimeFactor c) c := by
  unfold squareRootBornPartnerCount squareRootPrimeIntervalCount
  rw [squareRootBornPartnerSet_eq_primeInterval_of_lt_root hcR]

/-- Explicit born parent/child interval difference when the fresh child remains
below `R`.  Roughness identifies the child's largest prime factor with `p`. -/
theorem squareRootBornPartnerCount_sub_child_eq_primeIntervalDifference
    {R p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hrough : canonicalLargestPrimeFactor a < p)
    (hchildR : p * a < R) :
    ((squareRootBornPartnerCount R a : ℕ) : ℂ) -
        ((squareRootBornPartnerCount R (p * a) : ℕ) : ℂ) =
      ((squareRootPrimeIntervalCount
          (canonicalLargestPrimeFactor a) a : ℕ) : ℂ) -
        ((squareRootPrimeIntervalCount p (p * a) : ℕ) : ℂ) := by
  have haLe : a ≤ p * a := Nat.le_mul_of_pos_left a hp.pos
  have haR : a < R := lt_of_le_of_lt haLe hchildR
  have hlpfChild : canonicalLargestPrimeFactor (p * a) = p := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough ha hp hrough
    simpa [Nat.mul_comm] using h
  rw [squareRootBornPartnerCount_eq_primeIntervalCount_of_lt_root haR,
    squareRootBornPartnerCount_eq_primeIntervalCount_of_lt_root hchildR,
    hlpfChild]

/-- The born interval finite difference attached to one old parent. -/
def squareRootBornPrimeIntervalDifference (p a : ℕ) : ℂ :=
  ((squareRootPrimeIntervalCount
      (canonicalLargestPrimeFactor a) a : ℕ) : ℂ) -
    ((squareRootPrimeIntervalCount p (p * a) : ℕ) : ℂ)

/-- The two response channels are deliberately combined before any case split
or estimate. -/
def squareRootBornPostTailCombinedParentChildDifference
    (R K j p a : ℕ) : ℂ :=
  (((squareRootBornPartnerCount R a : ℕ) : ℂ) -
      ((squareRootBornPartnerCount R (p * a) : ℕ) : ℂ)) +
    (((squareRootBornPostTailHighResponse R K j a : ℕ) : ℂ) -
      ((squareRootBornPostTailHighResponse R K j (p * a) : ℕ) : ℂ))

/-- **Combined born/high trichotomy on one common parent face.**

The middle transition is not discarded or estimated: it remains attached to
the born interval difference.  Beyond `K`, the high term is already the
completed partner mixed fold from the completed-partner window layer. -/
theorem squareRootBornPostTailCombinedParentChildDifference_trichotomy
    {R K j p a : ℕ} (hp : p.Prime) (hpR : p ≤ R)
    (hR : 2 ≤ R) (ha : 0 < a)
    (hrough : canonicalLargestPrimeFactor a < p)
    (hchildR : p * a < R) :
    squareRootBornPostTailCombinedParentChildDifference R K j p a =
      if p * a ≤ K then
        squareRootBornPrimeIntervalDifference p a
      else if a ≤ K then
        squareRootBornPrimeIntervalDifference p a +
          squareRootBornPostTailHighTransitionDifference R K j p a
      else
        squareRootBornPrimeIntervalDifference p a +
          (lowPrimeCompletedPartnerMixedFold
            p R (squareRootEndpoint R) a : ℂ) := by
  have hborn :=
    squareRootBornPartnerCount_sub_child_eq_primeIntervalDifference
      hp ha hrough hchildR
  unfold squareRootBornPostTailCombinedParentChildDifference
    squareRootBornPrimeIntervalDifference
  rw [hborn]
  by_cases hchildK : p * a ≤ K
  · rw [if_pos hchildK]
    rw [squareRootBornPostTailHighResponse_sub_child_eq_zero_of_child_le_K
      hp hchildK]
    ring
  · rw [if_neg hchildK]
    by_cases haK : a ≤ K
    · rw [if_pos haK]
      rfl
    · rw [if_neg haK]
      rw [squareRootBornPostTailHighResponse_sub_child_eq_completedPartnerMixedFold
        hp hpR hR ha (by omega)]

/-- Face-specialized form on the actual chronological old cube.  Membership in
`lowPrimeFreshParentFaces (R-1) p` supplies positivity, roughness, and the fact
that the fresh child is still below the root. -/
theorem squareRootBornPostTailCombinedParentChildDifference_face_trichotomy
    {R K j p : ℕ} (hp : p.Prime) (hpR : p ≤ R) (hR : 2 ≤ R)
    {u : Finset ℕ} (hu : u ∈ lowPrimeFreshParentFaces (R - 1) p) :
    squareRootBornPostTailCombinedParentChildDifference
        R K j p (primeFaceProduct u) =
      if p * primeFaceProduct u ≤ K then
        squareRootBornPrimeIntervalDifference p (primeFaceProduct u)
      else if primeFaceProduct u ≤ K then
        squareRootBornPrimeIntervalDifference p (primeFaceProduct u) +
          squareRootBornPostTailHighTransitionDifference
            R K j p (primeFaceProduct u)
      else
        squareRootBornPrimeIntervalDifference p (primeFaceProduct u) +
          (lowPrimeCompletedPartnerMixedFold
            p R (squareRootEndpoint R) (primeFaceProduct u) : ℂ) := by
  rcases mem_lowPrimeFreshParentFaces.mp hu with ⟨huOld, hchild⟩
  have ha : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset huOld
  have hrough : canonicalLargestPrimeFactor (primeFaceProduct u) < p :=
    canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hp huOld
  have hchildR : p * primeFaceProduct u < R := by omega
  exact squareRootBornPostTailCombinedParentChildDifference_trichotomy
    hp hpR hR ha hrough hchildR

/-! ## The born finite difference already has deletion/frontier form -/

/-- Prime counts are additive across a nested interval split. -/
theorem squareRootPrimeIntervalCount_add
    {L M U : ℕ} (hLM : L ≤ M) (hMU : M ≤ U) :
    squareRootPrimeIntervalCount L M +
        squareRootPrimeIntervalCount M U =
      squareRootPrimeIntervalCount L U := by
  unfold squareRootPrimeIntervalCount squareRootPrimeIntervalSet
  have hLM' := primeCard_Ioc_add_primeCounting_eq hLM
  have hMU' := primeCard_Ioc_add_primeCounting_eq hMU
  have hLU' := primeCard_Ioc_add_primeCounting_eq (hLM.trans hMU)
  omega

/-- The primes retained on the small side of a born parent/child pair. -/
def squareRootBornFrontierPrimeCount (p a : ℕ) : ℕ :=
  squareRootPrimeIntervalCount
    (canonicalLargestPrimeFactor a) (min p a)

/-- The new prime interval removed on the large side of a born parent/child
pair. -/
def squareRootBornDeletionPrimeCount (p a : ℕ) : ℕ :=
  squareRootPrimeIntervalCount (max p a) (p * a)

/-- Elementary interval cancellation.  The overlap between `(L,a]` and
`(p,p*a]` disappears exactly, leaving the small frontier
`(L,min(p,a)]` minus the newly deleted interval `(max(p,a),p*a]`. -/
theorem squareRootPrimeIntervalDifference_eq_frontier_sub_deletion
    {L p a : ℕ} (hp : 0 < p) (hLp : L < p) :
    ((squareRootPrimeIntervalCount L a : ℕ) : ℂ) -
        ((squareRootPrimeIntervalCount p (p * a) : ℕ) : ℂ) =
      ((squareRootPrimeIntervalCount L (min p a) : ℕ) : ℂ) -
        ((squareRootPrimeIntervalCount (max p a) (p * a) : ℕ) : ℂ) := by
  by_cases hap : a ≤ p
  · rw [min_eq_right hap, max_eq_left hap]
  · have hpa : p ≤ a := Nat.le_of_not_ge hap
    rw [min_eq_left hpa, max_eq_right hpa]
    have haChild : a ≤ p * a := Nat.le_mul_of_pos_left a hp
    have hparent :=
      squareRootPrimeIntervalCount_add (le_of_lt hLp) hpa
    have hchild := squareRootPrimeIntervalCount_add hpa haChild
    have hparentC :
        ((squareRootPrimeIntervalCount L p : ℕ) : ℂ) +
            ((squareRootPrimeIntervalCount p a : ℕ) : ℂ) =
          ((squareRootPrimeIntervalCount L a : ℕ) : ℂ) := by
      exact_mod_cast hparent
    have hchildC :
        ((squareRootPrimeIntervalCount p a : ℕ) : ℂ) +
            ((squareRootPrimeIntervalCount a (p * a) : ℕ) : ℂ) =
          ((squareRootPrimeIntervalCount p (p * a) : ℕ) : ℂ) := by
      exact_mod_cast hchild
    calc
      ((squareRootPrimeIntervalCount L a : ℕ) : ℂ) -
          ((squareRootPrimeIntervalCount p (p * a) : ℕ) : ℂ) =
        (((squareRootPrimeIntervalCount L p : ℕ) : ℂ) +
            ((squareRootPrimeIntervalCount p a : ℕ) : ℂ)) -
          (((squareRootPrimeIntervalCount p a : ℕ) : ℂ) +
            ((squareRootPrimeIntervalCount a (p * a) : ℕ) : ℂ)) := by
              rw [hparentC, hchildC]
      _ = ((squareRootPrimeIntervalCount L p : ℕ) : ℂ) -
          ((squareRootPrimeIntervalCount a (p * a) : ℕ) : ℂ) := by ring

/-- **Born parent/child response = frontier - deletion.**  This is the local
signed form sought by the sequential dissipation route; no inequality is used. -/
theorem squareRootBornPrimeIntervalDifference_eq_frontier_sub_deletion
    {p a : ℕ} (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor a < p) :
    squareRootBornPrimeIntervalDifference p a =
      ((squareRootBornFrontierPrimeCount p a : ℕ) : ℂ) -
        ((squareRootBornDeletionPrimeCount p a : ℕ) : ℂ) := by
  unfold squareRootBornPrimeIntervalDifference
    squareRootBornFrontierPrimeCount squareRootBornDeletionPrimeCount
  exact squareRootPrimeIntervalDifference_eq_frontier_sub_deletion
    hp.pos hrough

/-- The combined three-way theorem with the born contribution already exposed
as a nonnegative deletion count and a canonically located frontier count. -/
theorem squareRootBornPostTailCombinedParentChildDifference_frontier_trichotomy
    {R K j p a : ℕ} (hp : p.Prime) (hpR : p ≤ R)
    (hR : 2 ≤ R) (ha : 0 < a)
    (hrough : canonicalLargestPrimeFactor a < p)
    (hchildR : p * a < R) :
    squareRootBornPostTailCombinedParentChildDifference R K j p a =
      if p * a ≤ K then
        ((squareRootBornFrontierPrimeCount p a : ℕ) : ℂ) -
          ((squareRootBornDeletionPrimeCount p a : ℕ) : ℂ)
      else if a ≤ K then
        (((squareRootBornFrontierPrimeCount p a : ℕ) : ℂ) -
          ((squareRootBornDeletionPrimeCount p a : ℕ) : ℂ)) +
            squareRootBornPostTailHighTransitionDifference R K j p a
      else
        (((squareRootBornFrontierPrimeCount p a : ℕ) : ℂ) -
          ((squareRootBornDeletionPrimeCount p a : ℕ) : ℂ)) +
            (lowPrimeCompletedPartnerMixedFold
              p R (squareRootEndpoint R) a : ℂ) := by
  rw [squareRootBornPostTailCombinedParentChildDifference_trichotomy
    hp hpR hR ha hrough hchildR]
  simp_rw [squareRootBornPrimeIntervalDifference_eq_frontier_sub_deletion
    hp hrough]

/-! ## The shallow high transition is a window minus admitted seats -/

/-- In the middle case `a <= K < p*a`, the high defect is not opaque.  It is
the post-root prime-prefix window from `K` to `p*a`, minus the `j` seats already
admitted in the crossing layer. -/
theorem squareRootBornPostTailHighTransitionDifference_eq_prefixWindow_sub_admitted
    {R K j p a : ℕ}
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hK : 1 ≤ K) (hKR : K < R)
    (haK : a ≤ K) (hchildK : K < p * a) :
    squareRootBornPostTailHighTransitionDifference R K j p a =
      squareRootPostRootPrimePrefix R K -
        squareRootPostRootPrimePrefix R (p * a) - (j : ℂ) := by
  have hchildNot : ¬ p * a ≤ K := by omega
  have hN :
      ((squareRootReciprocalPrimeLayerCard R K : ℕ) : ℂ) =
        squareRootPostRootPrimePrefix R K -
          squareRootPostRootPrimePrefix R (K + 1) := by
    rw [← squareRootReciprocalPrimeCount_eq_layerCard]
    exact squareRoot_reciprocalPrimeCount_eq_postRootPrefix_diff
      (by omega : 1 ≤ R) hK hKR
  unfold squareRootBornPostTailHighTransitionDifference
    squareRootBornPostTailHighResponse
  rw [if_pos haK, if_neg hchildNot]
  rw [Nat.cast_add, Nat.cast_sub hj,
    squareRootPostRootPrimePrefixCard_cast,
    squareRootPostRootPrimePrefixCard_cast, hN]
  ring

/-! ## Completing the high cutoff isolates one root-crossing boundary -/

/-- Fresh-parent faces are monotone in their arithmetic product cutoff. -/
theorem lowPrimeFreshParentFaces_mono
    {B C p : ℕ} (hBC : B ≤ C) :
    lowPrimeFreshParentFaces B p ⊆ lowPrimeFreshParentFaces C p := by
  intro u hu
  rcases mem_lowPrimeFreshParentFaces.mp hu with ⟨huOld, hchildB⟩
  exact mem_lowPrimeFreshParentFaces.mpr ⟨huOld, hchildB.trans hBC⟩

/-- Extend the high response to the complete born parent cube before taking the
parent/child finite difference.  The artificial extension is corrected below by
one explicit boundary rather than by an estimate. -/
def squareRootBornPostTailExtendedCombinedPairedDifferenceLayer
    (R K j p : ℕ) : ℂ :=
  lowPrimeFreshPairedDifferenceMass (squareRootEndpoint R) p
    (fun c =>
      (squareRootBornPartnerCount R c : ℂ) +
        (squareRootBornPostTailHighResponse R K j c : ℂ))

/-- Faces present at the complete born cutoff but absent from the honest high
cutoff `R-1`. -/
def squareRootBornPostTailHighCutoffBoundaryFaces
    (R p : ℕ) : Finset (Finset ℕ) :=
  lowPrimeFreshParentFaces (squareRootEndpoint R) p \
    lowPrimeFreshParentFaces (R - 1) p

/-- Signed high parent/child mass on the cutoff discrepancy. -/
def squareRootBornPostTailHighCutoffBoundaryLayer
    (R K j p : ℕ) : ℂ :=
  ∑ u ∈ squareRootBornPostTailHighCutoffBoundaryFaces R p,
    (booleanCubeSign u : ℂ) *
      ((squareRootBornPostTailHighResponse
          R K j (primeFaceProduct u) : ℂ) -
        (squareRootBornPostTailHighResponse
          R K j (p * primeFaceProduct u) : ℂ))

/-- Membership in the high cutoff discrepancy means exactly that the fresh
child lies at or beyond the root while remaining inside the complete square
endpoint. -/
@[simp] theorem mem_squareRootBornPostTailHighCutoffBoundaryFaces
    {R p : ℕ} {u : Finset ℕ} (hR : 1 ≤ R) :
    u ∈ squareRootBornPostTailHighCutoffBoundaryFaces R p ↔
      u ∈ (primesUpTo (p - 1)).powerset ∧
        p * primeFaceProduct u ≤ squareRootEndpoint R ∧
          R ≤ p * primeFaceProduct u := by
  unfold squareRootBornPostTailHighCutoffBoundaryFaces
  rw [Finset.mem_sdiff]
  constructor
  · rintro ⟨hlarge, hnotSmall⟩
    rcases mem_lowPrimeFreshParentFaces.mp hlarge with ⟨huOld, hchildX⟩
    refine ⟨huOld, hchildX, ?_⟩
    by_contra hnot
    have hchildSmall : p * primeFaceProduct u ≤ R - 1 := by omega
    exact hnotSmall
      (mem_lowPrimeFreshParentFaces.mpr ⟨huOld, hchildSmall⟩)
  · rintro ⟨huOld, hchildX, hrootChild⟩
    refine ⟨mem_lowPrimeFreshParentFaces.mpr ⟨huOld, hchildX⟩, ?_⟩
    intro hsmall
    have hchildSmall := (mem_lowPrimeFreshParentFaces.mp hsmall).2
    omega

/-- **Honest paired layer = completed combined cube - cutoff boundary.**

This is the exact algebra needed to remove the artificial mismatch between the
born cutoff `X=R^2-1` and the high cutoff `R-1`.  No boundary state is repeated:
each lies in the literal set difference of the two fresh-parent cubes. -/
theorem squareRootBornPostTailFreshPairedDifferenceLayer_eq_extended_sub_highCutoffBoundary
    (R K j p : ℕ) (hR : 2 ≤ R) :
    squareRootBornPostTailFreshPairedDifferenceLayer R K j p =
      squareRootBornPostTailExtendedCombinedPairedDifferenceLayer R K j p -
        squareRootBornPostTailHighCutoffBoundaryLayer R K j p := by
  have hpredX : R - 1 ≤ squareRootEndpoint R := by
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  have hsub :
      lowPrimeFreshParentFaces (R - 1) p ⊆
        lowPrimeFreshParentFaces (squareRootEndpoint R) p :=
    lowPrimeFreshParentFaces_mono hpredX
  have hext :
      squareRootBornPostTailExtendedCombinedPairedDifferenceLayer R K j p =
        lowPrimeFreshPairedDifferenceMass (squareRootEndpoint R) p
            (fun c => (squareRootBornPartnerCount R c : ℂ)) +
          lowPrimeFreshPairedDifferenceMass (squareRootEndpoint R) p
            (fun c =>
              (squareRootBornPostTailHighResponse R K j c : ℂ)) := by
    unfold squareRootBornPostTailExtendedCombinedPairedDifferenceLayer
      lowPrimeFreshPairedDifferenceMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _hu
    ring
  have hhigh :
      squareRootBornPostTailHighCutoffBoundaryLayer R K j p +
          lowPrimeFreshPairedDifferenceMass (R - 1) p
            (fun c =>
              (squareRootBornPostTailHighResponse R K j c : ℂ)) =
        lowPrimeFreshPairedDifferenceMass (squareRootEndpoint R) p
          (fun c =>
            (squareRootBornPostTailHighResponse R K j c : ℂ)) := by
    unfold squareRootBornPostTailHighCutoffBoundaryLayer
      squareRootBornPostTailHighCutoffBoundaryFaces
      lowPrimeFreshPairedDifferenceMass
    exact Finset.sum_sdiff hsub
  unfold squareRootBornPostTailFreshPairedDifferenceLayer
  rw [hext, ← hhigh]
  ring

/-- Once a cofactor reaches the root, its post-root prime-prefix response is
empty. -/
theorem squareRootPostRootPrimePrefixCard_eq_zero_of_root_le
    {R c : ℕ} (hR : 2 ≤ R) (hc : R ≤ c) :
    squareRootPostRootPrimePrefixCard R c = 0 := by
  have hcpos : 0 < c := by omega
  have hsq : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    rw [pow_two]
    have hpos : 0 < R * R := Nat.mul_pos (by omega) (by omega)
    omega
  have hXc : squareRootEndpoint R < R * c :=
    hsq.trans_le (Nat.mul_le_mul_left R hc)
  have hdiv : squareRootEndpoint R / c < R :=
    (Nat.div_lt_iff_lt_mul hcpos).2 hXc
  unfold squareRootPostRootPrimePrefixCard
  rw [max_eq_left hdiv.le]
  simp

/-- Therefore the entire high response vanishes on cofactors at or beyond the
root, independently of the partial-seat index `j`. -/
theorem squareRootBornPostTailHighResponse_eq_zero_of_root_le
    {R K j c : ℕ} (hR : 2 ≤ R) (hKR : K < R) (hc : R ≤ c) :
    squareRootBornPostTailHighResponse R K j c = 0 := by
  have hcK : ¬ c ≤ K := by omega
  unfold squareRootBornPostTailHighResponse
  rw [if_neg hcK,
    squareRootPostRootPrimePrefixCard_eq_zero_of_root_le hR hc]

/-- The only nonzero part of the cutoff discrepancy has an old parent below
`R` and a fresh child at or above `R`. -/
def squareRootBornPostTailRootCrossingHighBoundaryFaces
    (R p : ℕ) : Finset (Finset ℕ) :=
  (squareRootBornPostTailHighCutoffBoundaryFaces R p).filter fun u =>
    primeFaceProduct u < R

/-- Signed high correction supported on the genuine root-crossing faces. -/
def squareRootBornPostTailRootCrossingHighBoundaryLayer
    (R K j p : ℕ) : ℂ :=
  ∑ u ∈ squareRootBornPostTailRootCrossingHighBoundaryFaces R p,
    (booleanCubeSign u : ℂ) *
      ((squareRootBornPostTailHighResponse
          R K j (primeFaceProduct u) : ℂ) -
        (squareRootBornPostTailHighResponse
          R K j (p * primeFaceProduct u) : ℂ))

/-- Exact membership description of the uniquely assigned root-crossing
boundary. -/
@[simp] theorem mem_squareRootBornPostTailRootCrossingHighBoundaryFaces
    {R p : ℕ} {u : Finset ℕ} (hR : 1 ≤ R) :
    u ∈ squareRootBornPostTailRootCrossingHighBoundaryFaces R p ↔
      u ∈ (primesUpTo (p - 1)).powerset ∧
        p * primeFaceProduct u ≤ squareRootEndpoint R ∧
          primeFaceProduct u < R ∧
            R ≤ p * primeFaceProduct u := by
  unfold squareRootBornPostTailRootCrossingHighBoundaryFaces
  rw [Finset.mem_filter,
    mem_squareRootBornPostTailHighCutoffBoundaryFaces hR]
  tauto

/-- All discrepancy faces whose parent was already at or beyond the root carry
zero high response on both parent and child.  Hence the cutoff correction is
literally the root-crossing boundary, not a larger uncontrolled shell. -/
theorem squareRootBornPostTailHighCutoffBoundaryLayer_eq_rootCrossing
    (R K j p : ℕ) (hR : 2 ≤ R) (hKR : K < R) :
    squareRootBornPostTailHighCutoffBoundaryLayer R K j p =
      squareRootBornPostTailRootCrossingHighBoundaryLayer R K j p := by
  unfold squareRootBornPostTailHighCutoffBoundaryLayer
    squareRootBornPostTailRootCrossingHighBoundaryLayer
    squareRootBornPostTailRootCrossingHighBoundaryFaces
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hparentR : primeFaceProduct u < R
  · simp [hparentR]
  · have hrootParent : R ≤ primeFaceProduct u :=
      Nat.le_of_not_gt hparentR
    have hboundary :=
      (mem_squareRootBornPostTailHighCutoffBoundaryFaces
        (R := R) (p := p) (u := u) (by omega)).mp hu
    have hrootChild : R ≤ p * primeFaceProduct u := hboundary.2.2
    have hparentZero :
        squareRootBornPostTailHighResponse R K j (primeFaceProduct u) = 0 :=
      squareRootBornPostTailHighResponse_eq_zero_of_root_le
        (R := R) (K := K) (j := j) (c := primeFaceProduct u)
        hR hKR hrootParent
    have hchildZero :
        squareRootBornPostTailHighResponse R K j (p * primeFaceProduct u) = 0 :=
      squareRootBornPostTailHighResponse_eq_zero_of_root_le
        (R := R) (K := K) (j := j) (c := p * primeFaceProduct u)
        hR hKR hrootChild
    rw [hparentZero, hchildZero]
    simp [hparentR]

/-- **Final cutoff-completed form.**  The honest BornPostTail paired layer is a
single combined born/high parent cube minus one canonically assigned
root-crossing high frontier. -/
theorem squareRootBornPostTailFreshPairedDifferenceLayer_eq_extended_sub_rootCrossing
    (R K j p : ℕ) (hR : 2 ≤ R) (hKR : K < R) :
    squareRootBornPostTailFreshPairedDifferenceLayer R K j p =
      squareRootBornPostTailExtendedCombinedPairedDifferenceLayer R K j p -
        squareRootBornPostTailRootCrossingHighBoundaryLayer R K j p := by
  rw [squareRootBornPostTailFreshPairedDifferenceLayer_eq_extended_sub_highCutoffBoundary
      R K j p hR,
    squareRootBornPostTailHighCutoffBoundaryLayer_eq_rootCrossing
      R K j p hR hKR]

end RHLean.Proof