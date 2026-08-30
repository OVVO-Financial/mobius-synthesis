import Mathlib
import RHLean.Proof.LowPrimeCombinedBornHighTransition
import RHLean.Proof.LowWheelSequentialSmoothRoughBoundary

/-!
# Combined born/high step with first-failure transition control

`LowPrimeCombinedBornHighTransition` keeps the born and high parent/child
responses signed together and isolates the only mismatch between their natural
cutoffs as one root-crossing high boundary.

This module resolves the other artificial-looking term in that representation:
the constant `j` attached to each shallow-to-deep transition

`a <= K < p*a`.

It must not be bounded once for every fresh prime.  On the complete old
Boolean cube, those transition faces form exactly the smooth multiplicative
shell

`K / p < P(u) <= K`.

Therefore their signed mass is the existing `lowWheelSmoothFaceShellMass`.
Any previously processed prime coordinate then collapses that entire shell to
two exact first-failure frontiers.  The final theorem writes the honest
BornPostTail paired layer as

* the complete born parent/child layer;
* plus a clipped high-prefix finite-difference layer;
* minus one `j`-weighted first-failure shell;
* minus one uniquely assigned root-crossing high boundary.

All identities are finite and exact.  No norm, absolute value, PNT, density,
endpoint Mertens estimate, RH-equivalent statement, or dissipation inequality
is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The high response after clipping every cofactor to the shallow cutoff `K`.
Its parent/child finite difference is the geometric part of the high channel;
the admitted-seat defect is separated below. -/
def squareRootBornPostTailClippedHighResponse
    (R K c : ℕ) : ℂ :=
  squareRootPostRootPrimePrefix R (max K c)

/-- **Pointwise high response = clipped geometry - one transition seat.**

The admitted-seat term occurs exactly when the old parent is still in the
shallow plateau while its fresh child has crossed it.  It is not present in the
fully shallow or fully deep cases. -/
theorem squareRootBornPostTailHighResponse_sub_child_eq_clipped_sub_transitionSeat
    {R K j p a : ℕ} (hp : p.Prime)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hK : 1 ≤ K) (hKR : K < R) :
    ((squareRootBornPostTailHighResponse R K j a : ℕ) : ℂ) -
        ((squareRootBornPostTailHighResponse R K j (p * a) : ℕ) : ℂ) =
      (squareRootBornPostTailClippedHighResponse R K a -
        squareRootBornPostTailClippedHighResponse R K (p * a)) -
      if a ≤ K ∧ K < p * a then (j : ℂ) else 0 := by
  have haChild : a ≤ p * a := Nat.le_mul_of_pos_left a hp.pos
  by_cases hchildK : p * a ≤ K
  · have haK : a ≤ K := haChild.trans hchildK
    have hnotChildGt : ¬ K < p * a := Nat.not_lt_of_ge hchildK
    have hzero :=
      squareRootBornPostTailHighResponse_sub_child_eq_zero_of_child_le_K
        (R := R) (j := j) hp hchildK
    simpa [squareRootBornPostTailClippedHighResponse,
      max_eq_left haK, max_eq_left hchildK, haK, hnotChildGt] using hzero
  · have hchildGt : K < p * a := Nat.lt_of_not_ge hchildK
    by_cases haK : a ≤ K
    · have htransition :=
        squareRootBornPostTailHighTransitionDifference_eq_prefixWindow_sub_admitted
          (R := R) (j := j) (p := p) (a := a)
          hj hK hKR haK hchildGt
      simpa [squareRootBornPostTailHighTransitionDifference,
        squareRootBornPostTailClippedHighResponse,
        max_eq_left haK, max_eq_right hchildGt.le,
        haK, hchildGt] using htransition
    · have haGt : K < a := Nat.lt_of_not_ge haK
      unfold squareRootBornPostTailClippedHighResponse
        squareRootBornPostTailHighResponse
      rw [if_neg haK, if_neg hchildK,
        squareRootPostRootPrimePrefixCard_cast,
        squareRootPostRootPrimePrefixCard_cast,
        max_eq_right haGt.le, max_eq_right hchildGt.le]
      simp [haK]

/-- Old faces whose product crosses the shallow cutoff when the fresh prime is
inserted. -/
def squareRootBornPostTailTransitionFaces
    (p K : ℕ) : Finset (Finset ℕ) :=
  ((primesUpTo (p - 1)).powerset).filter fun u =>
    primeFaceProduct u ≤ K ∧ K < p * primeFaceProduct u

@[simp] theorem mem_squareRootBornPostTailTransitionFaces
    {p K : ℕ} {u : Finset ℕ} :
    u ∈ squareRootBornPostTailTransitionFaces p K ↔
      u ∈ (primesUpTo (p - 1)).powerset ∧
        primeFaceProduct u ≤ K ∧ K < p * primeFaceProduct u := by
  simp [squareRootBornPostTailTransitionFaces]

/-- Alternating mass of all shallow-to-deep transition faces. -/
def squareRootBornPostTailTransitionFaceMass
    (p K : ℕ) : ℤ :=
  ∑ u ∈ squareRootBornPostTailTransitionFaces p K,
    booleanCubeSign u

/-- **The transition population is exactly the existing smooth shell.** -/
theorem squareRootBornPostTailTransitionFaceMass_eq_smoothShell
    {p K : ℕ} (hp : 0 < p) :
    squareRootBornPostTailTransitionFaceMass p K =
      lowWheelSmoothFaceShellMass p K := by
  classical
  unfold squareRootBornPostTailTransitionFaceMass
    squareRootBornPostTailTransitionFaces
    lowWheelSmoothFaceShellMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _hu
  have hdiv :
      K / p < primeFaceProduct u ↔
        K < p * primeFaceProduct u := by
    constructor
    · intro h
      have h' := (Nat.div_lt_iff_lt_mul hp).1 h
      simpa [Nat.mul_comm] using h'
    · intro h
      apply (Nat.div_lt_iff_lt_mul hp).2
      simpa [Nat.mul_comm] using h
  simp [hdiv, and_comm]

/-- Every transition face lies in the complete square-endpoint parent cube.
This is where completing the high channel is useful: the full shell is counted
once, and the previously isolated root-crossing boundary corrects the extension
exactly. -/
theorem squareRootBornPostTailTransitionFaces_eq_extendedParent_filter
    {R K p : ℕ} (hpR : p ≤ R) (hKR : K < R) :
    squareRootBornPostTailTransitionFaces p K =
      (lowPrimeFreshParentFaces (squareRootEndpoint R) p).filter fun u =>
        primeFaceProduct u ≤ K ∧ K < p * primeFaceProduct u := by
  classical
  ext u
  rw [mem_squareRootBornPostTailTransitionFaces,
    Finset.mem_filter, mem_lowPrimeFreshParentFaces]
  constructor
  · rintro ⟨huOld, haK, hcross⟩
    have haR : primeFaceProduct u < R := haK.trans_lt hKR
    have hRpos : 0 < R := by omega
    have hchildSq :
        p * primeFaceProduct u < R * R := by
      calc
        p * primeFaceProduct u ≤ R * primeFaceProduct u :=
          Nat.mul_le_mul_right (primeFaceProduct u) hpR
        _ < R * R := Nat.mul_lt_mul_of_pos_left haR hRpos
    have hchildX :
        p * primeFaceProduct u ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      rw [pow_two]
      omega
    exact ⟨⟨huOld, hchildX⟩, haK, hcross⟩
  · rintro ⟨⟨huOld, _hchildX⟩, haK, hcross⟩
    exact ⟨huOld, haK, hcross⟩

/-- The admitted-seat contribution of the entire transition shell. -/
def squareRootBornPostTailTransitionSeatLayer
    (p K j : ℕ) : ℂ :=
  ∑ u ∈ squareRootBornPostTailTransitionFaces p K,
    (booleanCubeSign u : ℂ) * (j : ℂ)

/-- The direct transition-shell sum is the same as summing its indicator over
the completed square-endpoint parent cube. -/
theorem squareRootBornPostTailTransitionSeatLayer_eq_extendedParentIndicator
    {R K j p : ℕ} (hpR : p ≤ R) (hKR : K < R) :
    squareRootBornPostTailTransitionSeatLayer p K j =
      ∑ u ∈ lowPrimeFreshParentFaces (squareRootEndpoint R) p,
        (booleanCubeSign u : ℂ) *
          (if primeFaceProduct u ≤ K ∧
              K < p * primeFaceProduct u then
            (j : ℂ)
          else 0) := by
  classical
  unfold squareRootBornPostTailTransitionSeatLayer
  rw [squareRootBornPostTailTransitionFaces_eq_extendedParent_filter
    hpR hKR, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _hu
  by_cases htransition :
      primeFaceProduct u ≤ K ∧ K < p * primeFaceProduct u
  · simp [htransition]
  · simp [htransition]

/-- The constant `j` is multiplied by one alternating shell mass, not by an
independent local error for every prime. -/
theorem squareRootBornPostTailTransitionSeatLayer_eq_admitted_mul_smoothShell
    {p K j : ℕ} (hp : 0 < p) :
    squareRootBornPostTailTransitionSeatLayer p K j =
      (j : ℂ) * ((lowWheelSmoothFaceShellMass p K : ℤ) : ℂ) := by
  have hmass :=
    squareRootBornPostTailTransitionFaceMass_eq_smoothShell
      (p := p) (K := K) hp
  have hcast :
      ((squareRootBornPostTailTransitionFaceMass p K : ℤ) : ℂ) =
        ∑ u ∈ squareRootBornPostTailTransitionFaces p K,
          (booleanCubeSign u : ℂ) := by
    unfold squareRootBornPostTailTransitionFaceMass
    push_cast
    rfl
  unfold squareRootBornPostTailTransitionSeatLayer
  calc
    (∑ u ∈ squareRootBornPostTailTransitionFaces p K,
        (booleanCubeSign u : ℂ) * (j : ℂ)) =
      ∑ u ∈ squareRootBornPostTailTransitionFaces p K,
        (j : ℂ) * (booleanCubeSign u : ℂ) := by
          apply Finset.sum_congr rfl
          intro u _hu
          ring
    _ = (j : ℂ) *
        ∑ u ∈ squareRootBornPostTailTransitionFaces p K,
          (booleanCubeSign u : ℂ) := by
            rw [Finset.mul_sum]
    _ = (j : ℂ) *
        ((squareRootBornPostTailTransitionFaceMass p K : ℤ) : ℂ) := by
          rw [hcast]
    _ = (j : ℂ) * ((lowWheelSmoothFaceShellMass p K : ℤ) : ℂ) := by
          rw [hmass]

/-- Integer mass of the two first-failure frontiers produced by any previously
processed prime coordinate `ell`. -/
def squareRootBornPostTailTransitionFirstFailureMass
    (p K ell : ℕ) : ℤ :=
  (∑ u ∈ primeProductFirstFailureBoundary
      (primesUpTo (p - 1)) K ell,
    booleanCubeSign u) -
  ∑ u ∈ primeProductFirstFailureBoundary
      (primesUpTo (p - 1)) (K / p) ell,
    booleanCubeSign u

/-- The transition first-failure mass is exactly the smooth shell mass. -/
theorem squareRootBornPostTailTransitionFirstFailureMass_eq_smoothShell
    {p K ell : ℕ} (hell : ell ∈ primesUpTo (p - 1)) :
    squareRootBornPostTailTransitionFirstFailureMass p K ell =
      lowWheelSmoothFaceShellMass p K := by
  unfold squareRootBornPostTailTransitionFirstFailureMass
  exact (lowWheelSmoothFaceShellMass_eq_twoFirstFailureFrontiers
    (p := p) (B := K) (ell := ell) hell).symm

/-- The admitted-seat multiplier on the two first-failure frontiers. -/
def squareRootBornPostTailTransitionFirstFailureSeatLayer
    (p K j ell : ℕ) : ℂ :=
  (j : ℂ) *
    ((squareRootBornPostTailTransitionFirstFailureMass p K ell : ℤ) : ℂ)

/-- **The whole transition-seat population is two first-failure frontiers.** -/
theorem squareRootBornPostTailTransitionSeatLayer_eq_firstFailure
    {p K j ell : ℕ} (hp : 0 < p)
    (hell : ell ∈ primesUpTo (p - 1)) :
    squareRootBornPostTailTransitionSeatLayer p K j =
      squareRootBornPostTailTransitionFirstFailureSeatLayer p K j ell := by
  rw [squareRootBornPostTailTransitionSeatLayer_eq_admitted_mul_smoothShell hp]
  unfold squareRootBornPostTailTransitionFirstFailureSeatLayer
  rw [squareRootBornPostTailTransitionFirstFailureMass_eq_smoothShell hell]

/-! ## Aggregate completed high layer -/

/-- Born parent/child layer on the complete square endpoint. -/
def squareRootBornPostTailExtendedBornPairedDifferenceLayer
    (R p : ℕ) : ℂ :=
  lowPrimeFreshPairedDifferenceMass (squareRootEndpoint R) p
    (fun c => (squareRootBornPartnerCount R c : ℂ))

/-- Artificially completed high parent/child layer.  Its excess is exactly the
root-crossing boundary already isolated in the previous module. -/
def squareRootBornPostTailExtendedHighPairedDifferenceLayer
    (R K j p : ℕ) : ℂ :=
  lowPrimeFreshPairedDifferenceMass (squareRootEndpoint R) p
    (fun c => (squareRootBornPostTailHighResponse R K j c : ℂ))

/-- Completed high geometry after clipping every cofactor to `K`. -/
def squareRootBornPostTailClippedHighPairedDifferenceLayer
    (R K p : ℕ) : ℂ :=
  lowPrimeFreshPairedDifferenceMass (squareRootEndpoint R) p
    (squareRootBornPostTailClippedHighResponse R K)

/-- Split the completed combined response into its born and high finite
differences without changing signs. -/
theorem squareRootBornPostTailExtendedCombinedPairedDifferenceLayer_eq_born_add_high
    (R K j p : ℕ) :
    squareRootBornPostTailExtendedCombinedPairedDifferenceLayer R K j p =
      squareRootBornPostTailExtendedBornPairedDifferenceLayer R p +
        squareRootBornPostTailExtendedHighPairedDifferenceLayer R K j p := by
  unfold squareRootBornPostTailExtendedCombinedPairedDifferenceLayer
    squareRootBornPostTailExtendedBornPairedDifferenceLayer
    squareRootBornPostTailExtendedHighPairedDifferenceLayer
    lowPrimeFreshPairedDifferenceMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _hu
  ring

/-- **Completed high layer = clipped geometry - one transition shell.** -/
theorem squareRootBornPostTailExtendedHighPairedDifferenceLayer_eq_clipped_sub_transitionSeat
    {R K j p : ℕ} (hp : p.Prime) (hpR : p ≤ R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hK : 1 ≤ K) (hKR : K < R) :
    squareRootBornPostTailExtendedHighPairedDifferenceLayer R K j p =
      squareRootBornPostTailClippedHighPairedDifferenceLayer R K p -
        squareRootBornPostTailTransitionSeatLayer p K j := by
  unfold squareRootBornPostTailExtendedHighPairedDifferenceLayer
    squareRootBornPostTailClippedHighPairedDifferenceLayer
    lowPrimeFreshPairedDifferenceMass
  rw [squareRootBornPostTailTransitionSeatLayer_eq_extendedParentIndicator
    hpR hKR]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hpoint :=
    squareRootBornPostTailHighResponse_sub_child_eq_clipped_sub_transitionSeat
      (R := R) (K := K) (j := j) (p := p)
      (a := primeFaceProduct u) hp hj hK hKR
  rw [hpoint]
  ring

/-- Completed combined layer with the constant transition defect compressed to
one shell. -/
theorem squareRootBornPostTailExtendedCombinedPairedDifferenceLayer_eq_born_add_clipped_sub_transitionSeat
    {R K j p : ℕ} (hp : p.Prime) (hpR : p ≤ R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hK : 1 ≤ K) (hKR : K < R) :
    squareRootBornPostTailExtendedCombinedPairedDifferenceLayer R K j p =
      squareRootBornPostTailExtendedBornPairedDifferenceLayer R p +
        squareRootBornPostTailClippedHighPairedDifferenceLayer R K p -
          squareRootBornPostTailTransitionSeatLayer p K j := by
  rw [squareRootBornPostTailExtendedCombinedPairedDifferenceLayer_eq_born_add_high,
    squareRootBornPostTailExtendedHighPairedDifferenceLayer_eq_clipped_sub_transitionSeat
      hp hpR hj hK hKR]
  ring

/-- Completed combined layer with the transition shell replaced by two
first-failure frontiers. -/
theorem squareRootBornPostTailExtendedCombinedPairedDifferenceLayer_eq_born_add_clipped_sub_firstFailure
    {R K j p ell : ℕ} (hp : p.Prime) (hpR : p ≤ R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hK : 1 ≤ K) (hKR : K < R)
    (hell : ell ∈ primesUpTo (p - 1)) :
    squareRootBornPostTailExtendedCombinedPairedDifferenceLayer R K j p =
      squareRootBornPostTailExtendedBornPairedDifferenceLayer R p +
        squareRootBornPostTailClippedHighPairedDifferenceLayer R K p -
          squareRootBornPostTailTransitionFirstFailureSeatLayer p K j ell := by
  rw [squareRootBornPostTailExtendedCombinedPairedDifferenceLayer_eq_born_add_clipped_sub_transitionSeat
      hp hpR hj hK hKR,
    squareRootBornPostTailTransitionSeatLayer_eq_firstFailure hp.pos hell]

/-- **Cutoff-completed sequential identity with uniquely assigned frontiers.**

The honest BornPostTail paired layer is the complete born finite difference plus
the clipped high finite difference, minus two canonically assigned corrections:
one old-prime first-failure shell and one root-crossing high boundary.  This is
the exact local architecture needed before formulating any dissipation
inequality. -/
theorem squareRootBornPostTailFreshPairedDifferenceLayer_eq_born_add_clipped_sub_firstFailure_sub_rootCrossing
    {R K j p ell : ℕ} (hp : p.Prime) (hpR : p ≤ R)
    (hR : 2 ≤ R) (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hK : 1 ≤ K) (hKR : K < R)
    (hell : ell ∈ primesUpTo (p - 1)) :
    squareRootBornPostTailFreshPairedDifferenceLayer R K j p =
      squareRootBornPostTailExtendedBornPairedDifferenceLayer R p +
        squareRootBornPostTailClippedHighPairedDifferenceLayer R K p -
          squareRootBornPostTailTransitionFirstFailureSeatLayer p K j ell -
            squareRootBornPostTailRootCrossingHighBoundaryLayer R K j p := by
  rw [squareRootBornPostTailFreshPairedDifferenceLayer_eq_extended_sub_rootCrossing
      R K j p hR hKR,
    squareRootBornPostTailExtendedCombinedPairedDifferenceLayer_eq_born_add_clipped_sub_firstFailure
      hp hpR hj hK hKR hell]

end RHLean.Proof
