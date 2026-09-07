import Mathlib
import RHLean.Proof.OrderedEulerCutProjection
import RHLean.Proof.TerminalAxiomAudit

/-!
# Complex vertical-interval / Euler ledger bridge

`OrderedEulerCutProjection` puts every canonically oriented Euler occurrence on
one static ordered-cut atom `y = (t,(c,p))`.  The same atom already carries

* its low face product `a = P(t)`;
* its rough high cofactor `c`;
* its distinguished fresh pivot `p`;
* the upper factor `q = p*a`;
* the physical child integer `n = c*q`;
* the Fermat point whose square is
  `n + ((q^2-c^2)/2)i`;
* its Möbius/Boolean-cube sign;
* its exact half-open lifetime in square-root time.

This file performs only the aggregate reindexing.  The signed mass of the
squared vertical factor strip is defined by summing the native ordered-cut
weights at each endpoint, then taking the endpoint difference across a forward
square run.  The result is proved exactly equal to the existing canonical
oriented Euler run ledger, before every norm.

The final proposition `SignedVerticalIntervalEnergyBound` is deliberately only
an open `Prop`.  Its theorem below proves that it is exactly the pre-existing
`CanonicalOrientedRunDifferenceEnergyBoundedStatement`; no analytic estimate is
introduced or hidden by the coordinate change.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership

attribute [local instance] Classical.propDecidable

/-- Signed squared-Fermat vertical-strip mass at one square-root endpoint.
Every summand is an actual ordered-cut atom of `OrderedEulerCutProjection`, so
its complex coordinate and its Euler/Möbius sign are already attached to the
same carrier point. -/
noncomputable def signedVerticalIntervalEndpointMass (R : ℕ) : ℂ :=
  ∑ y ∈ orderedEulerCutCarrier R, orderedEulerCutWeight y

/-- Every atom counted by the vertical-strip mass satisfies the full
complex/Fermat, square-root-window, and fresh-prime sign package. -/
theorem signedVerticalIntervalAtom_complexFiber_package
    {R : ℕ} {y : OrderedEulerCutTaggedState}
    (hy : y ∈ orderedEulerCutCarrier R) :
    ((orderedEulerCutFermatPoint y) ^ 2).re =
        (orderedEulerCutChildInteger y : ℝ) ∧
      ((orderedEulerCutFermatPoint y) ^ 2).im =
        orderedEulerCutVerticalHeight y ∧
      orderedEulerCutHighCofactor y ≤
        Nat.sqrt (orderedEulerCutChildInteger y) ∧
      Nat.sqrt (orderedEulerCutChildInteger y) < R ∧
      R < orderedEulerCutUpperFactor y ∧
      canonicalMoebiusWeight (orderedEulerCutChildInteger y) =
        -orderedEulerCutWeight y := by
  have hshape := orderedEulerCutShape_of_mem_carrier hy
  have hocc := mem_orderedEulerCutCarrier.mp hy
  exact orderedEulerCut_complexFiber_lifetime_package hshape hocc

/-- The same endpoint mass with Möbius parity displayed directly on the parent
integer of each ordered-cut atom. -/
theorem signedVerticalIntervalEndpointMass_eq_sum_parentMoebius
    (R : ℕ) :
    signedVerticalIntervalEndpointMass R =
      ∑ y ∈ orderedEulerCutCarrier R,
        canonicalMoebiusWeight (orderedEulerCutParentInteger y) := by
  unfold signedVerticalIntervalEndpointMass
  apply Finset.sum_congr rfl
  intro y hy
  exact orderedEulerCutWeight_eq_parentMoebius
    (orderedEulerCutShape_of_mem_carrier hy)

/-- **Endpoint bridge.**  The signed vertical-strip mass is literally the
canonically oriented Euler ledger at the same root.  No norm or estimate is
used. -/
theorem signedVerticalIntervalEndpointMass_eq_orientedEulerLedger
    (R : ℕ) :
    signedVerticalIntervalEndpointMass R =
      lowWheelCanonicalDowncrossOrientedLedger R := by
  symm
  exact lowWheelCanonicalDowncrossOrientedLedger_eq_sum_orderedEulerCutWeights R

/-- **Cross-coordinate closure.**  The complex vertical endpoint is not merely
analogous to the historical canonical defect: it is exactly the same signed
scalar.  The equality passes through the already-compiled late-parent
cancellation from the full downcross ledger to the oriented ledger. -/
theorem signedVerticalIntervalEndpointMass_eq_canonicalDefectLedger
    (R : ℕ) :
    signedVerticalIntervalEndpointMass R = lowWheelCanonicalDefectLedger R := by
  rw [signedVerticalIntervalEndpointMass_eq_orientedEulerLedger]
  rw [← LateParentCancellation.downcrossLedger_eq_orientedLedger R]
  rw [← lowWheelCanonicalDefectLedger_eq_downcrossLedger R]

/-- Net signed vertical-interval mass across the run from root `a` to root
`b+1`.  This is the arrival-side vertical strip minus the completion-side
vertical strip on the same growing-prefix process. -/
noncomputable def signedVerticalIntervalMass (a b : ℕ) : ℂ :=
  signedVerticalIntervalEndpointMass (b + 1) -
    signedVerticalIntervalEndpointMass a

/-- The complete vertical run is therefore exactly one increment of the
historical canonical defect ledger.  In particular, the Green--Kubo process
introduced later is an energy decomposition of this already-existing defect
trajectory, not a new arithmetic residual. -/
theorem signedVerticalIntervalMass_eq_canonicalDefectDifference
    (a b : ℕ) :
    signedVerticalIntervalMass a b =
      lowWheelCanonicalDefectLedger (b + 1) -
        lowWheelCanonicalDefectLedger a := by
  unfold signedVerticalIntervalMass
  rw [signedVerticalIntervalEndpointMass_eq_canonicalDefectLedger,
    signedVerticalIntervalEndpointMass_eq_canonicalDefectLedger]

/-- **Aggregate complex/Fermat-to-Euler bridge.**  The original signed vertical
factor-strip mass is exactly the active RH-critical oriented Euler run object,
before every absolute value or triangle inequality. -/
theorem signedVerticalIntervalMass_eq_orientedEulerLedger
    (a b : ℕ) :
    signedVerticalIntervalMass a b =
      canonicalOrientedRunDifference a b := by
  unfold signedVerticalIntervalMass canonicalOrientedRunDifference
  rw [signedVerticalIntervalEndpointMass_eq_orientedEulerLedger,
    signedVerticalIntervalEndpointMass_eq_orientedEulerLedger]

/-- The vertical-strip coordinate is also exactly the already-compiled signed
lifetime residual.  Thus the complex/Fermat and lifetime coordinates are not
separate analytic obligations. -/
theorem signedVerticalIntervalMass_eq_signedPrefixLifetimeResidual
    (a b : ℕ) :
    signedVerticalIntervalMass a b = signedPrefixLifetimeResidual a b := by
  rw [signedVerticalIntervalMass_eq_orientedEulerLedger,
    signedPrefixLifetimeResidual_eq_canonicalOrientedRunDifference]

/-- **Exact contracted run identity in the vertical coordinate.**  The signed
vertical mass is the global sum of dense-state differences plus the global sum
of first-jump differences.  No statewise norm is taken. -/
theorem signedVerticalIntervalMass_eq_sqrtDenseDifference_add_firstJumpDifference
    (a b : ℕ) :
    signedVerticalIntervalMass a b =
      (∑ x ∈ canonicalOrientedRunStateCarrier a b,
        (lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre (b + 1) x -
          lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre a x)) +
      ∑ x ∈ canonicalOrientedRunStateCarrier a b,
        (lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre (b + 1) x -
          lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre a x) := by
  rw [signedVerticalIntervalMass_eq_orientedEulerLedger]
  exact
    canonicalOrientedRunDifference_eq_sqrtDenseDifference_add_firstJumpDifference
      a b

/-- The remaining RH-scale estimate in the squared vertical-strip coordinate.

This is the squared-energy form of
`|vertical mass| <<_eps (b+1)^(1+eps)` on forward strict subdoubling square
runs.  No constant is assumed: for every positive `ε` one must construct a
uniform nonnegative constant. -/
def SignedVerticalIntervalEnergyBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ, 3 ≤ a → a ≤ b →
        (b + 1) ^ 2 < 2 * a ^ 2 →
        ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
          C * Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε)

/-- **No new analytic seam.**  The vertical-interval energy proposition is
exactly the already-exposed canonical oriented-run energy proposition.  Hence
the complex/Fermat bridge changes coordinates only; the remaining arithmetic
obligation is unchanged. -/
theorem signedVerticalIntervalEnergyBound_iff_canonicalOrientedRunDifferenceEnergyBounded :
    SignedVerticalIntervalEnergyBound ↔
      CanonicalOrientedRunDifferenceEnergyBoundedStatement := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro a b ha hab hsub
    rw [← signedVerticalIntervalMass_eq_orientedEulerLedger]
    exact hbound a b ha hab hsub
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro a b ha hab hsub
    rw [signedVerticalIntervalMass_eq_orientedEulerLedger]
    exact hbound a b ha hab hsub

end RHLean.Proof