import Mathlib
import RHLean.Proof.SquareRootLowPrimeOppositeFixedClassification

/-!
# Weight-preserving finite equivalence at the no-liberty seam

The true fixed population of the second processed-seat Othello matching and the
four-class tagged no-liberty boundary live in different coordinate types.  The
correct closure object is therefore not literal Finset equality, but an
Equiv between the corresponding finite subtypes which preserves signed weight.

The stable set is already literally the descending processed frontier as a
Finset.  We first package that equality as a value-preserving subtype
Equiv.  Thus the only arithmetic construction left in this file is exactly the
weight-preserving equivalence from the descending frontier to the tagged
boundary.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The true stable population of the second processed-seat Othello matching. -/
abbrev SquareRootLowPrimeProcessedSeatNoLibertyStable
    (R K j U : ℕ) :=
  ↥(finiteOthelloStablePart
      (squareRootLowPrimeProcessedSeatCarrier R K j U)
      (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U))

/-- The descending processed terminal frontier as a finite subtype. -/
abbrev SquareRootLowPrimeProcessedSeatDescendingFrontier
    (R K j U : ℕ) :=
  ↥(squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U)

/-- The tagged four-class terminal boundary as a finite subtype. -/
abbrev SquareRootLowPrimeProcessedSeatNoLibertyTaggedBoundary
    (R K j U : ℕ) :=
  ↥(squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U)

/-- The already-proved stable-set equality, exposed as a subtype equivalence.
It changes only the membership proof; the underlying processed state is
unchanged. -/
noncomputable def squareRootLowPrimeProcessedSeatNoLibertyStableEquivDescending
    (R K j U : ℕ) :
    SquareRootLowPrimeProcessedSeatNoLibertyStable R K j U ≃
      SquareRootLowPrimeProcessedSeatDescendingFrontier R K j U where
  toFun x :=
    ⟨x.1, by
      rw [← finiteOthelloStablePart_processedSeatNoLibertyMate_eq_descendingFrontier
        R K j U]
      exact x.2⟩
  invFun x :=
    ⟨x.1, by
      rw [finiteOthelloStablePart_processedSeatNoLibertyMate_eq_descendingFrontier
        R K j U]
      exact x.2⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl

@[simp] theorem squareRootLowPrimeProcessedSeatNoLibertyStableEquivDescending_val
    (R K j U : ℕ)
    (x : SquareRootLowPrimeProcessedSeatNoLibertyStable R K j U) :
    ((squareRootLowPrimeProcessedSeatNoLibertyStableEquivDescending R K j U x :
      SquareRootLowPrimeProcessedSeatDescendingFrontier R K j U) :
        SquareRootLowPrimeProcessedState) = x := by
  rfl

/-- The genuinely arithmetic seam: a finite equivalence from the descending
processed terminal frontier to the four tagged homes, preserving the native
signed weight pointwise. -/
structure SquareRootLowPrimeDescendingBoundaryWeightEquiv
    (R K j U : ℕ) where
  toEquiv :
    SquareRootLowPrimeProcessedSeatDescendingFrontier R K j U ≃
      SquareRootLowPrimeProcessedSeatNoLibertyTaggedBoundary R K j U
  weight_eq : ∀ x,
    squareRootLowPrimeNoLibertyBoundaryWeight (toEquiv x :
      SquareRootLowPrimeProcessedSeatNoLibertyState) =
      squareRootLowPrimeProcessedSeatWeightReal
        (x : SquareRootLowPrimeProcessedState)

/-- A finite equivalence across the original stable set and tagged boundary,
together with exact pointwise preservation of the native signed weights. -/
structure SquareRootLowPrimeNoLibertyWeightEquiv
    (R K j U : ℕ) where
  toEquiv :
    SquareRootLowPrimeProcessedSeatNoLibertyStable R K j U ≃
      SquareRootLowPrimeProcessedSeatNoLibertyTaggedBoundary R K j U
  weight_eq : ∀ x,
    squareRootLowPrimeNoLibertyBoundaryWeight (toEquiv x :
      SquareRootLowPrimeProcessedSeatNoLibertyState) =
      squareRootLowPrimeProcessedSeatWeightReal
        (x : SquareRootLowPrimeProcessedState)

/-- Once the descending-frontier classifier is supplied, composition with the
already-compiled stable/frontier equivalence gives the requested stable-set
classifier with no further arithmetic. -/
noncomputable def SquareRootLowPrimeDescendingBoundaryWeightEquiv.toStable
    {R K j U : ℕ}
    (e : SquareRootLowPrimeDescendingBoundaryWeightEquiv R K j U) :
    SquareRootLowPrimeNoLibertyWeightEquiv R K j U where
  toEquiv :=
    (squareRootLowPrimeProcessedSeatNoLibertyStableEquivDescending R K j U).trans
      e.toEquiv
  weight_eq := by
    intro x
    simpa using e.weight_eq
      (squareRootLowPrimeProcessedSeatNoLibertyStableEquivDescending R K j U x)

/-- A weight-preserving finite equivalence transfers the complete signed mass.
This is the exact replacement for the ill-typed claim that the two finite sets
are literally equal. -/
theorem squareRootLowPrimeNoLibertyWeightEquiv_sum_eq
    {R K j U : ℕ}
    (e : SquareRootLowPrimeNoLibertyWeightEquiv R K j U) :
    (∑ x ∈ finiteOthelloStablePart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U),
      squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U,
        squareRootLowPrimeNoLibertyBoundaryWeight z := by
  classical
  let A := finiteOthelloStablePart
    (squareRootLowPrimeProcessedSeatCarrier R K j U)
    (squareRootLowPrimeProcessedSeatNoLibertyMate R K j U)
  let B := squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U
  calc
    (∑ x ∈ A, squareRootLowPrimeProcessedSeatWeightReal x) =
        ∑ x : ↥A, squareRootLowPrimeProcessedSeatWeightReal
          (x : SquareRootLowPrimeProcessedState) := by
      exact (Finset.sum_attach A squareRootLowPrimeProcessedSeatWeightReal).symm
    _ = ∑ z : ↥B, squareRootLowPrimeNoLibertyBoundaryWeight
          (z : SquareRootLowPrimeProcessedSeatNoLibertyState) := by
      rw [← e.toEquiv.sum_comp]
      apply Finset.sum_congr rfl
      intro x _hx
      simpa [A, B] using (e.weight_eq x).symm
    _ = ∑ z ∈ B, squareRootLowPrimeNoLibertyBoundaryWeight z := by
      exact Finset.sum_attach B squareRootLowPrimeNoLibertyBoundaryWeight

/-- Once the carrier-specific weight equivalence is constructed, the tagged
boundary mass is exactly the running imbalance already computed on the true
processed carrier. -/
theorem squareRootLowPrimeNoLibertyWeightEquiv_boundaryMass_eq_runningImbalance
    {R K j U : ℕ} (hR : 2 ≤ R)
    (e : SquareRootLowPrimeNoLibertyWeightEquiv R K j U) :
    (∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U,
      squareRootLowPrimeNoLibertyBoundaryWeight z) =
      squareRootLowPrimeRunningImbalanceReal R K j U := by
  rw [← squareRootLowPrimeNoLibertyWeightEquiv_sum_eq e]
  exact squareRootLowPrimeProcessedSeatNoLibertyMate_stableMass_eq_runningImbalance hR

end RHLean.Proof
