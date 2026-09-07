import Mathlib
import RHLean.Analysis.SquareRootFixedCrossing18349
import RHLean.Proof.SquareRootLowPrimeOppositeFixedClassification
import RHLean.Proof.SquareRootLowPrimeSmoothTransportRecoupling

/-!
# Weight-preserving finite equivalence at the no-liberty seam

The true fixed population of the second processed-seat Othello matching and the
four-class tagged no-liberty boundary live in different coordinate types.  The
correct closure object is therefore not literal Finset equality, but a
pointwise weight-preserving map between the corresponding finite subtypes.

The stable set is already literally the descending processed frontier as a
Finset.  We first package that equality as a value-preserving subtype
Equiv.  For quantitative closure, an injective weight-preserving classifier is
enough; the older full-equivalence interface is retained for exact signed-mass
transfer when surjectivity is also available.
-/

noncomputable section

open Filter
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

/-- Every tagged no-liberty endpoint has native weight of absolute value at most
one.  The head and packet cells have weights `+1` and `-1`; the two arithmetic
endpoint classes are Möbius weights. -/
theorem abs_squareRootLowPrimeNoLibertyBoundaryWeight_le_one
    (x : SquareRootLowPrimeProcessedSeatNoLibertyState) :
    |squareRootLowPrimeNoLibertyBoundaryWeight x| ≤ 1 := by
  rcases x with u | x
  · simp [squareRootLowPrimeNoLibertyBoundaryWeight]
  · rcases x with s | x
    · simp [squareRootLowPrimeNoLibertyBoundaryWeight]
    · rcases x with z | z
      · have hInt :
          |(ArithmeticFunction.moebius
              (squareRootLowPrimeBadAtomChild z) : ℤ)| ≤ 1 := by
          simpa using
            (ArithmeticFunction.abs_moebius_le_one
              (n := squareRootLowPrimeBadAtomChild z))
        change |((ArithmeticFunction.moebius
          (squareRootLowPrimeBadAtomChild z) : ℤ) : ℝ)| ≤ 1
        exact_mod_cast hInt
      · have hInt :
          |(ArithmeticFunction.moebius (z.1.2 * z.2) : ℤ)| ≤ 1 := by
          simpa using
            (ArithmeticFunction.abs_moebius_le_one
              (n := z.1.2 * z.2))
        change |((ArithmeticFunction.moebius (z.1.2 * z.2) : ℤ) : ℝ)| ≤ 1
        exact_mod_cast hInt

/-- The source side is pointwise unit-bounded before any mass-from-cardinality
argument is made. -/
theorem abs_squareRootLowPrimeProcessedSeatDescendingFrontierWeight_le_one
    {R K j U : ℕ}
    (x : SquareRootLowPrimeProcessedSeatDescendingFrontier R K j U) :
    |squareRootLowPrimeProcessedSeatWeightReal
        (x : SquareRootLowPrimeProcessedState)| ≤ 1 := by
  exact abs_squareRootLowPrimeProcessedSeatWeightReal_le_one
    (x : SquareRootLowPrimeProcessedState)

/-- Consequently the absolute signed mass of any finite no-liberty boundary is
bounded by its number of unit endpoints. -/
theorem abs_squareRootLowPrimeNoLibertyBoundaryMass_le_card
    (R K j U : ℕ) :
    |∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U,
        squareRootLowPrimeNoLibertyBoundaryWeight z| ≤
      ((squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U).card : ℝ) := by
  calc
    |∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U,
        squareRootLowPrimeNoLibertyBoundaryWeight z| ≤
      ∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U,
        |squareRootLowPrimeNoLibertyBoundaryWeight z| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U,
        (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro z _hz
      exact abs_squareRootLowPrimeNoLibertyBoundaryWeight_le_one z
    _ = ((squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U).card : ℝ) := by
      simp

/-- Unit source weights bound the absolute descending-frontier mass by the
number of surviving processed seats. -/
theorem abs_squareRootLowPrimeProcessedSeatDescendingFrontierMass_le_card
    (R K j U : ℕ) :
    |∑ x ∈ squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x| ≤
      ((squareRootLowPrimeProcessedSeatDescendingTerminalFrontier
          R K j U).card : ℝ) := by
  calc
    |∑ x ∈ squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x| ≤
      ∑ x ∈ squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U,
        |squareRootLowPrimeProcessedSeatWeightReal x| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U,
        (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _hx
      exact abs_squareRootLowPrimeProcessedSeatWeightReal_le_one x
    _ = ((squareRootLowPrimeProcessedSeatDescendingTerminalFrontier
          R K j U).card : ℝ) := by
      simp

/-- At the canonical terminal cutoff, the already-proved `4*R` endpoint count
therefore gives the same `4*R` bound for signed boundary mass. -/
theorem abs_squareRootLowPrimeNoLibertyBoundaryMass_le_four_root
    {R K j : ℕ} (hR : 1 ≤ R) (hKR : K < R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    |∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j
        (squareRootBornPostTailLowPrimeCutoff R),
        squareRootLowPrimeNoLibertyBoundaryWeight z| ≤ 4 * (R : ℝ) := by
  have hmass := abs_squareRootLowPrimeNoLibertyBoundaryMass_le_card
    R K j (squareRootBornPostTailLowPrimeCutoff R)
  have hcard := squareRootLowPrimeProcessedSeatNoLibertyBoundary_card_le_four_root
    hR hKR hV0 hVK
  exact hmass.trans (by exact_mod_cast hcard)

/-- A pointwise no-liberty classifier: every descending terminal survivor is
sent to one actual tagged boundary endpoint, injectively and with its signed
weight unchanged. -/
structure SquareRootLowPrimeDescendingBoundaryWeightEmbedding
    (R K j U : ℕ) where
  toEmbedding :
    SquareRootLowPrimeProcessedSeatDescendingFrontier R K j U ↪
      SquareRootLowPrimeProcessedSeatNoLibertyTaggedBoundary R K j U
  weight_eq : ∀ x,
    squareRootLowPrimeNoLibertyBoundaryWeight
        (toEmbedding x : SquareRootLowPrimeProcessedSeatNoLibertyState) =
      squareRootLowPrimeProcessedSeatWeightReal
        (x : SquareRootLowPrimeProcessedState)

/-- An actual pointwise embedding transfers source cardinality to the tagged
boundary cardinality. -/
theorem squareRootLowPrimeProcessedSeatDescendingFrontier_card_le_boundary
    {R K j U : ℕ}
    (e : SquareRootLowPrimeDescendingBoundaryWeightEmbedding R K j U) :
    (squareRootLowPrimeProcessedSeatDescendingTerminalFrontier R K j U).card ≤
      (squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U).card := by
  have hcard :
      Fintype.card (SquareRootLowPrimeProcessedSeatDescendingFrontier R K j U) ≤
        Fintype.card (SquareRootLowPrimeProcessedSeatNoLibertyTaggedBoundary
          R K j U) :=
    Fintype.card_le_of_injective e.toEmbedding e.toEmbedding.injective
  simpa using hcard

/-- **Mass transfer from the actual classifier.**  At the canonical terminal
cutoff, a weight-preserving injection into the four tagged endpoint classes
immediately gives the `4*R` bound.  No surjectivity and no arbitrary finite-set
equivalence are used. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_four_root_of_embedding
    {R K j : ℕ}
    (hR : 2 ≤ R) (hKR : K < R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (e : SquareRootLowPrimeDescendingBoundaryWeightEmbedding
      R K j (squareRootBornPostTailLowPrimeCutoff R)) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤ 4 * (R : ℝ) := by
  rw [← squareRootLowPrimeProcessedSeatDescendingTerminalFrontier_weight_sum hR]
  have hmass :=
    abs_squareRootLowPrimeProcessedSeatDescendingFrontierMass_le_card
      R K j (squareRootBornPostTailLowPrimeCutoff R)
  have hsourceTarget :=
    squareRootLowPrimeProcessedSeatDescendingFrontier_card_le_boundary e
  have htarget :=
    squareRootLowPrimeProcessedSeatNoLibertyBoundary_card_le_four_root
      (R := R) (K := K) (j := j) (by omega) hKR hV0 hVK
  exact hmass.trans <| by
    exact_mod_cast hsourceTarget.trans htarget

/-- The fixed certified crossing at depth `18349` supplies one actual partial
layer index satisfying every packet-range hypothesis used by both the `4*R`
no-liberty boundary and the `R+K` smooth/transport recoupling. -/
theorem squareRootLowPrimeFixedCrossing18349_exists_boundary_and_recoupling
    {R : ℕ} (hR : 56 ≤ R) (hKR : 18349 < R)
    (hcross : SquareRootPacketCrossesAt R 18349) :
    ∃ j : ℕ,
      j ≤ squareRootReciprocalPrimeLayerCard R 18349 ∧
        0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j ∧
        squareRootCrossingLayerPartialPacketInt R 18349 j < (18349 : ℤ) ∧
        |∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R 18349 j
            (squareRootBornPostTailLowPrimeCutoff R),
            squareRootLowPrimeNoLibertyBoundaryWeight z| ≤ 4 * (R : ℝ) ∧
        ‖squareRootLowPrimeRunningImbalance R 18349 j
            (squareRootBornPostTailLowPrimeCutoff R) -
          squareRootMatchedBornSmoothTransport R‖ ≤
            (R : ℝ) + (18349 : ℝ) := by
  rcases squareRootPacketCrossing_exists_partial_residual_lt_depth hcross with
    ⟨j, hj, hV0, hVK⟩
  refine ⟨j, hj, hV0, hVK, ?_, ?_⟩
  · exact abs_squareRootLowPrimeNoLibertyBoundaryMass_le_four_root
      (R := R) (K := 18349) (j := j) (by omega) hKR hV0 hVK
  · exact norm_squareRootLowPrimeRunningImbalance_sub_matched_le_root_add_depth
      R 18349 j hR (by norm_num) hKR hj hV0 hVK

/-- The fixed crossing theorem is now wired into the terminal proof graph:
for all sufficiently large roots there is a concrete crossing-layer index `j`
for which both elementary bounds hold simultaneously. -/
theorem eventually_squareRootLowPrimeFixedCrossing18349_boundary_and_recoupling :
    ∀ᶠ R : ℕ in atTop,
      ∃ j : ℕ,
        j ≤ squareRootReciprocalPrimeLayerCard R 18349 ∧
          0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j ∧
          squareRootCrossingLayerPartialPacketInt R 18349 j < (18349 : ℤ) ∧
          |∑ z ∈ squareRootLowPrimeProcessedSeatNoLibertyBoundary R 18349 j
              (squareRootBornPostTailLowPrimeCutoff R),
              squareRootLowPrimeNoLibertyBoundaryWeight z| ≤ 4 * (R : ℝ) ∧
          ‖squareRootLowPrimeRunningImbalance R 18349 j
              (squareRootBornPostTailLowPrimeCutoff R) -
            squareRootMatchedBornSmoothTransport R‖ ≤
              (R : ℝ) + (18349 : ℝ) := by
  filter_upwards
    [eventually_squareRootPacketCrossesAt_18349,
      eventually_ge_atTop (18350 : ℕ)] with R hcross hRlarge
  exact squareRootLowPrimeFixedCrossing18349_exists_boundary_and_recoupling
    (R := R) (by omega) (by omega) hcross

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
