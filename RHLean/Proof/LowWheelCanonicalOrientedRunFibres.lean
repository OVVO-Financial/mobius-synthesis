import Mathlib
import RHLean.Analysis.FrozenSquareRunDowncrossBridge
import RHLean.Proof.LowWheelCanonicalOrientedFrozenFibres

/-!
# Common frozen-owner carrier for the oriented square-run difference

`LowWheelCanonicalOrientedFrozenFibres` identifies the signed Boolean faces
charging one fixed oriented state with one frozen predecessor window through
its canonical pivot.  This file performs the remaining finite Fubini step.

At one root `R`, the oriented ledger is regrouped by physical states `(c,k)`.
The signed face mass of each state is then replaced by its exact frozen
predecessor-window mass.  For two endpoints `a` and `b+1`, both endpoint sums
are extended to the union of their state carriers.  Hence

`O_{b+1} - O_a`

is one signed sum on a common carrier, and each state keeps the *same* canonical
owner `p = minFac(c*k)` at both endpoints.  Only its two frozen window endpoints
move with `R`.

This is the representation needed by the recursive Go laws: predecessor-cube
cancellation is preserved state-by-state before any norm is taken.

No triangle inequality, PNT input, prime-gap estimate, or asymptotic hypothesis
appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open SignedOwnershipInterval

attribute [local instance] Classical.propDecidable

/-- Fixed rectangular state ambient large enough for every oriented downcross
state at root `R`. -/
def lowWheelCanonicalDowncrossOrientedStateAmbient
    (R : ℕ) : Finset LowWheelCofactorQuotientState :=
  (Finset.Ico 1 R) ×ˢ (Finset.Icc 1 (squareRootEndpoint R))

/-- The physical states actually charged by at least one oriented Boolean face. -/
def lowWheelCanonicalDowncrossOrientedStateCarrier
    (R : ℕ) : Finset LowWheelCofactorQuotientState :=
  (lowWheelCanonicalDowncrossOrientedStateAmbient R).filter fun x =>
    (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty

@[simp] theorem mem_lowWheelCanonicalDowncrossOrientedStateCarrier
    {R : ℕ} {x : LowWheelCofactorQuotientState} :
    x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R ↔
      x ∈ lowWheelCanonicalDowncrossOrientedStateAmbient R ∧
        (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty := by
  simp [lowWheelCanonicalDowncrossOrientedStateCarrier]

/-- Every oriented downcross state lies in the fixed rectangular ambient. -/
theorem lowWheelCanonicalDowncrossOrientedPart_subset_stateAmbient
    {R : ℕ} {t : Finset ℕ} :
    lowWheelCanonicalDowncrossOrientedPart R t ⊆
      lowWheelCanonicalDowncrossOrientedStateAmbient R := by
  intro x hx
  have hdown := (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1
  have hphys :=
    mem_lowWheelCanonicalPhysicalStateSet.mp
      (mem_lowWheelCanonicalDowncrossPart.mp hdown).1
  exact Finset.mem_product.mpr ⟨hphys.1, hphys.2.1⟩

/-- Filtering the rectangular ambient by one face recovers exactly that face's
oriented state part. -/
theorem filter_stateAmbient_mem_orientedPart
    (R : ℕ) (t : Finset ℕ) :
    (lowWheelCanonicalDowncrossOrientedStateAmbient R).filter
        (fun x => x ∈ lowWheelCanonicalDowncrossOrientedPart R t) =
      lowWheelCanonicalDowncrossOrientedPart R t := by
  ext x
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    exact Finset.mem_filter.mpr
      ⟨lowWheelCanonicalDowncrossOrientedPart_subset_stateAmbient hx, hx⟩

/-- Nonempty oriented charging automatically puts a state in the canonical
state carrier. -/
theorem mem_orientedStateCarrier_of_chargingFaces_nonempty
    {R : ℕ} {x : LowWheelCofactorQuotientState}
    (hne : (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty) :
    x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R := by
  rcases hne with ⟨t, ht⟩
  rcases mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht with
    ⟨_htPow, hx⟩
  apply mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mpr
  exact ⟨lowWheelCanonicalDowncrossOrientedPart_subset_stateAmbient hx,
    ⟨t, ht⟩⟩

/-- Complex signed Boolean-face mass attached to one physical oriented state. -/
def lowWheelCanonicalDowncrossOrientedStateFaceMass
    (R : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  ∑ t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R x,
    (booleanCubeSign t : ℂ)

/-- State contribution before replacing its Boolean cube by the frozen
predecessor window. -/
def lowWheelCanonicalDowncrossOrientedStateFibre
    (R : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  canonicalMoebiusWeight x.1 *
    lowWheelCanonicalDowncrossOrientedStateFaceMass R x

/-- The exact frozen predecessor-window contribution of one state.  It is zero
when the state is not actually present at root `R`. -/
def lowWheelCanonicalDowncrossOrientedFrozenStateFibre
    (R : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  if (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty then
    canonicalMoebiusWeight x.1 *
      ((frozenPrimeUniverseWindowMass
        (primesUpTo (lowWheelCanonicalDowncrossPivot x - 1))
        (R / x.2)
        (lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2) : ℤ) : ℂ)
  else 0

/-- Complex form of the one-state frozen predecessor-window theorem. -/
theorem lowWheelCanonicalDowncrossOrientedStateFaceMass_eq_frozenWindowMass
    {R c k : ℕ}
    (hne : (lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)).Nonempty) :
    lowWheelCanonicalDowncrossOrientedStateFaceMass R (c, k) =
      ((frozenPrimeUniverseWindowMass
        (primesUpTo (lowWheelCanonicalDowncrossPivot (c, k) - 1))
        (R / k)
        (lowWheelCanonicalDowncrossOwnershipUpper R c k) : ℤ) : ℂ) := by
  have h :=
    sum_booleanCubeSign_orientedChargingFaces_eq_frozenWindowMass hne
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  simpa [lowWheelCanonicalDowncrossOrientedStateFaceMass] using hc

/-- The state-fibre and frozen-window presentations agree for every state,
including absent states. -/
theorem lowWheelCanonicalDowncrossOrientedStateFibre_eq_frozenStateFibre
    (R : ℕ) (x : LowWheelCofactorQuotientState) :
    lowWheelCanonicalDowncrossOrientedStateFibre R x =
      lowWheelCanonicalDowncrossOrientedFrozenStateFibre R x := by
  by_cases hne : (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty
  · rcases x with ⟨c, k⟩
    simp only [lowWheelCanonicalDowncrossOrientedFrozenStateFibre, hne, if_true]
    unfold lowWheelCanonicalDowncrossOrientedStateFibre
    rw [lowWheelCanonicalDowncrossOrientedStateFaceMass_eq_frozenWindowMass hne]
  · have hempty : lowWheelCanonicalDowncrossOrientedChargingFaces R x = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    simp [lowWheelCanonicalDowncrossOrientedStateFibre,
      lowWheelCanonicalDowncrossOrientedStateFaceMass,
      lowWheelCanonicalDowncrossOrientedFrozenStateFibre, hempty]

/-- A state outside the oriented state carrier has zero state fibre. -/
theorem lowWheelCanonicalDowncrossOrientedStateFibre_eq_zero_of_not_mem
    {R : ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∉ lowWheelCanonicalDowncrossOrientedStateCarrier R) :
    lowWheelCanonicalDowncrossOrientedStateFibre R x = 0 := by
  by_cases hne : (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty
  · exact (hx (mem_orientedStateCarrier_of_chargingFaces_nonempty hne)).elim
  · have hempty : lowWheelCanonicalDowncrossOrientedChargingFaces R x = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    simp [lowWheelCanonicalDowncrossOrientedStateFibre,
      lowWheelCanonicalDowncrossOrientedStateFaceMass, hempty]

/-- The same zero-extension property in the frozen-window presentation. -/
theorem lowWheelCanonicalDowncrossOrientedFrozenStateFibre_eq_zero_of_not_mem
    {R : ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∉ lowWheelCanonicalDowncrossOrientedStateCarrier R) :
    lowWheelCanonicalDowncrossOrientedFrozenStateFibre R x = 0 := by
  rw [← lowWheelCanonicalDowncrossOrientedStateFibre_eq_frozenStateFibre]
  exact lowWheelCanonicalDowncrossOrientedStateFibre_eq_zero_of_not_mem hx

/-- Extend one face's oriented-state sum to the fixed rectangular ambient. -/
theorem sum_orientedPart_eq_sum_stateAmbient_indicator
    (R : ℕ) (t : Finset ℕ) :
    (∑ x ∈ lowWheelCanonicalDowncrossOrientedPart R t,
        canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
      ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateAmbient R,
        if x ∈ lowWheelCanonicalDowncrossOrientedPart R t then
          canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)
        else 0 := by
  rw [← Finset.sum_filter,
    filter_stateAmbient_mem_orientedPart]

/-- **Finite Fubini by physical state.**  The oriented Euler ledger is exactly
the sum of its signed state fibres. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sum_stateFibres
    (R : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger R =
      ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedStateFibre R x := by
  classical
  unfold lowWheelCanonicalDowncrossOrientedLedger
  calc
    (∑ t ∈ (primesUpTo R).powerset,
        ∑ x ∈ lowWheelCanonicalDowncrossOrientedPart R t,
          canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
      ∑ t ∈ (primesUpTo R).powerset,
        ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateAmbient R,
          if x ∈ lowWheelCanonicalDowncrossOrientedPart R t then
            canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)
          else 0 := by
      apply Finset.sum_congr rfl
      intro t _ht
      exact sum_orientedPart_eq_sum_stateAmbient_indicator R t
    _ = ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateAmbient R,
        ∑ t ∈ (primesUpTo R).powerset,
          if x ∈ lowWheelCanonicalDowncrossOrientedPart R t then
            canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateAmbient R,
        lowWheelCanonicalDowncrossOrientedStateFibre R x := by
      apply Finset.sum_congr rfl
      intro x _hx
      unfold lowWheelCanonicalDowncrossOrientedStateFibre
        lowWheelCanonicalDowncrossOrientedStateFaceMass
        lowWheelCanonicalDowncrossOrientedChargingFaces
      rw [← Finset.sum_filter, Finset.mul_sum]
    _ = ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedStateFibre R x := by
      symm
      unfold lowWheelCanonicalDowncrossOrientedStateCarrier
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hne :
          (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty
      · simp [hne]
      · have hempty : lowWheelCanonicalDowncrossOrientedChargingFaces R x = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hne
        simp [lowWheelCanonicalDowncrossOrientedStateFibre,
          lowWheelCanonicalDowncrossOrientedStateFaceMass, hempty]

/-- State-fibre Fubini with the predecessor cube made explicit. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sum_frozenStateFibres
    (R : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger R =
      ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedFrozenStateFibre R x := by
  rw [lowWheelCanonicalDowncrossOrientedLedger_eq_sum_stateFibres]
  apply Finset.sum_congr rfl
  intro x _hx
  exact lowWheelCanonicalDowncrossOrientedStateFibre_eq_frozenStateFibre R x

/-- Common physical state carrier for the two endpoints of a forward square
run.  A state may be born, persist, or die between the endpoints; absent
endpoint contributions are exactly zero. -/
def canonicalOrientedRunStateCarrier (a b : ℕ) :
    Finset LowWheelCofactorQuotientState :=
  lowWheelCanonicalDowncrossOrientedStateCarrier a ∪
    lowWheelCanonicalDowncrossOrientedStateCarrier (b + 1)

/-- Extend the lower endpoint oriented ledger to the common run carrier. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sum_runCarrier_left
    (a b : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger a =
      ∑ x ∈ canonicalOrientedRunStateCarrier a b,
        lowWheelCanonicalDowncrossOrientedFrozenStateFibre a x := by
  rw [lowWheelCanonicalDowncrossOrientedLedger_eq_sum_frozenStateFibres]
  refine Finset.sum_subset Finset.subset_union_left ?_
  intro x hxUnion hxNot
  exact lowWheelCanonicalDowncrossOrientedFrozenStateFibre_eq_zero_of_not_mem hxNot

/-- Extend the upper endpoint oriented ledger to the common run carrier. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sum_runCarrier_right
    (a b : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger (b + 1) =
      ∑ x ∈ canonicalOrientedRunStateCarrier a b,
        lowWheelCanonicalDowncrossOrientedFrozenStateFibre (b + 1) x := by
  rw [lowWheelCanonicalDowncrossOrientedLedger_eq_sum_frozenStateFibres]
  refine Finset.sum_subset Finset.subset_union_right ?_
  intro x hxUnion hxNot
  exact lowWheelCanonicalDowncrossOrientedFrozenStateFibre_eq_zero_of_not_mem hxNot

/-- **Common-owner frozen-strip representation of the square-run frontier.**

Both endpoint ledgers have been placed on one physical-state carrier.  For each
state `x`, its canonical owner `lowWheelCanonicalDowncrossPivot x` is fixed by
`x` itself, so the two terms are frozen windows in the same predecessor prime
universe `primesUpTo (pivot x - 1)`.

This is the exact representation on which the existing strictly-smaller-owner
Go recursion should now be iterated before taking an energy norm. -/
theorem canonicalOrientedRunDifference_eq_sum_frozenStateFibreDifferences
    (a b : ℕ) :
    canonicalOrientedRunDifference a b =
      ∑ x ∈ canonicalOrientedRunStateCarrier a b,
        (lowWheelCanonicalDowncrossOrientedFrozenStateFibre (b + 1) x -
          lowWheelCanonicalDowncrossOrientedFrozenStateFibre a x) := by
  unfold canonicalOrientedRunDifference
  rw [lowWheelCanonicalDowncrossOrientedLedger_eq_sum_runCarrier_right,
    lowWheelCanonicalDowncrossOrientedLedger_eq_sum_runCarrier_left,
    ← Finset.sum_sub_distrib]

/-! ## Sequential insertion law for predecessor density

The squarefree dense-divisibility criterion has a smooth core: only a newly
inserted prime `p > Y` is constrained.  Thus, if `p` is inserted after every
coordinate already in `t`, all old predecessor products are unchanged and the
only possible new condition is

`Y < p -> p^d <= Y * primeFaceProduct t`.

Once the old face is dense, failure after adjoining `p` is therefore exactly a
large multiplicative jump above the smooth threshold. -/

/-- Inserting a later coordinate does not change the predecessor face of an
older coordinate. -/
theorem predecessorPrimeFace_insert_of_lt
    {t : Finset ℕ} {p q : ℕ} (hqp : q < p) :
    predecessorPrimeFace (insert p t) q = predecessorPrimeFace t q := by
  ext r
  constructor
  · intro hr
    rcases mem_predecessorPrimeFace.mp hr with ⟨hrins, hrq⟩
    rcases Finset.mem_insert.mp hrins with hrp | hrt
    · subst r
      omega
    · exact mem_predecessorPrimeFace.mpr ⟨hrt, hrq⟩
  · intro hr
    rcases mem_predecessorPrimeFace.mp hr with ⟨hrt, hrq⟩
    exact mem_predecessorPrimeFace.mpr ⟨Finset.mem_insert_of_mem hrt, hrq⟩

/-- If `p` is larger than the whole old face, its predecessor face after
insertion is literally the whole old face. -/
theorem predecessorPrimeFace_insert_top
    {t : Finset ℕ} {p : ℕ}
    (hpTop : ∀ q ∈ t, q < p) :
    predecessorPrimeFace (insert p t) p = t := by
  ext q
  constructor
  · intro hq
    rcases mem_predecessorPrimeFace.mp hq with ⟨hqins, hqp⟩
    rcases Finset.mem_insert.mp hqins with hEq | hqt
    · subst q
      omega
    · exact hqt
  · intro hqt
    exact mem_predecessorPrimeFace.mpr
      ⟨Finset.mem_insert_of_mem hqt, hpTop q hqt⟩

/-- Product form of `predecessorPrimeFace_insert_of_lt`. -/
theorem predecessorPrimeFaceProduct_insert_of_lt
    {t : Finset ℕ} {p q : ℕ} (hqp : q < p) :
    predecessorPrimeFaceProduct (insert p t) q =
      predecessorPrimeFaceProduct t q := by
  unfold predecessorPrimeFaceProduct
  rw [predecessorPrimeFace_insert_of_lt hqp]

/-- Product form of the top-insertion identity. -/
theorem predecessorPrimeFaceProduct_insert_top
    {t : Finset ℕ} {p : ℕ}
    (hpTop : ∀ q ∈ t, q < p) :
    predecessorPrimeFaceProduct (insert p t) p = primeFaceProduct t := by
  unfold predecessorPrimeFaceProduct
  rw [predecessorPrimeFace_insert_top hpTop]

/-- **Sequential Euler insertion law.**  Once `p` is the new largest
coordinate, predecessor density of the enlarged face is exactly old density
plus the one possible large-prime condition at `p`. -/
theorem predecessorDenseFace_insert_top_iff
    {d Y p : ℕ} {t : Finset ℕ}
    (hpTop : ∀ q ∈ t, q < p) :
    PredecessorDenseFace d Y (insert p t) ↔
      PredecessorDenseFace d Y t ∧
        (Y < p → p ^ d ≤ Y * primeFaceProduct t) := by
  unfold PredecessorDenseFace
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro q hqt hYq
      have hq := h q (Finset.mem_insert_of_mem hqt) hYq
      rw [predecessorPrimeFaceProduct_insert_of_lt (hpTop q hqt)] at hq
      exact hq
    · intro hYp
      have hp := h p (by simp) hYp
      rw [predecessorPrimeFaceProduct_insert_top hpTop] at hp
      exact hp
  · rintro ⟨ht, hp⟩ q hq hYq
    rcases Finset.mem_insert.mp hq with hEq | hqt
    · subst q
      rw [predecessorPrimeFaceProduct_insert_top hpTop]
      exact hp hYq
    · have hqp := hpTop q hqt
      rw [predecessorPrimeFaceProduct_insert_of_lt hqp]
      exact ht q hqt hYq

/-- With the predecessor already dense, adjoining a new largest coordinate
fails density exactly when that coordinate lies above the smooth threshold and
is too large relative to the whole predecessor product. -/
theorem not_predecessorDenseFace_insert_top_iff
    {d Y p : ℕ} {t : Finset ℕ}
    (hpTop : ∀ q ∈ t, q < p)
    (hdense : PredecessorDenseFace d Y t) :
    ¬ PredecessorDenseFace d Y (insert p t) ↔
      Y < p ∧ Y * primeFaceProduct t < p ^ d := by
  rw [predecessorDenseFace_insert_top_iff hpTop]
  simp only [hdense, true_and]
  constructor
  · intro h
    have hYp : Y < p := by
      by_contra hnot
      apply h
      intro hYp
      exact (hnot hYp).elim
    refine ⟨hYp, ?_⟩
    by_contra hnot
    apply h
    intro _hYp
    omega
  · rintro ⟨hYp, hfail⟩ hgood
    have hle := hgood hYp
    omega

/-- Truncating at `p` and then looking below an earlier `q` gives the same
predecessor face as looking below `q` in the original face. -/
theorem predecessorPrimeFace_predecessor_of_lt
    {t : Finset ℕ} {p q : ℕ} (hqp : q < p) :
    predecessorPrimeFace (predecessorPrimeFace t p) q =
      predecessorPrimeFace t q := by
  ext r
  constructor
  · intro hr
    rcases mem_predecessorPrimeFace.mp hr with ⟨hrp, hrq⟩
    exact mem_predecessorPrimeFace.mpr
      ⟨(mem_predecessorPrimeFace.mp hrp).1, hrq⟩
  · intro hr
    rcases mem_predecessorPrimeFace.mp hr with ⟨hrt, hrq⟩
    exact mem_predecessorPrimeFace.mpr
      ⟨mem_predecessorPrimeFace.mpr ⟨hrt, hrq.trans hqp⟩, hrq⟩

/-- Product form of predecessor truncation stability. -/
theorem predecessorPrimeFaceProduct_predecessor_of_lt
    {t : Finset ℕ} {p q : ℕ} (hqp : q < p) :
    predecessorPrimeFaceProduct (predecessorPrimeFace t p) q =
      predecessorPrimeFaceProduct t q := by
  unfold predecessorPrimeFaceProduct
  rw [predecessorPrimeFace_predecessor_of_lt hqp]

/-- If every large coordinate before `p` satisfies the density inequality, then
the entire predecessor face below `p` is itself predecessor-dense. -/
theorem predecessorPrimeFace_dense_of_previous
    {d Y p : ℕ} {t : Finset ℕ}
    (hprev : ∀ q ∈ t, q < p → Y < q →
      q ^ d ≤ Y * predecessorPrimeFaceProduct t q) :
    PredecessorDenseFace d Y (predecessorPrimeFace t p) := by
  intro q hq hYq
  rcases mem_predecessorPrimeFace.mp hq with ⟨hqt, hqp⟩
  rw [predecessorPrimeFaceProduct_predecessor_of_lt hqp]
  exact hprev q hqt hqp hYq

/-- A non-dense face therefore has a first large multiplicative jump attached
to a predecessor face which is already dense. -/
theorem exists_first_predecessorDenseFailure_with_densePredecessor
    {d Y : ℕ} {t : Finset ℕ}
    (hnot : ¬ PredecessorDenseFace d Y t) :
    ∃ p ∈ t,
      Y < p ∧
      Y * predecessorPrimeFaceProduct t p < p ^ d ∧
        PredecessorDenseFace d Y (predecessorPrimeFace t p) := by
  rcases exists_first_predecessorDenseFailure hnot with
    ⟨p, hpt, hYp, hfail, hprev⟩
  exact ⟨p, hpt, hYp, hfail,
    predecessorPrimeFace_dense_of_previous hprev⟩

/-- On an oriented charging face, the exceptional first jump is a strictly
smaller owner than the current fresh pivot, is above the smooth threshold, and
is attached to an already-dense predecessor cube. -/
theorem orientedChargingFace_dense_or_firstLowerJump_with_densePredecessor
    {R c k d Y : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)) :
    PredecessorDenseFace d Y t ∨
      ∃ p ∈ t,
        p < lowWheelCanonicalDowncrossPivot (c, k) ∧
        Y < p ∧
        Y * predecessorPrimeFaceProduct t p < p ^ d ∧
          PredecessorDenseFace d Y (predecessorPrimeFace t p) := by
  rcases mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht with
    ⟨htPow, hx⟩
  by_cases hdense : PredecessorDenseFace d Y t
  · exact Or.inl hdense
  · right
    rcases exists_first_predecessorDenseFailure_with_densePredecessor hdense with
      ⟨p, hpt, hYp, hfail, hpredDense⟩
    have hpLt :=
      lowWheelCanonicalDowncrossOriented_facePrime_lt_pivot htPow hx hpt
    exact ⟨p, hpt, hpLt, hYp, hfail, hpredDense⟩

/-! ## Triply dense faces and the fourth-power wall

For a coordinate above the smooth threshold, the `d`-fold predecessor
inequality gains one more power after multiplying by that coordinate.  For a
coordinate at or below `Y`, the same `d+1` power is controlled by `Y^(d+1)`.
Hence, if both

`Y^(d+1) <= X`  and  `Y * primeFaceProduct t <= X`,

all coordinates of a predecessor-dense face satisfy `p^(d+1) <= X`.

At `d = 3` this lands exactly on the fourth-power wall already isolated by the
Go geometry.  The scale `Y` remains independent of the physical state: the
smooth core is not accidentally enlarged to the entire oriented face.
-/

/-- For a face of prime coordinates, adjoining `p` to its strict predecessor
face gives a subproduct of the full face product. -/
theorem prime_mul_predecessorPrimeFaceProduct_le
    {t : Finset ℕ} {p : ℕ}
    (hprime : ∀ q ∈ t, q.Prime) (hpt : p ∈ t) :
    p * predecessorPrimeFaceProduct t p ≤ primeFaceProduct t := by
  have hsub : insert p (predecessorPrimeFace t p) ⊆ t := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hEq | hpred
    · subst q
      exact hpt
    · exact (mem_predecessorPrimeFace.mp hpred).1
  have hdiv :
      primeFaceProduct (insert p (predecessorPrimeFace t p)) ∣
        primeFaceProduct t := by
    unfold primeFaceProduct
    exact Finset.prod_dvd_prod_of_subset _ _ id hsub
  have hprodPos : 0 < primeFaceProduct t := by
    unfold primeFaceProduct
    exact Finset.prod_pos fun q hq => (hprime q hq).pos
  have hle := Nat.le_of_dvd hprodPos hdiv
  have hpNot : p ∉ predecessorPrimeFace t p := by simp
  simpa [primeFaceProduct, predecessorPrimeFaceProduct, hpNot] using hle

/-- Every *large* coordinate of a predecessor-dense prime face obeys the
corresponding `d+1` power bound against the complete face product. -/
theorem predecessorDenseFace_coordinate_power_succ_le_of_large
    {d Y p : ℕ} {t : Finset ℕ}
    (hprime : ∀ q ∈ t, q.Prime)
    (hdense : PredecessorDenseFace d Y t) (hpt : p ∈ t)
    (hYp : Y < p) :
    p ^ (d + 1) ≤ Y * primeFaceProduct t := by
  have hd := hdense p hpt hYp
  have hprefix := prime_mul_predecessorPrimeFaceProduct_le hprime hpt
  calc
    p ^ (d + 1) = p ^ d * p := by rw [pow_succ]
    _ ≤ (Y * predecessorPrimeFaceProduct t p) * p :=
      Nat.mul_le_mul_right p hd
    _ = Y * (p * predecessorPrimeFaceProduct t p) := by ring
    _ ≤ Y * primeFaceProduct t := Nat.mul_le_mul_left Y hprefix

/-- Combining the smooth and large branches: if both natural `Y`-scale
quantities fit below `X`, then every coordinate of a predecessor-dense prime
face lies below the `d+1` power wall at `X`. -/
theorem predecessorDenseFace_coordinate_power_succ_le_of_scale
    {d Y X p : ℕ} {t : Finset ℕ}
    (hprime : ∀ q ∈ t, q.Prime)
    (hdense : PredecessorDenseFace d Y t) (hpt : p ∈ t)
    (hYpow : Y ^ (d + 1) ≤ X)
    (hYprod : Y * primeFaceProduct t ≤ X) :
    p ^ (d + 1) ≤ X := by
  by_cases hYp : Y < p
  · exact
      (predecessorDenseFace_coordinate_power_succ_le_of_large
        hprime hdense hpt hYp).trans hYprod
  · have hpY : p ≤ Y := Nat.le_of_not_gt hYp
    exact (Nat.pow_le_pow_left hpY (d + 1)).trans hYpow

/-- Every oriented charging face has product at most the root parameter `R`.
This is just the exact state ownership interval already proved for the frozen
carrier. -/
theorem orientedChargingFace_faceProduct_le_root
    {R c k : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)) :
    primeFaceProduct t ≤ R := by
  rcases mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht with
    ⟨htPow, hx⟩
  have htCharging :
      t ∈ lowWheelCanonicalDowncrossChargingFaces R (c, k) :=
    mem_lowWheelCanonicalDowncrossChargingFaces.mpr
      ⟨htPow, (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1⟩
  have hwindow := primeFaceProduct_mem_exactOwnershipInterval htCharging
  have hup := (Finset.mem_Ioc.mp hwindow).2
  have hupperLeR :
      lowWheelCanonicalDowncrossOwnershipUpper R c k ≤ R := by
    unfold lowWheelCanonicalDowncrossOwnershipUpper
    exact (min_le_left _ _).trans (Nat.div_le_self _ _)
  exact hup.trans hupperLeR

/-- **Triply dense oriented faces are fourth-power safe at any admissible
smooth scale.**  It is enough that the smooth fourth power and the complete
`Y`-weighted face product both fit below the square endpoint. -/
theorem orientedChargingFace_triplyDense_facePrimeFourth_le_endpoint
    {R c k Y p : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k))
    (hdense : PredecessorDenseFace 3 Y t)
    (hY4 : Y ^ 4 ≤ squareRootEndpoint R)
    (hYR : Y * R ≤ squareRootEndpoint R)
    (hpt : p ∈ t) :
    p ^ 4 ≤ squareRootEndpoint R := by
  rcases mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht with
    ⟨htPow, _hx⟩
  have hsub := Finset.mem_powerset.mp htPow
  have hprime : ∀ q ∈ t, q.Prime := by
    intro q hqt
    exact prime_of_mem_primesUpTo (hsub hqt)
  have hface := orientedChargingFace_faceProduct_le_root ht
  have hYprod : Y * primeFaceProduct t ≤ squareRootEndpoint R :=
    (Nat.mul_le_mul_left Y hface).trans hYR
  have hpower :=
    predecessorDenseFace_coordinate_power_succ_le_of_scale
      (d := 3) (Y := Y) (X := squareRootEndpoint R)
      hprime hdense hpt (by simpa using hY4) hYprod
  simpa using hpower

/-- A fourth-power-unsafe prime coordinate is an exact certificate that the
face is not triply predecessor-dense at any admissible smooth scale. -/
theorem orientedChargingFace_fourthUnsafe_not_triplyDense
    {R c k Y p : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k))
    (hY4 : Y ^ 4 ≤ squareRootEndpoint R)
    (hYR : Y * R ≤ squareRootEndpoint R)
    (hpt : p ∈ t) (hunsafe : squareRootEndpoint R < p ^ 4) :
    ¬ PredecessorDenseFace 3 Y t := by
  intro hdense
  have hsafe :=
    orientedChargingFace_triplyDense_facePrimeFourth_le_endpoint
      ht hdense hY4 hYR hpt
  omega

/-- Consequently a fourth-power-unsafe coordinate forces the canonical
first-jump alternative: a strictly lower owner above the smooth threshold,
with an already-triply-dense predecessor cube. -/
theorem orientedChargingFace_fourthUnsafe_forces_firstLowerJump
    {R c k Y p : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k))
    (hY4 : Y ^ 4 ≤ squareRootEndpoint R)
    (hYR : Y * R ≤ squareRootEndpoint R)
    (hpt : p ∈ t) (hunsafe : squareRootEndpoint R < p ^ 4) :
    ∃ q ∈ t,
      q < lowWheelCanonicalDowncrossPivot (c, k) ∧
      Y < q ∧
      Y * predecessorPrimeFaceProduct t q < q ^ 3 ∧
        PredecessorDenseFace 3 Y (predecessorPrimeFace t q) := by
  have hnot :=
    orientedChargingFace_fourthUnsafe_not_triplyDense
      ht hY4 hYR hpt hunsafe
  rcases orientedChargingFace_dense_or_firstLowerJump_with_densePredecessor
      (d := 3) (Y := Y) ht with hdense | hjump
  · exact (hnot hdense).elim
  · exact hjump

/-! ## The actual owner fourth-power wall

The Go fourth-power geometry is expressed at the *fresh owner* itself, not at
an arbitrary face prime.  At smooth scale `Y = 1`, every prime coordinate is
large.  If the canonical pivot `q` satisfies `X_R < q^4`, the physical ceiling
forces `primeFaceProduct t < q^3`; therefore adjoining `q` to its complete old
face is not triply predecessor-dense.  Its canonical first multiplicative jump
is either exactly `q` (the terminal owner wall) or occurs at a strictly smaller
face prime. -/

/-- If the fresh canonical owner lies beyond the fourth-power wall, adjoining
it to the old face fails triply predecessor density at smooth scale one. -/
theorem orientedChargingFace_ownerFourthUnsafe_insert_not_triplyDense
    {R c k : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k))
    (hunsafe :
      squareRootEndpoint R <
        (lowWheelCanonicalDowncrossPivot (c, k)) ^ 4) :
    ¬ PredecessorDenseFace 3 1
      (insert (lowWheelCanonicalDowncrossPivot (c, k)) t) := by
  let q := lowWheelCanonicalDowncrossPivot (c, k)
  change ¬ PredecessorDenseFace 3 1 (insert q t)
  rcases mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht with
    ⟨htPow, hx⟩
  have hdown := (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1
  have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hdown
  dsimp only at hgeom
  have hqPrime : q.Prime := by
    simpa [q] using hgeom.1
  have hkPivot := lowWheelCanonicalDowncrossOriented_quotient_eq_pivot hx
  have hk : k = q := by
    simpa [q] using hkPivot
  have hpTop : ∀ p ∈ t, p < q := by
    intro p hpt
    simpa [q] using
      lowWheelCanonicalDowncrossOriented_facePrime_lt_pivot htPow hx hpt
  have hphys := (mem_lowWheelCanonicalDowncrossPart.mp hdown).1
  have hphysical := mem_lowWheelCanonicalPhysicalStateSet.mp hphys
  have hcarrier := hphysical.2.2.2
  rcases hcarrier with ⟨hc1, _hcR, _hhigh, htop⟩
  rw [hk] at htop
  have hQle : primeFaceProduct t ≤ c * primeFaceProduct t := by
    simpa [one_mul] using Nat.mul_le_mul_right (primeFaceProduct t) hc1
  have hQq : primeFaceProduct t * q ≤ squareRootEndpoint R := by
    exact (Nat.mul_le_mul_right q hQle).trans htop
  have hQlt : primeFaceProduct t < q ^ 3 := by
    by_contra hnot
    have hq3Q : q ^ 3 ≤ primeFaceProduct t := Nat.le_of_not_gt hnot
    have hq4Qq : q ^ 4 ≤ primeFaceProduct t * q := by
      calc
        q ^ 4 = q ^ 3 * q := by ring
        _ ≤ primeFaceProduct t * q := Nat.mul_le_mul_right q hq3Q
    have hq4X : q ^ 4 ≤ squareRootEndpoint R := hq4Qq.trans hQq
    have hXq4 : squareRootEndpoint R < q ^ 4 := by
      simpa [q] using hunsafe
    omega
  intro hdense
  have hqCond := hdense q (by simp) hqPrime.one_lt
  rw [predecessorPrimeFaceProduct_insert_top hpTop] at hqCond
  have hq3Q : q ^ 3 ≤ primeFaceProduct t := by
    simpa using hqCond
  omega

/-- **Descending-or-terminal owner classification.**  Beyond the owner
fourth-power wall, the canonical first multiplicative jump on `insert q t` is
either the owner itself, in which case the complete predecessor face `t` is
already triply dense and has product below `q^3`, or a strictly lower face
prime with its own already-dense predecessor cube. -/
theorem orientedChargingFace_ownerFourthUnsafe_firstJump_dichotomy
    {R c k : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k))
    (hunsafe :
      squareRootEndpoint R <
        (lowWheelCanonicalDowncrossPivot (c, k)) ^ 4) :
    (PredecessorDenseFace 3 1 t ∧
      primeFaceProduct t <
        (lowWheelCanonicalDowncrossPivot (c, k)) ^ 3) ∨
      ∃ p ∈ t,
        p < lowWheelCanonicalDowncrossPivot (c, k) ∧
        predecessorPrimeFaceProduct t p < p ^ 3 ∧
          PredecessorDenseFace 3 1 (predecessorPrimeFace t p) := by
  let q := lowWheelCanonicalDowncrossPivot (c, k)
  have hnot : ¬ PredecessorDenseFace 3 1 (insert q t) := by
    simpa [q] using
      orientedChargingFace_ownerFourthUnsafe_insert_not_triplyDense ht hunsafe
  rcases exists_first_predecessorDenseFailure_with_densePredecessor hnot with
    ⟨p, hpins, _h1p, hfail, hpredDense⟩
  rcases mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mp ht with
    ⟨htPow, hx⟩
  have hpTop : ∀ r ∈ t, r < q := by
    intro r hrt
    simpa [q] using
      lowWheelCanonicalDowncrossOriented_facePrime_lt_pivot htPow hx hrt
  rcases Finset.mem_insert.mp hpins with hpq | hpt
  · subst p
    left
    rw [predecessorPrimeFace_insert_top hpTop] at hpredDense
    rw [predecessorPrimeFaceProduct_insert_top hpTop] at hfail
    refine ⟨hpredDense, ?_⟩
    simpa [q] using hfail
  · right
    have hpq : p < q := hpTop p hpt
    rw [predecessorPrimeFaceProduct_insert_of_lt hpq] at hfail
    rw [predecessorPrimeFace_insert_of_lt hpq] at hpredDense
    refine ⟨p, hpt, ?_, ?_, hpredDense⟩
    · simpa [q] using hpq
    · simpa using hfail

end RHLean.Proof