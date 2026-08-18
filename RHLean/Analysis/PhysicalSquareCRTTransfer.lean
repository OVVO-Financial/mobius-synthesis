import Mathlib
import RHLean.Analysis.FinitePrimeTMixing
import RHLean.Analysis.ThreeSlotMertensDegreeOneProjection

/-!
# Physical square-clock transfer to complete finite-prime CRT periods

This module isolates the geometric transfer that is needed before the exact
finite-prime `T`-sector law can be used on the physical square clock.

The physical object is the actual Mobius transition population: adjacent
three-slot cells lying wholly inside one square block, with both source and
destination in the eight-state zero-free sector.  A finite set of prime-square
coordinates gives a CRT period.  We retain exactly those physical `T` cells
whose entire aligned CRT period lies inside the square-block transition window.
The remaining cells are the square-clock boundary defect.

No probabilistic independence statement is asserted here.  In particular,
`crtT` below is still the actual physical Mobius observable restricted to
complete CRT periods.  The next arithmetic theorem must identify that complete-
period contribution with the finite-prime CRT law, using the existing
large-prime transport bridge for the rough coordinates.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Explicit decidability for the zero-free three-slot predicate.  As with the
finite-prime predicates, instance synthesis does not unfold the plain `def`
through a `Finset.filter` automatically. -/
instance physicalSquareIsThreeSlotNonzeroState_decidable (i : Fin 27) :
    Decidable (IsThreeSlotNonzeroState i) :=
  inferInstanceAs
    (Decidable (chiA i ≠ 0 ∧ chiB i ≠ 0 ∧ chiC i ≠ 0))

/-- Exact physical zero-free transition population in the square block
`[R^2,(R+1)^2)`.  Both endpoints of the adjacent transition are required to lie
in the eight-state sign sector. -/
def physicalSquareTTransitionCells (R : ℕ) : Finset ℕ :=
  (threeSlotSquareBlockTransitionCells R).filter fun k =>
    IsThreeSlotNonzeroState (threeSlotState k) ∧
      IsThreeSlotNonzeroState (threeSlotState (k + 1))

/-- Degree-one physical observable on the source cell of a `T` transition. -/
def physicalTCellValue (k : ℕ) : ℤ :=
  threeSlotDegreeOneValue (threeSlotState k)

/-- Actual signed physical `T` mass in one square block. -/
def physicalT (R : ℕ) : ℤ :=
  ∑ k ∈ physicalSquareTTransitionCells R, physicalTCellValue k

/-- Product of the selected prime-square local periods.  For a genuine finite
set of distinct primes this is the usual combined CRT modulus.  `max 1` keeps
the geometric definitions total even before primality hypotheses are supplied. -/
def finitePrimeCRTPeriod (P : Finset ℕ) : ℕ :=
  max 1 (∏ p ∈ P, p ^ 2)

/-- The exact finite-prime CRT coordinate vector of a physical cell index.
Each selected prime records the residue of `k` modulo its square. -/
def physicalTCRTProjection (P : Finset ℕ) (k : ℕ) :
    (p : {p // p ∈ P}) → ZMod (p.1 ^ 2) :=
  fun p => (k : ZMod (p.1 ^ 2))

/-- The aligned complete CRT period containing `k`. -/
def finitePrimeCRTOrbit (P : Finset ℕ) (k : ℕ) : Finset ℕ :=
  let M := finitePrimeCRTPeriod P
  Finset.Ico ((k / M) * M) ((k / M + 1) * M)

/-- Physical `T` cells whose entire aligned CRT period remains inside the
geometric square-clock transition window.  These are the cells on which a
complete-period CRT count can be applied without endpoint truncation. -/
def physicalSquareCompleteCRTCells (P : Finset ℕ) (R : ℕ) : Finset ℕ :=
  (physicalSquareTTransitionCells R).filter fun k =>
    finitePrimeCRTOrbit P k ⊆ threeSlotSquareBlockTransitionCells R

/-- Physical `T` cells belonging to incomplete CRT periods at the square-clock
boundary. -/
def physicalSquareCRTBoundaryCells (P : Finset ℕ) (R : ℕ) : Finset ℕ :=
  physicalSquareTTransitionCells R \ physicalSquareCompleteCRTCells P R

/-- Every complete-period cell is an actual physical zero-free transition. -/
theorem physicalSquareCompleteCRTCells_subset
    (P : Finset ℕ) (R : ℕ) :
    physicalSquareCompleteCRTCells P R ⊆ physicalSquareTTransitionCells R := by
  exact Finset.filter_subset _ _

/-- Membership in the complete core records exactly the promised geometric
fact: the whole aligned CRT period is inside the physical square clock. -/
theorem finitePrimeCRTOrbit_subset_squareBlock_of_mem_complete
    {P : Finset ℕ} {R k : ℕ}
    (hk : k ∈ physicalSquareCompleteCRTCells P R) :
    finitePrimeCRTOrbit P k ⊆ threeSlotSquareBlockTransitionCells R := by
  exact (Finset.mem_filter.mp hk).2

/-- Actual physical `T` mass carried by complete CRT periods.  This is not yet
replaced by an abstract kernel or probability law. -/
def crtT (P : Finset ℕ) (R : ℕ) : ℤ :=
  ∑ k ∈ physicalSquareCompleteCRTCells P R, physicalTCellValue k

/-- Exact signed square-clock boundary contribution. -/
def boundaryT (P : Finset ℕ) (R : ℕ) : ℤ :=
  ∑ k ∈ physicalSquareCRTBoundaryCells P R, physicalTCellValue k

/-- Exact physical-to-CRT-period decomposition.  The content is geometric: the
physical zero-free population is partitioned into cells lying on complete CRT
periods and the incomplete square-clock boundary. -/
theorem physicalTransport_is_crtTransport_add_boundary
    (P : Finset ℕ) (R : ℕ) :
    physicalT R = crtT P R + boundaryT P R := by
  classical
  have hsub :
      physicalSquareCompleteCRTCells P R ⊆ physicalSquareTTransitionCells R :=
    physicalSquareCompleteCRTCells_subset P R
  unfold physicalT crtT boundaryT physicalSquareCRTBoundaryCells
  rw [← Finset.sum_sdiff hsub]
  ring

end RHLean.Analysis
