import Mathlib
import RHLean.Proof.LowWheelCanonicalDowncrossParentFibers

/-!
# Signed canonical downcross parent split

The complete square-endpoint defect is already the single canonical tagged
downcross carrier.  This file flattens the nested face ledger without losing
multiplicity, then splits that exact signed ledger into unique-parent and
repeated-parent pieces.

The unique-parent piece costs at most one unit per root because the existing
parent map is injective into `1..R`.  No estimate is made on the repeated piece;
it is retained with its sign for the opposite-coordinate Othello reduction.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- One tagged face fibre of the canonical downcross carrier. -/
def lowWheelCanonicalTaggedDowncrossFiber
    (R : ℕ) (t : Finset ℕ) : Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalDowncrossPart R t).image fun x => (t, x)

/-- Different Boolean faces give disjoint tagged downcross fibres. -/
theorem lowWheelCanonicalTaggedDowncrossFiber_pairwise
    (R : ℕ) :
    Set.PairwiseDisjoint (↑(primesUpTo R).powerset)
      (lowWheelCanonicalTaggedDowncrossFiber R) := by
  intro t _ht u _hu htu
  change Disjoint
    (lowWheelCanonicalTaggedDowncrossFiber R t)
    (lowWheelCanonicalTaggedDowncrossFiber R u)
  rw [Finset.disjoint_left]
  intro y hyt hyu
  rcases Finset.mem_image.mp hyt with ⟨x, _hx, rfl⟩
  rcases Finset.mem_image.mp hyu with ⟨z, _hz, huz⟩
  have hut : u = t := congrArg Prod.fst huz
  exact htu hut.symm

/-- Native signed weight of one tagged canonical downcross occurrence. -/
def lowWheelTaggedDowncrossWeight
    (y : LowWheelTaggedDowncrossState) : ℂ :=
  canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)

/-- Flattened signed canonical downcross ledger. -/
def lowWheelCanonicalTaggedDowncrossLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalTaggedDowncrossCarrier R,
    lowWheelTaggedDowncrossWeight y

/-- The flattened tagged carrier is definitionally the disjoint union of its
face fibres. -/
theorem lowWheelCanonicalTaggedDowncrossCarrier_eq_biUnion_fibers
    (R : ℕ) :
    lowWheelCanonicalTaggedDowncrossCarrier R =
      (primesUpTo R).powerset.biUnion
        (lowWheelCanonicalTaggedDowncrossFiber R) := by
  rfl

/-- Flattening the canonical downcross ledger loses neither sign nor
multiplicity. -/
theorem lowWheelCanonicalDowncrossLedger_eq_tagged
    (R : ℕ) :
    lowWheelCanonicalDowncrossLedger R =
      lowWheelCanonicalTaggedDowncrossLedger R := by
  unfold lowWheelCanonicalTaggedDowncrossLedger
  rw [lowWheelCanonicalTaggedDowncrossCarrier_eq_biUnion_fibers]
  rw [Finset.sum_biUnion (lowWheelCanonicalTaggedDowncrossFiber_pairwise R)]
  unfold lowWheelCanonicalDowncrossLedger
    lowWheelCanonicalTaggedDowncrossFiber
  apply Finset.sum_congr rfl
  intro t _ht
  symm
  apply Finset.sum_image
  intro a _ha b _hb hab
  exact congrArg Prod.snd hab

/-- Signed unique-parent part of the canonical downcross ledger. -/
def lowWheelCanonicalDowncrossUniqueParentLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalDowncrossUniqueParentPart R,
    lowWheelTaggedDowncrossWeight y

/-- Signed repeated-parent part of the canonical downcross ledger. -/
def lowWheelCanonicalDowncrossRepeatedParentLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalDowncrossRepeatedParentPart R,
    lowWheelTaggedDowncrossWeight y

/-- Exact signed parent split of the entire canonical downcross residual. -/
theorem lowWheelCanonicalTaggedDowncrossLedger_eq_unique_add_repeated
    (R : ℕ) :
    lowWheelCanonicalTaggedDowncrossLedger R =
      lowWheelCanonicalDowncrossUniqueParentLedger R +
        lowWheelCanonicalDowncrossRepeatedParentLedger R := by
  unfold lowWheelCanonicalTaggedDowncrossLedger
    lowWheelCanonicalDowncrossUniqueParentLedger
    lowWheelCanonicalDowncrossRepeatedParentLedger
  rw [lowWheelCanonicalTaggedDowncrossCarrier_eq_unique_union_repeated R]
  rw [Finset.sum_union (lowWheelCanonicalDowncrossUnique_disjoint_repeated R)]

/-- Every tagged downcross occurrence has weight norm at most one. -/
theorem norm_lowWheelTaggedDowncrossWeight_le_one
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (_hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R) :
    ‖lowWheelTaggedDowncrossWeight y‖ ≤ 1 := by
  unfold lowWheelTaggedDowncrossWeight canonicalMoebiusWeight
  rw [norm_mul, Complex.norm_intCast]
  have hface : ‖(booleanCubeSign y.1 : ℂ)‖ = 1 := by
    simp [booleanCubeSign]
  rw [hface, mul_one]
  have hmu : |μ y.2.1| ≤ (1 : ℤ) := by
    rcases ArithmeticFunction.moebius_eq_or y.2.1 with h | h | h <;> simp [h]
  exact_mod_cast hmu

/-- The unique-parent signed downcross mass is already root scale. -/
theorem norm_lowWheelCanonicalDowncrossUniqueParentLedger_le_root
    (R : ℕ) :
    ‖lowWheelCanonicalDowncrossUniqueParentLedger R‖ ≤ (R : ℝ) := by
  unfold lowWheelCanonicalDowncrossUniqueParentLedger
  calc
    ‖∑ y ∈ lowWheelCanonicalDowncrossUniqueParentPart R,
        lowWheelTaggedDowncrossWeight y‖ ≤
      ∑ y ∈ lowWheelCanonicalDowncrossUniqueParentPart R,
        ‖lowWheelTaggedDowncrossWeight y‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ _y ∈ lowWheelCanonicalDowncrossUniqueParentPart R, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro y hy
      exact norm_lowWheelTaggedDowncrossWeight_le_one
        (Finset.mem_filter.mp hy).1
    _ = ((lowWheelCanonicalDowncrossUniqueParentPart R).card : ℝ) := by simp
    _ ≤ (R : ℝ) := by
      exact_mod_cast lowWheelCanonicalDowncrossUniqueParentPart_card_le_root R

/-- The original nested canonical downcross ledger is the root-bounded unique
mass plus the still-signed repeated-parent obstruction. -/
theorem lowWheelCanonicalDowncrossLedger_eq_unique_add_repeated
    (R : ℕ) :
    lowWheelCanonicalDowncrossLedger R =
      lowWheelCanonicalDowncrossUniqueParentLedger R +
        lowWheelCanonicalDowncrossRepeatedParentLedger R := by
  rw [lowWheelCanonicalDowncrossLedger_eq_tagged,
    lowWheelCanonicalTaggedDowncrossLedger_eq_unique_add_repeated]

end RHLean.Proof
