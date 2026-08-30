import Mathlib
import RHLean.Proof.LowWheelOthelloRepeatedInvolution

/-!
# Signed parent split on the lightweight Othello downcross carrier

The nested downcross ledger is flattened to its tagged carrier without losing
multiplicity.  It then splits exactly into unique-parent and repeated-parent
pieces.  Only the unique piece is estimated: every individual weight has norm
at most one and the existing parent charge is injective into `1..R`.

The repeated piece remains signed and is reduced exactly by the opposite
Othello involution from `LowWheelOthelloRepeatedInvolution`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Nested lightweight downcross ledger. -/
def lowWheelOthelloDowncrossLedger (R : ℕ) : ℂ :=
  ∑ t ∈ (primesUpTo R).powerset,
    ∑ x ∈ lowWheelOthelloDowncrossPart R t,
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)

/-- One tagged face fibre. -/
def lowWheelOthelloTaggedDowncrossFiber
    (R : ℕ) (t : Finset ℕ) : Finset LowWheelOthelloTaggedDowncrossState :=
  (lowWheelOthelloDowncrossPart R t).image fun x => (t, x)

/-- Different face fibres are disjoint because the face is retained as a tag. -/
theorem lowWheelOthelloTaggedDowncrossFiber_pairwise
    (R : ℕ) :
    Set.PairwiseDisjoint (↑(primesUpTo R).powerset)
      (lowWheelOthelloTaggedDowncrossFiber R) := by
  intro t _ht u _hu htu
  change Disjoint
    (lowWheelOthelloTaggedDowncrossFiber R t)
    (lowWheelOthelloTaggedDowncrossFiber R u)
  rw [Finset.disjoint_left]
  intro y hyt hyu
  rcases Finset.mem_image.mp hyt with ⟨x, _hx, rfl⟩
  rcases Finset.mem_image.mp hyu with ⟨z, _hz, huz⟩
  have hut : u = t := congrArg Prod.fst huz
  exact htu hut.symm

/-- The tagged carrier is literally the disjoint union of its face fibres. -/
theorem lowWheelOthelloTaggedDowncrossCarrier_eq_biUnion_fibers
    (R : ℕ) :
    lowWheelOthelloTaggedDowncrossCarrier R =
      (primesUpTo R).powerset.biUnion
        (lowWheelOthelloTaggedDowncrossFiber R) := by
  rfl

/-- Flattened tagged signed ledger. -/
def lowWheelOthelloTaggedDowncrossLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelOthelloTaggedDowncrossCarrier R,
    lowWheelOthelloWeight y

/-- Flattening loses neither sign nor multiplicity. -/
theorem lowWheelOthelloDowncrossLedger_eq_tagged
    (R : ℕ) :
    lowWheelOthelloDowncrossLedger R =
      lowWheelOthelloTaggedDowncrossLedger R := by
  unfold lowWheelOthelloDowncrossLedger lowWheelOthelloTaggedDowncrossLedger
  rw [lowWheelOthelloTaggedDowncrossCarrier_eq_biUnion_fibers R]
  rw [Finset.sum_biUnion (lowWheelOthelloTaggedDowncrossFiber_pairwise R)]
  apply Finset.sum_congr rfl
  intro t _ht
  change
    (∑ x ∈ lowWheelOthelloDowncrossPart R t,
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
    ∑ y ∈ lowWheelOthelloTaggedDowncrossFiber R t,
      lowWheelOthelloWeight y
  unfold lowWheelOthelloTaggedDowncrossFiber
  rw [Finset.sum_image]
  · rfl
  · intro a _ha b _hb hab
    exact congrArg Prod.snd hab

/-- Signed unique-parent ledger. -/
def lowWheelOthelloUniqueLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelOthelloDowncrossUniqueParentPart R,
    lowWheelOthelloWeight y

/-- The tagged downcross ledger splits exactly into unique and repeated parent
masses. -/
theorem lowWheelOthelloTaggedDowncrossLedger_eq_unique_add_repeated
    (R : ℕ) :
    lowWheelOthelloTaggedDowncrossLedger R =
      lowWheelOthelloUniqueLedger R + lowWheelOthelloRepeatedLedger R := by
  unfold lowWheelOthelloTaggedDowncrossLedger lowWheelOthelloUniqueLedger
    lowWheelOthelloRepeatedLedger
  rw [lowWheelOthelloTaggedDowncrossCarrier_eq_unique_union_repeated R]
  rw [Finset.sum_union (lowWheelOthelloDowncrossUnique_disjoint_repeated R)]

/-- Every tagged downcross weight has norm at most one. -/
theorem norm_lowWheelOthelloWeight_le_one
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (_hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R) :
    ‖lowWheelOthelloWeight y‖ ≤ 1 := by
  unfold lowWheelOthelloWeight canonicalMoebiusWeight
  rw [norm_mul, Complex.norm_intCast]
  have hface : ‖(booleanCubeSign y.1 : ℂ)‖ = 1 := by
    simp [booleanCubeSign]
  rw [hface, mul_one]
  have hmu : |μ y.2.1| ≤ (1 : ℤ) := by
    rcases ArithmeticFunction.moebius_eq_or y.2.1 with h | h | h <;> simp [h]
  exact_mod_cast hmu

/-- The signed unique-parent mass is already root scale. -/
theorem norm_lowWheelOthelloUniqueLedger_le_root
    (R : ℕ) :
    ‖lowWheelOthelloUniqueLedger R‖ ≤ (R : ℝ) := by
  unfold lowWheelOthelloUniqueLedger
  calc
    ‖∑ y ∈ lowWheelOthelloDowncrossUniqueParentPart R,
        lowWheelOthelloWeight y‖ ≤
      ∑ y ∈ lowWheelOthelloDowncrossUniqueParentPart R,
        ‖lowWheelOthelloWeight y‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ _y ∈ lowWheelOthelloDowncrossUniqueParentPart R, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro y hy
      exact norm_lowWheelOthelloWeight_le_one
        (Finset.mem_filter.mp hy).1
    _ = ((lowWheelOthelloDowncrossUniqueParentPart R).card : ℝ) := by simp
    _ ≤ (R : ℝ) := by
      exact_mod_cast lowWheelOthelloDowncrossUniqueParentPart_card_le_root R

/-- **Exact signed Othello reduction.**  The complete downcross ledger is a
root-bounded unique mass plus the frozen repeated frontier. -/
theorem lowWheelOthelloDowncrossLedger_eq_unique_add_frozen
    (R : ℕ) :
    lowWheelOthelloDowncrossLedger R =
      lowWheelOthelloUniqueLedger R +
        ∑ y ∈ lowWheelOthelloRepeatedFrozenPart R,
          lowWheelOthelloWeight y := by
  rw [lowWheelOthelloDowncrossLedger_eq_tagged,
    lowWheelOthelloTaggedDowncrossLedger_eq_unique_add_repeated,
    lowWheelOthelloRepeatedLedger_eq_frozen]

end RHLean.Proof
