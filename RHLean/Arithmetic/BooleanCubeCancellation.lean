import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

open scoped BigOperators

namespace RHLean.Arithmetic

/-- Alternating parity sign attached to a Boolean-cube vertex. -/
def booleanCubeSign {α : Type*} (t : Finset α) : ℤ :=
  (-1 : ℤ) ^ t.card

/-- Alternating signed mass of the complete Boolean cube on `s`. -/
def booleanCubeAlternatingSum {α : Type*} (s : Finset α) : ℤ :=
  ∑ t ∈ s.powerset, booleanCubeSign t

/-- The zero-dimensional Boolean cube has signed mass one. -/
theorem booleanCubeAlternatingSum_empty {α : Type*} :
    booleanCubeAlternatingSum (∅ : Finset α) = 1 := by
  simp [booleanCubeAlternatingSum, booleanCubeSign]

/-- Adding a new cube coordinate negates the contribution of every old vertex. -/
theorem booleanCube_inserted_half_eq_neg
    {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} (ha : a ∉ s) :
    (∑ t ∈ s.powerset, booleanCubeSign (insert a t)) =
      -∑ t ∈ s.powerset, booleanCubeSign t := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hat : a ∉ t :=
    Finset.notMem_of_mem_powerset_of_notMem ht ha
  simp [booleanCubeSign, Finset.card_insert_of_notMem, hat, pow_succ]

/-- Every positive-dimensional complete Boolean cube has exact alternating cancellation. -/
theorem booleanCubeAlternatingSum_eq_zero
    {α : Type*} [DecidableEq α]
    {s : Finset α} (hs : s.Nonempty) :
    booleanCubeAlternatingSum s = 0 := by
  rcases hs with ⟨a, ha⟩
  have hdecomp : s = insert a (s.erase a) := by
    exact (Finset.insert_erase ha).symm
  rw [hdecomp]
  unfold booleanCubeAlternatingSum
  rw [Finset.sum_powerset_insert (Finset.notMem_erase a s)]
  rw [booleanCube_inserted_half_eq_neg (Finset.notMem_erase a s)]
  simp

/-- Complete-cube cancellation written directly as a parity sum. -/
theorem sum_neg_one_pow_card_powerset_eq_zero
    {α : Type*} [DecidableEq α]
    {s : Finset α} (hs : s.Nonempty) :
    (∑ t ∈ s.powerset, (-1 : ℤ) ^ t.card) = 0 := by
  exact booleanCubeAlternatingSum_eq_zero hs

end RHLean.Arithmetic
