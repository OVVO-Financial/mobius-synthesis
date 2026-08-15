import Mathlib
import RHLean.Arithmetic.TruncatedBooleanCube

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-!
# Exact Boolean-coordinate finite differences

A sign-reversing Boolean coordinate does not require the support predicate to be
downward closed. Pairing the two halves of the cube at one pivot `a` writes the
complete alternating mass as the first discrete difference of the support
indicator. Pairing further independent pivots gives higher finite Walsh
derivatives.

For two pivots the stencil is

```text
I(u) - I(a+u) - I(b+u) + I(a+b+u).
```

For three pivots it is the corresponding eight-point third difference. This is
purely algebraic and makes no Markov, uniformity, or probabilistic assumption.
-/

/-- Integer indicator of an arbitrary Boolean-face predicate. -/
noncomputable def booleanPredicateIndicator
    {α : Type*} (P : Finset α → Prop) (u : Finset α) : ℤ := by
  classical
  exact if P u then 1 else 0

/-- First discrete difference in one Boolean coordinate. -/
def booleanPivotDifference
    {α : Type*} [DecidableEq α]
    (a : α) (P : Finset α → Prop) (u : Finset α) : ℤ :=
  booleanPredicateIndicator P u -
    booleanPredicateIndicator P (insert a u)

/-- Four-point second discrete difference in two Boolean coordinates. -/
def booleanTwoPivotDifference
    {α : Type*} [DecidableEq α]
    (a b : α) (P : Finset α → Prop) (u : Finset α) : ℤ :=
  booleanPredicateIndicator P u -
    booleanPredicateIndicator P (insert a u) -
    booleanPredicateIndicator P (insert b u) +
    booleanPredicateIndicator P (insert a (insert b u))

/-- Eight-point third discrete difference in three Boolean coordinates. It is
written recursively as the difference of the two-pivot stencil before and after
inserting the third pivot. -/
def booleanThreePivotDifference
    {α : Type*} [DecidableEq α]
    (a b c : α) (P : Finset α → Prop) (u : Finset α) : ℤ :=
  booleanTwoPivotDifference a b P u -
    booleanTwoPivotDifference a b P (insert c u)

/-- **One-coordinate exact finite difference.** The alternating mass of an
arbitrary support is the signed first difference across any selected cube
coordinate. -/
theorem truncatedCubeAlternatingSum_eq_pivotDifference
    {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} (P : Finset α → Prop)
    (ha : a ∈ s) :
    truncatedCubeAlternatingSum s P =
      ∑ u ∈ (s.erase a).powerset,
        booleanCubeSign u * booleanPivotDifference a P u := by
  classical
  have hdecomp : s = insert a (s.erase a) :=
    (Finset.insert_erase ha).symm
  unfold truncatedCubeAlternatingSum
  conv_lhs => rw [hdecomp]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase a s)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hau : a ∉ u :=
    Finset.notMem_of_mem_powerset_of_notMem
      hu (Finset.notMem_erase a s)
  have hsign :
      booleanCubeSign (insert a u) = -booleanCubeSign u := by
    simp [booleanCubeSign, Finset.card_insert_of_notMem, hau, pow_succ]
  unfold booleanPivotDifference booleanPredicateIndicator
  rw [hsign]
  by_cases h0 : P u <;> by_cases h1 : P (insert a u) <;>
    simp [h0, h1]

/-- **Two-coordinate exact finite difference.** Two independent sign toggles
reduce the arbitrary Boolean-supported alternating mass to the four-point
second derivative on faces omitting both pivots. -/
theorem truncatedCubeAlternatingSum_eq_twoPivotDifference
    {α : Type*} [DecidableEq α]
    {s : Finset α} {a b : α} (P : Finset α → Prop)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    truncatedCubeAlternatingSum s P =
      ∑ u ∈ ((s.erase a).erase b).powerset,
        booleanCubeSign u * booleanTwoPivotDifference a b P u := by
  classical
  rw [truncatedCubeAlternatingSum_eq_pivotDifference P ha]
  have hba : b ∈ s.erase a := by
    exact Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have hdecomp : s.erase a = insert b ((s.erase a).erase b) :=
    (Finset.insert_erase hba).symm
  conv_lhs => rw [hdecomp]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase b (s.erase a))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hbu : b ∉ u :=
    Finset.notMem_of_mem_powerset_of_notMem
      hu (Finset.notMem_erase b (s.erase a))
  have hsign :
      booleanCubeSign (insert b u) = -booleanCubeSign u := by
    simp [booleanCubeSign, Finset.card_insert_of_notMem, hbu, pow_succ]
  rw [hsign]
  unfold booleanPivotDifference booleanTwoPivotDifference
  ring

/-- **Three-coordinate exact finite difference.** Three distinct sign toggles
reduce an arbitrary Boolean-supported alternating mass to one eight-state
stencil over faces omitting all three pivots. -/
theorem truncatedCubeAlternatingSum_eq_threePivotDifference
    {α : Type*} [DecidableEq α]
    {s : Finset α} {a b c : α} (P : Finset α → Prop)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    truncatedCubeAlternatingSum s P =
      ∑ u ∈ (((s.erase a).erase b).erase c).powerset,
        booleanCubeSign u * booleanThreePivotDifference a b c P u := by
  classical
  rw [truncatedCubeAlternatingSum_eq_twoPivotDifference P ha hb hab]
  have hca : c ≠ a := Ne.symm hac
  have hcb : c ≠ b := Ne.symm hbc
  have hcT : c ∈ (s.erase a).erase b := by
    exact Finset.mem_erase.mpr
      ⟨hcb, Finset.mem_erase.mpr ⟨hca, hc⟩⟩
  have hdecomp :
      (s.erase a).erase b =
        insert c (((s.erase a).erase b).erase c) :=
    (Finset.insert_erase hcT).symm
  conv_lhs => rw [hdecomp]
  rw [Finset.sum_powerset_insert
    (Finset.notMem_erase c ((s.erase a).erase b))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hcu : c ∉ u :=
    Finset.notMem_of_mem_powerset_of_notMem hu
      (Finset.notMem_erase c ((s.erase a).erase b))
  have hsign :
      booleanCubeSign (insert c u) = -booleanCubeSign u := by
    simp [booleanCubeSign, Finset.card_insert_of_notMem, hcu, pow_succ]
  rw [hsign]
  unfold booleanThreePivotDifference
  ring

/-- The two-pivot difference is symmetric in the selected coordinates. -/
theorem booleanTwoPivotDifference_comm
    {α : Type*} [DecidableEq α]
    (a b : α) (P : Finset α → Prop) (u : Finset α) :
    booleanTwoPivotDifference a b P u =
      booleanTwoPivotDifference b a P u := by
  unfold booleanTwoPivotDifference
  have hins : insert a (insert b u) = insert b (insert a u) := by
    exact Finset.insert_comm a b u
  rw [hins]
  ring

end RHLean.Arithmetic
