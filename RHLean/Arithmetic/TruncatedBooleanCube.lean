import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import RHLean.Arithmetic.BooleanCubeCancellation

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- A support predicate on finite faces is downward closed when every admitted
face brings all of its subfaces with it.  Product cutoffs have exactly this
shape: an admitted prime product always contains its lower-dimensional parents. -/
def CubeDownwardClosed {α : Type*} (admissible : Finset α → Prop) : Prop :=
  ∀ u v : Finset α, u ⊆ v → admissible v → admissible u

/-- Alternating mass of the admitted part of a Boolean cube.  Writing the sum
on the complete powerset and inserting an indicator keeps every rejected face
explicit rather than silently changing the ambient cube. -/
def truncatedCubeAlternatingSum {α : Type*} [DecidableEq α]
    (s : Finset α) (admissible : Finset α → Prop) : ℤ := by
  classical
  exact ∑ t ∈ s.powerset, if admissible t then booleanCubeSign t else 0

/-- At coordinate `a`, the first-failure boundary consists of admitted parent
faces whose `a`-child is rejected by the truncated support. -/
def firstFailureBoundary {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α) (admissible : Finset α → Prop) : Finset (Finset α) := by
  classical
  exact (s.erase a).powerset.filter fun t =>
    admissible t ∧ ¬ admissible (insert a t)

/-- Alternating mass carried by the explicit first-failure boundary. -/
def firstFailureBoundaryAlternatingSum {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α) (admissible : Finset α → Prop) : ℤ :=
  ∑ t ∈ firstFailureBoundary s a admissible, booleanCubeSign t

@[simp] theorem mem_firstFailureBoundary
    {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} {admissible : Finset α → Prop}
    {t : Finset α} :
    t ∈ firstFailureBoundary s a admissible ↔
      t ⊆ s.erase a ∧ admissible t ∧ ¬ admissible (insert a t) := by
  classical
  simp [firstFailureBoundary]

/-- Exact one-coordinate truncated-cube decomposition.

Every admitted `a`-child has an admitted parent by downward closure, and the
parent/child alternating signs cancel.  The entire truncated cube therefore
reduces exactly to parents whose extension by `a` is the first failed face.
No cardinality estimate and no cancellation assumption is used. -/
theorem truncatedCubeAlternatingSum_eq_firstFailureBoundary
    {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} {admissible : Finset α → Prop}
    (ha : a ∈ s)
    (hdown : CubeDownwardClosed admissible) :
    truncatedCubeAlternatingSum s admissible =
      firstFailureBoundaryAlternatingSum s a admissible := by
  classical
  have hdecomp : s = insert a (s.erase a) := by
    exact (Finset.insert_erase ha).symm
  unfold truncatedCubeAlternatingSum firstFailureBoundaryAlternatingSum
    firstFailureBoundary
  calc
    (∑ t ∈ s.powerset, if admissible t then booleanCubeSign t else 0) =
        ∑ t ∈ (insert a (s.erase a)).powerset,
          if admissible t then booleanCubeSign t else 0 := by
      rw [← hdecomp]
    _ =
        (∑ t ∈ (s.erase a).powerset,
          if admissible t then booleanCubeSign t else 0) +
        ∑ t ∈ (s.erase a).powerset,
          if admissible (insert a t) then
            booleanCubeSign (insert a t) else 0 := by
      rw [Finset.sum_powerset_insert (Finset.notMem_erase a s)]
    _ =
        ∑ t ∈ (s.erase a).powerset,
          ((if admissible t then booleanCubeSign t else 0) +
            if admissible (insert a t) then
              booleanCubeSign (insert a t) else 0) := by
      rw [Finset.sum_add_distrib]
    _ =
        ∑ t ∈ (s.erase a).powerset,
          if admissible t ∧ ¬ admissible (insert a t) then
            booleanCubeSign t else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      have hat : a ∉ t :=
        Finset.notMem_of_mem_powerset_of_notMem ht (Finset.notMem_erase a s)
      by_cases hchild : admissible (insert a t)
      · have hparent : admissible t :=
          hdown t (insert a t) (Finset.subset_insert a t) hchild
        simp [hchild, hparent, booleanCubeSign,
          Finset.card_insert_of_notMem, hat, pow_succ]
      · by_cases hparent : admissible t
        · simp [hchild, hparent]
        · simp [hchild, hparent]
    _ =
        ∑ t ∈ (s.erase a).powerset.filter
          (fun t => admissible t ∧ ¬ admissible (insert a t)),
          booleanCubeSign t := by
      rw [Finset.sum_filter]

/-- If every admitted parent extends across coordinate `a`, then the truncated
cube is complete in that coordinate and its alternating mass is exactly zero. -/
theorem truncatedCubeAlternatingSum_eq_zero_of_no_firstFailure
    {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} {admissible : Finset α → Prop}
    (ha : a ∈ s)
    (hdown : CubeDownwardClosed admissible)
    (hcomplete : ∀ t ∈ (s.erase a).powerset,
      admissible t → admissible (insert a t)) :
    truncatedCubeAlternatingSum s admissible = 0 := by
  classical
  rw [truncatedCubeAlternatingSum_eq_firstFailureBoundary ha hdown]
  unfold firstFailureBoundaryAlternatingSum firstFailureBoundary
  apply Finset.sum_eq_zero
  intro t ht
  have hpow : t ∈ (s.erase a).powerset := (Finset.mem_filter.mp ht).1
  have hparent : admissible t := (Finset.mem_filter.mp ht).2.1
  have hnotChild : ¬ admissible (insert a t) :=
    (Finset.mem_filter.mp ht).2.2
  exact (hnotChild (hcomplete t hpow hparent)).elim

/-- Every surviving first-failure face is genuinely admitted, omits the pivot,
and has a rejected pivot extension. -/
theorem firstFailureBoundary_spec
    {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} {admissible : Finset α → Prop}
    {t : Finset α}
    (ht : t ∈ firstFailureBoundary s a admissible) :
    admissible t ∧ a ∉ t ∧ ¬ admissible (insert a t) := by
  classical
  have hmem := mem_firstFailureBoundary.mp ht
  refine ⟨hmem.2.1, ?_, hmem.2.2⟩
  exact Finset.notMem_of_mem_powerset_of_notMem
    (Finset.mem_powerset.mpr hmem.1) (Finset.notMem_erase a s)

end RHLean.Arithmetic
