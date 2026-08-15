import Mathlib
import RHLean.Arithmetic.TruncatedBooleanCube

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-!
# Second-coordinate cancellation on a first-failure frontier

A single Boolean coordinate collapses a downward-closed truncated cube to its
first-failure frontier.  That frontier is no longer downward closed, so a second
coordinate cannot be handled by simply reapplying the one-coordinate theorem.
Nevertheless its alternating mass still has an exact two-corner decomposition.

Let `a` be the first pivot and `b` a distinct second pivot.  After pairing the
`b`-free and `b`-present faces inside the `a` first-failure frontier, every
matched pair cancels.  Only two kinds of `b`-free parent can survive:

* both single insertions fail: `A u`, `not A(a+u)`, `not A(b+u)`;
* both single insertions succeed but the double insertion fails:
  `A u`, `A(a+u)`, `A(b+u)`, `not A(a+b+u)`.

The second corner enters with the opposite sign because it is represented by
the `b`-present member of the pair.  This is a finite exact identity; no
cardinality estimate or probabilistic assumption is used.
-/

/-- Exact second-toggle decomposition of one first-failure alternating sum. -/
theorem firstFailureBoundaryAlternatingSum_eq_secondToggleCorners
    {α : Type*} [DecidableEq α]
    {s : Finset α} {a b : α} {admissible : Finset α → Prop}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hdown : CubeDownwardClosed admissible) :
    firstFailureBoundaryAlternatingSum s a admissible =
      (∑ u ∈ ((s.erase a).erase b).powerset,
        if admissible u ∧
            ¬ admissible (insert a u) ∧
            ¬ admissible (insert b u) then
          booleanCubeSign u
        else 0) -
      ∑ u ∈ ((s.erase a).erase b).powerset,
        if admissible u ∧
            admissible (insert a u) ∧
            admissible (insert b u) ∧
            ¬ admissible (insert a (insert b u)) then
          booleanCubeSign u
        else 0 := by
  classical
  have hba : b ∈ s.erase a := by
    exact Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have hdecomp : s.erase a = insert b ((s.erase a).erase b) := by
    exact (Finset.insert_erase hba).symm
  unfold firstFailureBoundaryAlternatingSum firstFailureBoundary
  conv_lhs => rw [Finset.sum_filter]
  conv_lhs => rw [hdecomp]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase b (s.erase a))]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ u ∈ ((s.erase a).erase b).powerset,
        ((if admissible u ∧ ¬ admissible (insert a u) then
            booleanCubeSign u else 0) +
          (if admissible (insert b u) ∧
              ¬ admissible (insert a (insert b u)) then
            booleanCubeSign (insert b u) else 0))) =
      ∑ u ∈ ((s.erase a).erase b).powerset,
        ((if admissible u ∧
              ¬ admissible (insert a u) ∧
              ¬ admissible (insert b u) then
            booleanCubeSign u
          else 0) -
        (if admissible u ∧
              admissible (insert a u) ∧
              admissible (insert b u) ∧
              ¬ admissible (insert a (insert b u)) then
            booleanCubeSign u
          else 0)) := by
        apply Finset.sum_congr rfl
        intro u hu
        have hbu : b ∉ u :=
          Finset.notMem_of_mem_powerset_of_notMem
            hu (Finset.notMem_erase b (s.erase a))
        have hau : a ∉ u := by
          have husub := Finset.mem_powerset.mp hu
          have hua : u ⊆ s.erase a :=
            husub.trans (Finset.erase_subset b (s.erase a))
          exact fun hmem => (Finset.notMem_erase a s) (hua hmem)
        have hsign :
            booleanCubeSign (insert b u) = -booleanCubeSign u := by
          simp [booleanCubeSign, Finset.card_insert_of_notMem, hbu, pow_succ]
        have h_b_to_base :
            admissible (insert b u) → admissible u := by
          intro h
          exact hdown u (insert b u) (Finset.subset_insert b u) h
        have h_a_to_base :
            admissible (insert a u) → admissible u := by
          intro h
          exact hdown u (insert a u) (Finset.subset_insert a u) h
        have h_ab_to_b :
            admissible (insert a (insert b u)) →
              admissible (insert b u) := by
          intro h
          exact hdown (insert b u) (insert a (insert b u))
            (Finset.subset_insert a (insert b u)) h
        have h_ab_to_a :
            admissible (insert a (insert b u)) →
              admissible (insert a u) := by
          intro h
          apply hdown (insert a u) (insert a (insert b u))
          · intro x hx
            simp only [Finset.mem_insert] at hx ⊢
            rcases hx with rfl | hx
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hx)
          · exact h
        rw [hsign]
        by_cases h0 : admissible u
        · by_cases ha1 : admissible (insert a u)
          · by_cases hb1 : admissible (insert b u)
            · by_cases hab1 : admissible (insert a (insert b u))
              · simp [h0, ha1, hb1, hab1]
              · simp [h0, ha1, hb1, hab1]
            · have hab1 : ¬ admissible (insert a (insert b u)) := by
                intro h
                exact hb1 (h_ab_to_b h)
              simp [h0, ha1, hb1, hab1]
          · by_cases hb1 : admissible (insert b u)
            · have hab1 : ¬ admissible (insert a (insert b u)) := by
                intro h
                exact ha1 (h_ab_to_a h)
              simp [h0, ha1, hb1, hab1]
            · have hab1 : ¬ admissible (insert a (insert b u)) := by
                intro h
                exact hb1 (h_ab_to_b h)
              simp [h0, ha1, hb1, hab1]
        · have ha1 : ¬ admissible (insert a u) := by
            intro h
            exact h0 (h_a_to_base h)
          have hb1 : ¬ admissible (insert b u) := by
            intro h
            exact h0 (h_b_to_base h)
          have hab1 : ¬ admissible (insert a (insert b u)) := by
            intro h
            exact hb1 (h_ab_to_b h)
          simp [h0, ha1, hb1, hab1]
    _ =
      (∑ u ∈ ((s.erase a).erase b).powerset,
        if admissible u ∧
            ¬ admissible (insert a u) ∧
            ¬ admissible (insert b u) then
          booleanCubeSign u
        else 0) -
      ∑ u ∈ ((s.erase a).erase b).powerset,
        if admissible u ∧
            admissible (insert a u) ∧
            admissible (insert b u) ∧
            ¬ admissible (insert a (insert b u)) then
          booleanCubeSign u
        else 0 := by
      rw [Finset.sum_sub_distrib]

end RHLean.Arithmetic
