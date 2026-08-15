import Mathlib
import RHLean.Arithmetic.TruncatedBooleanCubeSecondToggle

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-!
# Mask-preserving second-coordinate cancellation

The second-toggle identity remains valid after restricting the first-failure
frontier by any predicate that is invariant under the second coordinate.  This
is the exact form needed for residue-fibre survivor cancellation: a square-one
prime preserves the residue mask while reversing the Boolean sign.
-/

/-- Alternating first-failure mass after imposing an additional face mask. -/
def maskedFirstFailureBoundaryAlternatingSum
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α)
    (admissible mask : Finset α → Prop) : ℤ := by
  classical
  exact ∑ u ∈ (s.erase a).powerset,
    if admissible u ∧ ¬ admissible (insert a u) ∧ mask u then
      booleanCubeSign u
    else 0

/-- **Masked second-toggle cancellation.**  If the extra mask is invariant
under inserting the second coordinate `b`, every matched pair on the first
`a`-failure frontier still cancels.  Only the same two corner types survive,
now restricted by the mask. -/
theorem maskedFirstFailureBoundaryAlternatingSum_eq_secondToggleCorners
    {α : Type*} [DecidableEq α]
    {s : Finset α} {a b : α}
    {admissible mask : Finset α → Prop}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hdown : CubeDownwardClosed admissible)
    (hmask : ∀ u ∈ ((s.erase a).erase b).powerset,
      mask (insert b u) ↔ mask u) :
    maskedFirstFailureBoundaryAlternatingSum s a admissible mask =
      (∑ u ∈ ((s.erase a).erase b).powerset,
        if admissible u ∧
            ¬ admissible (insert a u) ∧
            ¬ admissible (insert b u) ∧
            mask u then
          booleanCubeSign u
        else 0) -
      ∑ u ∈ ((s.erase a).erase b).powerset,
        if admissible u ∧
            admissible (insert a u) ∧
            admissible (insert b u) ∧
            ¬ admissible (insert a (insert b u)) ∧
            mask u then
          booleanCubeSign u
        else 0 := by
  classical
  have hba : b ∈ s.erase a := by
    exact Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have hdecomp : s.erase a = insert b ((s.erase a).erase b) := by
    exact (Finset.insert_erase hba).symm
  unfold maskedFirstFailureBoundaryAlternatingSum
  conv_lhs => rw [hdecomp]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase b (s.erase a))]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ u ∈ ((s.erase a).erase b).powerset,
        ((if admissible u ∧ ¬ admissible (insert a u) ∧ mask u then
            booleanCubeSign u else 0) +
          (if admissible (insert b u) ∧
              ¬ admissible (insert a (insert b u)) ∧
              mask (insert b u) then
            booleanCubeSign (insert b u) else 0))) =
      ∑ u ∈ ((s.erase a).erase b).powerset,
        ((if admissible u ∧
              ¬ admissible (insert a u) ∧
              ¬ admissible (insert b u) ∧
              mask u then
            booleanCubeSign u
          else 0) -
        (if admissible u ∧
              admissible (insert a u) ∧
              admissible (insert b u) ∧
              ¬ admissible (insert a (insert b u)) ∧
              mask u then
            booleanCubeSign u
          else 0)) := by
        apply Finset.sum_congr rfl
        intro u hu
        have hbu : b ∉ u :=
          Finset.notMem_of_mem_powerset_of_notMem
            hu (Finset.notMem_erase b (s.erase a))
        have hsign :
            booleanCubeSign (insert b u) = -booleanCubeSign u := by
          simp [booleanCubeSign, Finset.card_insert_of_notMem, hbu, pow_succ]
        have hmasku := hmask u hu
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
              · by_cases hm : mask u <;>
                  simp [h0, ha1, hb1, hab1, hmasku, hm]
              · by_cases hm : mask u <;>
                  simp [h0, ha1, hb1, hab1, hmasku, hm]
            · have hab1 : ¬ admissible (insert a (insert b u)) := by
                intro h
                exact hb1 (h_ab_to_b h)
              by_cases hm : mask u <;>
                simp [h0, ha1, hb1, hab1, hmasku, hm]
          · by_cases hb1 : admissible (insert b u)
            · have hab1 : ¬ admissible (insert a (insert b u)) := by
                intro h
                exact ha1 (h_ab_to_a h)
              by_cases hm : mask u <;>
                simp [h0, ha1, hb1, hab1, hmasku, hm]
            · have hab1 : ¬ admissible (insert a (insert b u)) := by
                intro h
                exact hb1 (h_ab_to_b h)
              by_cases hm : mask u <;>
                simp [h0, ha1, hb1, hab1, hmasku, hm]
        · have ha1 : ¬ admissible (insert a u) := by
            intro h
            exact h0 (h_a_to_base h)
          have hb1 : ¬ admissible (insert b u) := by
            intro h
            exact h0 (h_b_to_base h)
          have hab1 : ¬ admissible (insert a (insert b u)) := by
            intro h
            exact hb1 (h_ab_to_b h)
          by_cases hm : mask u <;>
            simp [h0, ha1, hb1, hab1, hmasku, hm]
    _ =
      (∑ u ∈ ((s.erase a).erase b).powerset,
        if admissible u ∧
            ¬ admissible (insert a u) ∧
            ¬ admissible (insert b u) ∧
            mask u then
          booleanCubeSign u
        else 0) -
      ∑ u ∈ ((s.erase a).erase b).powerset,
        if admissible u ∧
            admissible (insert a u) ∧
            admissible (insert b u) ∧
            ¬ admissible (insert a (insert b u)) ∧
            mask u then
          booleanCubeSign u
        else 0 := by
      rw [Finset.sum_sub_distrib]

end RHLean.Arithmetic
