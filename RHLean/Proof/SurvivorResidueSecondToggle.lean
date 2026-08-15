import Mathlib
import RHLean.Arithmetic.TruncatedBooleanCubeMaskedSecondToggle
import RHLean.Proof.SurvivorResiduePrimeToggle

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-!
# Second prime toggle inside survivor residue fibres

The first residue-preserving prime toggle collapses a survivor Boolean cube to a
first-failure frontier.  A second square-one prime coordinate still preserves
the residue mask, so the first-failure frontier itself admits another exact sign
pairing.  What remains are two explicit codimension-two corner types.

At parity modulus `2`, primes `3` and `5` are both square-one.  Hence for every
distinguished upper prime face with `q >= 7`, the existing three-frontier
survivor identity at pivot `3` refines to six signed corner sums after toggling
prime `5`.
-/

/-- First second-toggle corner: the parent is admitted, while inserting either
pivot separately leaves the support. -/
noncomputable def residueConditionedSecondToggleSingleFailureCornerSum
    (modulus q : ℕ) (r : ZMod modulus)
    (ambient : Finset ℕ) (a b : ℕ)
    (admissible : Finset ℕ → Prop) : ℤ := by
  classical
  exact ∑ u ∈ ((ambient.erase a).erase b).powerset,
    if admissible u ∧
        ¬ admissible (insert a u) ∧
        ¬ admissible (insert b u) ∧
        survivorHeightResidue modulus (primeFaceProduct u) q = r then
      booleanCubeSign u
    else 0

/-- Second second-toggle corner: each single pivot extension remains admitted,
but their double extension is the first failure. -/
noncomputable def residueConditionedSecondToggleDoubleFailureCornerSum
    (modulus q : ℕ) (r : ZMod modulus)
    (ambient : Finset ℕ) (a b : ℕ)
    (admissible : Finset ℕ → Prop) : ℤ := by
  classical
  exact ∑ u ∈ ((ambient.erase a).erase b).powerset,
    if admissible u ∧
        admissible (insert a u) ∧
        admissible (insert b u) ∧
        ¬ admissible (insert a (insert b u)) ∧
        survivorHeightResidue modulus (primeFaceProduct u) q = r then
      booleanCubeSign u
    else 0

/-- The residue-conditioned first-failure sum is the generic masked frontier
sum with the survivor-height residue as its mask. -/
theorem residueConditionedFirstFailureBoundaryAlternatingSum_eq_masked
    (modulus q : ℕ) (r : ZMod modulus)
    (ambient : Finset ℕ) (a : ℕ)
    (admissible : Finset ℕ → Prop) :
    residueConditionedFirstFailureBoundaryAlternatingSum
        modulus q r ambient a admissible =
      maskedFirstFailureBoundaryAlternatingSum ambient a admissible
        (fun u => survivorHeightResidue modulus (primeFaceProduct u) q = r) := by
  classical
  unfold residueConditionedFirstFailureBoundaryAlternatingSum
    maskedFirstFailureBoundaryAlternatingSum firstFailureBoundary
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hboundary : admissible u ∧ ¬ admissible (insert a u) <;>
    by_cases hres : survivorHeightResidue modulus (primeFaceProduct u) q = r <;>
    simp [hboundary, hres]

/-- **Residue-preserving second toggle.**  A second square-one prime coordinate
pairs the first-failure frontier inside the same survivor residue fibre. -/
theorem residueConditionedFirstFailureBoundaryAlternatingSum_eq_secondToggleCorners
    (modulus q : ℕ) (r : ZMod modulus)
    (ambient : Finset ℕ) (a b : ℕ)
    (admissible : Finset ℕ → Prop)
    (ha : a ∈ ambient) (hb : b ∈ ambient) (hab : a ≠ b)
    (hdown : CubeDownwardClosed admissible)
    (hsq : (b : ZMod modulus) ^ 2 = 1) :
    residueConditionedFirstFailureBoundaryAlternatingSum
        modulus q r ambient a admissible =
      residueConditionedSecondToggleSingleFailureCornerSum
        modulus q r ambient a b admissible -
      residueConditionedSecondToggleDoubleFailureCornerSum
        modulus q r ambient a b admissible := by
  rw [residueConditionedFirstFailureBoundaryAlternatingSum_eq_masked]
  rw [maskedFirstFailureBoundaryAlternatingSum_eq_secondToggleCorners
    ha hb hab hdown]
  · unfold residueConditionedSecondToggleSingleFailureCornerSum
      residueConditionedSecondToggleDoubleFailureCornerSum
    apply congrArg₂ (fun x y : ℤ => x - y)
    · apply Finset.sum_congr rfl
      intro u hu
      by_cases h : admissible u ∧
          ¬ admissible (insert a u) ∧
          ¬ admissible (insert b u) ∧
          survivorHeightResidue modulus (primeFaceProduct u) q = r <;>
        simp [h]
    · apply Finset.sum_congr rfl
      intro u hu
      by_cases h : admissible u ∧
          admissible (insert a u) ∧
          admissible (insert b u) ∧
          ¬ admissible (insert a (insert b u)) ∧
          survivorHeightResidue modulus (primeFaceProduct u) q = r <;>
        simp [h]
  · intro u hu
    have hbu : b ∉ u := by
      have husub := Finset.mem_powerset.mp hu
      exact fun hmem =>
        (Finset.notMem_erase b (ambient.erase a)) (husub hmem)
    exact survivor_primeFace_residue_iff_insert_of_sq_eq_one
      modulus b q u r hbu hsq

/-- At parity modulus `2`, the first pivot `3` and second pivot `5` are both
residue-preserving sign toggles for every upper-prime face with `q >= 7`.  The
entire residue-conditioned survivor high mass is therefore a signed combination
of six explicit codimension-two corner sums. -/
theorem survivorPrimeFaceParityHigh_alternatingMass_eq_sixCorners_at_three_five
    (Λ : ℝ) (t q : ℕ) (r : ZMod 2)
    (hΛ : 0 ≤ Λ) (hq : 7 ≤ q) :
    survivorPrimeFaceResidueHighAlternatingMass Λ t q 2 r =
      (residueConditionedSecondToggleSingleFailureCornerSum
          2 q r (survivorPrimeFaceAmbient q) 3 5
          (survivorPrimeFaceTransportPrefix Λ t q) -
        residueConditionedSecondToggleDoubleFailureCornerSum
          2 q r (survivorPrimeFaceAmbient q) 3 5
          (survivorPrimeFaceTransportPrefix Λ t q)) +
      (residueConditionedSecondToggleSingleFailureCornerSum
          2 q r (survivorPrimeFaceAmbient q) 3 5
          (survivorPrimeFaceProductPrefix t q) -
        residueConditionedSecondToggleDoubleFailureCornerSum
          2 q r (survivorPrimeFaceAmbient q) 3 5
          (survivorPrimeFaceProductPrefix t q)) -
      (residueConditionedSecondToggleSingleFailureCornerSum
          2 q r (survivorPrimeFaceAmbient q) 3 5
          (survivorPrimeFaceBelowSmoothPrefix Λ t q) -
        residueConditionedSecondToggleDoubleFailureCornerSum
          2 q r (survivorPrimeFaceAmbient q) 3 5
          (survivorPrimeFaceBelowSmoothPrefix Λ t q)) := by
  have h3 : 3 ∈ survivorPrimeFaceAmbient q := by
    unfold survivorPrimeFaceAmbient
    exact mem_primesUpTo.mpr ⟨by norm_num, by omega⟩
  have h5 : 5 ∈ survivorPrimeFaceAmbient q := by
    unfold survivorPrimeFaceAmbient
    exact mem_primesUpTo.mpr ⟨by norm_num, by omega⟩
  have h35 : (3 : ℕ) ≠ 5 := by norm_num
  have hsq5 : ((5 : ℕ) : ZMod 2) ^ 2 = 1 := by native_decide
  rw [survivorPrimeFaceParityHigh_alternatingMass_eq_threeFrontiers_at_three
    Λ t q r hΛ (by omega)]
  rw [residueConditionedFirstFailureBoundaryAlternatingSum_eq_secondToggleCorners
      2 q r (survivorPrimeFaceAmbient q) 3 5
      (survivorPrimeFaceTransportPrefix Λ t q)
      h3 h5 h35 (survivorPrimeFaceTransportPrefix_downward Λ t q) hsq5,
    residueConditionedFirstFailureBoundaryAlternatingSum_eq_secondToggleCorners
      2 q r (survivorPrimeFaceAmbient q) 3 5
      (survivorPrimeFaceProductPrefix t q)
      h3 h5 h35 (survivorPrimeFaceProductPrefix_downward t q) hsq5,
    residueConditionedFirstFailureBoundaryAlternatingSum_eq_secondToggleCorners
      2 q r (survivorPrimeFaceAmbient q) 3 5
      (survivorPrimeFaceBelowSmoothPrefix Λ t q)
      h3 h5 h35 (survivorPrimeFaceBelowSmoothPrefix_downward Λ t q) hsq5]

end RHLean.Proof
