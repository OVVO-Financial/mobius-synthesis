import Mathlib
import RHLean.Proof.LowWheelCanonicalCofactorQuotientPairing

/-!
# Finite canonical-pairing frontier

The state-dependent least-prime toggle is now applied to an actual finite
physical carrier.  As in the repository's collision-frontier pairing pattern,
we split any finite state set into

* pairable states whose mate remains in the set and is distinct;
* fixed states;
* mate-crosses-set defects.

On squarefree cofactor states the pairable mass cancels exactly by
`Finset.sum_involution`.  For the physical square-root carrier, a defect cannot
be an arbitrary missing mate: once the mate still satisfies the physical
inequalities, squarefreeness and the ambient finite bounds are automatic.
The square-endpoint product ceiling further collapses the apparent two-boundary
failure to a single one-sided frontier: every genuine defect is a quotient
root-downcross after the least-prime insertion move.

No absolute value, density estimate, or analytic asymptotic appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Pairable part of an arbitrary finite cofactor/quotient frontier. -/
def lowWheelCanonicalPairablePart
    (F : Finset LowWheelCofactorQuotientState) :
    Finset LowWheelCofactorQuotientState :=
  F.filter fun x =>
    lowWheelCanonicalCofactorQuotientToggle x ∈ F ∧
      lowWheelCanonicalCofactorQuotientToggle x ≠ x

/-- Fixed part of an arbitrary finite cofactor/quotient frontier. -/
def lowWheelCanonicalFixedPart
    (F : Finset LowWheelCofactorQuotientState) :
    Finset LowWheelCofactorQuotientState :=
  F.filter fun x => lowWheelCanonicalCofactorQuotientToggle x = x

/-- Exact mate-crosses-frontier defect. -/
def lowWheelCanonicalDefectPart
    (F : Finset LowWheelCofactorQuotientState) :
    Finset LowWheelCofactorQuotientState :=
  F.filter fun x => lowWheelCanonicalCofactorQuotientToggle x ∉ F

/-- Product-one states are fixed by the canonical toggle. -/
theorem lowWheelCanonicalToggle_eq_self_of_product_eq_one
    {c k : ℕ} (hprod : c * k = 1) :
    lowWheelCanonicalCofactorQuotientToggle (c, k) = (c, k) := by
  unfold lowWheelCanonicalCofactorQuotientToggle
    lowWheelCanonicalCofactorQuotientPivot
  rw [hprod]
  simp [lowWheelCofactorQuotientToggleAt]

/-- A genuinely moved state necessarily has nontrivial invariant product. -/
theorem lowWheelCanonical_product_ne_one_of_toggle_ne
    {c k : ℕ}
    (hne : lowWheelCanonicalCofactorQuotientToggle (c, k) ≠ (c, k)) :
    c * k ≠ 1 := by
  intro hprod
  exact hne (lowWheelCanonicalToggle_eq_self_of_product_eq_one hprod)

/-- The canonical mate of a pairable state is again pairable whenever every
state of the ambient frontier has squarefree cofactor. -/
theorem lowWheelCanonicalToggle_mem_pairable
    (F : Finset LowWheelCofactorQuotientState)
    (hsqF : ∀ x ∈ F, Squarefree x.1)
    {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalPairablePart F) :
    lowWheelCanonicalCofactorQuotientToggle x ∈
      lowWheelCanonicalPairablePart F := by
  classical
  have hdata := Finset.mem_filter.mp hx
  have hsq := hsqF x hdata.1
  have hprod : x.1 * x.2 ≠ 1 :=
    lowWheelCanonical_product_ne_one_of_toggle_ne hdata.2.2
  have hinv := lowWheelCanonicalCofactorQuotientToggle_involutive hsq hprod
  apply Finset.mem_filter.mpr
  refine ⟨hdata.2.1, ?_⟩
  constructor
  · simpa [hinv] using hdata.1
  · intro hfix
    rw [hinv] at hfix
    exact hdata.2.2 hfix.symm

/-- Every pairable squarefree-cofactor frontier cancels exactly. -/
theorem sum_lowWheelCanonicalPairablePart_eq_zero
    (F : Finset LowWheelCofactorQuotientState)
    (t : Finset ℕ)
    (hsqF : ∀ x ∈ F, Squarefree x.1) :
    (∑ x ∈ lowWheelCanonicalPairablePart F,
        canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) = 0 := by
  classical
  let w : LowWheelCofactorQuotientState → ℂ := fun x =>
    canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)
  exact Finset.sum_involution
    (s := lowWheelCanonicalPairablePart F) (f := w)
    (fun x _hx => lowWheelCanonicalCofactorQuotientToggle x)
    (fun x hx => by
      have hdata := Finset.mem_filter.mp hx
      have hsq := hsqF x hdata.1
      have hprod : x.1 * x.2 ≠ 1 :=
        lowWheelCanonical_product_ne_one_of_toggle_ne hdata.2.2
      change w x + w (lowWheelCanonicalCofactorQuotientToggle x) = 0
      unfold w
      rw [lowWheelCanonicalCofactorQuotientToggle_weight_neg hsq hprod]
      simp)
    (fun x hx _hw => (Finset.mem_filter.mp hx).2.2)
    (fun _x hx => lowWheelCanonicalToggle_mem_pairable F hsqF hx)
    (fun x hx => by
      have hdata := Finset.mem_filter.mp hx
      have hsq := hsqF x hdata.1
      have hprod : x.1 * x.2 ≠ 1 :=
        lowWheelCanonical_product_ne_one_of_toggle_ne hdata.2.2
      exact lowWheelCanonicalCofactorQuotientToggle_involutive hsq hprod)

/-- The pairable/fixed/defect pieces partition every finite frontier. -/
theorem lowWheelCanonical_frontier_partition
    (F : Finset LowWheelCofactorQuotientState) :
    lowWheelCanonicalPairablePart F ∪
        lowWheelCanonicalFixedPart F ∪
        lowWheelCanonicalDefectPart F = F := by
  classical
  ext x
  simp only [Finset.mem_union]
  constructor
  · intro hx
    rcases hx with (hp | hf) | hd
    · exact (Finset.mem_filter.mp hp).1
    · exact (Finset.mem_filter.mp hf).1
    · exact (Finset.mem_filter.mp hd).1
  · intro hx
    by_cases hmate : lowWheelCanonicalCofactorQuotientToggle x ∈ F
    · by_cases hfix : lowWheelCanonicalCofactorQuotientToggle x = x
      · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hx, hfix⟩))
      · exact Or.inl (Or.inl
          (Finset.mem_filter.mpr ⟨hx, hmate, hfix⟩))
    · exact Or.inr (Finset.mem_filter.mpr ⟨hx, hmate⟩)

/-- Pairable and fixed parts are disjoint. -/
theorem lowWheelCanonical_pairable_disjoint_fixed
    (F : Finset LowWheelCofactorQuotientState) :
    Disjoint (lowWheelCanonicalPairablePart F)
      (lowWheelCanonicalFixedPart F) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro x hp hf
  exact (Finset.mem_filter.mp hp).2.2 (Finset.mem_filter.mp hf).2

/-- Pairable-plus-fixed is disjoint from the mate-crosses-set defect. -/
theorem lowWheelCanonical_pairable_fixed_disjoint_defect
    (F : Finset LowWheelCofactorQuotientState) :
    Disjoint
      (lowWheelCanonicalPairablePart F ∪ lowWheelCanonicalFixedPart F)
      (lowWheelCanonicalDefectPart F) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro x hpf hd
  have hnotmate := (Finset.mem_filter.mp hd).2
  rcases Finset.mem_union.mp hpf with hp | hf
  · exact hnotmate (Finset.mem_filter.mp hp).2.1
  · have hF := (Finset.mem_filter.mp hf).1
    have hfix := (Finset.mem_filter.mp hf).2
    apply hnotmate
    rw [hfix]
    exact hF

/-- **Exact canonical frontier reduction.**  All interior pairs disappear before
any magnitude is taken. -/
theorem sum_lowWheelCanonicalFrontier_eq_fixed_add_defect
    (F : Finset LowWheelCofactorQuotientState)
    (t : Finset ℕ)
    (hsqF : ∀ x ∈ F, Squarefree x.1) :
    (∑ x ∈ F,
        canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
      (∑ x ∈ lowWheelCanonicalFixedPart F,
        canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) +
      ∑ x ∈ lowWheelCanonicalDefectPart F,
        canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ) := by
  classical
  have hpart := lowWheelCanonical_frontier_partition F
  have hpf := lowWheelCanonical_pairable_disjoint_fixed F
  have hud := lowWheelCanonical_pairable_fixed_disjoint_defect F
  calc
    (∑ x ∈ F, canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
      ∑ x ∈
        lowWheelCanonicalPairablePart F ∪
          lowWheelCanonicalFixedPart F ∪
          lowWheelCanonicalDefectPart F,
        canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ) := by
          rw [hpart]
    _ =
      (∑ x ∈ lowWheelCanonicalPairablePart F ∪
          lowWheelCanonicalFixedPart F,
          canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) +
        ∑ x ∈ lowWheelCanonicalDefectPart F,
          canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ) := by
            rw [Finset.sum_union hud]
    _ =
      ((∑ x ∈ lowWheelCanonicalPairablePart F,
          canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) +
        ∑ x ∈ lowWheelCanonicalFixedPart F,
          canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) +
        ∑ x ∈ lowWheelCanonicalDefectPart F,
          canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ) := by
            rw [Finset.sum_union hpf]
    _ =
      (∑ x ∈ lowWheelCanonicalFixedPart F,
          canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) +
        ∑ x ∈ lowWheelCanonicalDefectPart F,
          canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ) := by
      rw [sum_lowWheelCanonicalPairablePart_eq_zero F t hsqF]
      simp

/-- Actual finite physical state set for one low-prime face `t`. -/
def lowWheelCanonicalPhysicalStateSet
    (R : ℕ) (t : Finset ℕ) : Finset LowWheelCofactorQuotientState := by
  classical
  exact ((Finset.Ico 1 R).product (Finset.Icc 1 (squareRootEndpoint R))).filter
    fun x => Squarefree x.1 ∧ LowWheelTransportPairCarrier R t x

@[simp] theorem mem_lowWheelCanonicalPhysicalStateSet
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState} :
    x ∈ lowWheelCanonicalPhysicalStateSet R t ↔
      x.1 ∈ Finset.Ico 1 R ∧
      x.2 ∈ Finset.Icc 1 (squareRootEndpoint R) ∧
      Squarefree x.1 ∧ LowWheelTransportPairCarrier R t x := by
  classical
  simp [lowWheelCanonicalPhysicalStateSet, and_assoc]

/-- The physical finite carrier has squarefree cofactors by construction. -/
theorem lowWheelCanonicalPhysicalStateSet_squarefree
    {R : ℕ} {t : Finset ℕ}
    (x : LowWheelCofactorQuotientState)
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t) :
    Squarefree x.1 :=
  (mem_lowWheelCanonicalPhysicalStateSet.mp hx).2.2.1

/-- The canonical mate of a nontrivial squarefree cofactor is squarefree. -/
theorem lowWheelCanonicalToggle_squarefree
    {c k : ℕ} (hsq : Squarefree c) (hne : c * k ≠ 1) :
    Squarefree (lowWheelCanonicalCofactorQuotientToggle (c, k)).1 := by
  let p := lowWheelCanonicalCofactorQuotientPivot (c, k)
  have hp : p.Prime := by
    simpa [p] using lowWheelCanonicalCofactorQuotientPivot_prime hne
  have hactive : p ∣ c ∨ p ∣ k := by
    simpa [p] using lowWheelCanonicalCofactorQuotientPivot_active hne
  by_cases hpc : p ∣ c
  · have hd : c / p ∣ c := ⟨p, (Nat.div_mul_cancel hpc).symm⟩
    have hsqd : Squarefree (c / p) := hsq.squarefree_of_dvd hd
    change Squarefree (lowWheelCofactorQuotientToggleAt p (c, k)).1
    unfold lowWheelCofactorQuotientToggleAt
    rw [if_pos hpc]
    exact hsqd
  · have hpk : p ∣ k := hactive.resolve_left hpc
    have hmuC : μ c ≠ 0 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
    have hmu := moebius_prime_mul hp hpc
    have hmuNe : μ (p * c) ≠ 0 := by
      rw [hmu]
      exact neg_ne_zero.mpr hmuC
    have hsqp : Squarefree (p * c) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuNe
    change Squarefree (lowWheelCofactorQuotientToggleAt p (c, k)).1
    unfold lowWheelCofactorQuotientToggleAt
    rw [if_neg hpc, if_pos hpk]
    simpa [Nat.mul_comm] using hsqp

/-- The physical carrier inequalities themselves force the ambient finite range
for `c` and `k`. -/
theorem lowWheelTransportPairCarrier_mem_ranges
    {R c k : ℕ} {t : Finset ℕ}
    (h : LowWheelTransportPairCarrier R t (c, k)) :
    c ∈ Finset.Ico 1 R ∧ k ∈ Finset.Icc 1 (squareRootEndpoint R) := by
  rcases h with ⟨hc1, hcR, hhigh, htop⟩
  have hkpos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    simp at hhigh
  have htpos : 0 < primeFaceProduct t := by
    by_contra ht
    have ht0 : primeFaceProduct t = 0 := Nat.eq_zero_of_not_pos ht
    rw [ht0] at hhigh
    simp at hhigh
  have hcoef : 1 ≤ c * primeFaceProduct t :=
    Nat.mul_pos (by omega) htpos
  have hkX : k ≤ squareRootEndpoint R := by
    calc
      k = 1 * k := by simp
      _ ≤ (c * primeFaceProduct t) * k := Nat.mul_le_mul_right k hcoef
      _ ≤ squareRootEndpoint R := htop
  exact ⟨Finset.mem_Ico.mpr ⟨hc1, hcR⟩,
    Finset.mem_Icc.mpr ⟨by omega, hkX⟩⟩

/-- If a nontrivial physical state has a physical canonical mate, that mate is
also in the actual finite physical set. -/
theorem lowWheelCanonicalToggle_mem_physical_of_carrier
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t)
    (hne : x.1 * x.2 ≠ 1)
    (hmate : LowWheelTransportPairCarrier R t
      (lowWheelCanonicalCofactorQuotientToggle x)) :
    lowWheelCanonicalCofactorQuotientToggle x ∈
      lowWheelCanonicalPhysicalStateSet R t := by
  rcases x with ⟨c, k⟩
  have hsq : Squarefree c :=
    lowWheelCanonicalPhysicalStateSet_squarefree (c, k) hx
  have hsquareMate := lowWheelCanonicalToggle_squarefree hsq hne
  have hrange := lowWheelTransportPairCarrier_mem_ranges hmate
  apply mem_lowWheelCanonicalPhysicalStateSet.mpr
  exact ⟨hrange.1, hrange.2, hsquareMate, hmate⟩

/-- Every genuine physical pairing defect lies on one of the original two
root-crossing boundaries.  Retained for compatibility with the pre-reduction
interface. -/
theorem lowWheelCanonicalPhysicalDefect_boundary
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalDefectPart
      (lowWheelCanonicalPhysicalStateSet R t)) :
    R ≤ x.1 * lowWheelCanonicalCofactorQuotientPivot x ∨
      primeFaceProduct t *
          (x.2 / lowWheelCanonicalCofactorQuotientPivot x) ≤ R := by
  have hdata := Finset.mem_filter.mp hx
  have hxF := hdata.1
  have hnotmate := hdata.2
  have hcarrier := (mem_lowWheelCanonicalPhysicalStateSet.mp hxF).2.2.2
  have hprod : x.1 * x.2 ≠ 1 := by
    intro hone
    have hfix := lowWheelCanonicalToggle_eq_self_of_product_eq_one hone
    apply hnotmate
    rw [hfix]
    exact hxF
  have hnotCarrier : ¬ LowWheelTransportPairCarrier R t
      (lowWheelCanonicalCofactorQuotientToggle x) := by
    intro hmate
    exact hnotmate
      (lowWheelCanonicalToggle_mem_physical_of_carrier hxF hprod hmate)
  rcases x with ⟨c, k⟩
  exact lowWheelCanonicalCofactorQuotientToggle_boundary_of_not_preserves
    hcarrier hprod hnotCarrier

/-- **Reduced physical defect support.**  Every surviving canonical defect is a
genuine quotient root-downcross; there is no independent cofactor boundary. -/
theorem lowWheelCanonicalPhysicalDefect_downcross
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalDefectPart
      (lowWheelCanonicalPhysicalStateSet R t)) :
    primeFaceProduct t *
        (x.2 / lowWheelCanonicalCofactorQuotientPivot x) ≤ R := by
  have hdata := Finset.mem_filter.mp hx
  have hxF := hdata.1
  have hnotmate := hdata.2
  have hcarrier := (mem_lowWheelCanonicalPhysicalStateSet.mp hxF).2.2.2
  have hprod : x.1 * x.2 ≠ 1 := by
    intro hone
    have hfix := lowWheelCanonicalToggle_eq_self_of_product_eq_one hone
    apply hnotmate
    rw [hfix]
    exact hxF
  have hnotCarrier : ¬ LowWheelTransportPairCarrier R t
      (lowWheelCanonicalCofactorQuotientToggle x) := by
    intro hmate
    exact hnotmate
      (lowWheelCanonicalToggle_mem_physical_of_carrier hxF hprod hmate)
  rcases x with ⟨c, k⟩
  exact lowWheelCanonicalCofactorQuotientToggle_downcross_of_not_preserves
    hcarrier hprod hnotCarrier

/-- The actual physical signed mass is exactly fixed mass plus explicit
mate-crosses-geometry defect mass. -/
theorem sum_lowWheelCanonicalPhysicalState_eq_fixed_add_defect
    (R : ℕ) (t : Finset ℕ) :
    (∑ x ∈ lowWheelCanonicalPhysicalStateSet R t,
        canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
      (∑ x ∈ lowWheelCanonicalFixedPart
          (lowWheelCanonicalPhysicalStateSet R t),
        canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) +
      ∑ x ∈ lowWheelCanonicalDefectPart
          (lowWheelCanonicalPhysicalStateSet R t),
        canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ) := by
  exact sum_lowWheelCanonicalFrontier_eq_fixed_add_defect
    (lowWheelCanonicalPhysicalStateSet R t) t
    (fun x hx => lowWheelCanonicalPhysicalStateSet_squarefree x hx)

end RHLean.Proof
