import Mathlib
import RHLean.Arithmetic.PrimeSquareCollisionInvolution
import RHLean.Arithmetic.PrimeSquareCollisionPrefix

noncomputable section

open scoped BigOperators

namespace RHLean.Arithmetic

/-!
# Sign-reversing pairing on a physical collision frontier

This file keeps complete-period cancellation separate from the actual physical
prefix.  For an arbitrary finite set `F` of the nine CRT collision slot-pair
labels, we split `F` into three exact pieces:

* pairable labels whose involution mate also lies in `F` and is distinct;
* fixed labels;
* a pairing defect whose mate lies outside `F`.

`Finset.sum_involution` cancels the pairable piece only after the physical
weight has separately been proved sign-reversing for the chosen slot matching.
Therefore every such signed frontier sum is exactly the fixed-point contribution
plus the mate-crosses-cutoff defect.  When the physical prefix is invariant
under the slot matching, the defect is empty and only the tiny fixed set remains.
-/

/-- Labels whose distinct involution mate is also present in the same finite
frontier. -/
def collisionInvolutionPairablePart
    (F : Finset TwoPrimeCollisionState) : Finset TwoPrimeCollisionState :=
  F.filter (fun s =>
    collisionExponentStateInvolution s ∈ F ∧
      collisionExponentStateInvolution s ≠ s)

/-- Fixed labels retained by a finite frontier. -/
def collisionInvolutionFixedPart
    (F : Finset TwoPrimeCollisionState) : Finset TwoPrimeCollisionState :=
  F.filter (fun s => collisionExponentStateInvolution s = s)

/-- Exact pairing defect: labels lying in `F` whose involution mate has crossed
outside `F`. -/
def collisionInvolutionDefectPart
    (F : Finset TwoPrimeCollisionState) : Finset TwoPrimeCollisionState :=
  F.filter (fun s => collisionExponentStateInvolution s ∉ F)

/-- The slot-label involution preserves the pairable part by construction. -/
theorem collisionExponentStateInvolution_mem_pairable
    (F : Finset TwoPrimeCollisionState)
    {s : TwoPrimeCollisionState}
    (hs : s ∈ collisionInvolutionPairablePart F) :
    collisionExponentStateInvolution s ∈
      collisionInvolutionPairablePart F := by
  classical
  have hdata := Finset.mem_filter.mp hs
  apply Finset.mem_filter.mpr
  refine ⟨hdata.2.1, ?_⟩
  constructor
  · simpa using hdata.1
  · intro hfix
    have heq : s = collisionExponentStateInvolution s := by
      simpa using hfix
    exact hdata.2.2 heq.symm

/-- Every separately proved sign-reversing physical weight cancels exactly on
the pairable part. -/
theorem sum_collisionInvolutionPairablePart_eq_zero
    {A : Type*} [AddCommGroup A]
    (F : Finset TwoPrimeCollisionState)
    (w : TwoPrimeCollisionState → A)
    (hpair : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
        w (collisionExponentStateInvolution s) = -w s) :
    ∑ s ∈ collisionInvolutionPairablePart F, w s = 0 := by
  classical
  exact Finset.sum_involution
    (s := collisionInvolutionPairablePart F) (f := w)
    (fun s _hs => collisionExponentStateInvolution s)
    (fun s hs => by
      have hne := (Finset.mem_filter.mp hs).2.2
      rw [hpair s hne]
      simp)
    (fun s hs _hw => (Finset.mem_filter.mp hs).2.2)
    (fun _s hs => collisionExponentStateInvolution_mem_pairable F hs)
    (fun s _hs => collisionExponentStateInvolution_involutive s)

/-- The three pieces give an exact partition of every finite label frontier. -/
theorem collisionInvolution_frontier_partition
    (F : Finset TwoPrimeCollisionState) :
    collisionInvolutionPairablePart F ∪
        collisionInvolutionFixedPart F ∪
        collisionInvolutionDefectPart F = F := by
  classical
  ext s
  simp only [Finset.mem_union]
  constructor
  · intro hs
    rcases hs with (hp | hf) | hd
    · exact (Finset.mem_filter.mp hp).1
    · exact (Finset.mem_filter.mp hf).1
    · exact (Finset.mem_filter.mp hd).1
  · intro hs
    by_cases hmate : collisionExponentStateInvolution s ∈ F
    · by_cases hfix : collisionExponentStateInvolution s = s
      · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hs, hfix⟩))
      · exact Or.inl (Or.inl
          (Finset.mem_filter.mpr ⟨hs, hmate, hfix⟩))
    · exact Or.inr (Finset.mem_filter.mpr ⟨hs, hmate⟩)

/-- Pairable and fixed labels are disjoint. -/
theorem collisionInvolution_pairable_disjoint_fixed
    (F : Finset TwoPrimeCollisionState) :
    Disjoint (collisionInvolutionPairablePart F)
      (collisionInvolutionFixedPart F) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro s hp hf
  exact (Finset.mem_filter.mp hp).2.2 (Finset.mem_filter.mp hf).2

/-- The union of pairable and fixed labels is disjoint from the pairing defect. -/
theorem collisionInvolution_pairable_fixed_disjoint_defect
    (F : Finset TwoPrimeCollisionState) :
    Disjoint
      (collisionInvolutionPairablePart F ∪
        collisionInvolutionFixedPart F)
      (collisionInvolutionDefectPart F) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro s hpf hd
  have hnotmate := (Finset.mem_filter.mp hd).2
  rcases Finset.mem_union.mp hpf with hp | hf
  · exact hnotmate (Finset.mem_filter.mp hp).2.1
  · have hF := (Finset.mem_filter.mp hf).1
    have hfix := (Finset.mem_filter.mp hf).2
    apply hnotmate
    rw [hfix]
    exact hF

/-- **The pairing defect has at most three labels.**  The six nonfixed labels
form three two-cycles, one for each second collision-slot coordinate.  A finite
frontier can strand at most one member of each two-cycle: if both members with
the same second coordinate were present, neither could lie in the defect. -/
theorem collisionInvolutionDefectPart_card_le_three
    (F : Finset TwoPrimeCollisionState) :
    (collisionInvolutionDefectPart F).card ≤ 3 := by
  classical
  have hinj : Set.InjOn
      (fun s : TwoPrimeCollisionState => s.2)
      (collisionInvolutionDefectPart F) := by
    intro s hs t ht hsecond
    rcases s with ⟨a, b⟩
    rcases t with ⟨c, d⟩
    change b = d at hsecond
    subst d
    unfold collisionInvolutionDefectPart at hs ht
    have hsdata := Finset.mem_filter.mp hs
    have htdata := Finset.mem_filter.mp ht
    fin_cases a <;> fin_cases c <;>
      simp_all [collisionExponentStateInvolution, collisionSlotFlip]
  have hcard :
      ((collisionInvolutionDefectPart F).image
        (fun s : TwoPrimeCollisionState => s.2)).card =
        (collisionInvolutionDefectPart F).card :=
    Finset.card_image_iff.mpr hinj
  calc
    (collisionInvolutionDefectPart F).card =
        ((collisionInvolutionDefectPart F).image
          (fun s : TwoPrimeCollisionState => s.2)).card := hcard.symm
    _ ≤ (Finset.univ : Finset CollisionSlotLabel).card := by
      apply Finset.card_le_card
      intro b hb
      simp
    _ = 3 := by simp [CollisionSlotLabel]

/-- Consequently any integer weight bounded by one on the defect has total
absolute defect mass at most three.  This is a signed-frontier bound, not a
per-residue count of all nine CRT classes. -/
theorem abs_sum_collisionInvolutionDefectPart_le_three
    (F : Finset TwoPrimeCollisionState)
    (w : TwoPrimeCollisionState → ℤ)
    (hunit : ∀ s ∈ collisionInvolutionDefectPart F, |w s| ≤ 1) :
    |∑ s ∈ collisionInvolutionDefectPart F, w s| ≤ 3 := by
  calc
    |∑ s ∈ collisionInvolutionDefectPart F, w s| ≤
        ∑ s ∈ collisionInvolutionDefectPart F, |w s| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ collisionInvolutionDefectPart F, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro s hs
      exact hunit s hs
    _ = ((collisionInvolutionDefectPart F).card : ℤ) := by simp
    _ ≤ 3 := by
      exact_mod_cast collisionInvolutionDefectPart_card_le_three F

/-- **Exact finite-frontier pairing reduction.**  A sign-reversing involution
removes every pair whose two members remain in the physical finite set.  The
whole sum is therefore the fixed-point sum plus the explicit mate-crosses-cutoff
defect. -/
theorem sum_collisionFrontier_eq_fixed_add_defect
    {A : Type*} [AddCommGroup A]
    (F : Finset TwoPrimeCollisionState)
    (w : TwoPrimeCollisionState → A)
    (hpair : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
        w (collisionExponentStateInvolution s) = -w s) :
    (∑ s ∈ F, w s) =
      (∑ s ∈ collisionInvolutionFixedPart F, w s) +
        ∑ s ∈ collisionInvolutionDefectPart F, w s := by
  classical
  have hpart := collisionInvolution_frontier_partition F
  have hpf := collisionInvolution_pairable_disjoint_fixed F
  have hud := collisionInvolution_pairable_fixed_disjoint_defect F
  calc
    (∑ s ∈ F, w s) =
        ∑ s ∈
          collisionInvolutionPairablePart F ∪
            collisionInvolutionFixedPart F ∪
            collisionInvolutionDefectPart F, w s := by
      rw [hpart]
    _ =
        (∑ s ∈
          collisionInvolutionPairablePart F ∪
            collisionInvolutionFixedPart F, w s) +
          ∑ s ∈ collisionInvolutionDefectPart F, w s := by
      rw [Finset.sum_union hud]
    _ =
        ((∑ s ∈ collisionInvolutionPairablePart F, w s) +
          ∑ s ∈ collisionInvolutionFixedPart F, w s) +
          ∑ s ∈ collisionInvolutionDefectPart F, w s := by
      rw [Finset.sum_union hpf]
    _ =
        (∑ s ∈ collisionInvolutionFixedPart F, w s) +
          ∑ s ∈ collisionInvolutionDefectPart F, w s := by
      rw [sum_collisionInvolutionPairablePart_eq_zero F w hpair]
      simp

/-- If a finite frontier is invariant under the slot-label involution, its
pairing defect is empty. -/
theorem collisionInvolutionDefectPart_eq_empty_of_invariant
    (F : Finset TwoPrimeCollisionState)
    (hinv : ∀ s : TwoPrimeCollisionState,
      s ∈ F ↔ collisionExponentStateInvolution s ∈ F) :
    collisionInvolutionDefectPart F = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have hdata := Finset.mem_filter.mp hs
  exact hdata.2 ((hinv s).mp hdata.1)

/-- Under exact frontier invariance only the fixed-point sum remains. -/
theorem sum_collisionFrontier_eq_fixed_of_invariant
    {A : Type*} [AddCommGroup A]
    (F : Finset TwoPrimeCollisionState)
    (w : TwoPrimeCollisionState → A)
    (hpair : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
        w (collisionExponentStateInvolution s) = -w s)
    (hinv : ∀ s : TwoPrimeCollisionState,
      s ∈ F ↔ collisionExponentStateInvolution s ∈ F) :
    (∑ s ∈ F, w s) =
      ∑ s ∈ collisionInvolutionFixedPart F, w s := by
  rw [sum_collisionFrontier_eq_fixed_add_defect F w hpair,
    collisionInvolutionDefectPart_eq_empty_of_invariant F hinv]
  simp

/-- The slot-labelled physical incomplete-period frontier.  It is the preimage
of the usual residue cutoff under the CRT realization of the nine labels. -/
def collisionExponentStatePrefixFrontier
    (p q K : ℕ) (hcop : Nat.Coprime (p ^ 2) (q ^ 2)) :
    Finset TwoPrimeCollisionState :=
  Finset.univ.filter (fun s =>
    (collisionExponentStateResidue p q hcop s).val <
      K % ((p ^ 2) * (q ^ 2)))

/-- Every label admitted by the slot-labelled physical frontier realizes a
residue in the existing exact `residuePrefixFrontier`. -/
theorem collisionExponentStatePrefixFrontier_residue_mem
    (p q K : ℕ) (hcop : Nat.Coprime (p ^ 2) (q ^ 2))
    [NeZero ((p ^ 2) * (q ^ 2))]
    {s : TwoPrimeCollisionState}
    (hs : s ∈ collisionExponentStatePrefixFrontier p q K hcop) :
    collisionExponentStateResidue p q hcop s ∈
      residuePrefixFrontier ((p ^ 2) * (q ^ 2)) K
        (collisionCRTResidues p q hcop) := by
  unfold residuePrefixFrontier
  apply Finset.mem_filter.mpr
  refine ⟨collisionExponentStateResidue_mem p q hcop s, ?_⟩
  exact (Finset.mem_filter.mp hs).2

/-- Physical-prefix specialization of the exact pairing reduction.  Its only
arithmetic premise is the explicit sign-reversal theorem `hpair` for the weight
being summed. -/
theorem sum_collisionExponentStatePrefixFrontier_eq_fixed_add_defect
    {A : Type*} [AddCommGroup A]
    (p q K : ℕ) (hcop : Nat.Coprime (p ^ 2) (q ^ 2))
    (w : TwoPrimeCollisionState → A)
    (hpair : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
        w (collisionExponentStateInvolution s) = -w s) :
    (∑ s ∈ collisionExponentStatePrefixFrontier p q K hcop, w s) =
      (∑ s ∈ collisionInvolutionFixedPart
        (collisionExponentStatePrefixFrontier p q K hcop), w s) +
      ∑ s ∈ collisionInvolutionDefectPart
        (collisionExponentStatePrefixFrontier p q K hcop), w s := by
  exact sum_collisionFrontier_eq_fixed_add_defect
    (collisionExponentStatePrefixFrontier p q K hcop) w hpair

end RHLean.Arithmetic
