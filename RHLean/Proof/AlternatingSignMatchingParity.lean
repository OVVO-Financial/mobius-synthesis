import Mathlib

/-!
# Alternating sign-matching parity

The Othello-style invariant needed by the square-root low-prime argument is
parity of a complete alternating component, not raw frontier cardinality.
This file isolates the finite combinatorial kernel in the form most useful for
formal transport: a sign-reversing involution cancels every moved state, so the
signed mass of the whole finite carrier is exactly the mass of its fixed set.
Two such involutions on the same signed carrier therefore transfer signed mass
between their fixed sets.  This is the elementary finite core of the
Garsia--Milne involution principle.

No arithmetic, estimate, choice of encoding, or asymptotic input occurs here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Fixed states of a self-map on a finite carrier. -/
def signMatchingFixedPart {α : Type*} [DecidableEq α]
    (S : Finset α) (τ : α → α) : Finset α :=
  S.filter fun x => τ x = x

/-- Moved states of a self-map on a finite carrier. -/
def signMatchingMovedPart {α : Type*} [DecidableEq α]
    (S : Finset α) (τ : α → α) : Finset α :=
  S.filter fun x => τ x ≠ x

@[simp] theorem mem_signMatchingFixedPart
    {α : Type*} [DecidableEq α] {S : Finset α} {τ : α → α} {x : α} :
    x ∈ signMatchingFixedPart S τ ↔ x ∈ S ∧ τ x = x := by
  simp [signMatchingFixedPart]

@[simp] theorem mem_signMatchingMovedPart
    {α : Type*} [DecidableEq α] {S : Finset α} {τ : α → α} {x : α} :
    x ∈ signMatchingMovedPart S τ ↔ x ∈ S ∧ τ x ≠ x := by
  simp [signMatchingMovedPart]

/-- Fixed and moved states exhaust the carrier. -/
theorem signMatchingMoved_union_fixed
    {α : Type*} [DecidableEq α]
    (S : Finset α) (τ : α → α) :
    signMatchingMovedPart S τ ∪ signMatchingFixedPart S τ = S := by
  ext x
  by_cases hxS : x ∈ S
  · by_cases hfix : τ x = x <;> simp [hxS, hfix]
  · simp [hxS]

/-- Fixed and moved states are disjoint. -/
theorem signMatchingMoved_disjoint_fixed
    {α : Type*} [DecidableEq α]
    (S : Finset α) (τ : α → α) :
    Disjoint (signMatchingMovedPart S τ) (signMatchingFixedPart S τ) := by
  rw [Finset.disjoint_left]
  intro x hm hf
  exact (mem_signMatchingMovedPart.mp hm).2
    (mem_signMatchingFixedPart.mp hf).2

/-- Every moved orbit of a sign-reversing involution cancels exactly. -/
theorem sum_signMatchingMovedPart_eq_zero
    {α G : Type*} [DecidableEq α] [AddCommGroup G]
    (S : Finset α) (τ : α → α) (w : α → G)
    (hmem : ∀ x ∈ S, τ x ∈ S)
    (hinv : ∀ x ∈ S, τ (τ x) = x)
    (hneg : ∀ x ∈ S, τ x ≠ x → w (τ x) = -w x) :
    (∑ x ∈ signMatchingMovedPart S τ, w x) = 0 := by
  classical
  exact Finset.sum_involution
    (s := signMatchingMovedPart S τ) (f := w)
    (fun x _hx => τ x)
    (fun x hx => by
      have hxS := (mem_signMatchingMovedPart.mp hx).1
      have hxne := (mem_signMatchingMovedPart.mp hx).2
      rw [hneg x hxS hxne]
      simp)
    (fun x hx _hw => (mem_signMatchingMovedPart.mp hx).2)
    (fun x hx => by
      have hxS := (mem_signMatchingMovedPart.mp hx).1
      have hxne := (mem_signMatchingMovedPart.mp hx).2
      apply mem_signMatchingMovedPart.mpr
      refine ⟨hmem x hxS, ?_⟩
      intro hfix
      have hback := hinv x hxS
      rw [hfix] at hback
      exact hxne hback)
    (fun x hx =>
      hinv x (mem_signMatchingMovedPart.mp hx).1)

/-- **Fixed-set parity principle.**  A sign-reversing involution moves zero
net mass, so the complete finite signed carrier has exactly the mass of its
fixed states. -/
theorem sum_eq_sum_signMatchingFixedPart
    {α G : Type*} [DecidableEq α] [AddCommGroup G]
    (S : Finset α) (τ : α → α) (w : α → G)
    (hmem : ∀ x ∈ S, τ x ∈ S)
    (hinv : ∀ x ∈ S, τ (τ x) = x)
    (hneg : ∀ x ∈ S, τ x ≠ x → w (τ x) = -w x) :
    (∑ x ∈ S, w x) =
      ∑ x ∈ signMatchingFixedPart S τ, w x := by
  have hpart := signMatchingMoved_union_fixed S τ
  have hdisj := signMatchingMoved_disjoint_fixed S τ
  calc
    (∑ x ∈ S, w x) =
        ∑ x ∈ signMatchingMovedPart S τ ∪ signMatchingFixedPart S τ, w x := by
      rw [hpart]
    _ = (∑ x ∈ signMatchingMovedPart S τ, w x) +
        ∑ x ∈ signMatchingFixedPart S τ, w x := by
      rw [Finset.sum_union hdisj]
    _ = ∑ x ∈ signMatchingFixedPart S τ, w x := by
      rw [sum_signMatchingMovedPart_eq_zero S τ w hmem hinv hneg]
      simp

/-- **Two-involution/Othello transfer.**  Two sign-reversing involutions on the
same finite signed carrier have fixed sets of exactly the same signed mass.
Equivalently, following the alternating forced line can change the exposed
representative but not the net parity unit. -/
theorem sum_signMatchingFixedPart_eq_of_two_involutions
    {α G : Type*} [DecidableEq α] [AddCommGroup G]
    (S : Finset α) (τ σ : α → α) (w : α → G)
    (hτmem : ∀ x ∈ S, τ x ∈ S)
    (hτinv : ∀ x ∈ S, τ (τ x) = x)
    (hτneg : ∀ x ∈ S, τ x ≠ x → w (τ x) = -w x)
    (hσmem : ∀ x ∈ S, σ x ∈ S)
    (hσinv : ∀ x ∈ S, σ (σ x) = x)
    (hσneg : ∀ x ∈ S, σ x ≠ x → w (σ x) = -w x) :
    (∑ x ∈ signMatchingFixedPart S τ, w x) =
      ∑ x ∈ signMatchingFixedPart S σ, w x := by
  rw [← sum_eq_sum_signMatchingFixedPart S τ w hτmem hτinv hτneg,
    sum_eq_sum_signMatchingFixedPart S σ w hσmem hσinv hσneg]

end RHLean.Proof