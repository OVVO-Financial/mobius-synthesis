import Mathlib
import RHLean.Proof.CreationResponseFrontierCancellation

/-!
# Real-valued bounds after exact creation-to-response cancellation

This module is the ordered real counterpart of the exact additive cancellation
theorem.  It is used after the shallow creation and deep response carriers have
been expanded into literal unit seats.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Unit real weights bound the paired total by the two unmatched populations. -/
theorem abs_creationResponse_realSum_le_unmatchedCards
    {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (C M : Finset α) (R : Finset β)
    (φ : α → β) (wC : α → ℝ) (wR : β → ℝ)
    (hMC : M ⊆ C)
    (hmap : ∀ c ∈ M, φ c ∈ R)
    (hinj : Set.InjOn φ M)
    (hcancel : ∀ c ∈ M, wC c + wR (φ c) = 0)
    (hCunit : ∀ c ∈ C, |wC c| ≤ 1)
    (hRunit : ∀ r ∈ R, |wR r| ≤ 1) :
    |(∑ c ∈ C, wC c) + (∑ r ∈ R, wR r)| ≤
      (((C \ M).card +
        (R \ creationResponseMatchedImage M φ).card : ℕ) : ℝ) := by
  rw [creationResponse_sum_eq_unmatchedFrontiers
    C M R φ wC wR hMC hmap hinj hcancel]
  calc
    |(∑ c ∈ C \ M, wC c) +
        ∑ r ∈ R \ creationResponseMatchedImage M φ, wR r| ≤
      |∑ c ∈ C \ M, wC c| +
        |∑ r ∈ R \ creationResponseMatchedImage M φ, wR r| :=
      abs_add_le _ _
    _ ≤ (∑ c ∈ C \ M, |wC c|) +
        ∑ r ∈ R \ creationResponseMatchedImage M φ, |wR r| := by
      exact add_le_add
        (Finset.abs_sum_le_sum_abs _ _)
        (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (∑ _c ∈ C \ M, (1 : ℝ)) +
        ∑ _r ∈ R \ creationResponseMatchedImage M φ, (1 : ℝ) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro c hc
        exact hCunit c (Finset.mem_sdiff.mp hc).1
      · apply Finset.sum_le_sum
        intro r hr
        exact hRunit r (Finset.mem_sdiff.mp hr).1
    _ = (((C \ M).card +
        (R \ creationResponseMatchedImage M φ).card : ℕ) : ℝ) := by
      simp

/-- A common finite owner box bounds the real paired total. -/
theorem abs_creationResponse_realSum_le_boxCard
    {α β δ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq δ]
    (C M : Finset α) (R : Finset β)
    (φ : α → β) (wC : α → ℝ) (wR : β → ℝ)
    (box : Finset δ) (encode : Sum α β → δ)
    (hMC : M ⊆ C)
    (hmap : ∀ c ∈ M, φ c ∈ R)
    (hinj : Set.InjOn φ M)
    (hcancel : ∀ c ∈ M, wC c + wR (φ c) = 0)
    (hCunit : ∀ c ∈ C, |wC c| ≤ 1)
    (hRunit : ∀ r ∈ R, |wR r| ≤ 1)
    (hencodeInj : Set.InjOn encode
      (creationResponseTaggedFrontier C M R φ))
    (hbox : ∀ z ∈ creationResponseTaggedFrontier C M R φ,
      encode z ∈ box) :
    |(∑ c ∈ C, wC c) + (∑ r ∈ R, wR r)| ≤ (box.card : ℝ) := by
  have hfrontier := abs_creationResponse_realSum_le_unmatchedCards
    C M R φ wC wR hMC hmap hinj hcancel hCunit hRunit
  have himage :
      (creationResponseTaggedFrontier C M R φ).image encode ⊆ box := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨z, hz, rfl⟩
    exact hbox z hz
  have hcardImage :
      ((creationResponseTaggedFrontier C M R φ).image encode).card =
        (creationResponseTaggedFrontier C M R φ).card :=
    Finset.card_image_iff.mpr hencodeInj
  have hcard :
      (creationResponseTaggedFrontier C M R φ).card ≤ box.card := by
    rw [← hcardImage]
    exact Finset.card_le_card himage
  rw [card_creationResponseTaggedFrontier] at hcard
  exact hfrontier.trans (by exact_mod_cast hcard)

end RHLean.Proof
