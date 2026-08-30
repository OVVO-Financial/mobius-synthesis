import Mathlib
import RHLean.Proof.CollisionCellFrontierBound

/-!
# Exact creation-to-response frontier cancellation

A quantitative sequential-dissipation theorem must not bound the deep response
carrier by itself: that response is expected to cancel the large shallow
creation.  The correct finite operation is to insert the existing map from a
matched creation population into the response population and remove the paired
states before taking any norm.

For a matched creation subset `M ⊆ C`, an injective map

`φ : M → R`

with opposite weights gives the exact identity

`sum_C wC + sum_R wR
  = sum_{C \ M} wC + sum_{R \ φ(M)} wR`.

Thus only the genuinely unmatched creation and response frontiers need a
cardinality or root-seat bound.  No estimate is used in the cancellation
identity.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Response states occupied by the matched creation population. -/
def creationResponseMatchedImage
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (M : Finset α) (φ : α → β) : Finset β :=
  M.image φ

/-- **Exact finite creation-to-response cancellation.** -/
theorem creationResponse_sum_eq_unmatchedFrontiers
    {α β G : Type*}
    [DecidableEq α] [DecidableEq β] [AddCommGroup G]
    (C M : Finset α) (R : Finset β)
    (φ : α → β) (wC : α → G) (wR : β → G)
    (hMC : M ⊆ C)
    (hmap : ∀ c ∈ M, φ c ∈ R)
    (hinj : Set.InjOn φ M)
    (hcancel : ∀ c ∈ M, wC c + wR (φ c) = 0) :
    (∑ c ∈ C, wC c) + (∑ r ∈ R, wR r) =
      (∑ c ∈ C \ M, wC c) +
        ∑ r ∈ R \ creationResponseMatchedImage M φ, wR r := by
  have himageR : creationResponseMatchedImage M φ ⊆ R := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨c, hc, rfl⟩
    exact hmap c hc
  have hCsplit :
      (∑ c ∈ C \ M, wC c) + (∑ c ∈ M, wC c) =
        ∑ c ∈ C, wC c :=
    Finset.sum_sdiff hMC
  have hRsplit :
      (∑ r ∈ R \ creationResponseMatchedImage M φ, wR r) +
          (∑ r ∈ creationResponseMatchedImage M φ, wR r) =
        ∑ r ∈ R, wR r :=
    Finset.sum_sdiff himageR
  have himageSum :
      (∑ r ∈ creationResponseMatchedImage M φ, wR r) =
        ∑ c ∈ M, wR (φ c) := by
    unfold creationResponseMatchedImage
    apply Finset.sum_image
    intro a ha b hb hab
    exact hinj ha hb hab
  have hpair :
      (∑ c ∈ M, wC c) + (∑ c ∈ M, wR (φ c)) = 0 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ c ∈ M, (wC c + wR (φ c))) =
          ∑ _c ∈ M, (0 : G) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hcancel c hc
      _ = 0 := by simp
  rw [← hCsplit, ← hRsplit, himageSum]
  calc
    _ = (∑ c ∈ C \ M, wC c) +
          (∑ r ∈ R \ creationResponseMatchedImage M φ, wR r) +
          ((∑ c ∈ M, wC c) + ∑ c ∈ M, wR (φ c)) := by
      abel
    _ = _ := by rw [hpair, add_zero]

/-- Integer unit weights give a pure unmatched-population bound. -/
theorem abs_creationResponse_sum_le_unmatchedCards
    {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (C M : Finset α) (R : Finset β)
    (φ : α → β) (wC : α → ℤ) (wR : β → ℤ)
    (hMC : M ⊆ C)
    (hmap : ∀ c ∈ M, φ c ∈ R)
    (hinj : Set.InjOn φ M)
    (hcancel : ∀ c ∈ M, wC c + wR (φ c) = 0)
    (hCunit : ∀ c ∈ C, |wC c| ≤ 1)
    (hRunit : ∀ r ∈ R, |wR r| ≤ 1) :
    |(∑ c ∈ C, wC c) + (∑ r ∈ R, wR r)| ≤
      ((C \ M).card : ℤ) +
        ((R \ creationResponseMatchedImage M φ).card : ℤ) := by
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
    _ ≤ (∑ _c ∈ C \ M, (1 : ℤ)) +
        ∑ _r ∈ R \ creationResponseMatchedImage M φ, (1 : ℤ) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro c hc
        exact hCunit c (Finset.mem_sdiff.mp hc).1
      · apply Finset.sum_le_sum
        intro r hr
        exact hRunit r (Finset.mem_sdiff.mp hr).1
    _ = ((C \ M).card : ℤ) +
        ((R \ creationResponseMatchedImage M φ).card : ℤ) := by simp

/-- A tagged union keeps the unmatched creation and response populations
separate while allowing one common owner map. -/
def creationResponseTaggedFrontier
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (C M : Finset α) (R : Finset β) (φ : α → β) :
    Finset (Sum α β) :=
  (C \ M).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (R \ creationResponseMatchedImage M φ).map
      ⟨Sum.inr, Sum.inr_injective⟩

/-- The tagged unmatched populations are disjoint and their cardinalities add. -/
theorem card_creationResponseTaggedFrontier
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (C M : Finset α) (R : Finset β) (φ : α → β) :
    (creationResponseTaggedFrontier C M R φ).card =
      (C \ M).card +
        (R \ creationResponseMatchedImage M φ).card := by
  classical
  unfold creationResponseTaggedFrontier
  have hdisj :
      Disjoint ((C \ M).map ⟨Sum.inl, Sum.inl_injective⟩)
        ((R \ creationResponseMatchedImage M φ).map
          ⟨Sum.inr, Sum.inr_injective⟩) := by
    rw [Finset.disjoint_left]
    intro z hzL hzR
    rcases Finset.mem_map.mp hzL with ⟨a, _ha, haz⟩
    rcases Finset.mem_map.mp hzR with ⟨b, _hb, hbz⟩
    cases haz.trans hbz.symm
  rw [Finset.card_union_of_disjoint hdisj]
  simp

/-- An injective encoding of the tagged unmatched frontier into a finite box
turns exact cancellation into a box-cardinality estimate. -/
theorem abs_creationResponse_sum_le_boxCard
    {α β δ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq δ]
    (C M : Finset α) (R : Finset β)
    (φ : α → β) (wC : α → ℤ) (wR : β → ℤ)
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
    |(∑ c ∈ C, wC c) + (∑ r ∈ R, wR r)| ≤ (box.card : ℤ) := by
  have hfrontier := abs_creationResponse_sum_le_unmatchedCards
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
