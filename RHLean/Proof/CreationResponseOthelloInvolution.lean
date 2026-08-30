import Mathlib
import RHLean.Proof.FiniteOthelloMatching
import RHLean.Proof.CreationResponseFrontierCancellation

/-!
# Creation-response matching as a finite Othello involution

A matched creation state moves to its response image and a response state in
that image moves back to the unique creation preimage. Unmatched states are
fixed. This is the same finite matching used by the creation-response
cancellation theorem, packaged on one tagged carrier for `FiniteOthelloMatching`.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Tagged carrier containing all creation and response states. -/
def creationResponseOthelloCarrier
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (C : Finset α) (R : Finset β) : Finset (Sum α β) :=
  C.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    R.map ⟨Sum.inr, Sum.inr_injective⟩

/-- The unique matched creation preimage of a response state in `M.image φ`. -/
noncomputable def creationResponseOthelloPreimage
    {α β : Type*} [DecidableEq α]
    (M : Finset α) (φ : α → β) (r : β)
    (h : ∃ c ∈ M, φ c = r) : α :=
  Classical.choose h

private theorem creationResponseOthelloPreimage_spec
    {α β : Type*} [DecidableEq α]
    {M : Finset α} {φ : α → β} {r : β}
    (h : ∃ c ∈ M, φ c = r) :
    creationResponseOthelloPreimage M φ r h ∈ M ∧
      φ (creationResponseOthelloPreimage M φ r h) = r := by
  exact Classical.choose_spec h

/-- Complete the partial creation-response matching by fixed points. -/
noncomputable def creationResponseOthelloMate
    {α β : Type*} [DecidableEq α]
    (M : Finset α) (φ : α → β) : Sum α β → Sum α β
  | .inl c => if c ∈ M then .inr (φ c) else .inl c
  | .inr r =>
      if h : ∃ c ∈ M, φ c = r then
        .inl (creationResponseOthelloPreimage M φ r h)
      else .inr r

/-- The mate preserves the complete tagged carrier. -/
theorem creationResponseOthelloMate_mem
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (C M : Finset α) (R : Finset β) (φ : α → β)
    (hMC : M ⊆ C)
    (hmap : ∀ c ∈ M, φ c ∈ R)
    {x : Sum α β} (hx : x ∈ creationResponseOthelloCarrier C R) :
    creationResponseOthelloMate M φ x ∈ creationResponseOthelloCarrier C R := by
  classical
  rcases x with c | r
  · have hcC : c ∈ C := by
      simpa [creationResponseOthelloCarrier] using hx
    by_cases hcM : c ∈ M
    · simp [creationResponseOthelloMate, hcM,
        creationResponseOthelloCarrier, hmap c hcM]
    · simp [creationResponseOthelloMate, hcM,
        creationResponseOthelloCarrier, hcC]
  · have hrR : r ∈ R := by
      simpa [creationResponseOthelloCarrier] using hx
    by_cases hpre : ∃ c ∈ M, φ c = r
    · have hspec := creationResponseOthelloPreimage_spec hpre
      have hcC := hMC hspec.1
      simp [creationResponseOthelloMate, hpre,
        creationResponseOthelloCarrier, hcC]
    · simp [creationResponseOthelloMate, hpre,
        creationResponseOthelloCarrier, hrR]

/-- Injectivity of the matched map makes the completed matching involutive. -/
theorem creationResponseOthelloMate_involutive
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (M : Finset α) (φ : α → β)
    (hinj : Set.InjOn φ M) (x : Sum α β) :
    creationResponseOthelloMate M φ (creationResponseOthelloMate M φ x) = x := by
  classical
  rcases x with c | r
  · by_cases hcM : c ∈ M
    · have hpre : ∃ a ∈ M, φ a = φ c := ⟨c, hcM, rfl⟩
      have hspec := creationResponseOthelloPreimage_spec hpre
      have heq : creationResponseOthelloPreimage M φ (φ c) hpre = c :=
        hinj hspec.1 hcM hspec.2
      simp [creationResponseOthelloMate, hcM, hpre, heq]
    · simp [creationResponseOthelloMate, hcM]
  · by_cases hpre : ∃ c ∈ M, φ c = r
    · have hspec := creationResponseOthelloPreimage_spec hpre
      simp [creationResponseOthelloMate, hpre, hspec.1, hspec.2]
    · simp [creationResponseOthelloMate, hpre]

/-- Tagged weight retaining each side's native sign. -/
def creationResponseOthelloWeight
    {α β G : Type*} (wC : α → G) (wR : β → G) : Sum α β → G
  | .inl c => wC c
  | .inr r => wR r

/-- Every moved creation-response edge reverses weight. -/
theorem creationResponseOthelloMate_weight_neg
    {α β G : Type*} [DecidableEq α] [AddCommGroup G]
    (M : Finset α) (φ : α → β) (wC : α → G) (wR : β → G)
    (_hinj : Set.InjOn φ M)
    (hcancel : ∀ c ∈ M, wC c + wR (φ c) = 0)
    (x : Sum α β)
    (hne : creationResponseOthelloMate M φ x ≠ x) :
    creationResponseOthelloWeight wC wR (creationResponseOthelloMate M φ x) =
      -creationResponseOthelloWeight wC wR x := by
  classical
  rcases x with c | r
  · by_cases hcM : c ∈ M
    · have hpair := hcancel c hcM
      simp [creationResponseOthelloMate, hcM,
        creationResponseOthelloWeight]
      exact eq_neg_of_add_eq_zero_right hpair
    · simp [creationResponseOthelloMate, hcM] at hne
  · by_cases hpre : ∃ c ∈ M, φ c = r
    · have hspec := creationResponseOthelloPreimage_spec hpre
      have hpair := hcancel _ hspec.1
      rw [hspec.2] at hpair
      simp [creationResponseOthelloMate, hpre,
        creationResponseOthelloWeight]
      exact eq_neg_of_add_eq_zero_left hpair
    · simp [creationResponseOthelloMate, hpre] at hne

/-- Fixed states are exactly the unmatched tagged frontier. -/
theorem finiteOthelloStablePart_creationResponse_eq_frontier
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (C M : Finset α) (R : Finset β) (φ : α → β)
    (hMC : M ⊆ C)
    (_hinj : Set.InjOn φ M) :
    finiteOthelloStablePart
        (creationResponseOthelloCarrier C R)
        (creationResponseOthelloMate M φ) =
      creationResponseTaggedFrontier C M R φ := by
  classical
  ext x
  rcases x with c | r
  · simp only [finiteOthelloStablePart, Finset.mem_filter]
    have htag : Sum.inl c ∈ creationResponseOthelloCarrier C R ↔ c ∈ C := by
      simp [creationResponseOthelloCarrier]
    rw [htag]
    by_cases hcM : c ∈ M
    · have hcC := hMC hcM
      simp [creationResponseOthelloMate, hcM,
        creationResponseTaggedFrontier, hcC]
    · simp [creationResponseOthelloMate, hcM,
        creationResponseTaggedFrontier]
  · simp only [finiteOthelloStablePart, Finset.mem_filter]
    have htag : Sum.inr r ∈ creationResponseOthelloCarrier C R ↔ r ∈ R := by
      simp [creationResponseOthelloCarrier]
    rw [htag]
    have himage : r ∈ creationResponseMatchedImage M φ ↔
        ∃ c ∈ M, φ c = r := by
      simp [creationResponseMatchedImage]
    by_cases hpre : ∃ c ∈ M, φ c = r
    · have him : r ∈ creationResponseMatchedImage M φ := himage.mpr hpre
      simp [creationResponseOthelloMate, hpre,
        creationResponseTaggedFrontier, him]
    · have hnot : r ∉ creationResponseMatchedImage M φ := by
        simpa [himage] using hpre
      simp [creationResponseOthelloMate, hpre,
        creationResponseTaggedFrontier, hnot]

end RHLean.Proof
