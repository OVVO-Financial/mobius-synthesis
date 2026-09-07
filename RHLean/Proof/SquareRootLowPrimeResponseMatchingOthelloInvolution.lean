import Mathlib
import RHLean.Proof.AlternatingSignMatchingParity
import RHLean.Proof.FiniteOthelloMatching
import RHLean.Proof.SquareRootLowPrimeMatchingFrontierSaturation

/-!
# Response-child matching as one Othello involution

The complete response-child matching already exists as an iterated frontier
construction.  This file packages the same chronology as one self-map: a child
is paired at the first fresh-prime coordinate that removes it, and every child
never removed by the chronology is fixed.

Thus the fixed set of this involution is literally
`squareRootLowPrimeOwnedResponseMatchingFrontier`.  No new arithmetic matching
is introduced; this is the Othello wrapper around the existing response-child
frontier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Canonical lower endpoint whose `ell`-multiple is a specified upper endpoint. -/
noncomputable def squareRootLowPrimeResponsePairPreimage
    (S : Finset ℕ) (ell x : ℕ)
    (h : ∃ y ∈ squareRootLowPrimeResponsePairLower S ell, ell * y = x) : ℕ :=
  Classical.choose h

private theorem squareRootLowPrimeResponsePairPreimage_spec
    {S : Finset ℕ} {ell x : ℕ}
    (h : ∃ y ∈ squareRootLowPrimeResponsePairLower S ell, ell * y = x) :
    squareRootLowPrimeResponsePairPreimage S ell x h ∈
        squareRootLowPrimeResponsePairLower S ell ∧
      ell * squareRootLowPrimeResponsePairPreimage S ell x h = x := by
  exact Classical.choose_spec h

/-- One response-child prime coordinate, completed by fixed points. -/
noncomputable def squareRootLowPrimeResponseStepInvolution
    (S : Finset ℕ) (ell : ℕ) : ℕ → ℕ := fun x =>
  if x ∈ squareRootLowPrimeResponsePairLower S ell then
    ell * x
  else if hupper :
      ∃ y ∈ squareRootLowPrimeResponsePairLower S ell, ell * y = x then
    squareRootLowPrimeResponsePairPreimage S ell x hupper
  else x

private theorem squareRootLowPrimeResponsePairUpper_iff_exists_lower
    {S : Finset ℕ} {ell x : ℕ} :
    x ∈ squareRootLowPrimeResponsePairUpper S ell ↔
      ∃ y ∈ squareRootLowPrimeResponsePairLower S ell, ell * y = x := by
  simp [squareRootLowPrimeResponsePairUpper]

private theorem squareRootLowPrimeResponseStepInvolution_of_lower
    {S : Finset ℕ} {ell x : ℕ}
    (hx : x ∈ squareRootLowPrimeResponsePairLower S ell) :
    squareRootLowPrimeResponseStepInvolution S ell x = ell * x := by
  dsimp only [squareRootLowPrimeResponseStepInvolution]
  rw [if_pos hx]

private theorem squareRootLowPrimeResponseStepInvolution_of_upper
    {S : Finset ℕ} {ell x : ℕ}
    (hx : x ∉ squareRootLowPrimeResponsePairLower S ell)
    (hupper : ∃ y ∈ squareRootLowPrimeResponsePairLower S ell, ell * y = x) :
    squareRootLowPrimeResponseStepInvolution S ell x =
      squareRootLowPrimeResponsePairPreimage S ell x hupper := by
  dsimp only [squareRootLowPrimeResponseStepInvolution]
  rw [if_neg hx, dif_pos hupper]

private theorem squareRootLowPrimeResponseStepInvolution_of_unpaired
    {S : Finset ℕ} {ell x : ℕ}
    (hx : x ∉ squareRootLowPrimeResponsePairLower S ell)
    (hupper : ¬ ∃ y ∈ squareRootLowPrimeResponsePairLower S ell, ell * y = x) :
    squareRootLowPrimeResponseStepInvolution S ell x = x := by
  dsimp only [squareRootLowPrimeResponseStepInvolution]
  rw [if_neg hx, dif_neg hupper]

/-- One response-child involution preserves its ambient carrier. -/
theorem squareRootLowPrimeResponseStepInvolution_mem
    (S : Finset ℕ) (ell : ℕ) {x : ℕ} (hxS : x ∈ S) :
    squareRootLowPrimeResponseStepInvolution S ell x ∈ S := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeResponsePairLower S ell
  · rw [squareRootLowPrimeResponseStepInvolution_of_lower hxLower]
    exact (mem_squareRootLowPrimeResponsePairLower.mp hxLower).2.2
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeResponsePairLower S ell, ell * y = x
    · rw [squareRootLowPrimeResponseStepInvolution_of_upper hxLower hupper]
      exact squareRootLowPrimeResponsePairLower_subset S ell
        (squareRootLowPrimeResponsePairPreimage_spec hupper).1
    · rw [squareRootLowPrimeResponseStepInvolution_of_unpaired hxLower hupper]
      exact hxS

/-- The one-coordinate response-child map is an involution. -/
theorem squareRootLowPrimeResponseStepInvolution_involutive
    (S : Finset ℕ) {ell : ℕ} (hell : 0 < ell) (x : ℕ) :
    squareRootLowPrimeResponseStepInvolution S ell
        (squareRootLowPrimeResponseStepInvolution S ell x) = x := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeResponsePairLower S ell
  · let y := ell * x
    have hyUpper : y ∈ squareRootLowPrimeResponsePairUpper S ell := by
      unfold y squareRootLowPrimeResponsePairUpper
      exact Finset.mem_image.mpr ⟨x, hxLower, rfl⟩
    have hyNotLower : y ∉ squareRootLowPrimeResponsePairLower S ell := by
      intro hyLower
      exact (Finset.disjoint_left.mp
        (squareRootLowPrimeResponsePairLower_disjoint_upper S ell))
        hyLower hyUpper
    have hpre :
        ∃ z ∈ squareRootLowPrimeResponsePairLower S ell, ell * z = y :=
      ⟨x, hxLower, rfl⟩
    have hspec := squareRootLowPrimeResponsePairPreimage_spec hpre
    have hmul :
        ell * squareRootLowPrimeResponsePairPreimage S ell y hpre = ell * x := by
      simpa [y] using hspec.2
    have hback : squareRootLowPrimeResponsePairPreimage S ell y hpre = x :=
      Nat.mul_left_cancel hell hmul
    rw [squareRootLowPrimeResponseStepInvolution_of_lower hxLower]
    change squareRootLowPrimeResponseStepInvolution S ell y = x
    rw [squareRootLowPrimeResponseStepInvolution_of_upper hyNotLower hpre, hback]
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeResponsePairLower S ell, ell * y = x
    · let y := squareRootLowPrimeResponsePairPreimage S ell x hupper
      have hyLower : y ∈ squareRootLowPrimeResponsePairLower S ell :=
        (squareRootLowPrimeResponsePairPreimage_spec hupper).1
      have hyExt : ell * y = x :=
        (squareRootLowPrimeResponsePairPreimage_spec hupper).2
      rw [squareRootLowPrimeResponseStepInvolution_of_upper hxLower hupper]
      change squareRootLowPrimeResponseStepInvolution S ell y = x
      rw [squareRootLowPrimeResponseStepInvolution_of_lower hyLower, hyExt]
    · rw [squareRootLowPrimeResponseStepInvolution_of_unpaired hxLower hupper,
        squareRootLowPrimeResponseStepInvolution_of_unpaired hxLower hupper]

/-- One-step fixed points are exactly children outside that paired population. -/
theorem squareRootLowPrimeResponseStepInvolution_eq_self_iff
    (S : Finset ℕ) (ell : ℕ) {x : ℕ} :
    squareRootLowPrimeResponseStepInvolution S ell x = x ↔
      x ∉ squareRootLowPrimeResponsePaired S ell := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeResponsePairLower S ell
  · have hxPaired : x ∈ squareRootLowPrimeResponsePaired S ell :=
      Finset.mem_union.mpr (Or.inl hxLower)
    have hne : ell * x ≠ x := by
      intro heq
      have hxUpper : x ∈ squareRootLowPrimeResponsePairUpper S ell := by
        unfold squareRootLowPrimeResponsePairUpper
        exact Finset.mem_image.mpr ⟨x, hxLower, heq⟩
      exact (Finset.disjoint_left.mp
        (squareRootLowPrimeResponsePairLower_disjoint_upper S ell))
        hxLower hxUpper
    rw [squareRootLowPrimeResponseStepInvolution_of_lower hxLower]
    exact ⟨fun h => (hne h).elim, fun h => (h hxPaired).elim⟩
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeResponsePairLower S ell, ell * y = x
    · have hxUpper : x ∈ squareRootLowPrimeResponsePairUpper S ell :=
        squareRootLowPrimeResponsePairUpper_iff_exists_lower.mpr hupper
      have hxPaired : x ∈ squareRootLowPrimeResponsePaired S ell :=
        Finset.mem_union.mpr (Or.inr hxUpper)
      have hspec := squareRootLowPrimeResponsePairPreimage_spec hupper
      have hne : squareRootLowPrimeResponsePairPreimage S ell x hupper ≠ x := by
        intro heq
        have hxLower' : x ∈ squareRootLowPrimeResponsePairLower S ell := by
          rw [← heq]
          exact hspec.1
        exact hxLower hxLower'
      rw [squareRootLowPrimeResponseStepInvolution_of_upper hxLower hupper]
      exact ⟨fun h => (hne h).elim, fun h => (h hxPaired).elim⟩
    · have hxNotUpper : x ∉ squareRootLowPrimeResponsePairUpper S ell := by
        intro hxUpper
        exact hupper (squareRootLowPrimeResponsePairUpper_iff_exists_lower.mp hxUpper)
      have hxNotPaired : x ∉ squareRootLowPrimeResponsePaired S ell := by
        intro hx
        rcases Finset.mem_union.mp hx with h | h
        · exact hxLower h
        · exact hxNotUpper h
      rw [squareRootLowPrimeResponseStepInvolution_of_unpaired hxLower hupper]
      exact ⟨fun _ => hxNotPaired, fun _ => rfl⟩

/-- Moved one-step children reverse Möbius sign. -/
theorem squareRootLowPrimeResponseStepInvolution_weight_neg
    (S : Finset ℕ) {ell : ℕ} (hell : ell.Prime) (x : ℕ)
    (hne : squareRootLowPrimeResponseStepInvolution S ell x ≠ x) :
    μ (squareRootLowPrimeResponseStepInvolution S ell x) = -μ x := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeResponsePairLower S ell
  · rw [squareRootLowPrimeResponseStepInvolution_of_lower hxLower]
    exact moebius_prime_mul_eq_neg_of_not_dvd hell
      (mem_squareRootLowPrimeResponsePairLower.mp hxLower).2.1
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeResponsePairLower S ell, ell * y = x
    · have hspec := squareRootLowPrimeResponsePairPreimage_spec hupper
      have hforward := moebius_prime_mul_eq_neg_of_not_dvd hell
        (mem_squareRootLowPrimeResponsePairLower.mp hspec.1).2.1
      rw [hspec.2] at hforward
      rw [squareRootLowPrimeResponseStepInvolution_of_upper hxLower hupper]
      omega
    · exact (hne
        (squareRootLowPrimeResponseStepInvolution_of_unpaired hxLower hupper)).elim

/-- Complete response-child chronology, pairing each child at its first removal. -/
noncomputable def squareRootLowPrimeResponseMatchingInvolution :
    List ℕ → Finset ℕ → ℕ → ℕ
  | [], _S => id
  | ell :: ells, S => fun x =>
      if x ∈ squareRootLowPrimeResponsePaired S ell then
        squareRootLowPrimeResponseStepInvolution S ell x
      else
        squareRootLowPrimeResponseMatchingInvolution ells
          (squareRootLowPrimeResponseFrontierStep S ell) x

/-- The global response-child chronology preserves its original carrier. -/
theorem squareRootLowPrimeResponseMatchingInvolution_mem
    (ells : List ℕ) (S : Finset ℕ) {x : ℕ} (hxS : x ∈ S) :
    squareRootLowPrimeResponseMatchingInvolution ells S x ∈ S := by
  induction ells generalizing S x with
  | nil => simpa [squareRootLowPrimeResponseMatchingInvolution] using hxS
  | cons ell ells ih =>
      by_cases hxPaired : x ∈ squareRootLowPrimeResponsePaired S ell
      · rw [squareRootLowPrimeResponseMatchingInvolution]
        simp only [hxPaired, if_true]
        exact squareRootLowPrimeResponseStepInvolution_mem S ell hxS
      · have hxFrontier : x ∈ squareRootLowPrimeResponseFrontierStep S ell :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        have hrec := ih (S := squareRootLowPrimeResponseFrontierStep S ell) hxFrontier
        rw [squareRootLowPrimeResponseMatchingInvolution]
        simp only [hxPaired, if_false]
        exact squareRootLowPrimeResponseFrontierStep_subset S ell hrec

/-- The global response-child chronology is involutive. -/
theorem squareRootLowPrimeResponseMatchingInvolution_involutive
    (ells : List ℕ) (S : Finset ℕ)
    (hpos : ∀ ell ∈ ells, 0 < ell)
    {x : ℕ} (hxS : x ∈ S) :
    squareRootLowPrimeResponseMatchingInvolution ells S
        (squareRootLowPrimeResponseMatchingInvolution ells S x) = x := by
  induction ells generalizing S x with
  | nil => simp [squareRootLowPrimeResponseMatchingInvolution]
  | cons ell ells ih =>
      have hell : 0 < ell := hpos ell (by simp)
      have hrest : ∀ q ∈ ells, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      by_cases hxPaired : x ∈ squareRootLowPrimeResponsePaired S ell
      · let y := squareRootLowPrimeResponseStepInvolution S ell x
        have hyS : y ∈ S :=
          squareRootLowPrimeResponseStepInvolution_mem S ell
            (squareRootLowPrimeResponsePaired_subset S ell hxPaired)
        have hyPaired : y ∈ squareRootLowPrimeResponsePaired S ell := by
          by_contra hnot
          have hyFixed : squareRootLowPrimeResponseStepInvolution S ell y = y :=
            (squareRootLowPrimeResponseStepInvolution_eq_self_iff S ell (x := y)).mpr hnot
          have hback := squareRootLowPrimeResponseStepInvolution_involutive S hell x
          change squareRootLowPrimeResponseStepInvolution S ell y = x at hback
          rw [hyFixed] at hback
          exact hnot (hback.symm ▸ hxPaired)
        rw [squareRootLowPrimeResponseMatchingInvolution]
        simp only [hxPaired, if_true]
        change squareRootLowPrimeResponseMatchingInvolution (ell :: ells) S y = x
        rw [squareRootLowPrimeResponseMatchingInvolution]
        simp only [hyPaired, if_true]
        exact squareRootLowPrimeResponseStepInvolution_involutive S hell x
      · have hxFrontier : x ∈ squareRootLowPrimeResponseFrontierStep S ell :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        let y := squareRootLowPrimeResponseMatchingInvolution ells
          (squareRootLowPrimeResponseFrontierStep S ell) x
        have hyFrontier : y ∈ squareRootLowPrimeResponseFrontierStep S ell :=
          squareRootLowPrimeResponseMatchingInvolution_mem ells
            (squareRootLowPrimeResponseFrontierStep S ell) hxFrontier
        have hyNotPaired : y ∉ squareRootLowPrimeResponsePaired S ell :=
          (Finset.mem_sdiff.mp hyFrontier).2
        have hrec := ih
          (S := squareRootLowPrimeResponseFrontierStep S ell) hrest hxFrontier
        rw [squareRootLowPrimeResponseMatchingInvolution]
        simp only [hxPaired, if_false]
        change squareRootLowPrimeResponseMatchingInvolution (ell :: ells) S y = x
        rw [squareRootLowPrimeResponseMatchingInvolution]
        simp only [hyNotPaired, if_false]
        exact hrec

/-- Every moved global response child reverses Möbius sign. -/
theorem squareRootLowPrimeResponseMatchingInvolution_weight_neg
    (ells : List ℕ) (S : Finset ℕ)
    (hprime : ∀ ell ∈ ells, ell.Prime)
    {x : ℕ} (hxS : x ∈ S)
    (hne : squareRootLowPrimeResponseMatchingInvolution ells S x ≠ x) :
    μ (squareRootLowPrimeResponseMatchingInvolution ells S x) = -μ x := by
  induction ells generalizing S x with
  | nil => simp [squareRootLowPrimeResponseMatchingInvolution] at hne
  | cons ell ells ih =>
      have hell : ell.Prime := hprime ell (by simp)
      have hrest : ∀ q ∈ ells, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      by_cases hxPaired : x ∈ squareRootLowPrimeResponsePaired S ell
      · have hstepNe : squareRootLowPrimeResponseStepInvolution S ell x ≠ x :=
          fun h =>
            (squareRootLowPrimeResponseStepInvolution_eq_self_iff S ell).mp h hxPaired
        rw [squareRootLowPrimeResponseMatchingInvolution]
        simp only [hxPaired, if_true]
        exact squareRootLowPrimeResponseStepInvolution_weight_neg S hell x hstepNe
      · have hxFrontier : x ∈ squareRootLowPrimeResponseFrontierStep S ell :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        rw [squareRootLowPrimeResponseMatchingInvolution] at hne ⊢
        simp only [hxPaired, if_false] at hne ⊢
        exact ih (S := squareRootLowPrimeResponseFrontierStep S ell)
          hrest hxFrontier hne

/-- The fixed set of the response-child chronology is exactly its iterated frontier. -/
theorem signMatchingFixedPart_responseMatching_eq_frontier
    (ells : List ℕ) (S : Finset ℕ)
    (hpos : ∀ ell ∈ ells, 0 < ell) :
    signMatchingFixedPart S
        (squareRootLowPrimeResponseMatchingInvolution ells S) =
      squareRootLowPrimeResponseMatchingFrontier ells S := by
  classical
  induction ells generalizing S with
  | nil =>
      ext x
      simp [signMatchingFixedPart, squareRootLowPrimeResponseMatchingInvolution,
        squareRootLowPrimeResponseMatchingFrontier]
  | cons ell ells ih =>
      have hrest : ∀ q ∈ ells, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      ext x
      simp only [mem_signMatchingFixedPart]
      by_cases hxS : x ∈ S
      · by_cases hxPaired : x ∈ squareRootLowPrimeResponsePaired S ell
        · have hstepNe : squareRootLowPrimeResponseStepInvolution S ell x ≠ x :=
            fun h =>
              (squareRootLowPrimeResponseStepInvolution_eq_self_iff S ell).mp h hxPaired
          have hxNotFrontier :
              x ∉ squareRootLowPrimeResponseMatchingFrontier (ell :: ells) S := by
            intro hx
            have hxStep := squareRootLowPrimeResponseMatchingFrontier_subset ells
              (squareRootLowPrimeResponseFrontierStep S ell) hx
            exact (Finset.mem_sdiff.mp hxStep).2 hxPaired
          rw [squareRootLowPrimeResponseMatchingInvolution]
          simp only [hxPaired, if_true]
          exact ⟨fun h => (hstepNe h.2).elim,
            fun h => (hxNotFrontier h).elim⟩
        · have hxStep : x ∈ squareRootLowPrimeResponseFrontierStep S ell :=
            Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
          have hih := Finset.ext_iff.mp
            (ih (S := squareRootLowPrimeResponseFrontierStep S ell) hrest) x
          simp only [mem_signMatchingFixedPart] at hih
          have hreciff :
              squareRootLowPrimeResponseMatchingInvolution ells
                    (squareRootLowPrimeResponseFrontierStep S ell) x = x ↔
                x ∈ squareRootLowPrimeResponseMatchingFrontier ells
                  (squareRootLowPrimeResponseFrontierStep S ell) := by
            constructor
            · intro hrec
              exact hih.mp ⟨hxStep, hrec⟩
            · intro hfront
              exact (hih.mpr hfront).2
          rw [squareRootLowPrimeResponseMatchingInvolution]
          simp only [hxPaired, if_false]
          change (x ∈ S ∧
              squareRootLowPrimeResponseMatchingInvolution ells
                (squareRootLowPrimeResponseFrontierStep S ell) x = x) ↔
            x ∈ squareRootLowPrimeResponseMatchingFrontier ells
              (squareRootLowPrimeResponseFrontierStep S ell)
          rw [hreciff]
          simp [hxS]
      · have hxNotFrontier :
          x ∉ squareRootLowPrimeResponseMatchingFrontier (ell :: ells) S :=
          fun hx => hxS
            (squareRootLowPrimeResponseMatchingFrontier_subset (ell :: ells) S hx)
        have hxNotPaired : x ∉ squareRootLowPrimeResponsePaired S ell :=
          fun hx => hxS (squareRootLowPrimeResponsePaired_subset S ell hx)
        rw [squareRootLowPrimeResponseMatchingInvolution]
        simp only [hxNotPaired, if_false]
        exact ⟨fun h => (hxS h.1).elim, fun h => (hxNotFrontier h).elim⟩

/-- Canonical response-child Othello mate on the complete owned child carrier. -/
noncomputable def squareRootLowPrimeOwnedResponseMatchingMate
    (R K U : ℕ) : ℕ → ℕ :=
  squareRootLowPrimeResponseMatchingInvolution
    (squareRootLowPrimeFreshPrimeList K U)
    (squareRootLowPrimeOwnedResponseChildren R K U)

/-- The owned response-child mate preserves the exact child carrier. -/
theorem squareRootLowPrimeOwnedResponseMatchingMate_mem
    {R K U n : ℕ}
    (hn : n ∈ squareRootLowPrimeOwnedResponseChildren R K U) :
    squareRootLowPrimeOwnedResponseMatchingMate R K U n ∈
      squareRootLowPrimeOwnedResponseChildren R K U := by
  exact squareRootLowPrimeResponseMatchingInvolution_mem _ _ hn

/-- The owned response-child mate is involutive. -/
theorem squareRootLowPrimeOwnedResponseMatchingMate_involutive
    {R K U n : ℕ}
    (hn : n ∈ squareRootLowPrimeOwnedResponseChildren R K U) :
    squareRootLowPrimeOwnedResponseMatchingMate R K U
        (squareRootLowPrimeOwnedResponseMatchingMate R K U n) = n := by
  apply squareRootLowPrimeResponseMatchingInvolution_involutive
    (squareRootLowPrimeFreshPrimeList K U)
    (squareRootLowPrimeOwnedResponseChildren R K U)
  · intro ell hell
    exact (prime_of_mem_squareRootLowPrimeFreshPrimeList hell).pos
  · exact hn

/-- Moved owned response children reverse native Möbius sign. -/
theorem squareRootLowPrimeOwnedResponseMatchingMate_weight_neg
    {R K U n : ℕ}
    (hn : n ∈ squareRootLowPrimeOwnedResponseChildren R K U)
    (hne : squareRootLowPrimeOwnedResponseMatchingMate R K U n ≠ n) :
    μ (squareRootLowPrimeOwnedResponseMatchingMate R K U n) = -μ n := by
  apply squareRootLowPrimeResponseMatchingInvolution_weight_neg
    (squareRootLowPrimeFreshPrimeList K U)
    (squareRootLowPrimeOwnedResponseChildren R K U)
  · intro ell hell
    exact prime_of_mem_squareRootLowPrimeFreshPrimeList hell
  · exact hn
  · exact hne

/-- The owned child mate has exactly the already-defined response matching frontier
as its fixed set. -/
theorem signMatchingFixedPart_ownedResponseMatchingMate_eq_frontier
    (R K U : ℕ) :
    signMatchingFixedPart
        (squareRootLowPrimeOwnedResponseChildren R K U)
        (squareRootLowPrimeOwnedResponseMatchingMate R K U) =
      squareRootLowPrimeOwnedResponseMatchingFrontier R K U := by
  unfold squareRootLowPrimeOwnedResponseMatchingMate
    squareRootLowPrimeOwnedResponseMatchingFrontier
  apply signMatchingFixedPart_responseMatching_eq_frontier
  intro ell hell
  exact (prime_of_mem_squareRootLowPrimeFreshPrimeList hell).pos

end RHLean.Proof