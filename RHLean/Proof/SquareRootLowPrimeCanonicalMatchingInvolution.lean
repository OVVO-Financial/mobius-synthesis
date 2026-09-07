import Mathlib
import RHLean.Proof.SquareRootLowPrimeProcessedMatchingInvolution
import RHLean.Proof.SquareRootLowPrimeCanonicalLiberty

/-!
# Canonical Euler chronology as one Othello involution

The quantitative canonical matcher in `SquareRootLowPrimeCanonicalLiberty`
removes only genuine Euler edges: a lower state with cofactor `c` may use the
fresh prime `p` only when `P⁺(c) < p`.  This file packages that entire ordered
matching into one sign-reversing involution on the original processed-seat
carrier.

This is the first Othello involution used by the final alternating classifier.
Its fixed set is exactly the canonical Euler terminal frontier.  The second
involution is the descending no-liberty matcher from
`SquareRootLowPrimeOppositeFixedClassification`.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Unique canonical lower endpoint whose `p`-extension is a given upper
endpoint. -/
noncomputable def squareRootLowPrimeProcessedSeatCanonicalPairPreimage
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ)
    (x : SquareRootLowPrimeProcessedState)
    (h : ∃ y ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
      squareRootLowPrimeProcessedSeatExtend p y = x) :
    SquareRootLowPrimeProcessedState :=
  Classical.choose h

private theorem squareRootLowPrimeProcessedSeatCanonicalPairPreimage_spec
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState}
    (h : ∃ y ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
      squareRootLowPrimeProcessedSeatExtend p y = x) :
    squareRootLowPrimeProcessedSeatCanonicalPairPreimage S p x h ∈
        squareRootLowPrimeProcessedSeatCanonicalPairLower S p ∧
      squareRootLowPrimeProcessedSeatExtend p
        (squareRootLowPrimeProcessedSeatCanonicalPairPreimage S p x h) = x := by
  exact Classical.choose_spec h

/-- One canonical Euler prime matching, completed by fixed points. -/
noncomputable def squareRootLowPrimeProcessedSeatCanonicalStepInvolution
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    SquareRootLowPrimeProcessedState → SquareRootLowPrimeProcessedState :=
  fun x =>
    if x ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p then
      squareRootLowPrimeProcessedSeatExtend p x
    else if hupper :
        ∃ y ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
          squareRootLowPrimeProcessedSeatExtend p y = x then
      squareRootLowPrimeProcessedSeatCanonicalPairPreimage S p x hupper
    else x

private theorem squareRootLowPrimeProcessedSeatCanonicalPairUpper_iff_exists_lower
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeProcessedSeatCanonicalPairUpper S p ↔
      ∃ y ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x := by
  simp [squareRootLowPrimeProcessedSeatCanonicalPairUpper]

private theorem squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_lower
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p) :
    squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p x =
      squareRootLowPrimeProcessedSeatExtend p x := by
  dsimp only [squareRootLowPrimeProcessedSeatCanonicalStepInvolution]
  rw [if_pos hx]

private theorem squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_upper
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∉ squareRootLowPrimeProcessedSeatCanonicalPairLower S p)
    (hupper : ∃ y ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
      squareRootLowPrimeProcessedSeatExtend p y = x) :
    squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p x =
      squareRootLowPrimeProcessedSeatCanonicalPairPreimage S p x hupper := by
  dsimp only [squareRootLowPrimeProcessedSeatCanonicalStepInvolution]
  rw [if_neg hx, dif_pos hupper]

private theorem squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_unpaired
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∉ squareRootLowPrimeProcessedSeatCanonicalPairLower S p)
    (hupper : ¬ ∃ y ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
      squareRootLowPrimeProcessedSeatExtend p y = x) :
    squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p x = x := by
  dsimp only [squareRootLowPrimeProcessedSeatCanonicalStepInvolution]
  rw [if_neg hx, dif_neg hupper]

/-- One canonical Euler step preserves the ambient finite carrier. -/
theorem squareRootLowPrimeProcessedSeatCanonicalStepInvolution_mem
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S) :
    squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p x ∈ S := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p
  · rw [squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_lower hxLower]
    have hxGeneric :=
      squareRootLowPrimeProcessedSeatCanonicalPairLower_subset S p hxLower
    exact (mem_squareRootLowPrimeProcessedSeatPairLower.mp hxGeneric).2.2.2
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x
    · rw [squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_upper
        hxLower hupper]
      exact squareRootLowPrimeProcessedSeatPairLower_subset S p
        (squareRootLowPrimeProcessedSeatCanonicalPairLower_subset S p
          (squareRootLowPrimeProcessedSeatCanonicalPairPreimage_spec hupper).1)
    · rw [squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_unpaired
        hxLower hupper]
      exact hxS

/-- The canonical one-step map is an involution. -/
theorem squareRootLowPrimeProcessedSeatCanonicalStepInvolution_involutive
    (S : Finset SquareRootLowPrimeProcessedState) {p : ℕ} (hp : 0 < p)
    (x : SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p
        (squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p x) = x := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p
  · let y := squareRootLowPrimeProcessedSeatExtend p x
    have hyUpper : y ∈ squareRootLowPrimeProcessedSeatCanonicalPairUpper S p := by
      unfold y squareRootLowPrimeProcessedSeatCanonicalPairUpper
      exact Finset.mem_image.mpr ⟨x, hxLower, rfl⟩
    have hyNotLower :
        y ∉ squareRootLowPrimeProcessedSeatCanonicalPairLower S p := by
      intro hyLower
      exact (Finset.disjoint_left.mp
        (squareRootLowPrimeProcessedSeatCanonicalPairLower_disjoint_upper S p))
        hyLower hyUpper
    have hpre :
        ∃ z ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
          squareRootLowPrimeProcessedSeatExtend p z = y :=
      ⟨x, hxLower, rfl⟩
    have hspec := squareRootLowPrimeProcessedSeatCanonicalPairPreimage_spec hpre
    have hback :
        squareRootLowPrimeProcessedSeatCanonicalPairPreimage S p y hpre = x := by
      apply squareRootLowPrimeProcessedSeatExtend_injOn hp
      · exact squareRootLowPrimeProcessedSeatCanonicalPairLower_subset S p hspec.1
      · exact squareRootLowPrimeProcessedSeatCanonicalPairLower_subset S p hxLower
      · exact hspec.2
    rw [squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_lower hxLower]
    change squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p y = x
    rw [squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_upper
      hyNotLower hpre, hback]
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x
    · let y := squareRootLowPrimeProcessedSeatCanonicalPairPreimage S p x hupper
      have hyLower : y ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p :=
        (squareRootLowPrimeProcessedSeatCanonicalPairPreimage_spec hupper).1
      have hyExt : squareRootLowPrimeProcessedSeatExtend p y = x :=
        (squareRootLowPrimeProcessedSeatCanonicalPairPreimage_spec hupper).2
      rw [squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_upper
        hxLower hupper]
      change squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p y = x
      rw [squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_lower
        hyLower, hyExt]
    · rw [squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_unpaired
        hxLower hupper,
      squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_unpaired
        hxLower hupper]

/-- Canonical one-step fixed points are exactly states outside the canonical
paired population. -/
theorem squareRootLowPrimeProcessedSeatCanonicalStepInvolution_eq_self_iff
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ)
    {x : SquareRootLowPrimeProcessedState} :
    squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p x = x ↔
      x ∉ squareRootLowPrimeProcessedSeatCanonicalPaired S p := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p
  · have hxPaired : x ∈ squareRootLowPrimeProcessedSeatCanonicalPaired S p :=
      Finset.mem_union.mpr (Or.inl hxLower)
    have hne : squareRootLowPrimeProcessedSeatExtend p x ≠ x := by
      intro heq
      have hxUpper :
          x ∈ squareRootLowPrimeProcessedSeatCanonicalPairUpper S p := by
        unfold squareRootLowPrimeProcessedSeatCanonicalPairUpper
        exact Finset.mem_image.mpr ⟨x, hxLower, heq⟩
      exact (Finset.disjoint_left.mp
        (squareRootLowPrimeProcessedSeatCanonicalPairLower_disjoint_upper S p))
        hxLower hxUpper
    rw [squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_lower hxLower]
    exact ⟨fun h => (hne h).elim, fun h => (h hxPaired).elim⟩
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x
    · have hxUpper : x ∈ squareRootLowPrimeProcessedSeatCanonicalPairUpper S p :=
        squareRootLowPrimeProcessedSeatCanonicalPairUpper_iff_exists_lower.mpr
          hupper
      have hxPaired : x ∈ squareRootLowPrimeProcessedSeatCanonicalPaired S p :=
        Finset.mem_union.mpr (Or.inr hxUpper)
      have hspec := squareRootLowPrimeProcessedSeatCanonicalPairPreimage_spec hupper
      have hne :
          squareRootLowPrimeProcessedSeatCanonicalPairPreimage S p x hupper ≠ x := by
        intro heq
        have hxLower' :
            x ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p := by
          rw [← heq]
          exact hspec.1
        exact hxLower hxLower'
      rw [squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_upper
        hxLower hupper]
      exact ⟨fun h => (hne h).elim, fun h => (h hxPaired).elim⟩
    · have hxNotUpper :
          x ∉ squareRootLowPrimeProcessedSeatCanonicalPairUpper S p := by
        intro hxUpper
        exact hupper
          (squareRootLowPrimeProcessedSeatCanonicalPairUpper_iff_exists_lower.mp
            hxUpper)
      have hxNotPaired :
          x ∉ squareRootLowPrimeProcessedSeatCanonicalPaired S p := by
        intro hx
        rcases Finset.mem_union.mp hx with h | h
        · exact hxLower h
        · exact hxNotUpper h
      rw [squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_unpaired
        hxLower hupper]
      exact ⟨fun _ => hxNotPaired, fun _ => rfl⟩

/-- Every moved canonical one-step state has opposite processed-seat weight. -/
theorem squareRootLowPrimeProcessedSeatCanonicalStepInvolution_weight_neg
    (S : Finset SquareRootLowPrimeProcessedState) {p : ℕ} (hp : p.Prime)
    (x : SquareRootLowPrimeProcessedState)
    (hne : squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p x ≠ x) :
    squareRootLowPrimeProcessedSeatWeightReal
        (squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p x) =
      -squareRootLowPrimeProcessedSeatWeightReal x := by
  classical
  by_cases hxLower : x ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p
  · rw [squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_lower hxLower]
    exact squareRootLowPrimeProcessedSeatExtend_weight_eq_neg hp
      (squareRootLowPrimeProcessedSeatCanonicalPairLower_subset S p hxLower)
  · by_cases hupper :
      ∃ y ∈ squareRootLowPrimeProcessedSeatCanonicalPairLower S p,
        squareRootLowPrimeProcessedSeatExtend p y = x
    · have hspec := squareRootLowPrimeProcessedSeatCanonicalPairPreimage_spec hupper
      have hforward := squareRootLowPrimeProcessedSeatExtend_weight_eq_neg hp
        (squareRootLowPrimeProcessedSeatCanonicalPairLower_subset S p hspec.1)
      rw [hspec.2] at hforward
      rw [squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_upper
        hxLower hupper]
      linarith
    · exact (hne
        (squareRootLowPrimeProcessedSeatCanonicalStepInvolution_of_unpaired
          hxLower hupper)).elim

/-- Complete canonical Euler chronology, pairing each state at the first
canonical stage that removes it and fixing terminal states. -/
noncomputable def squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution :
    List ℕ → Finset SquareRootLowPrimeProcessedState →
      SquareRootLowPrimeProcessedState → SquareRootLowPrimeProcessedState
  | [], _S => id
  | p :: ps, S => fun x =>
      if x ∈ squareRootLowPrimeProcessedSeatCanonicalPaired S p then
        squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p x
      else
        squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution ps
          (squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p) x

/-- The canonical global chronology preserves the original carrier. -/
theorem squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution_mem
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S) :
    squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution ps S x ∈ S := by
  induction ps generalizing S x with
  | nil =>
      simpa [squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution] using hxS
  | cons p ps ih =>
      by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatCanonicalPaired S p
      · rw [squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution]
        simp only [hxPaired, if_true]
        exact squareRootLowPrimeProcessedSeatCanonicalStepInvolution_mem S p hxS
      · have hxFrontier :
          x ∈ squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p :=
        Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        have hrec := ih
          (S := squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p) hxFrontier
        rw [squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution]
        simp only [hxPaired, if_false]
        exact squareRootLowPrimeProcessedSeatCanonicalFrontierStep_subset S p hrec

/-- The complete canonical Euler chronology is an involution. -/
theorem squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution_involutive
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (hpos : ∀ p ∈ ps, 0 < p)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S) :
    squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution ps S
        (squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution ps S x) = x := by
  induction ps generalizing S x with
  | nil => simp [squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution]
  | cons p ps ih =>
      have hp : 0 < p := hpos p (by simp)
      have hrest : ∀ q ∈ ps, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatCanonicalPaired S p
      · let y := squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p x
        have hyS : y ∈ S :=
          squareRootLowPrimeProcessedSeatCanonicalStepInvolution_mem S p
            (squareRootLowPrimeProcessedSeatCanonicalPaired_subset S p hxPaired)
        have hyPaired :
            y ∈ squareRootLowPrimeProcessedSeatCanonicalPaired S p := by
          by_contra hnot
          have hyFixed :
              squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p y = y :=
            (squareRootLowPrimeProcessedSeatCanonicalStepInvolution_eq_self_iff
              S p (x := y)).mpr hnot
          have hback :=
            squareRootLowPrimeProcessedSeatCanonicalStepInvolution_involutive
              S hp x
          change squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p y = x
            at hback
          rw [hyFixed] at hback
          exact hnot (hback.symm ▸ hxPaired)
        rw [squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution]
        simp only [hxPaired, if_true]
        change squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution
          (p :: ps) S y = x
        rw [squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution]
        simp only [hyPaired, if_true]
        exact squareRootLowPrimeProcessedSeatCanonicalStepInvolution_involutive
          S hp x
      · have hxFrontier :
          x ∈ squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        let y := squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution ps
          (squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p) x
        have hyFrontier :
            y ∈ squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p :=
          squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution_mem ps
            (squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p) hxFrontier
        have hyNotPaired :
            y ∉ squareRootLowPrimeProcessedSeatCanonicalPaired S p :=
          (Finset.mem_sdiff.mp hyFrontier).2
        have hrec := ih
          (S := squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p)
          hrest hxFrontier
        rw [squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution]
        simp only [hxPaired, if_false]
        change squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution
          (p :: ps) S y = x
        rw [squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution]
        simp only [hyNotPaired, if_false]
        exact hrec

/-- Moved states of the complete canonical chronology reverse signed weight. -/
theorem squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution_weight_neg
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (hprime : ∀ p ∈ ps, p.Prime)
    {x : SquareRootLowPrimeProcessedState} (hxS : x ∈ S)
    (hne : squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution ps S x ≠ x) :
    squareRootLowPrimeProcessedSeatWeightReal
        (squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution ps S x) =
      -squareRootLowPrimeProcessedSeatWeightReal x := by
  induction ps generalizing S x with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution] at hne
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hrest : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatCanonicalPaired S p
      · have hstepNe :
          squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p x ≠ x :=
          fun h =>
            (squareRootLowPrimeProcessedSeatCanonicalStepInvolution_eq_self_iff
              S p).mp h hxPaired
        rw [squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution]
        simp only [hxPaired, if_true]
        exact squareRootLowPrimeProcessedSeatCanonicalStepInvolution_weight_neg
          S hp x hstepNe
      · have hxFrontier :
          x ∈ squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p :=
          Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
        rw [squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution] at hne ⊢
        simp only [hxPaired, if_false] at hne ⊢
        exact ih
          (S := squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p)
          hrest hxFrontier hne

/-- The fixed states of the global canonical Euler involution are exactly the
canonical terminal frontier. -/
theorem signMatchingFixedPart_processedSeatCanonicalMatching_eq_frontier
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (hpos : ∀ p ∈ ps, 0 < p) :
    signMatchingFixedPart S
        (squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution ps S) =
      squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier ps S := by
  classical
  induction ps generalizing S with
  | nil =>
      ext x
      simp [signMatchingFixedPart,
        squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution,
        squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier]
  | cons p ps ih =>
      have hrest : ∀ q ∈ ps, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      ext x
      simp only [mem_signMatchingFixedPart]
      by_cases hxS : x ∈ S
      · by_cases hxPaired : x ∈ squareRootLowPrimeProcessedSeatCanonicalPaired S p
        · have hstepNe :
            squareRootLowPrimeProcessedSeatCanonicalStepInvolution S p x ≠ x :=
            fun h =>
              (squareRootLowPrimeProcessedSeatCanonicalStepInvolution_eq_self_iff
                S p).mp h hxPaired
          have hxNotFrontier :
              x ∉ squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier
                (p :: ps) S := by
            intro hx
            have hxStep :=
              squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier_subset
                ps (squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p) hx
            exact (Finset.mem_sdiff.mp hxStep).2 hxPaired
          rw [squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution]
          simp only [hxPaired, if_true]
          exact ⟨fun h => (hstepNe h.2).elim,
            fun h => (hxNotFrontier h).elim⟩
        · have hxStep :
            x ∈ squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p :=
            Finset.mem_sdiff.mpr ⟨hxS, hxPaired⟩
          have hih := Finset.ext_iff.mp
            (ih (S := squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p)
              hrest) x
          simp only [mem_signMatchingFixedPart] at hih
          have hreciff :
              squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution ps
                    (squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p) x = x ↔
                x ∈ squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier ps
                  (squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p) := by
            constructor
            · intro hrec
              exact hih.mp ⟨hxStep, hrec⟩
            · intro hfront
              exact (hih.mpr hfront).2
          rw [squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution]
          simp only [hxPaired, if_false]
          change (x ∈ S ∧
              squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution ps
                (squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p) x = x) ↔
            x ∈ squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier ps
              (squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p)
          rw [hreciff]
          simp [hxS]
      · have hxNotFrontier :
          x ∉ squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier
            (p :: ps) S :=
          fun hx => hxS
            (squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier_subset
              (p :: ps) S hx)
        have hxNotPaired :
            x ∉ squareRootLowPrimeProcessedSeatCanonicalPaired S p :=
          fun hx => hxS
            (squareRootLowPrimeProcessedSeatCanonicalPaired_subset S p hx)
        rw [squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution]
        simp only [hxNotPaired, if_false]
        exact ⟨fun h => (hxS h.1).elim, fun h => (hxNotFrontier h).elim⟩

/-- The canonical Euler Othello mate on the actual processed carrier. -/
noncomputable def squareRootLowPrimeProcessedSeatCanonicalMate
    (R K j U : ℕ) :
    SquareRootLowPrimeProcessedState → SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution
    (squareRootLowPrimeFreshPrimeList K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)

/-- The canonical mate preserves the processed carrier. -/
theorem squareRootLowPrimeProcessedSeatCanonicalMate_mem
    (R K j U : ℕ) {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedSeatCanonicalMate R K j U x ∈
      squareRootLowPrimeProcessedSeatCarrier R K j U := by
  exact squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution_mem
    _ _ hx

/-- The canonical mate is involutive on the processed carrier. -/
theorem squareRootLowPrimeProcessedSeatCanonicalMate_involutive
    (R K j U : ℕ) {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U) :
    squareRootLowPrimeProcessedSeatCanonicalMate R K j U
        (squareRootLowPrimeProcessedSeatCanonicalMate R K j U x) = x := by
  apply squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution_involutive
    (squareRootLowPrimeFreshPrimeList K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)
  · intro p hp
    exact (prime_of_mem_squareRootLowPrimeFreshPrimeList hp).pos
  · exact hx

/-- Every moved canonical mate state has opposite native weight. -/
theorem squareRootLowPrimeProcessedSeatCanonicalMate_weight_neg
    (R K j U : ℕ) {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hne : squareRootLowPrimeProcessedSeatCanonicalMate R K j U x ≠ x) :
    squareRootLowPrimeProcessedSeatWeightReal
        (squareRootLowPrimeProcessedSeatCanonicalMate R K j U x) =
      -squareRootLowPrimeProcessedSeatWeightReal x := by
  apply squareRootLowPrimeProcessedSeatCanonicalMatchingInvolution_weight_neg
    (squareRootLowPrimeFreshPrimeList K U)
    (squareRootLowPrimeProcessedSeatCarrier R K j U)
  · intro p hp
    exact prime_of_mem_squareRootLowPrimeFreshPrimeList hp
  · exact hx
  · exact hne

/-- The fixed set of the canonical mate is exactly the canonical Euler terminal
frontier. -/
theorem signMatchingFixedPart_processedSeatCanonicalMate_eq_terminalFrontier
    (R K j U : ℕ) :
    signMatchingFixedPart
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatCanonicalMate R K j U) =
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U := by
  unfold squareRootLowPrimeProcessedSeatCanonicalMate
    squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier
  apply signMatchingFixedPart_processedSeatCanonicalMatching_eq_frontier
  intro p hp
  exact (prime_of_mem_squareRootLowPrimeFreshPrimeList hp).pos

end RHLean.Proof
