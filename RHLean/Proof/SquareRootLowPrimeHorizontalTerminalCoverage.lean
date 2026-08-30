import Mathlib
import RHLean.Proof.SquareRootLowPrimeHorizontalOwnerFallout

/-!
# Terminal coverage by intrinsic first missing-child owners

There are two distinct notions of a missing child in sequential matching.

* **Stage fallout:** the child is absent from the mutable row entering owner
  `p`.  This proves only that the state is unmatched at that stage; the child
  may have existed in the original carrier and been consumed earlier.
* **Intrinsic fallout:** the child is absent from the original carrier itself.
  This is the genuine fixed-owner boundary `U_p`.  Earlier displacement is not
  silently counted as fallout.

For a fixed original carrier `S`, the intrinsic first-owner function scans the
owner list chronologically and returns the first `p` for which the state belongs
to canonical fallout relative to `S`.  Its fibres are pairwise disjoint by
construction.  Any chosen target population therefore splits exactly into the
sum of its first-owner fibres plus an honest residual of states with no
intrinsic owner.

For a terminal state in that residual, every eligible listed coordinate whose
child is legal in the original carrier is an actual skip.  The existing
matching-displacement theorem then produces a strictly earlier blocker.  Thus
displacement remains visible in the residual until it is proved to be one of
the already-classified head/boundary populations.

No estimate, chain-parity bound, PNT input, Mertens bound, or RH-equivalent
statement is used here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## Mutable-row stage fallout is only a diagnostic -/

/-- A terminal survivor with an eligible coordinate `p` is necessarily a
canonical missing-child state in the mutable row entering the `p` stage.

This does not imply intrinsic fallout relative to the original carrier. -/
theorem squareRootLowPrimeProcessedSeatTerminal_mem_canonicalOwnerFalloff
    (pre post : List ℕ)
    (S : Finset SquareRootLowPrimeProcessedState)
    {p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier
      (pre ++ p :: post) S)
    (hxHead : x ≠ none)
    (hpFresh : ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x)
    (hlpf : canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) < p) :
    x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p := by
  have hxRewritten :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier post
        (squareRootLowPrimeProcessedSeatFrontierStep
          (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p) := by
    rw [squareRootLowPrimeProcessedSeatMatchingFrontier_append] at hx
    simpa [squareRootLowPrimeProcessedSeatMatchingFrontier] using hx
  have hxStep :
      x ∈ squareRootLowPrimeProcessedSeatFrontierStep
        (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p :=
    squareRootLowPrimeProcessedSeatMatchingFrontier_subset' post _ hxRewritten
  have hxPre :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier pre S :=
    (Finset.mem_sdiff.mp hxStep).1
  have hmissing :
      squareRootLowPrimeProcessedSeatExtend p x ∉
        squareRootLowPrimeProcessedSeatMatchingFrontier pre S := by
    intro hchild
    have hxLower :
        x ∈ squareRootLowPrimeProcessedSeatPairLower
          (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p :=
      mem_squareRootLowPrimeProcessedSeatPairLower.mpr
        ⟨hxPre, hxHead, hpFresh, hchild⟩
    exact (Finset.mem_sdiff.mp hxStep).2
      (Finset.mem_union.mpr (Or.inl hxLower))
  exact mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mpr
    ⟨hxPre, hxHead, hpFresh, hmissing, hlpf⟩

/-- Non-head part of an arbitrary processed terminal frontier. -/
def squareRootLowPrimeProcessedSeatNonHeadTerminalTarget
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeProcessedSeatMatchingFrontier ps S).erase none

/-! ## Static chronological intrinsic-owner assignment -/

/-- First chronological owner whose child is intrinsically absent from the
original carrier `S`.  The carrier is deliberately *not* updated during this
scan. -/
def squareRootLowPrimeProcessedSeatIntrinsicFirstOwner :
    List ℕ → Finset SquareRootLowPrimeProcessedState →
      SquareRootLowPrimeProcessedState → Option ℕ
  | [], _S, _x => none
  | p :: ps, S, x =>
      if x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p then
        some p
      else
        squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x

/-- The first-owner function is empty exactly when no listed owner sees
intrinsic fallout. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_eq_none_iff
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (x : SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x = none ↔
      ∀ p ∈ ps,
        x ∉ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p := by
  induction ps with
  | nil =>
      constructor
      · intro _ p hp
        simp at hp
      · intro _
        rfl
  | cons p ps ih =>
      by_cases hp :
          x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p
      · constructor
        · intro hnone
          simp [squareRootLowPrimeProcessedSeatIntrinsicFirstOwner, hp] at hnone
        · intro hall
          exfalso
          exact (hall p (by simp)) hp
      · rw [squareRootLowPrimeProcessedSeatIntrinsicFirstOwner]
        simp only [if_neg hp]
        rw [ih]
        constructor
        · intro htail q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hp
          · exact htail q hq
        · intro hall q hq
          exact hall q (by simp [hq])

/-- Any returned owner is actually listed and is an intrinsic fallout owner. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_some_mem
    {ps : List ℕ} {S : Finset SquareRootLowPrimeProcessedState}
    {x : SquareRootLowPrimeProcessedState} {p : ℕ}
    (hp : squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x = some p) :
    p ∈ ps ∧
      x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p := by
  induction ps with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatIntrinsicFirstOwner] at hp
  | cons q qs ih =>
      by_cases hq :
          x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S q
      · have hqp : q = p := by
          apply Option.some.inj
          simpa [squareRootLowPrimeProcessedSeatIntrinsicFirstOwner, hq] using hp
        subst p
        exact ⟨by simp, hq⟩
      · have hpTail :
            squareRootLowPrimeProcessedSeatIntrinsicFirstOwner qs S x = some p := by
          simpa [squareRootLowPrimeProcessedSeatIntrinsicFirstOwner, hq] using hp
        rcases ih hpTail with ⟨hpMem, hpFall⟩
        exact ⟨by simp [hpMem], hpFall⟩

/-- Fibre of the intrinsic chronological first-owner function inside a target
population. -/
def squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    (p : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  T.filter fun x =>
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x = some p

@[simp] theorem mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice
    {ps : List ℕ} {S T : Finset SquareRootLowPrimeProcessedState}
    {p : ℕ} {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T p ↔
      x ∈ T ∧
        squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x = some p := by
  simp [squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice]

/-- Union of all intrinsic first-owner fibres in the listed owner set. -/
def squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    Finset SquareRootLowPrimeProcessedState :=
  ps.toFinset.biUnion fun p =>
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T p

/-- Honest residual: target states with no intrinsic owner in the original
carrier.  Mutable-row skips remain here. -/
def squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    Finset SquareRootLowPrimeProcessedState :=
  T.filter fun x =>
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x = none

@[simp] theorem mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual
    {ps : List ℕ} {S T : Finset SquareRootLowPrimeProcessedState}
    {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T ↔
      x ∈ T ∧
        squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x = none := by
  simp [squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual]

/-- Different first owners have disjoint fibres. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice_disjoint
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    {p q : ℕ} (hpq : p ≠ q) :
    Disjoint
      (squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T p)
      (squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T q) := by
  rw [Finset.disjoint_left]
  intro x hxp hxq
  have hp :=
    (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mp hxp).2
  have hq :=
    (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mp hxq).2
  apply hpq
  exact Option.some.inj (hp.symm.trans hq)

/-- Every state in the assigned support has one and only one chronological
first owner. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_existsUnique
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T) :
    ∃! p : ℕ,
      p ∈ ps ∧
        x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T p := by
  rcases Finset.mem_biUnion.mp hx with ⟨p, hpList, hxp⟩
  refine ⟨p, ⟨by simpa using hpList, hxp⟩, ?_⟩
  intro q hq
  have hpEq :=
    (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mp hxp).2
  have hqEq :=
    (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mp hq.2).2
  exact Option.some.inj (hqEq.symm.trans hpEq)

/-- Assigned intrinsic fibres and the honest residual partition the target. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport_union_residual
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T ∪
        squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T = T := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hxSupport | hxResidual
    · rcases Finset.mem_biUnion.mp hxSupport with ⟨_p, _hp, hxp⟩
      exact
        (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mp hxp).1
    · exact
        (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mp
          hxResidual).1
  · intro hxT
    cases howner : squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x with
    | none =>
        exact Finset.mem_union.mpr <| Or.inr <|
          mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mpr
            ⟨hxT, howner⟩
    | some p =>
        have hpData :=
          squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_some_mem howner
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_biUnion.mpr
        refine ⟨p, by simpa using hpData.1, ?_⟩
        exact mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mpr
          ⟨hxT, howner⟩

/-- Assigned support is disjoint from the honest residual. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport_disjoint_residual
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    Disjoint
      (squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T)
      (squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T) := by
  rw [Finset.disjoint_left]
  intro x hxSupport hxResidual
  rcases Finset.mem_biUnion.mp hxSupport with ⟨_p, _hp, hxp⟩
  have hsome :=
    (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mp hxp).2
  have hnone :=
    (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mp
      hxResidual).2
  rw [hnone] at hsome
  simp at hsome

/-- Pairwise disjointness of the owner fibres. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice_pairwise
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    Set.PairwiseDisjoint (↑ps.toFinset)
      (squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T) := by
  intro p _hp q _hq hpq
  exact squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice_disjoint
    ps S T hpq

/-- Signed mass of the intrinsic chronological owner fibres.  No fibre is
asserted to have zero mass. -/
def squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) : ℝ :=
  ∑ p ∈ ps.toFinset,
    ∑ x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T p,
      squareRootLowPrimeProcessedSeatWeightReal x

/-- The assigned support mass is exactly the sum of its disjoint owner-fibre
masses. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport_weight_sum
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass ps S T := by
  unfold squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass
  rw [Finset.sum_biUnion
    (squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice_pairwise ps S T)]

/-- **Intrinsic horizontal mass decomposition.**  Target mass is the sum of
unique intrinsic first-owner fibres plus the honest residual. -/
theorem squareRootLowPrimeProcessedSeatTarget_weight_sum_eq_intrinsicFirstOwner_add_residual
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    (∑ x ∈ T, squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass ps S T +
        ∑ x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T,
          squareRootLowPrimeProcessedSeatWeightReal x := by
  have hdisj :=
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport_disjoint_residual
      ps S T
  have hunion :=
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport_union_residual
      ps S T
  calc
    (∑ x ∈ T, squareRootLowPrimeProcessedSeatWeightReal x) =
        ∑ x ∈
          (squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T ∪
            squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T),
          squareRootLowPrimeProcessedSeatWeightReal x := by
            rw [hunion]
    _ =
        (∑ x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T,
          squareRootLowPrimeProcessedSeatWeightReal x) +
        ∑ x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T,
          squareRootLowPrimeProcessedSeatWeightReal x :=
      Finset.sum_union hdisj
    _ = squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass ps S T +
        ∑ x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T,
          squareRootLowPrimeProcessedSeatWeightReal x := by
      rw [squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport_weight_sum]

/-- True intrinsic coverage empties the residual.  The hypothesis is actual
membership in `U_p` relative to the original carrier, not mere arithmetic
possibility of a later prime. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual_eq_empty_of_covered
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    (hcover : ∀ x ∈ T,
      ∃ p ∈ ps,
        x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p) :
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hxResidual
  have hxData :=
    mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mp hxResidual
  have hnone :=
    (squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_eq_none_iff ps S x).mp
      hxData.2
  rcases hcover x hxData.1 with ⟨p, hpList, hfall⟩
  exact hnone p hpList hfall

/-- Under true intrinsic coverage every target state has exactly one
chronological first owner. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_unique_of_covered
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    (hcover : ∀ x ∈ T,
      ∃ p ∈ ps,
        x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p) :
    ∀ x ∈ T,
      ∃! p : ℕ,
        p ∈ ps ∧
          x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T p := by
  intro x hxT
  have hresEmpty :=
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual_eq_empty_of_covered
      ps S T hcover
  have hpart :=
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport_union_residual
      ps S T
  have hxSupport :
      x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T := by
    have hxUnion :
        x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T ∪
          squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T := by
      rw [hpart]
      exact hxT
    rcases Finset.mem_union.mp hxUnion with hx | hx
    · exact hx
    · rw [hresEmpty] at hx
      simp at hx
  exact squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_existsUnique
    ps S T hxSupport

/-- Under true intrinsic coverage, target mass is literally the sum over the
unique chronological owner fibres. -/
theorem squareRootLowPrimeProcessedSeatTarget_weight_sum_eq_intrinsicFirstOwnerMass_of_covered
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    (hcover : ∀ x ∈ T,
      ∃ p ∈ ps,
        x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p) :
    (∑ x ∈ T, squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass ps S T := by
  rw [squareRootLowPrimeProcessedSeatTarget_weight_sum_eq_intrinsicFirstOwner_add_residual]
  rw [squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual_eq_empty_of_covered
    ps S T hcover]
  simp

/-! ## Honest terminal residual exposes displacement skips -/

/-- Intrinsic residual of the actual non-head terminal target. -/
def squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    Finset SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S
    (squareRootLowPrimeProcessedSeatNonHeadTerminalTarget ps S)

/-- If a non-head terminal residual state has an eligible listed coordinate
`p`, then its `p`-child was present in the original carrier.  Hence its failure
at the `p` row is a genuine displacement skip, and the existing theorem
produces a strictly earlier blocker.

This is the exact distinction required for final coverage: such a state is not
counted in `U_p`. -/
theorem squareRootLowPrimeProcessedSeatTerminalIntrinsicResidual_has_earlier_blocker
    (ps pre post : List ℕ)
    (S : Finset SquareRootLowPrimeProcessedState)
    {p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hxResidual :
      x ∈ squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual ps S)
    (hps : ps = pre ++ p :: post)
    (hpFresh : ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x)
    (hlpf : canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) < p)
    (hpre : ∀ q ∈ pre, q < p) :
    ∃ pre' q post' z,
      pre = pre' ++ q :: post' ∧ q < p ∧
        z ∈ squareRootLowPrimeProcessedSeatMatchingFrontier pre' S ∧
        ((squareRootLowPrimeProcessedSeatExtend p x ∈
              squareRootLowPrimeProcessedSeatPairLower
                (squareRootLowPrimeProcessedSeatMatchingFrontier pre' S) q ∧
            z = squareRootLowPrimeProcessedSeatExtend q
              (squareRootLowPrimeProcessedSeatExtend p x)) ∨
          (z ∈ squareRootLowPrimeProcessedSeatPairLower
              (squareRootLowPrimeProcessedSeatMatchingFrontier pre' S) q ∧
            squareRootLowPrimeProcessedSeatExtend p x =
              squareRootLowPrimeProcessedSeatExtend q z)) := by
  have hxResidual' :
      x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S
        (squareRootLowPrimeProcessedSeatNonHeadTerminalTarget ps S) := by
    simpa [squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual] using
      hxResidual
  have hxResidualData :=
    mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mp hxResidual'
  have hxTargetData :
      x ≠ none ∧
        x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps S :=
    Finset.mem_erase.mp hxResidualData.1
  have hxHead : x ≠ none := hxTargetData.1
  have hxTerminal :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps S :=
    hxTargetData.2
  have hxS : x ∈ S :=
    squareRootLowPrimeProcessedSeatMatchingFrontier_subset' ps S hxTerminal
  have hpList : p ∈ ps := by
    rw [hps]
    simp
  have hnone :=
    (squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_eq_none_iff ps S x).mp
      hxResidualData.2
  have hneighbor : squareRootLowPrimeProcessedSeatExtend p x ∈ S := by
    by_contra hmissing
    have hfall :
        x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p :=
      mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mpr
        ⟨hxS, hxHead, hpFresh, hmissing, hlpf⟩
    exact hnone p hpList hfall
  have hxStage :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier
        (pre ++ p :: post) S := by
    rw [← hps]
    exact hxTerminal
  exact squareRootLowPrimeProcessedSeatTerminal_neighbor_has_earlier_blocker
    pre post S hxStage hxHead hpFresh hneighbor hpre

end RHLean.Proof
