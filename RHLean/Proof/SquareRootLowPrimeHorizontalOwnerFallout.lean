import Mathlib
import RHLean.Proof.SquareRootLowPrimeMatchingDisplacement

/-!
# Horizontal owner cuts for processed low-prime matching

At one chronological prime `p` there are two different populations.

* `paired(S,p)` is the complete lower/upper population actually removed from
  the current row.  It has signed mass zero because every lower endpoint is
  paired with its fresh `p`-extension.
* a fresh parent whose `p`-child is absent is fallout.  Its signed mass is not
  zero and is retained for the quantitative argument.

The chronological paired populations are disjoint because every later row is a
subset of every earlier frontier.  Their union together with the terminal row
is exactly the original carrier.

The final section defines the fixed-owner missing-child population and its
canonical Euler-oriented subpopulation `P+(c) < p`.  Whether the row supplied
to that definition is the mutable stage row or the original static carrier is
an explicit choice; terminal coverage will use the original carrier so that a
child consumed by an earlier owner is not misclassified as intrinsic fallout.

No estimate, chain-parity argument, PNT input, Mertens bound, or RH-equivalent
statement is used here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## Chronological zero-mass paired cuts -/

/-- Owner-tagged populations actually removed by chronological matching. -/
def squareRootLowPrimeProcessedSeatRemovedPairSliceFamily :
    List ℕ → Finset SquareRootLowPrimeProcessedState →
      List (ℕ × Finset SquareRootLowPrimeProcessedState)
  | [], _S => []
  | p :: ps, S =>
      (p, squareRootLowPrimeProcessedSeatPaired S p) ::
        squareRootLowPrimeProcessedSeatRemovedPairSliceFamily ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p)

/-- Every recorded paired cut lies in the original carrier. -/
theorem squareRootLowPrimeProcessedSeatRemovedPairSliceFamily_entry_subset
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    {a : ℕ × Finset SquareRootLowPrimeProcessedState}
    (ha : a ∈ squareRootLowPrimeProcessedSeatRemovedPairSliceFamily ps S) :
    a.2 ⊆ S := by
  induction ps generalizing S a with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatRemovedPairSliceFamily] at ha
  | cons p ps ih =>
      simp only [squareRootLowPrimeProcessedSeatRemovedPairSliceFamily,
        List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact squareRootLowPrimeProcessedSeatPaired_subset S p
      · exact
          (ih (S := squareRootLowPrimeProcessedSeatFrontierStep S p) ha).trans
            (squareRootLowPrimeProcessedSeatFrontierStep_subset' S p)

/-- The population removed at one owner is disjoint from the row surviving that
owner. -/
theorem squareRootLowPrimeProcessedSeatPaired_disjoint_frontierStep
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Disjoint (squareRootLowPrimeProcessedSeatPaired S p)
      (squareRootLowPrimeProcessedSeatFrontierStep S p) := by
  rw [Finset.disjoint_left]
  intro x hxPaired hxFrontier
  exact (Finset.mem_sdiff.mp hxFrontier).2 hxPaired

/-- Distinct chronological paired cuts have disjoint support. -/
theorem squareRootLowPrimeProcessedSeatRemovedPairSliceFamily_disjoint
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    {a b : ℕ × Finset SquareRootLowPrimeProcessedState}
    (ha : a ∈ squareRootLowPrimeProcessedSeatRemovedPairSliceFamily ps S)
    (hb : b ∈ squareRootLowPrimeProcessedSeatRemovedPairSliceFamily ps S)
    (hab : a ≠ b) :
    Disjoint a.2 b.2 := by
  induction ps generalizing S a b with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatRemovedPairSliceFamily] at ha
  | cons p ps ih =>
      simp only [squareRootLowPrimeProcessedSeatRemovedPairSliceFamily,
        List.mem_cons] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact (hab rfl).elim
        · rw [Finset.disjoint_left]
          intro x hxHead hxTail
          have hxFrontier :=
            squareRootLowPrimeProcessedSeatRemovedPairSliceFamily_entry_subset ps
              (squareRootLowPrimeProcessedSeatFrontierStep S p) hb hxTail
          exact (Finset.disjoint_left.mp
            (squareRootLowPrimeProcessedSeatPaired_disjoint_frontierStep S p))
            hxHead hxFrontier
      · rcases hb with rfl | hb
        · rw [Finset.disjoint_left]
          intro x hxTail hxHead
          have hxFrontier :=
            squareRootLowPrimeProcessedSeatRemovedPairSliceFamily_entry_subset ps
              (squareRootLowPrimeProcessedSeatFrontierStep S p) ha hxTail
          exact (Finset.disjoint_left.mp
            (squareRootLowPrimeProcessedSeatPaired_disjoint_frontierStep S p))
            hxHead hxFrontier
        · exact ih
            (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
            ha hb hab

/-- Every chronological paired cut cancels by itself.  This theorem applies
only to the paired population, never to fallout. -/
theorem squareRootLowPrimeProcessedSeatRemovedPairSliceFamily_weight_sum_eq_zero
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (hprime : ∀ p ∈ ps, p.Prime)
    {a : ℕ × Finset SquareRootLowPrimeProcessedState}
    (ha : a ∈ squareRootLowPrimeProcessedSeatRemovedPairSliceFamily ps S) :
    (∑ x ∈ a.2, squareRootLowPrimeProcessedSeatWeightReal x) = 0 := by
  induction ps generalizing S a with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatRemovedPairSliceFamily] at ha
  | cons p ps ih =>
      simp only [squareRootLowPrimeProcessedSeatRemovedPairSliceFamily,
        List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact squareRootLowPrimeProcessedSeatPaired_weight_sum_eq_zero S
          (hprime p (by simp))
      · have htail : ∀ q ∈ ps, q.Prime := by
          intro q hq
          exact hprime q (by simp [hq])
        exact ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S p)
          htail ha

/-- Union of every population removed by the chronological owner cuts. -/
def squareRootLowPrimeProcessedSeatRemovedPairSupport :
    List ℕ → Finset SquareRootLowPrimeProcessedState →
      Finset SquareRootLowPrimeProcessedState
  | [], _S => ∅
  | p :: ps, S =>
      squareRootLowPrimeProcessedSeatPaired S p ∪
        squareRootLowPrimeProcessedSeatRemovedPairSupport ps
          (squareRootLowPrimeProcessedSeatFrontierStep S p)

/-- The complete removed support lies in the original carrier. -/
theorem squareRootLowPrimeProcessedSeatRemovedPairSupport_subset
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatRemovedPairSupport ps S ⊆ S := by
  induction ps generalizing S with
  | nil => simp [squareRootLowPrimeProcessedSeatRemovedPairSupport]
  | cons p ps ih =>
      intro x hx
      rcases Finset.mem_union.mp hx with hxPair | hxTail
      · exact squareRootLowPrimeProcessedSeatPaired_subset S p hxPair
      · exact squareRootLowPrimeProcessedSeatFrontierStep_subset' S p
          (ih (S := squareRootLowPrimeProcessedSeatFrontierStep S p) hxTail)

/-- Removed paired support is disjoint from the final terminal row. -/
theorem squareRootLowPrimeProcessedSeatRemovedPairSupport_disjoint_terminal
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    Disjoint
      (squareRootLowPrimeProcessedSeatRemovedPairSupport ps S)
      (squareRootLowPrimeProcessedSeatMatchingFrontier ps S) := by
  induction ps generalizing S with
  | nil => simp [squareRootLowPrimeProcessedSeatRemovedPairSupport]
  | cons p ps ih =>
      rw [Finset.disjoint_left]
      intro x hxRemoved hxTerminal
      rcases Finset.mem_union.mp hxRemoved with hxPair | hxTail
      · have hxStep :
            x ∈ squareRootLowPrimeProcessedSeatFrontierStep S p :=
          squareRootLowPrimeProcessedSeatMatchingFrontier_subset' ps
            (squareRootLowPrimeProcessedSeatFrontierStep S p) hxTerminal
        exact (Finset.disjoint_left.mp
          (squareRootLowPrimeProcessedSeatPaired_disjoint_frontierStep S p))
          hxPair hxStep
      · exact (Finset.disjoint_left.mp
          (ih (S := squareRootLowPrimeProcessedSeatFrontierStep S p)))
          hxTail hxTerminal

/-- **Exact horizontal partition.**  Chronological paired cuts together with the
terminal row are exactly the original carrier. -/
theorem squareRootLowPrimeProcessedSeatRemovedPairSupport_union_terminal
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatRemovedPairSupport ps S ∪
        squareRootLowPrimeProcessedSeatMatchingFrontier ps S = S := by
  induction ps generalizing S with
  | nil => simp [squareRootLowPrimeProcessedSeatRemovedPairSupport,
      squareRootLowPrimeProcessedSeatMatchingFrontier]
  | cons p ps ih =>
      simp only [squareRootLowPrimeProcessedSeatRemovedPairSupport,
        squareRootLowPrimeProcessedSeatMatchingFrontier,
        Finset.union_assoc]
      rw [ih (S := squareRootLowPrimeProcessedSeatFrontierStep S p)]
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hxPair | hxStep
        · exact squareRootLowPrimeProcessedSeatPaired_subset S p hxPair
        · exact squareRootLowPrimeProcessedSeatFrontierStep_subset' S p hxStep
      · intro hxS
        by_cases hxPair : x ∈ squareRootLowPrimeProcessedSeatPaired S p
        · exact Finset.mem_union.mpr (Or.inl hxPair)
        · exact Finset.mem_union.mpr (Or.inr
            (Finset.mem_sdiff.mpr ⟨hxS, hxPair⟩))

/-- The union of all chronological paired cuts has signed mass zero. -/
theorem squareRootLowPrimeProcessedSeatRemovedPairSupport_weight_sum_eq_zero
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (hprime : ∀ p ∈ ps, p.Prime) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatRemovedPairSupport ps S,
      squareRootLowPrimeProcessedSeatWeightReal x) = 0 := by
  induction ps generalizing S with
  | nil => simp [squareRootLowPrimeProcessedSeatRemovedPairSupport]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have htailPrime : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have htailSubset :
          squareRootLowPrimeProcessedSeatRemovedPairSupport ps
              (squareRootLowPrimeProcessedSeatFrontierStep S p) ⊆
            squareRootLowPrimeProcessedSeatFrontierStep S p :=
        squareRootLowPrimeProcessedSeatRemovedPairSupport_subset ps _
      have hdisj :
          Disjoint (squareRootLowPrimeProcessedSeatPaired S p)
            (squareRootLowPrimeProcessedSeatRemovedPairSupport ps
              (squareRootLowPrimeProcessedSeatFrontierStep S p)) := by
        rw [Finset.disjoint_left]
        intro x hxPair hxTail
        exact (Finset.disjoint_left.mp
          (squareRootLowPrimeProcessedSeatPaired_disjoint_frontierStep S p))
          hxPair (htailSubset hxTail)
      rw [squareRootLowPrimeProcessedSeatRemovedPairSupport,
        Finset.sum_union hdisj,
        squareRootLowPrimeProcessedSeatPaired_weight_sum_eq_zero S hp,
        ih (S := squareRootLowPrimeProcessedSeatFrontierStep S p) htailPrime]
      ring

/-! ## Fixed-owner missing-child fallout -/

/-- States eligible to be lower endpoints at owner `p`, before asking whether
their `p`-child is present. -/
def squareRootLowPrimeProcessedSeatFreshParentCandidates
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Finset SquareRootLowPrimeProcessedState :=
  S.filter fun x =>
    x ≠ none ∧ ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x

@[simp] theorem mem_squareRootLowPrimeProcessedSeatFreshParentCandidates
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeProcessedSeatFreshParentCandidates S p ↔
      x ∈ S ∧ x ≠ none ∧
        ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x := by
  simp [squareRootLowPrimeProcessedSeatFreshParentCandidates]

/-- Fresh parents whose `p`-child is absent from the supplied row. -/
def squareRootLowPrimeProcessedSeatOwnerFalloff
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeProcessedSeatFreshParentCandidates S p).filter fun x =>
    squareRootLowPrimeProcessedSeatExtend p x ∉ S

@[simp] theorem mem_squareRootLowPrimeProcessedSeatOwnerFalloff
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeProcessedSeatOwnerFalloff S p ↔
      x ∈ S ∧ x ≠ none ∧
        ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x ∧
        squareRootLowPrimeProcessedSeatExtend p x ∉ S := by
  constructor
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨hxCandidate, hmissing⟩
    have hdata :=
      mem_squareRootLowPrimeProcessedSeatFreshParentCandidates.mp hxCandidate
    exact ⟨hdata.1, hdata.2.1, hdata.2.2, hmissing⟩
  · rintro ⟨hxS, hxHead, hpFresh, hmissing⟩
    exact Finset.mem_filter.mpr
      ⟨mem_squareRootLowPrimeProcessedSeatFreshParentCandidates.mpr
          ⟨hxS, hxHead, hpFresh⟩,
        hmissing⟩

/-- At one owner, every fresh parent is either matched or its child is missing. -/
theorem squareRootLowPrimeProcessedSeatFreshParentCandidates_eq_pairLower_union_falloff
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    squareRootLowPrimeProcessedSeatFreshParentCandidates S p =
      squareRootLowPrimeProcessedSeatPairLower S p ∪
        squareRootLowPrimeProcessedSeatOwnerFalloff S p := by
  ext x
  by_cases hchild : squareRootLowPrimeProcessedSeatExtend p x ∈ S
  · simp [squareRootLowPrimeProcessedSeatFreshParentCandidates,
      squareRootLowPrimeProcessedSeatPairLower,
      squareRootLowPrimeProcessedSeatOwnerFalloff, hchild]
  · simp [squareRootLowPrimeProcessedSeatFreshParentCandidates,
      squareRootLowPrimeProcessedSeatPairLower,
      squareRootLowPrimeProcessedSeatOwnerFalloff, hchild]

/-- Matched lower endpoints and missing-child parents are disjoint. -/
theorem squareRootLowPrimeProcessedSeatPairLower_disjoint_ownerFalloff
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Disjoint (squareRootLowPrimeProcessedSeatPairLower S p)
      (squareRootLowPrimeProcessedSeatOwnerFalloff S p) := by
  rw [Finset.disjoint_left]
  intro x hxLower hxFalloff
  exact (mem_squareRootLowPrimeProcessedSeatOwnerFalloff.mp hxFalloff).2.2.2
    (mem_squareRootLowPrimeProcessedSeatPairLower.mp hxLower).2.2.2

/-- Fixed-owner cardinality identity for matched parents versus fallout. -/
theorem squareRootLowPrimeProcessedSeatFreshParentCandidates_card
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    (squareRootLowPrimeProcessedSeatFreshParentCandidates S p).card =
      (squareRootLowPrimeProcessedSeatPairLower S p).card +
        (squareRootLowPrimeProcessedSeatOwnerFalloff S p).card := by
  rw [squareRootLowPrimeProcessedSeatFreshParentCandidates_eq_pairLower_union_falloff,
    Finset.card_union_of_disjoint
      (squareRootLowPrimeProcessedSeatPairLower_disjoint_ownerFalloff S p)]

/-- A fresh parent candidate cannot be a same-owner upper endpoint because every
upper endpoint has cofactor divisible by `p`. -/
theorem squareRootLowPrimeProcessedSeatFreshParentCandidate_not_mem_pairUpper
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatFreshParentCandidates S p) :
    x ∉ squareRootLowPrimeProcessedSeatPairUpper S p := by
  intro hxUpper
  rcases Finset.mem_image.mp hxUpper with ⟨y, hyLower, hyx⟩
  have hyData := mem_squareRootLowPrimeProcessedSeatPairLower.mp hyLower
  have hpDiv :
      p ∣ squareRootLowPrimeProcessedStateCofactor
        (squareRootLowPrimeProcessedSeatExtend p y) := by
    rcases y with _ | z
    · exact (hyData.2.1 rfl).elim
    · change p ∣ p * z.1
      exact ⟨z.1, rfl⟩
  have hpFresh :=
    (mem_squareRootLowPrimeProcessedSeatFreshParentCandidates.mp hx).2.2
  apply hpFresh
  rw [← hyx]
  exact hpDiv

/-- Missing-child parents survive their owner step. -/
theorem squareRootLowPrimeProcessedSeatOwnerFalloff_subset_frontierStep
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    squareRootLowPrimeProcessedSeatOwnerFalloff S p ⊆
      squareRootLowPrimeProcessedSeatFrontierStep S p := by
  intro x hx
  have hxData := mem_squareRootLowPrimeProcessedSeatOwnerFalloff.mp hx
  apply Finset.mem_sdiff.mpr
  refine ⟨hxData.1, ?_⟩
  intro hxPaired
  rcases Finset.mem_union.mp hxPaired with hxLower | hxUpper
  · exact hxData.2.2.2
      (mem_squareRootLowPrimeProcessedSeatPairLower.mp hxLower).2.2.2
  · have hxCandidate :
        x ∈ squareRootLowPrimeProcessedSeatFreshParentCandidates S p :=
      mem_squareRootLowPrimeProcessedSeatFreshParentCandidates.mpr
        ⟨hxData.1, hxData.2.1, hxData.2.2.1⟩
    exact
      (squareRootLowPrimeProcessedSeatFreshParentCandidate_not_mem_pairUpper
        hxCandidate) hxUpper

/-- Among fresh parent candidates, the survivors of the `p` step are exactly
the missing-child fallout. -/
theorem squareRootLowPrimeProcessedSeatFreshParent_frontier_eq_ownerFalloff
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    squareRootLowPrimeProcessedSeatFreshParentCandidates S p ∩
        squareRootLowPrimeProcessedSeatFrontierStep S p =
      squareRootLowPrimeProcessedSeatOwnerFalloff S p := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxCandidate, hxFrontier⟩
    have hxData :=
      mem_squareRootLowPrimeProcessedSeatFreshParentCandidates.mp hxCandidate
    apply mem_squareRootLowPrimeProcessedSeatOwnerFalloff.mpr
    refine ⟨hxData.1, hxData.2.1, hxData.2.2, ?_⟩
    intro hchild
    have hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S p :=
      mem_squareRootLowPrimeProcessedSeatPairLower.mpr
        ⟨hxData.1, hxData.2.1, hxData.2.2, hchild⟩
    exact (Finset.mem_sdiff.mp hxFrontier).2
      (Finset.mem_union.mpr (Or.inl hxLower))
  · intro hxFalloff
    have hxData := mem_squareRootLowPrimeProcessedSeatOwnerFalloff.mp hxFalloff
    exact Finset.mem_inter.mpr
      ⟨mem_squareRootLowPrimeProcessedSeatFreshParentCandidates.mpr
          ⟨hxData.1, hxData.2.1, hxData.2.2.1⟩,
        squareRootLowPrimeProcessedSeatOwnerFalloff_subset_frontierStep
          S p hxFalloff⟩

/-- Genuine Euler-oriented fallout: the parent is rough below the proposed
fresh owner.  When `S` is the original carrier, this is the intrinsic fixed-owner
fallout used by the terminal assignment. -/
def squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
    (S : Finset SquareRootLowPrimeProcessedState) (p : ℕ) :
    Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeProcessedSeatOwnerFalloff S p).filter fun x =>
    canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) < p

@[simp] theorem mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p ↔
      x ∈ S ∧ x ≠ none ∧
        ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x ∧
        squareRootLowPrimeProcessedSeatExtend p x ∉ S ∧
        canonicalLargestPrimeFactor
          (squareRootLowPrimeProcessedStateCofactor x) < p := by
  constructor
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨hxFalloff, hlpf⟩
    have hdata := mem_squareRootLowPrimeProcessedSeatOwnerFalloff.mp hxFalloff
    exact ⟨hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2, hlpf⟩
  · rintro ⟨hxS, hxHead, hpFresh, hmissing, hlpf⟩
    exact Finset.mem_filter.mpr
      ⟨mem_squareRootLowPrimeProcessedSeatOwnerFalloff.mpr
          ⟨hxS, hxHead, hpFresh, hmissing⟩,
        hlpf⟩

end RHLean.Proof
