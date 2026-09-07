import Mathlib
import RHLean.Proof.LowWheelCanonicalDowncrossOwnership
import RHLean.Proof.LowWheelCanonicalDowncrossSignedParentSplit
import RHLean.Proof.LowWheelCanonicalRepeatedMovableOthello
import RHLean.Proof.LowWheelOthelloRepeatedInvolution
import RHLean.Proof.SquareRootCanonicalDowncrossFinalSeam

/-!
# Exact cancellation of the canonical late-parent downcross population

The ownership split isolates a `LateParent` population in which the root-side
parent still contains a prime coordinate `q >= p`, where `p` is the canonical
least-prime pivot.  The lightweight Othello development already proves the
exact fixed-point-free sign-reversing involution on precisely this movable
face/tail population.

This file supplies the missing carrier-identification bridge.  No new toggle is
introduced: the canonical downcross carrier and the lightweight Othello carrier
are definitionally the same finite set.  A late-parent prime factor is exactly
an Othello movable prime, and every such state is automatically in a repeated
parent fibre because its opposite mate is distinct and has the same parent.

Consequently the complete late-parent ledger vanishes exactly, leaving only the
canonically oriented first-crossing ledger.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

namespace LateParentCancellation

/-- The canonical and lightweight one-sided downcross carriers are literally
the same finite carrier. -/
theorem lowWheelCanonicalDowncrossPart_eq_othello
    (R : ℕ) (t : Finset ℕ) :
    lowWheelCanonicalDowncrossPart R t = lowWheelOthelloDowncrossPart R t := by
  rfl

/-- Hence the tagged carriers coincide without any reindexing loss. -/
theorem lowWheelCanonicalTaggedDowncrossCarrier_eq_othello
    (R : ℕ) :
    lowWheelCanonicalTaggedDowncrossCarrier R =
      lowWheelOthelloTaggedDowncrossCarrier R := by
  rfl

/-- The canonical and lightweight parent coordinates are the same integer. -/
theorem lowWheelCanonicalDowncrossParent_eq_othello
    (y : LowWheelTaggedDowncrossState) :
    lowWheelCanonicalDowncrossParent y = lowWheelOthelloDowncrossParent y := by
  rfl

/-- One tagged face fibre of the ownership `LateParent` population. -/
def lowWheelCanonicalTaggedLateParentFiber
    (R : ℕ) (t : Finset ℕ) : Finset LowWheelTaggedDowncrossState :=
  (LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossLateParentPart R t).image
    fun x => (t, x)

/-- Complete tagged ownership `LateParent` carrier. -/
def lowWheelCanonicalTaggedLateParentPart
    (R : ℕ) : Finset LowWheelTaggedDowncrossState :=
  (primesUpTo R).powerset.biUnion
    (lowWheelCanonicalTaggedLateParentFiber R)

@[simp] theorem mem_lowWheelCanonicalTaggedLateParentPart
    {R : ℕ} {y : LowWheelTaggedDowncrossState} :
    y ∈ lowWheelCanonicalTaggedLateParentPart R ↔
      y.1 ∈ (primesUpTo R).powerset ∧
        y.2 ∈
          LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossLateParentPart
            R y.1 := by
  classical
  constructor
  · intro hy
    rcases Finset.mem_biUnion.mp hy with ⟨t, ht, hy⟩
    rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
    subst y
    exact ⟨ht, hx⟩
  · intro hy
    rcases hy with ⟨ht, hx⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨y.1, ht, ?_⟩
    exact Finset.mem_image.mpr ⟨y.2, hx, Prod.ext rfl rfl⟩

/-- Different Boolean faces give disjoint tagged late-parent fibres. -/
theorem lowWheelCanonicalTaggedLateParentFiber_pairwise
    (R : ℕ) :
    Set.PairwiseDisjoint (↑(primesUpTo R).powerset)
      (lowWheelCanonicalTaggedLateParentFiber R) := by
  intro t _ht u _hu htu
  change Disjoint
    (lowWheelCanonicalTaggedLateParentFiber R t)
    (lowWheelCanonicalTaggedLateParentFiber R u)
  rw [Finset.disjoint_left]
  intro y hyt hyu
  rcases Finset.mem_image.mp hyt with ⟨x, _hx, rfl⟩
  rcases Finset.mem_image.mp hyu with ⟨z, _hz, huz⟩
  have hut : u = t := congrArg Prod.fst huz
  exact htu hut.symm

/-- On the common downcross carrier, the ownership late-parent condition is
exactly existence of an Othello movable prime. -/
theorem lateParentCondition_iff_othelloMovable
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R) :
    (∃ q ∈
        (LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossParent
          y.1 y.2).primeFactors,
        LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossPivot y.2 ≤ q) ↔
      ∃ q, LowWheelOthelloMovablePrime y q := by
  constructor
  · rintro ⟨q, hqFactors, hpq⟩
    have hparentPos : 0 < lowWheelCanonicalDowncrossParent y :=
      lowWheelCanonicalDowncrossParent_pos hy
    have hqData := Nat.mem_primeFactors.mp hqFactors
    have hqPrime : q.Prime := hqData.1
    have hqDvd : q ∣ lowWheelCanonicalDowncrossParent y := by
      simpa [LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossParent,
        lowWheelCanonicalDowncrossParent] using hqData.2.1
    have hqLeParent : q ≤ lowWheelCanonicalDowncrossParent y :=
      Nat.le_of_dvd hparentPos hqDvd
    have hqR : q ≤ R :=
      hqLeParent.trans (lowWheelCanonicalDowncrossParent_le_root hy)
    have hcand : q ∈ lowWheelCanonicalDowncrossMovablePrimeSet R y := by
      apply mem_lowWheelCanonicalDowncrossMovablePrimeSet.mpr
      refine ⟨mem_primesUpTo.mpr ⟨hqPrime, hqR⟩, ?_, hqDvd⟩
      simpa [lowWheelTaggedDowncrossPivot,
        LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossPivot] using hpq
    have hmov := lowWheelDowncrossMovablePrime_of_mem_candidateSet hy hcand
    refine ⟨q, ?_⟩
    simpa [LowWheelDowncrossMovablePrime, LowWheelOthelloMovablePrime,
      lowWheelTaggedDowncrossPivot, lowWheelOthelloDowncrossPivot] using hmov
  · rintro ⟨q, hmovO⟩
    have hmov : LowWheelDowncrossMovablePrime y q := by
      simpa [LowWheelDowncrossMovablePrime, LowWheelOthelloMovablePrime,
        lowWheelTaggedDowncrossPivot, lowWheelOthelloDowncrossPivot] using hmovO
    have hcand := lowWheelDowncrossMovablePrime_mem_candidateSet hy hmov
    rcases mem_lowWheelCanonicalDowncrossMovablePrimeSet.mp hcand with
      ⟨hqGlobal, hpq, hqDvd⟩
    have hqPrime : q.Prime := prime_of_mem_primesUpTo hqGlobal
    have hparentPos : 0 < lowWheelCanonicalDowncrossParent y :=
      lowWheelCanonicalDowncrossParent_pos hy
    have hqFactors : q ∈ (lowWheelCanonicalDowncrossParent y).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hqPrime, hqDvd, Nat.ne_of_gt hparentPos⟩
    refine ⟨q, ?_, ?_⟩
    · simpa [LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossParent,
        lowWheelCanonicalDowncrossParent] using hqFactors
    · simpa [lowWheelTaggedDowncrossPivot,
        LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossPivot] using hpq

/-- A movable Othello state is automatically repeated: its opposite face/tail
mate is distinct and has the same parent. -/
theorem othelloMovable_mem_repeated
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R)
    (hmov : ∃ q, LowWheelOthelloMovablePrime y q) :
    y ∈ lowWheelOthelloDowncrossRepeatedParentPart R := by
  rcases hmov with ⟨q, hq⟩
  have hmate := lowWheelOthelloParentToggleAt_mem hy hq
  have hparent := lowWheelOthelloParentToggleAt_parent hy hq
  have hne := lowWheelOthelloParentToggleAt_ne hq
  apply Finset.mem_filter.mpr
  refine ⟨hy, ?_⟩
  intro hunique
  have heq : lowWheelOthelloParentToggleAt q y = y :=
    hunique (lowWheelOthelloParentToggleAt q y) hmate hparent
  exact hne heq

/-- **Carrier synthesis.**  The ownership late-parent population is precisely
the movable repeated population on which the compiled Othello involution acts. -/
theorem lowWheelCanonicalTaggedLateParentPart_eq_othelloRepeatedMovable
    (R : ℕ) :
    lowWheelCanonicalTaggedLateParentPart R =
      lowWheelOthelloRepeatedMovablePart R := by
  ext y
  constructor
  · intro hyLate
    rcases mem_lowWheelCanonicalTaggedLateParentPart.mp hyLate with ⟨ht, hxLate⟩
    have hxDown :=
      (LowWheelCanonicalDowncrossOwnership.mem_lowWheelCanonicalDowncrossLateParentPart.mp
        hxLate).1
    have hyC : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R :=
      mem_lowWheelCanonicalTaggedDowncrossCarrier.mpr ⟨ht, hxDown⟩
    have hyO : y ∈ lowWheelOthelloTaggedDowncrossCarrier R := by
      rw [← lowWheelCanonicalTaggedDowncrossCarrier_eq_othello R]
      exact hyC
    have hlate :=
      (LowWheelCanonicalDowncrossOwnership.mem_lowWheelCanonicalDowncrossLateParentPart.mp
        hxLate).2
    have hmov : ∃ q, LowWheelOthelloMovablePrime y q :=
      (lateParentCondition_iff_othelloMovable hyC).1 hlate
    exact Finset.mem_filter.mpr
      ⟨othelloMovable_mem_repeated hyO hmov, hmov⟩
  · intro hyMov
    rcases Finset.mem_filter.mp hyMov with ⟨hyRep, hmov⟩
    have hyO := (Finset.mem_filter.mp hyRep).1
    have hyC : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R := by
      rw [lowWheelCanonicalTaggedDowncrossCarrier_eq_othello R]
      exact hyO
    rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hyC with ⟨ht, hxDown⟩
    have hlate := (lateParentCondition_iff_othelloMovable hyC).2 hmov
    apply mem_lowWheelCanonicalTaggedLateParentPart.mpr
    refine ⟨ht, ?_⟩
    exact LowWheelCanonicalDowncrossOwnership.mem_lowWheelCanonicalDowncrossLateParentPart.mpr
      ⟨hxDown, hlate⟩

/-- The ownership late-parent nested ledger flattens without loss. -/
theorem lowWheelCanonicalDowncrossLateParentLedger_eq_tagged
    (R : ℕ) :
    LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossLateParentLedger R =
      ∑ y ∈ lowWheelCanonicalTaggedLateParentPart R,
        lowWheelTaggedDowncrossWeight y := by
  unfold lowWheelCanonicalTaggedLateParentPart
  rw [Finset.sum_biUnion (lowWheelCanonicalTaggedLateParentFiber_pairwise R)]
  unfold LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossLateParentLedger
    lowWheelCanonicalTaggedLateParentFiber
  apply Finset.sum_congr rfl
  intro t _ht
  symm
  apply Finset.sum_image
  intro a _ha b _hb hab
  exact congrArg Prod.snd hab

/-- Movable and frozen Othello repeated populations are disjoint. -/
theorem lowWheelOthelloRepeatedMovable_disjoint_frozen
    (R : ℕ) :
    Disjoint (lowWheelOthelloRepeatedMovablePart R)
      (lowWheelOthelloRepeatedFrozenPart R) := by
  rw [Finset.disjoint_left]
  intro y hmov hfrozen
  have hmovData := (Finset.mem_filter.mp hmov).2
  have hfrozenData := (Finset.mem_filter.mp hfrozen).2
  rcases hmovData with ⟨q, hqPrime, hpq, hactive⟩
  rcases hactive with hface | htail
  · have hqlt := hfrozenData.2 q hface
    omega
  · have hyRep := (Finset.mem_filter.mp hfrozen).1
    have hyCarrier := (Finset.mem_filter.mp hyRep).1
    have hx := (mem_lowWheelOthelloTaggedDowncrossCarrier.mp hyCarrier).2
    have hp := (lowWheelOthelloDowncrossPart_adjacent_shell hx).1
    have hone : y.2.2 / lowWheelOthelloDowncrossPivot y = 1 := by
      rw [hfrozenData.1]
      exact Nat.div_self hp.pos
    rw [hone] at htail
    exact hqPrime.not_dvd_one htail

/-- Exact zero sum of the movable repeated Othello population. -/
theorem sum_lowWheelOthelloRepeatedMovablePart_eq_zero
    (R : ℕ) :
    (∑ y ∈ lowWheelOthelloRepeatedMovablePart R,
        lowWheelOthelloWeight y) = 0 := by
  have hcompress := lowWheelOthelloRepeatedLedger_eq_frozen R
  unfold lowWheelOthelloRepeatedLedger at hcompress
  rw [lowWheelOthelloRepeatedParent_eq_movable_union_frozen R,
    Finset.sum_union (lowWheelOthelloRepeatedMovable_disjoint_frozen R)] at hcompress
  simpa using hcompress

/-- **Exact late-parent cancellation.**  No estimate is taken. -/
theorem lateParentLedger_eq_zero
    (R : ℕ) :
    LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossLateParentLedger R = 0 := by
  rw [lowWheelCanonicalDowncrossLateParentLedger_eq_tagged,
    lowWheelCanonicalTaggedLateParentPart_eq_othelloRepeatedMovable]
  simpa [lowWheelTaggedDowncrossWeight, lowWheelOthelloWeight] using
    sum_lowWheelOthelloRepeatedMovablePart_eq_zero R

/-- The complete canonical downcross ledger is therefore exactly the oriented
first-crossing ledger. -/
theorem downcrossLedger_eq_orientedLedger
    (R : ℕ) :
    lowWheelCanonicalDowncrossLedger R =
      LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossOrientedLedger R := by
  rw [LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossLedger_eq_late_add_oriented,
    lateParentLedger_eq_zero]
  simp

/-- Remaining quantitative core after exact late-parent cancellation. -/
def SquareRootCanonicalOrientedLinearBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      ‖LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossOrientedLedger R‖ ≤
        C * (R : ℝ)

/-- The oriented linear bound is exactly strong enough to discharge the
primitive downcross seam. -/
theorem canonicalDowncrossLinear_of_orientedLinear
    (horiented : SquareRootCanonicalOrientedLinearBound) :
    SquareRootCanonicalDowncrossLinearBound := by
  rcases horiented with ⟨C, hC, hO⟩
  refine ⟨C, hC, ?_⟩
  intro R hR
  rw [downcrossLedger_eq_orientedLedger]
  exact hO R hR

/-- Consequently the only remaining quantitative theorem implies RH through the
already-native square-prefix energy bridge. -/
theorem riemannHypothesis_of_canonicalOrientedLinear
    (horiented : SquareRootCanonicalOrientedLinearBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_canonicalDowncrossLinear
    (canonicalDowncrossLinear_of_orientedLinear horiented)

end LateParentCancellation

end RHLean.Proof
