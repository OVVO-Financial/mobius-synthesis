import Mathlib
import RHLean.Proof.FiniteOthelloMatching
import RHLean.Proof.LowWheelOthelloOppositeMove

/-!
# Repeated-parent Othello involution on the lightweight carrier

Choose the least movable prime and transfer it between the Boolean face and the
residual tail.  The complete movable-prime set is invariant under this move, so
the same prime is selected on the return edge.  States with no movable prime
are fixed.

Hence the repeated-parent carrier has a genuine sign-reversing involution whose
stable set is exactly the frozen repeated frontier.  This cancels every movable
repeated state exactly, with no cardinality or norm estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Native signed weight of one tagged downcross occurrence. -/
def lowWheelOthelloWeight
    (y : LowWheelOthelloTaggedDowncrossState) : ℂ :=
  canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)

/-- Total canonical opposite mate on repeated-parent states. -/
def lowWheelOthelloRepeatedOppositeMate
    (R : ℕ) (y : LowWheelOthelloTaggedDowncrossState) :
    LowWheelOthelloTaggedDowncrossState :=
  if _h : (lowWheelOthelloMovablePrimeSet R y).Nonempty then
    lowWheelOthelloParentToggleAt (lowWheelOthelloOppositePrime R y) y
  else y

/-- A fixed-prime parent transfer is involutive on a movable downcross state. -/
theorem lowWheelOthelloParentToggleAt_involutive
    {R q : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R)
    (hq : LowWheelOthelloMovablePrime y q) :
    lowWheelOthelloParentToggleAt q (lowWheelOthelloParentToggleAt q y) = y := by
  let y' := lowWheelOthelloParentToggleAt q y
  let y'' := lowWheelOthelloParentToggleAt q y'
  have hy' : y' ∈ lowWheelOthelloTaggedDowncrossCarrier R :=
    lowWheelOthelloParentToggleAt_mem hy hq
  have hq' : LowWheelOthelloMovablePrime y' q :=
    (lowWheelOthelloParentToggleAt_movablePrime_iff hy hq).mpr hq
  have hy'' : y'' ∈ lowWheelOthelloTaggedDowncrossCarrier R :=
    lowWheelOthelloParentToggleAt_mem hy' hq'
  have hft1 := lowWheelOthelloFaceTail_parentToggleAt hy hq
  have hft2 := lowWheelOthelloFaceTail_parentToggleAt hy' hq'
  have hftInv : lowWheelOthelloFaceTail y'' = lowWheelOthelloFaceTail y := by
    rw [hft2, hft1]
    exact lowWheelFaceTailToggleAt_involutive hq.1.pos
      (lowWheelOthelloFaceTail y)
  have hface : y''.1 = y.1 :=
    congrArg (fun z : LowWheelFaceTailState => z.1) hftInv
  have htail : lowWheelOthelloDowncrossTail y'' =
      lowWheelOthelloDowncrossTail y :=
    congrArg (fun z : LowWheelFaceTailState => z.2) hftInv
  have hpiv1 := lowWheelOthelloParentToggleAt_pivot hy hq
  have hpiv2 := lowWheelOthelloParentToggleAt_pivot hy' hq'
  have hpiv : lowWheelOthelloDowncrossPivot y'' =
      lowWheelOthelloDowncrossPivot y := hpiv2.trans hpiv1
  have hc1 := lowWheelOthelloParentToggleAt_cofactor q y
  have hc2 := lowWheelOthelloParentToggleAt_cofactor q y'
  have hcofactor : y''.2.1 = y.2.1 := hc2.trans hc1
  have hpk :=
    (lowWheelOthelloDowncrossPart_adjacent_shell
      (mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy).2).2.2.1
  have hpk'' :=
    (lowWheelOthelloDowncrossPart_adjacent_shell
      (mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy'').2).2.2.1
  have hk :
      lowWheelOthelloDowncrossPivot y * lowWheelOthelloDowncrossTail y =
        y.2.2 := by
    simpa [lowWheelOthelloDowncrossPivot, lowWheelOthelloDowncrossTail] using
      Nat.mul_div_cancel' hpk
  have hk'' :
      lowWheelOthelloDowncrossPivot y'' * lowWheelOthelloDowncrossTail y'' =
        y''.2.2 := by
    simpa [lowWheelOthelloDowncrossPivot, lowWheelOthelloDowncrossTail] using
      Nat.mul_div_cancel' hpk''
  have hquotient : y''.2.2 = y.2.2 := by
    calc
      y''.2.2 = lowWheelOthelloDowncrossPivot y'' *
          lowWheelOthelloDowncrossTail y'' := hk''.symm
      _ = lowWheelOthelloDowncrossPivot y *
          lowWheelOthelloDowncrossTail y := by rw [hpiv, htail]
      _ = y.2.2 := hk
  change y'' = y
  exact Prod.ext hface (Prod.ext hcofactor hquotient)

/-- The total opposite mate preserves the repeated-parent carrier. -/
theorem lowWheelOthelloRepeatedOppositeMate_mem
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloDowncrossRepeatedParentPart R) :
    lowWheelOthelloRepeatedOppositeMate R y ∈
      lowWheelOthelloDowncrossRepeatedParentPart R := by
  have hyCarrier := (Finset.mem_filter.mp hy).1
  unfold lowWheelOthelloRepeatedOppositeMate
  by_cases h : (lowWheelOthelloMovablePrimeSet R y).Nonempty
  · rw [dif_pos h]
    let q := lowWheelOthelloOppositePrime R y
    have hq : LowWheelOthelloMovablePrime y q :=
      (lowWheelOthelloOppositePrime_data h).2
    have htarget : lowWheelOthelloParentToggleAt q y ∈
        lowWheelOthelloTaggedDowncrossCarrier R :=
      lowWheelOthelloParentToggleAt_mem hyCarrier hq
    have hparent := lowWheelOthelloParentToggleAt_parent hyCarrier hq
    have hne := lowWheelOthelloParentToggleAt_ne hq
    apply Finset.mem_filter.mpr
    refine ⟨htarget, ?_⟩
    intro hunique
    have hyEq : y = lowWheelOthelloParentToggleAt q y :=
      hunique y hyCarrier hparent.symm
    exact hne hyEq.symm
  · rw [dif_neg h]
    exact hy

/-- The total repeated-parent opposite mate is involutive. -/
theorem lowWheelOthelloRepeatedOppositeMate_involutive
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloDowncrossRepeatedParentPart R) :
    lowWheelOthelloRepeatedOppositeMate R
        (lowWheelOthelloRepeatedOppositeMate R y) = y := by
  have hyCarrier := (Finset.mem_filter.mp hy).1
  unfold lowWheelOthelloRepeatedOppositeMate
  by_cases h : (lowWheelOthelloMovablePrimeSet R y).Nonempty
  · rw [dif_pos h]
    let q := lowWheelOthelloOppositePrime R y
    have hq : LowWheelOthelloMovablePrime y q :=
      (lowWheelOthelloOppositePrime_data h).2
    have hset := lowWheelOthelloMovablePrimeSet_parentToggleAt hyCarrier hq
    have htarget :
        (lowWheelOthelloMovablePrimeSet R
          (lowWheelOthelloParentToggleAt q y)).Nonempty := by
      rw [hset]
      exact h
    rw [dif_pos htarget]
    have hqSame := lowWheelOthelloOppositePrime_parentToggleAt hyCarrier hq
    rw [hqSame]
    exact lowWheelOthelloParentToggleAt_involutive hyCarrier hq
  · rw [dif_neg h, dif_neg h]

/-- Every moved opposite edge reverses the tagged weight. -/
theorem lowWheelOthelloRepeatedOppositeMate_weight_neg
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (_hy : y ∈ lowWheelOthelloDowncrossRepeatedParentPart R)
    (hne : lowWheelOthelloRepeatedOppositeMate R y ≠ y) :
    lowWheelOthelloWeight (lowWheelOthelloRepeatedOppositeMate R y) =
      -lowWheelOthelloWeight y := by
  unfold lowWheelOthelloRepeatedOppositeMate at hne ⊢
  by_cases h : (lowWheelOthelloMovablePrimeSet R y).Nonempty
  · rw [dif_pos h] at hne ⊢
    exact lowWheelOthelloParentToggleAt_weight_neg
      (lowWheelOthelloOppositePrime_data h).2
  · rw [dif_neg h] at hne
    exact (hne rfl).elim

/-- No movable prime exists exactly at the frozen first-crossing shape. -/
theorem lowWheelOthelloMovablePrimeSet_not_nonempty_iff_frozen
    {R : ℕ} {y : LowWheelOthelloTaggedDowncrossState}
    (hy : y ∈ lowWheelOthelloTaggedDowncrossCarrier R) :
    ¬ (lowWheelOthelloMovablePrimeSet R y).Nonempty ↔
      LowWheelOthelloFrozenShape y := by
  constructor
  · intro hnone
    rcases lowWheelOthelloDowncross_movable_or_frozen hy with hmov | hfrozen
    · have hset : (lowWheelOthelloMovablePrimeSet R y).Nonempty :=
        (lowWheelOthelloMovablePrimeSet_nonempty_iff hy).2 hmov
      exact (hnone hset).elim
    · exact hfrozen
  · intro hfrozen hnonempty
    have hmov := (lowWheelOthelloMovablePrimeSet_nonempty_iff hy).1 hnonempty
    rcases hmov with ⟨q, hqPrime, hpq, hactive⟩
    rcases hactive with hface | htail
    · have hqlt := hfrozen.2 q hface
      omega
    · have hx := (mem_lowWheelOthelloTaggedDowncrossCarrier.mp hy).2
      have hp := (lowWheelOthelloDowncrossPart_adjacent_shell hx).1
      have hone : y.2.2 / lowWheelOthelloDowncrossPivot y = 1 := by
        rw [hfrozen.1]
        exact Nat.div_self hp.pos
      rw [hone] at htail
      exact hqPrime.not_dvd_one htail

/-- The stable set is exactly the frozen repeated frontier. -/
theorem finiteOthelloStablePart_lowWheelOthelloRepeated_eq_frozen
    (R : ℕ) :
    finiteOthelloStablePart
        (lowWheelOthelloDowncrossRepeatedParentPart R)
        (lowWheelOthelloRepeatedOppositeMate R) =
      lowWheelOthelloRepeatedFrozenPart R := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hyRep, hfix⟩
    have hyCarrier := (Finset.mem_filter.mp hyRep).1
    have hnone : ¬ (lowWheelOthelloMovablePrimeSet R y).Nonempty := by
      intro h
      unfold lowWheelOthelloRepeatedOppositeMate at hfix
      rw [dif_pos h] at hfix
      exact lowWheelOthelloParentToggleAt_ne
        (lowWheelOthelloOppositePrime_data h).2 hfix
    exact Finset.mem_filter.mpr
      ⟨hyRep,
        (lowWheelOthelloMovablePrimeSet_not_nonempty_iff_frozen hyCarrier).1 hnone⟩
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hyRep, hfrozen⟩
    have hyCarrier := (Finset.mem_filter.mp hyRep).1
    apply Finset.mem_filter.mpr
    refine ⟨hyRep, ?_⟩
    have hnone :=
      (lowWheelOthelloMovablePrimeSet_not_nonempty_iff_frozen hyCarrier).2 hfrozen
    unfold lowWheelOthelloRepeatedOppositeMate
    rw [dif_neg hnone]

/-- Signed repeated-parent mass. -/
def lowWheelOthelloRepeatedLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelOthelloDowncrossRepeatedParentPart R,
    lowWheelOthelloWeight y

/-- **Exact repeated-parent compression.**  Every movable repeated state
cancels; the whole repeated signed mass is carried by the frozen frontier. -/
theorem lowWheelOthelloRepeatedLedger_eq_frozen
    (R : ℕ) :
    lowWheelOthelloRepeatedLedger R =
      ∑ y ∈ lowWheelOthelloRepeatedFrozenPart R,
        lowWheelOthelloWeight y := by
  unfold lowWheelOthelloRepeatedLedger
  rw [← finiteOthelloStablePart_lowWheelOthelloRepeated_eq_frozen R]
  exact sum_finiteOthelloRegion_eq_stable
    (lowWheelOthelloDowncrossRepeatedParentPart R)
    (lowWheelOthelloRepeatedOppositeMate R)
    lowWheelOthelloWeight
    (fun _y hy => lowWheelOthelloRepeatedOppositeMate_mem hy)
    (fun _y hy => lowWheelOthelloRepeatedOppositeMate_involutive hy)
    (fun _y hy hne => lowWheelOthelloRepeatedOppositeMate_weight_neg hy hne)

end RHLean.Proof
