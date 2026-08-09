import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Analysis.CanonicalHighSectorBridge
import RHLean.Proof.CanonicalGapPrefixGram

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapAncestryEnergyBridge

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge
open CanonicalGapPrefixGram

/-!
# Canonical ancestry energy interface

This module is the exact interface between the finite canonical ancestry flow and
its protected square-prefix energy target. It contains only finite algebraic
identities. No analytic estimate is asserted.
-/

/-! ## Exact protected-sequence realization -/

/-- Admissible source products are squarefree. -/
theorem sourceProduct_squarefree_of_admissible {B : ℕ} {s : SourceIndex B}
    (hs : SourceAdmissible s) : Squarefree (sourceProduct s) := by
  rcases hs with ⟨hq, _hcpos, hsq, hcop, _hdom⟩
  exact (Nat.squarefree_mul hcop).2 ⟨hq.squarefree, hsq⟩

/-- Admissible source products are strictly larger than one. -/
theorem one_lt_sourceProduct_of_admissible {B : ℕ} {s : SourceIndex B}
    (hs : SourceAdmissible s) : 1 < sourceProduct s := by
  rcases hs with ⟨hq, hcpos, _hsq, _hcop, _hdom⟩
  unfold sourceProduct
  nlinarith [hq.two_le]

/-- The native square-root clock cutoff is exactly the complete-square endpoint. -/
theorem sourceClock_le_iff_sourceProduct_le_endpoint
    {B x : ℕ} (s : SourceIndex B) :
    sourceClock B s ≤ x ↔
      sourceProduct s ≤ RHLean.Analysis.squarePrefixEndpoint x := by
  unfold sourceClock
  constructor
  · intro hclock
    have hsqrt : Nat.sqrt (sourceProduct s) < x + 1 := by omega
    have hlt : sourceProduct s < (x + 1) ^ 2 :=
      (Nat.sqrt_lt').1 hsqrt
    rw [← RHLean.Analysis.squarePrefixEndpoint_add_one x] at hlt
    omega
  · intro hprod
    have hlt :
        sourceProduct s < RHLean.Analysis.squarePrefixEndpoint x + 1 :=
      Nat.lt_succ_of_le hprod
    rw [RHLean.Analysis.squarePrefixEndpoint_add_one x] at hlt
    have hsqrt : Nat.sqrt (sourceProduct s) < x + 1 :=
      (Nat.sqrt_lt').2 hlt
    omega

/-- Active admissible sources under a square-prefix clock. -/
noncomputable def activeSourceSet (B x : ℕ) : Finset (SourceIndex B) := by
  classical
  exact Finset.univ.filter fun s =>
    SourceAdmissible s ∧ sourceClock B s ≤ x

/-- Squarefree integers larger than one under the same clock. -/
noncomputable def activeSquarefreeIntegerSet (x : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.range (RHLean.Analysis.squarePrefixEndpoint x + 1)).filter
      fun m => 2 ≤ m ∧ Squarefree m

/-- The source prefix is the sum over active admissible source indices. -/
theorem sourcePrefix_eq_activeSource_sum (B x : ℕ) :
    sourcePrefix B x = ∑ s ∈ activeSourceSet B x, sourceWeight s := by
  classical
  rw [sourcePrefix_eq_sum]
  unfold activeSourceSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hadm : SourceAdmissible s <;>
    simp [sourceClock, sourceWeight, hadm]

/-- Exact finite reindexing from native source indices to squarefree integers. -/
theorem sourcePrefix_eq_squarefreeInteger_sum
    {B x : ℕ}
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    sourcePrefix B x =
      ∑ m ∈ activeSquarefreeIntegerSet x, (μ m : ℤ) := by
  classical
  rw [sourcePrefix_eq_activeSource_sum]
  refine Finset.sum_bij (fun s _hs => sourceProduct s) ?_ ?_ ?_ ?_
  · intro s hs
    have hsdata : SourceAdmissible s ∧ sourceClock B s ≤ x := by
      simpa [activeSourceSet] using hs
    have hprodle :=
      (sourceClock_le_iff_sourceProduct_le_endpoint (x := x) s).1 hsdata.2
    have hprodgt := one_lt_sourceProduct_of_admissible hsdata.1
    simp only [activeSquarefreeIntegerSet, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hprodle, hprodgt,
      sourceProduct_squarefree_of_admissible hsdata.1⟩
  · intro s₁ hs₁ s₂ hs₂ heq
    have hs₁data : SourceAdmissible s₁ ∧ sourceClock B s₁ ≤ x := by
      simpa [activeSourceSet] using hs₁
    have hs₂data : SourceAdmissible s₂ ∧ sourceClock B s₂ ≤ x := by
      simpa [activeSourceSet] using hs₂
    exact sourceProduct_injective_on_admissible hs₁data.1 hs₂data.1 heq
  · intro m hm
    have hmdata :
        m < RHLean.Analysis.squarePrefixEndpoint x + 1 ∧
          2 ≤ m ∧ Squarefree m := by
      simpa [activeSquarefreeIntegerSet] using hm
    have hmgt : 1 < m := hmdata.2.1
    have hmend : m ≤ RHLean.Analysis.squarePrefixEndpoint x :=
      Nat.lt_succ_iff.mp hmdata.1
    have hmB : m ≤ B := hmend.trans hB
    let s := canonicalSourceIndex B m hmdata.2.2 hmgt hmB
    refine ⟨s, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ s, ?_⟩
      refine ⟨canonicalSourceIndex_admissible hmdata.2.2 hmgt hmB, ?_⟩
      apply (sourceClock_le_iff_sourceProduct_le_endpoint (x := x) s).2
      rw [canonicalSourceIndex_product hmdata.2.2 hmgt hmB]
      exact hmend
    · exact canonicalSourceIndex_product hmdata.2.2 hmgt hmB
  · intro s hs
    have hsdata : SourceAdmissible s ∧ sourceClock B s ≤ x := by
      simpa [activeSourceSet] using hs
    exact sourceWeight_of_admissible s hsdata.1

/-- Filtering to squarefree terms does not change the Möbius tail beginning at
`m=2`. -/
theorem activeSquarefreeInteger_sum_eq_Ico_sum (x : ℕ) :
    (∑ m ∈ activeSquarefreeIntegerSet x, (μ m : ℤ)) =
      ∑ m ∈ Finset.Ico 2 (RHLean.Analysis.squarePrefixEndpoint x + 1),
        (μ m : ℤ) := by
  classical
  unfold activeSquarefreeIntegerSet
  rw [Finset.sum_filter]
  have hterm : ∀ m : ℕ,
      (if 2 ≤ m ∧ Squarefree m then (μ m : ℤ) else 0) =
        if 2 ≤ m then (μ m : ℤ) else 0 := by
    intro m
    by_cases hm2 : 2 ≤ m
    · by_cases hsq : Squarefree m
      · simp [hm2, hsq]
      · simp [hm2, hsq,
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    · simp [hm2]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  congr 1
  ext m
  simp [and_comm]

/-- Exact integer-valued realization, including the exceptional clock `x=0`. -/
theorem sourcePrefix_add_indicator_eq_mertens_sum
    {B x : ℕ}
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    sourcePrefix B x + indicator (1 ≤ x) =
      ∑ m ∈ Finset.range (RHLean.Analysis.squarePrefixEndpoint x + 1),
        (μ m : ℤ) := by
  rw [sourcePrefix_eq_squarefreeInteger_sum hB,
    activeSquarefreeInteger_sum_eq_Ico_sum]
  by_cases hx : x = 0
  · subst x
    simp [RHLean.Analysis.squarePrefixEndpoint, indicator]
  · have hx1 : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx
    have htwo : 2 ≤ x + 1 := by omega
    have hend : 2 ≤ RHLean.Analysis.squarePrefixEndpoint x + 1 := by
      rw [RHLean.Analysis.squarePrefixEndpoint_add_one]
      exact le_trans (by norm_num : 2 ≤ 2 ^ 2)
        (Nat.pow_le_pow_left htwo 2)
    rw [← Finset.sum_range_add_sum_Ico
      (f := fun m : ℕ => (μ m : ℤ)) hend]
    have hsmall :
        (∑ m ∈ Finset.range 2, (μ m : ℤ)) = 1 := by
      simp [Finset.sum_range_succ]
    rw [hsmall]
    simp [indicator, hx1, add_comm]

/-- Exact complex realization with the endpoint correction expressed explicitly. -/
theorem sourcePrefix_add_indicator_eq_squarePrefixMertens
    {B x : ℕ}
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    ((sourcePrefix B x + indicator (1 ≤ x) : ℤ) : ℂ) =
      RHLean.Analysis.squarePrefixMertens x := by
  rw [sourcePrefix_add_indicator_eq_mertens_sum hB]
  unfold RHLean.Analysis.squarePrefixMertens RHLean.Analysis.mertensSummatory
  push_cast
  rfl

/-- For every nonzero square-prefix clock, the sole omitted source is `m=1`. -/
theorem sourcePrefix_add_one_eq_squarePrefixMertens
    {B x : ℕ}
    (hx : 1 ≤ x)
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    ((sourcePrefix B x : ℤ) : ℂ) + 1 =
      RHLean.Analysis.squarePrefixMertens x := by
  have h := sourcePrefix_add_indicator_eq_squarePrefixMertens hB
  simpa [indicator, hx, Int.cast_add] using h

/-! ## Finite successor generations -/

/-- Unsigned generation `j`, obtained by pulling the transport-root field through
`j` successor steps. -/
def sourceGeneration (B j : ℕ) : SourceIndex B → ℤ :=
  ((boundedSourceFlow B).successorOperator^[j])
    (boundedSourceFlow B).rootField

/-- Signed generation with the alternating renewal sign kept separate from the
unsigned successor field. -/
def signedSourceGeneration (B j : ℕ) : SourceIndex B → ℤ := fun s =>
  (-1 : ℤ) ^ j * sourceGeneration B j s

/-- The zeroth unsigned generation is the transport-root field. -/
theorem sourceGeneration_zero (B : ℕ) :
    sourceGeneration B 0 = (boundedSourceFlow B).rootField := by
  rfl

/-- One more generation is one more application of the successor operator. -/
theorem sourceGeneration_succ (B j : ℕ) :
    sourceGeneration B (j + 1) =
      (boundedSourceFlow B).successorOperator (sourceGeneration B j) := by
  unfold sourceGeneration
  simpa only [Nat.succ_eq_add_one] using
    Function.iterate_succ_apply'
      (boundedSourceFlow B).successorOperator j
      (boundedSourceFlow B).rootField

/-- The zeroth signed generation is still the transport-root field. -/
theorem signedSourceGeneration_zero (B : ℕ) :
    signedSourceGeneration B 0 = (boundedSourceFlow B).rootField := by
  funext s
  simp [signedSourceGeneration, sourceGeneration_zero]

/-- Consecutive signed generations satisfy the same alternating successor
recursion as the finite renewal expansion. -/
theorem signedSourceGeneration_succ (B j : ℕ) :
    signedSourceGeneration B (j + 1) =
      - (boundedSourceFlow B).successorOperator
          (signedSourceGeneration B j) := by
  funext s
  change
    (-1 : ℤ) ^ (j + 1) * sourceGeneration B (j + 1) s =
      - ((boundedSourceFlow B).successorOperator
          (fun t => (-1 : ℤ) ^ j * sourceGeneration B j t)) s
  rw [sourceGeneration_succ]
  cases hparent : (boundedSourceFlow B).parent s with
  | none =>
      simp [ParentFlow.successorOperator, hparent]
  | some p =>
      simp [ParentFlow.successorOperator, hparent, pow_succ]

/-- Reindexing the positive generations pulls one successor through the whole
finite sum. -/
theorem sum_signedSourceGeneration_succ (B depth : ℕ) :
    (∑ j ∈ Finset.range depth, signedSourceGeneration B (j + 1)) =
      - (boundedSourceFlow B).successorOperator
          (∑ j ∈ Finset.range depth, signedSourceGeneration B j) := by
  calc
    (∑ j ∈ Finset.range depth, signedSourceGeneration B (j + 1)) =
        ∑ j ∈ Finset.range depth,
          - (boundedSourceFlow B).successorOperator
              (signedSourceGeneration B j) := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [signedSourceGeneration_succ]
    _ = - ∑ j ∈ Finset.range depth,
          (boundedSourceFlow B).successorOperator
            (signedSourceGeneration B j) := by
          rw [Finset.sum_neg_distrib]
    _ = - (boundedSourceFlow B).successorOperator
          (∑ j ∈ Finset.range depth, signedSourceGeneration B j) := by
          rw [map_sum]

/-- The recursive `alternatingPrefix` is the conventional finite sum of the
signed successor generations. -/
theorem alternatingPrefix_eq_sum_signedSourceGenerations
    (B depth : ℕ) :
    alternatingPrefix (boundedSourceFlow B).successorOperator
        (boundedSourceFlow B).rootField depth =
      ∑ j ∈ Finset.range depth, signedSourceGeneration B j := by
  induction depth with
  | zero =>
      simp [alternatingPrefix]
  | succ depth ih =>
      rw [alternatingPrefix, Finset.sum_range_succ']
      rw [signedSourceGeneration_zero,
        sum_signedSourceGeneration_succ, ← ih]
      abel

/-- Pointwise finite recombination of the bounded source weight from all signed
generations. -/
theorem sourceWeight_eq_sum_signedGenerations (B : ℕ) :
    (boundedSourceFlow B).weight =
      ∑ j ∈ Finset.range (B + 1), signedSourceGeneration B j := by
  rw [boundedSource_weight_eq_finite_alternating,
    alternatingPrefix_eq_sum_signedSourceGenerations]

/-! ## Clock-pushed generation increments -/

/-- Clock-pushed prefix of one unsigned successor generation. -/
def generationPrefix (B j x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x (sourceGeneration B j)

/-- Square-block increment of one unsigned successor generation. -/
def generationBlockIncrement (B j : ℕ) : ℕ → ℤ
  | 0 => generationPrefix B j 0
  | n + 1 => generationPrefix B j (n + 1) - generationPrefix B j n

/-- Clock pushforward commutes exactly with the fixed sign of one generation. -/
theorem clockPushforward_signedSourceGeneration (B j x : ℕ) :
    clockPushforward (sourceClock B) x (signedSourceGeneration B j) =
      (-1 : ℤ) ^ j * generationPrefix B j x := by
  classical
  unfold signedSourceGeneration generationPrefix
  change
    (∑ s : SourceIndex B,
      if sourceClock B s ≤ x then
        (-1 : ℤ) ^ j * sourceGeneration B j s else 0) =
      (-1 : ℤ) ^ j *
        ∑ s : SourceIndex B,
          if sourceClock B s ≤ x then sourceGeneration B j s else 0
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hclock : sourceClock B s ≤ x <;> simp [hclock]

/-- The native source prefix is the finite signed sum of its clock-pushed
unsigned generation prefixes. -/
theorem sourcePrefix_eq_generation_sum (B x : ℕ) :
    sourcePrefix B x =
      ∑ j ∈ Finset.range (B + 1),
        (-1 : ℤ) ^ j * generationPrefix B j x := by
  unfold sourcePrefix
  rw [sourceWeight_eq_sum_signedGenerations]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact clockPushforward_signedSourceGeneration B j x

/-- Every source block increment is the full finite signed sum of its unsigned
generation block increments. -/
theorem sourceBlockIncrement_eq_generation_sum (B n : ℕ) :
    sourceBlockIncrement B n =
      ∑ j ∈ Finset.range (B + 1),
        (-1 : ℤ) ^ j * generationBlockIncrement B j n := by
  cases n with
  | zero =>
      simpa [sourceBlockIncrement, generationBlockIncrement] using
        sourcePrefix_eq_generation_sum B 0
  | succ n =>
      change
        sourcePrefix B (n + 1) - sourcePrefix B n =
          ∑ j ∈ Finset.range (B + 1),
            (-1 : ℤ) ^ j *
              (generationPrefix B j (n + 1) - generationPrefix B j n)
      rw [sourcePrefix_eq_generation_sum B (n + 1),
        sourcePrefix_eq_generation_sum B n]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

/-- Generation block increments telescope exactly to the clock-pushed generation
prefix. -/
theorem sum_generationBlockIncrement_eq_prefix (B j x : ℕ) :
    ∑ n ∈ Finset.range (x + 1), generationBlockIncrement B j n =
      generationPrefix B j x := by
  induction x with
  | zero =>
      simp [generationBlockIncrement]
  | succ x ih =>
      rw [Finset.sum_range_succ, ih]
      simp [generationBlockIncrement]

/-! ## Actual windows with inherited backlog -/

/-- Generation value inherited from before a window beginning at `N`. -/
def generationBacklog (B j N : ℕ) : ℤ :=
  generationPrefix B j (N - 1)

/-- Actual generation prefix at offset `r`, consisting of inherited backlog plus
all block increments in `[N, N+r]`. -/
def generationWindowPrefix (B j N r : ℕ) : ℤ :=
  generationBacklog B j N +
    ∑ n ∈ Finset.Icc N (N + r), generationBlockIncrement B j n

/-- Backlog plus the within-window increments reconstructs the actual generation
prefix, not merely its displacement from the window origin. -/
theorem generationWindowPrefix_eq
    {B j N r : ℕ} (hN : 1 ≤ N) :
    generationWindowPrefix B j N r = generationPrefix B j (N + r) := by
  have hIcc : Finset.Icc N (N + r) = Finset.Ico N (N + r + 1) := by
    ext n
    simp
    omega
  have hsplit : N ≤ N + r + 1 := by omega
  have hNrange : N - 1 + 1 = N := by omega
  unfold generationWindowPrefix generationBacklog
  rw [hIcc]
  calc
    generationPrefix B j (N - 1) +
        ∑ n ∈ Finset.Ico N (N + r + 1), generationBlockIncrement B j n =
      (∑ n ∈ Finset.range N, generationBlockIncrement B j n) +
        ∑ n ∈ Finset.Ico N (N + r + 1),
          generationBlockIncrement B j n := by
            rw [← sum_generationBlockIncrement_eq_prefix B j (N - 1),
              hNrange]
    _ = ∑ n ∈ Finset.range (N + r + 1),
          generationBlockIncrement B j n := by
            exact Finset.sum_range_add_sum_Ico
              (f := generationBlockIncrement B j) hsplit
    _ = generationPrefix B j (N + r) := by
          simpa using sum_generationBlockIncrement_eq_prefix B j (N + r)

/-- Summing the actual generation windows, including their inherited backlogs,
recovers the actual full source prefix at every point in the window. -/
theorem sourcePrefix_eq_generationWindow_sum
    {B N r : ℕ} (hN : 1 ≤ N) :
    sourcePrefix B (N + r) =
      ∑ j ∈ Finset.range (B + 1),
        (-1 : ℤ) ^ j * generationWindowPrefix B j N r := by
  rw [sourcePrefix_eq_generation_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [generationWindowPrefix_eq hN]

end CanonicalGapAncestryEnergyBridge

end RHLean.Proof
