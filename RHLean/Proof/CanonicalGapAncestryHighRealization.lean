import RHLean.Proof.CanonicalGapAncestryGram

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapAncestryHighRealization

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge
open CanonicalGapAncestryEnergyBridge
open CanonicalGapAncestryGram

attribute [local instance] Classical.propDecidable

/-!
# Canonical high-source realization

This module realizes the native canonical high-height sector directly on the
finite ancestry source field. It records only exact finite identities:

* complementary low and high source projectors,
* the full signed-generation recombination after high projection,
* exact reindexing of the projected source prefix to the native
  `canonicalHighPrefix`, and
* the corresponding exact `localSequenceEnergy` identity.

No analytic estimate is asserted.
-/

/-! ## Source-height projectors -/

/-- Pointwise projection to sources lying in the native canonical low-height
sector at their own square-root entry clock. -/
noncomputable def sourceLowProjector (Λ : ℝ) (B : ℕ) :
    (SourceIndex B → ℤ) →+ (SourceIndex B → ℤ) where
  toFun f s :=
    if IsCanonicalLowHeight Λ (sourceClock B s) (sourceProduct s) then f s else 0
  map_zero' := by
    funext s
    by_cases h : IsCanonicalLowHeight Λ (sourceClock B s) (sourceProduct s) <;>
      simp [h]
  map_add' f g := by
    funext s
    by_cases h : IsCanonicalLowHeight Λ (sourceClock B s) (sourceProduct s) <;>
      simp [h]

/-- Pointwise projection to sources lying in the native canonical high-height
sector at their own square-root entry clock. -/
noncomputable def sourceHighProjector (Λ : ℝ) (B : ℕ) :
    (SourceIndex B → ℤ) →+ (SourceIndex B → ℤ) where
  toFun f s :=
    if IsCanonicalHighHeight Λ (sourceClock B s) (sourceProduct s) then f s else 0
  map_zero' := by
    funext s
    by_cases h : IsCanonicalHighHeight Λ (sourceClock B s) (sourceProduct s) <;>
      simp [h]
  map_add' f g := by
    funext s
    by_cases h : IsCanonicalHighHeight Λ (sourceClock B s) (sourceProduct s) <;>
      simp [h]

/-- The low and high projectors partition every source field exactly. -/
theorem sourceLowProjector_add_sourceHighProjector
    (Λ : ℝ) (B : ℕ) (f : SourceIndex B → ℤ) :
    sourceLowProjector Λ B f + sourceHighProjector Λ B f = f := by
  funext s
  by_cases h : IsCanonicalLowHeight Λ (sourceClock B s) (sourceProduct s)
  · simp [sourceLowProjector, sourceHighProjector, IsCanonicalHighHeight, h]
  · simp [sourceLowProjector, sourceHighProjector, IsCanonicalHighHeight, h]

/-- Clock-pushed low source prefix. -/
def sourceLowPrefix (Λ : ℝ) (B x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x
    (sourceLowProjector Λ B (boundedSourceFlow B).weight)

/-- Clock-pushed high source prefix. -/
def sourceHighPrefix (Λ : ℝ) (B x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x
    (sourceHighProjector Λ B (boundedSourceFlow B).weight)

/-- Literal finite-sum form of the projected high source prefix. -/
theorem sourceHighPrefix_eq_sum (Λ : ℝ) (B x : ℕ) :
    sourceHighPrefix Λ B x =
      ∑ s : SourceIndex B,
        if sourceClock B s ≤ x then
          if IsCanonicalHighHeight Λ (sourceClock B s) (sourceProduct s) then
            sourceWeight s else 0
        else 0 := by
  rfl

/-- Exact low/high recombination of the bounded source prefix. -/
theorem sourcePrefix_eq_sourceLow_add_high (Λ : ℝ) (B x : ℕ) :
    sourcePrefix B x = sourceLowPrefix Λ B x + sourceHighPrefix Λ B x := by
  unfold sourcePrefix sourceLowPrefix sourceHighPrefix
  rw [← map_add]
  rw [sourceLowProjector_add_sourceHighProjector]

/-! ## Projected successor generations -/

/-- High-projected clock pushforward of one signed successor generation. -/
def sourceHighGenerationPrefix (Λ : ℝ) (B j x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x
    (sourceHighProjector Λ B (signedSourceGeneration B j))

/-- The high source prefix remains the complete finite signed-generation sum
after projection. -/
theorem sourceHighPrefix_eq_generation_sum
    (Λ : ℝ) (B x : ℕ) :
    sourceHighPrefix Λ B x =
      ∑ j ∈ Finset.range (B + 1), sourceHighGenerationPrefix Λ B j x := by
  unfold sourceHighPrefix sourceHighGenerationPrefix
  rw [sourceWeight_eq_sum_signedGenerations]
  rw [map_sum, map_sum]

/-- Actual high source path in a window beginning at `N`. -/
def sourceHighWindowPath (Λ : ℝ) (B N : ℕ) : ℕ → ℤ := fun r =>
  sourceHighPrefix Λ B (N + r)

/-- Actual high-projected signed generation path in a window beginning at `N`. -/
def sourceHighGenerationWindowPath
    (Λ : ℝ) (B j N : ℕ) : ℕ → ℤ := fun r =>
  sourceHighGenerationPrefix Λ B j (N + r)

/-- Exact pathwise high-projected generation recombination. -/
theorem sourceHighWindowPath_eq_generation_sum
    (Λ : ℝ) (B N : ℕ) :
    sourceHighWindowPath Λ B N =
      fun r => ∑ j ∈ Finset.range (B + 1),
        sourceHighGenerationWindowPath Λ B j N r := by
  funext r
  unfold sourceHighWindowPath sourceHighGenerationWindowPath
  exact sourceHighPrefix_eq_generation_sum Λ B (N + r)

/-- Full raw Gram ledger after native high-height projection. -/
theorem sourceHighWindowEnergy_eq_generationGram
    (Λ : ℝ) (B N H : ℕ) :
    windowPathEnergy H (sourceHighWindowPath Λ B N) =
      ∑ j ∈ Finset.range (B + 1),
        ∑ k ∈ Finset.range (B + 1),
          windowPathCrossEnergy H
            (sourceHighGenerationWindowPath Λ B j N)
            (sourceHighGenerationWindowPath Λ B k N) := by
  rw [sourceHighWindowPath_eq_generation_sum]
  exact windowPathEnergy_sum H (Finset.range (B + 1))
    (fun j => sourceHighGenerationWindowPath Λ B j N)

/-- Full centered Gram ledger after native high-height projection. -/
theorem sourceHighWindowCenteredEnergy_eq_generationGram
    (Λ : ℝ) (B N H : ℕ) :
    centeredWindowEnergy H (sourceHighWindowPath Λ B N) =
      ∑ j ∈ Finset.range (B + 1),
        ∑ k ∈ Finset.range (B + 1),
          centeredWindowCrossEnergy H
            (sourceHighGenerationWindowPath Λ B j N)
            (sourceHighGenerationWindowPath Λ B k N) := by
  rw [sourceHighWindowPath_eq_generation_sum]
  exact centeredWindowEnergy_sum H (Finset.range (B + 1))
    (fun j => sourceHighGenerationWindowPath Λ B j N)

/-! ## Exact source-to-integer high-sector reindexing -/

/-- Active admissible high sources under a square-prefix clock. -/
noncomputable def activeHighSourceSet (Λ : ℝ) (B x : ℕ) :
    Finset (SourceIndex B) := by
  classical
  exact Finset.univ.filter fun s =>
    SourceAdmissible s ∧ sourceClock B s ≤ x ∧
      IsCanonicalHighHeight Λ (sourceClock B s) (sourceProduct s)

/-- Active squarefree integers larger than one in the same high sector. -/
noncomputable def activeHighSquarefreeIntegerSet (Λ : ℝ) (x : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.range (RHLean.Analysis.squarePrefixEndpoint x + 1)).filter
      fun m => 2 ≤ m ∧ Squarefree m ∧
        IsCanonicalHighHeight Λ (Nat.sqrt m) m

/-- The high source prefix is the sum over active admissible high sources. -/
theorem sourceHighPrefix_eq_activeHighSource_sum
    (Λ : ℝ) (B x : ℕ) :
    sourceHighPrefix Λ B x =
      ∑ s ∈ activeHighSourceSet Λ B x, sourceWeight s := by
  classical
  rw [sourceHighPrefix_eq_sum]
  unfold activeHighSourceSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hadm : SourceAdmissible s <;>
  by_cases hclock : sourceClock B s ≤ x <;>
  by_cases hhigh : IsCanonicalHighHeight Λ (sourceClock B s) (sourceProduct s) <;>
    simp [sourceWeight, hadm, hclock, hhigh]

/-- Exact finite reindexing of the high source prefix to squarefree integers. -/
theorem sourceHighPrefix_eq_squarefreeInteger_sum
    {Λ : ℝ} {B x : ℕ}
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    sourceHighPrefix Λ B x =
      ∑ m ∈ activeHighSquarefreeIntegerSet Λ x, (μ m : ℤ) := by
  classical
  rw [sourceHighPrefix_eq_activeHighSource_sum]
  refine Finset.sum_bij (fun s _hs => sourceProduct s) ?_ ?_ ?_ ?_
  · intro s hs
    have hsdata :
        SourceAdmissible s ∧ sourceClock B s ≤ x ∧
          IsCanonicalHighHeight Λ (sourceClock B s) (sourceProduct s) := by
      simpa [activeHighSourceSet] using hs
    have hprodle :=
      (sourceClock_le_iff_sourceProduct_le_endpoint (x := x) s).1 hsdata.2.1
    have hprodgt := one_lt_sourceProduct_of_admissible hsdata.1
    simp only [activeHighSquarefreeIntegerSet, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hprodle, hprodgt,
      sourceProduct_squarefree_of_admissible hsdata.1,
      by simpa [sourceClock] using hsdata.2.2⟩
  · intro s₁ hs₁ s₂ hs₂ heq
    have hs₁data : SourceAdmissible s₁ := by
      have hs₁full :
          SourceAdmissible s₁ ∧ sourceClock B s₁ ≤ x ∧
            IsCanonicalHighHeight Λ (sourceClock B s₁) (sourceProduct s₁) := by
        simpa [activeHighSourceSet] using hs₁
      exact hs₁full.1
    have hs₂data : SourceAdmissible s₂ := by
      have hs₂full :
          SourceAdmissible s₂ ∧ sourceClock B s₂ ≤ x ∧
            IsCanonicalHighHeight Λ (sourceClock B s₂) (sourceProduct s₂) := by
        simpa [activeHighSourceSet] using hs₂
      exact hs₂full.1
    exact sourceProduct_injective_on_admissible hs₁data hs₂data heq
  · intro m hm
    have hmdata :
        m < RHLean.Analysis.squarePrefixEndpoint x + 1 ∧
          2 ≤ m ∧ Squarefree m ∧
            IsCanonicalHighHeight Λ (Nat.sqrt m) m := by
      simpa [activeHighSquarefreeIntegerSet] using hm
    have hmgt : 1 < m := hmdata.2.1
    have hmend : m ≤ RHLean.Analysis.squarePrefixEndpoint x :=
      Nat.lt_succ_iff.mp hmdata.1
    have hmB : m ≤ B := hmend.trans hB
    let s := canonicalSourceIndex B m hmdata.2.2.1 hmgt hmB
    refine ⟨s, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ s, ?_⟩
      refine ⟨canonicalSourceIndex_admissible hmdata.2.2.1 hmgt hmB, ?_, ?_⟩
      · apply (sourceClock_le_iff_sourceProduct_le_endpoint (x := x) s).2
        rw [canonicalSourceIndex_product hmdata.2.2.1 hmgt hmB]
        exact hmend
      · rw [canonicalSourceIndex_clock hmdata.2.2.1 hmgt hmB,
          canonicalSourceIndex_product hmdata.2.2.1 hmgt hmB]
        exact hmdata.2.2.2
    · exact canonicalSourceIndex_product hmdata.2.2.1 hmgt hmB
  · intro s hs
    have hsfull :
        SourceAdmissible s ∧ sourceClock B s ≤ x ∧
          IsCanonicalHighHeight Λ (sourceClock B s) (sourceProduct s) := by
      simpa [activeHighSourceSet] using hs
    exact sourceWeight_of_admissible s hsfull.1

/-! ## Native high prefix as an integer sum -/

/-- Integer-valued native canonical high increment. -/
def canonicalHighIntegerIncrement (Λ : ℝ) (j : ℕ) : ℤ :=
  ∑ m ∈ canonicalSquareBlock j,
    if IsCanonicalHighHeight Λ j m then (μ m : ℤ) else 0

/-- Integer-valued native canonical high prefix. -/
def canonicalHighIntegerPrefix (Λ : ℝ) (x : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (x + 1), canonicalHighIntegerIncrement Λ j

/-- Every integer in square block `j` has square root exactly `j`. -/
theorem sqrt_eq_of_mem_canonicalSquareBlock
    {j m : ℕ} (hm : m ∈ canonicalSquareBlock j) :
    Nat.sqrt m = j := by
  have hmIco : m ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2) := by
    simpa [canonicalSquareBlock] using hm
  have hsqrt : j = Nat.sqrt m :=
    (Nat.eq_sqrt').2 (Finset.mem_Ico.mp hmIco)
  exact hsqrt.symm

/-- Flattening the consecutive square blocks gives the exact square-root-indexed
integer high prefix. -/
theorem canonicalHighIntegerPrefix_eq_range_sum
    (Λ : ℝ) (x : ℕ) :
    canonicalHighIntegerPrefix Λ x =
      ∑ m ∈ Finset.range (RHLean.Analysis.squarePrefixEndpoint x + 1),
        if IsCanonicalHighHeight Λ (Nat.sqrt m) m then (μ m : ℤ) else 0 := by
  induction x with
  | zero =>
      simp [canonicalHighIntegerPrefix, canonicalHighIntegerIncrement,
        canonicalSquareBlock, RHLean.Analysis.squarePrefixEndpoint]
  | succ x ih =>
      rw [canonicalHighIntegerPrefix, Finset.sum_range_succ]
      change canonicalHighIntegerPrefix Λ x +
        canonicalHighIntegerIncrement Λ (x + 1) = _
      rw [ih]
      unfold canonicalHighIntegerIncrement canonicalSquareBlock
      rw [RHLean.Analysis.squarePrefixEndpoint_add_one]
      rw [RHLean.Analysis.squarePrefixEndpoint_add_one]
      have hblock :
          (∑ m ∈ Finset.Ico ((x + 1) ^ 2) ((x + 2) ^ 2),
              if IsCanonicalHighHeight Λ (x + 1) m then (μ m : ℤ) else 0) =
            ∑ m ∈ Finset.Ico ((x + 1) ^ 2) ((x + 2) ^ 2),
              if IsCanonicalHighHeight Λ (Nat.sqrt m) m then (μ m : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro m hm
        have hsqrt : Nat.sqrt m = x + 1 := by
          apply sqrt_eq_of_mem_canonicalSquareBlock
          simpa [canonicalSquareBlock, Nat.add_assoc] using hm
        rw [hsqrt]
      rw [hblock]
      have hle : (x + 1) ^ 2 ≤ (x + 2) ^ 2 := by
        exact Nat.pow_le_pow_left (by omega) 2
      simpa [Nat.add_assoc] using
        (Finset.sum_range_add_sum_Ico
          (fun m : ℕ =>
            if IsCanonicalHighHeight Λ (Nat.sqrt m) m then (μ m : ℤ) else 0)
          hle)

/-- For nonnegative cutoff, filtering to squarefree integers larger than one does
not change the canonical high prefix. The excluded source `m=1` is low. -/
theorem canonicalHighIntegerPrefix_eq_activeHighSquarefree_sum
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (x : ℕ) :
    canonicalHighIntegerPrefix Λ x =
      ∑ m ∈ activeHighSquarefreeIntegerSet Λ x, (μ m : ℤ) := by
  rw [canonicalHighIntegerPrefix_eq_range_sum]
  unfold activeHighSquarefreeIntegerSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hm2 : 2 ≤ m
  · by_cases hsq : Squarefree m
    · by_cases hhigh : IsCanonicalHighHeight Λ (Nat.sqrt m) m <;>
        simp [hm2, hsq, hhigh]
    · simp [hm2, hsq]
  · have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with rfl | rfl
    · simp
    · simp [hm2, IsCanonicalHighHeight, IsCanonicalLowHeight,
        canonicalHeightTwice, canonicalLargestPrimeFactor,
        canonicalCofactor, hΛ]

/-- Casting the integer high increment gives the native complex increment. -/
theorem canonicalHighIntegerIncrement_cast
    (Λ : ℝ) (j : ℕ) :
    ((canonicalHighIntegerIncrement Λ j : ℤ) : ℂ) =
      canonicalHighIncrement Λ j := by
  unfold canonicalHighIntegerIncrement canonicalHighIncrement
    canonicalMoebiusWeight
  push_cast
  apply Finset.sum_congr rfl
  intro m _hm
  rfl

/-- Casting the integer high prefix gives the native complex high prefix. -/
theorem canonicalHighIntegerPrefix_cast
    (Λ : ℝ) (x : ℕ) :
    ((canonicalHighIntegerPrefix Λ x : ℤ) : ℂ) =
      canonicalHighPrefix Λ x := by
  unfold canonicalHighIntegerPrefix canonicalHighPrefix
  push_cast
  apply Finset.sum_congr rfl
  intro j _hj
  exact canonicalHighIntegerIncrement_cast Λ j

/-- Exact pointwise realization of the native canonical high prefix by the
bounded ancestry source field. -/
theorem sourceHighPrefix_cast_eq_canonicalHighPrefix
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {B x : ℕ}
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    ((sourceHighPrefix Λ B x : ℤ) : ℂ) = canonicalHighPrefix Λ x := by
  rw [sourceHighPrefix_eq_squarefreeInteger_sum hB]
  rw [← canonicalHighIntegerPrefix_eq_activeHighSquarefree_sum hΛ x]
  exact canonicalHighIntegerPrefix_cast Λ x

/-- Exact local-energy transport from the ancestry high source prefix to the
protected native canonical high sequence. -/
theorem localSequenceEnergy_sourceHighPrefix_eq_canonicalHighPrefix
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {B N H : ℕ}
    (hB : ∀ r ∈ Finset.range H,
      RHLean.Analysis.squarePrefixEndpoint (N + r) ≤ B) :
    RHLean.Analysis.localSequenceEnergy
        (fun n => ((sourceHighPrefix Λ B n : ℤ) : ℂ)) N H =
      RHLean.Analysis.localSequenceEnergy (canonicalHighPrefix Λ) N H := by
  unfold RHLean.Analysis.localSequenceEnergy
  apply Finset.sum_congr rfl
  intro r hr
  change ‖((sourceHighPrefix Λ B (N + r) : ℤ) : ℂ)‖ ^ 2 =
    ‖canonicalHighPrefix Λ (N + r)‖ ^ 2
  rw [sourceHighPrefix_cast_eq_canonicalHighPrefix hΛ (hB r hr)]

end CanonicalGapAncestryHighRealization

end RHLean.Proof
