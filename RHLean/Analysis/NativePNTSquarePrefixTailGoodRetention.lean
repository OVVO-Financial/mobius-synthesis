import RHLean.Analysis.NativePNTSquarePrefixTailIntervalUpper
import RHLean.Analysis.NativePNTSquarePrefixGoodMassRate

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Restricting the global good fibres to the contracted quotient tail loses at
most the entire finite-prefix reciprocal mass. -/
theorem nativeLambdaTwoGoodRecipMass_le_goodTail_add_small
    (N M : ℕ) (beta : ℝ) :
    nativeLambdaTwoGoodRecipMass N beta ≤
      nativeLambdaTwoGoodTailRecipMass N M beta +
        nativeLambdaTwoSmallQuotientRecipMass N M := by
  classical
  let good : ℕ → Prop := fun n =>
    |nativePNTError (N / n)| ≤ beta * ((N : ℝ) / (n : ℝ))
  let tail : ℕ → Prop := fun n => M ≤ N / n
  let G := (Finset.Icc 1 N).filter good
  let GT := G.filter tail
  let GS := G.filter fun n => ¬ tail n
  let w : ℕ → ℝ := fun n => nativeLambdaTwo n / (n : ℝ)
  have hsplit :
      (∑ n ∈ GT, w n) + (∑ n ∈ GS, w n) = ∑ n ∈ G, w n := by
    dsimp [GT, GS]
    apply Finset.sum_filter_add_sum_filter_not
  have hGT :
      (∑ n ∈ GT, w n) = nativeLambdaTwoGoodTailRecipMass N M beta := by
    unfold nativeLambdaTwoGoodTailRecipMass
      nativePNTSquarePrefixGoodTailFiberSet
    dsimp [GT, G, good, tail, w]
    apply Finset.sum_congr
    · ext n
      simp only [nativePNTSquarePrefixTailFiberSet, Finset.mem_filter,
        Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨hn1, hnN⟩, hgood⟩, htail⟩
        exact ⟨⟨⟨hn1, hnN⟩, htail⟩, hgood⟩
      · rintro ⟨⟨⟨hn1, hnN⟩, htail⟩, hgood⟩
        exact ⟨⟨⟨hn1, hnN⟩, hgood⟩, htail⟩
    · intro n _
      rfl
  have hGSsub : GS ⊆ nativePNTSquarePrefixSmallQuotientFiberSet N M := by
    intro n hn
    have hnGS := Finset.mem_filter.mp hn
    have hnG := Finset.mem_filter.mp hnGS.1
    unfold nativePNTSquarePrefixSmallQuotientFiberSet
    exact Finset.mem_filter.mpr ⟨hnG.1, by
      dsimp [tail] at hnGS
      exact lt_of_not_ge hnGS.2⟩
  have hGS :
      (∑ n ∈ GS, w n) ≤ nativeLambdaTwoSmallQuotientRecipMass N M := by
    unfold nativeLambdaTwoSmallQuotientRecipMass
    refine Finset.sum_le_sum_of_subset_of_nonneg hGSsub ?_
    intro n hn _
    have hnI := (Finset.mem_filter.mp hn).1
    have hn1 := (Finset.mem_Icc.mp hnI).1
    exact div_nonneg (nativeLambdaTwo_nonneg n hn1) (by positivity)
  unfold nativeLambdaTwoGoodRecipMass nativePNTGoodFiberSet
  dsimp [G, good, w] at hsplit
  rw [← hsplit, hGT]
  exact add_le_add_left hGS _

/-- Any global quadratic good-mass lower bound survives on the contracted tail
once the explicit finite-prefix carry consumes at most half of it. -/
theorem nativeLambdaTwoGoodTailRecipMass_half_of_global
    (N M : ℕ) (beta c : ℝ)
    (hglobal : c * (Real.log (N : ℝ)) ^ 2 ≤
      nativeLambdaTwoGoodRecipMass N beta)
    (hsmall : nativeLambdaTwoSmallQuotientRecipMass N M ≤
      (c / 2) * (Real.log (N : ℝ)) ^ 2) :
    (c / 2) * (Real.log (N : ℝ)) ^ 2 ≤
      nativeLambdaTwoGoodTailRecipMass N M beta := by
  have hsplit := nativeLambdaTwoGoodRecipMass_le_goodTail_add_small N M beta
  linarith

end RHLean.Analysis
