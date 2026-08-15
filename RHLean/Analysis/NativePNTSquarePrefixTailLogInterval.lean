import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixTailIntervalAbel

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

private theorem tailInterval_logRecipMass_sub_eq
    (A B : ℕ) (hAB : A ≤ B) :
    nativeLogRecipMass B - nativeLogRecipMass A =
      ∑ n ∈ Finset.Icc (A + 1) B, Real.log (n : ℝ) / (n : ℝ) := by
  have hsub : Finset.Icc 1 A ⊆ Finset.Icc 1 B := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnA⟩
    exact Finset.mem_Icc.mpr ⟨hn1, hnA.trans hAB⟩
  have hset : Finset.Icc 1 B \ Finset.Icc 1 A = Finset.Icc (A + 1) B := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    omega
  unfold nativeLogRecipMass
  rw [← Finset.sum_sdiff hsub, hset]
  ring

/-- The logarithmic reciprocal mass on `[A,B)` retains the exact integral
leading term. -/
theorem nativeLogRecipIco_interval_le
    (A B : ℕ) (hA : 3 ≤ A) (hAB : A ≤ B) :
    (∑ n ∈ Finset.Ico A B, Real.log (n : ℝ) / (n : ℝ)) ≤
      (1 / 2 : ℝ) * ((Real.log B) ^ 2 - (Real.log A) ^ 2) +
        Real.log B + 8 := by
  let f : ℕ → ℝ := fun n => Real.log (n : ℝ) / (n : ℝ)
  have hsub : Finset.Ico A B ⊆ insert A (Finset.Icc (A + 1) B) := by
    intro n hn
    rcases Finset.mem_Ico.mp hn with ⟨hAn, hnB⟩
    by_cases hnA : n = A
    · simp [hnA]
    · have hA1n : A + 1 ≤ n := by omega
      have hnBle : n ≤ B := by omega
      simp [Finset.mem_Icc, hA1n, hnBle]
  have hsumSubset :
      (∑ n ∈ Finset.Ico A B, f n) ≤
        ∑ n ∈ insert A (Finset.Icc (A + 1) B), f n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro n hnNew _hnOld
    have hnA : A ≤ n := by
      simp only [Finset.mem_insert, Finset.mem_Icc] at hnNew
      rcases hnNew with rfl | hnI
      · exact le_rfl
      · omega
    have hn1 : 1 ≤ n := by omega
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast hn1)) (by positivity)
  have hA_notmem : A ∉ Finset.Icc (A + 1) B := by simp
  have hsumInsert :
      (∑ n ∈ insert A (Finset.Icc (A + 1) B), f n) =
        f A + ∑ n ∈ Finset.Icc (A + 1) B, f n := by
    rw [Finset.sum_insert hA_notmem]
  have hJdiff := tailInterval_logRecipMass_sub_eq A B hAB
  have hdefA := nativeLogRecipDefect_abs_le_four A hA
  have hdefB := nativeLogRecipDefect_abs_le_four B (hA.trans hAB)
  rw [abs_le] at hdefA hdefB
  unfold nativeLogRecipDefect at hdefA hdefB
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  have hlogA0 : 0 ≤ Real.log (A : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ A by omega))
  have hlogMono : Real.log (A : ℝ) ≤ Real.log (B : ℝ) := by
    apply Real.log_le_log
    · exact hApos
    · exact_mod_cast hAB
  have hfA : f A ≤ Real.log B := by
    dsimp [f]
    have hA1R : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast (show 1 ≤ A by omega)
    have hdiv : Real.log (A : ℝ) / (A : ℝ) ≤ Real.log (A : ℝ) := by
      rw [div_le_iff₀ hApos]
      nlinarith
    exact hdiv.trans hlogMono
  calc
    (∑ n ∈ Finset.Ico A B, Real.log (n : ℝ) / (n : ℝ)) =
        ∑ n ∈ Finset.Ico A B, f n := by rfl
    _ ≤ ∑ n ∈ insert A (Finset.Icc (A + 1) B), f n := hsumSubset
    _ = f A + ∑ n ∈ Finset.Icc (A + 1) B, f n := hsumInsert
    _ = f A + (nativeLogRecipMass B - nativeLogRecipMass A) := by
      rw [hJdiff]
    _ ≤ (1 / 2 : ℝ) * ((Real.log B) ^ 2 - (Real.log A) ^ 2) +
          Real.log B + 8 := by
      nlinarith [hfA, hdefA.1, hdefB.2]

end RHLean.Analysis
