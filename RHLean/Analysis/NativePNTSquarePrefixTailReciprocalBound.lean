import RHLean.Analysis.NativePNTSquarePrefixTailLogInterval
import RHLean.Analysis.NativePNTErrorMass

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

theorem nativeTailReciprocalIco_le
    (A B : ℕ) (hA : 1 ≤ A) :
    (∑ n ∈ Finset.Ico A B, (1 : ℝ) / n) ≤ (harmonic B : ℝ) := by
  have hs : Finset.Ico A B ⊆ Finset.Icc 1 B := by
    intro n hn
    have h := Finset.mem_Ico.mp hn
    exact Finset.mem_Icc.mpr ⟨hA.trans h.1, by omega⟩
  have hsum :
      (∑ n ∈ Finset.Ico A B, (1 : ℝ) / n) ≤
        ∑ n ∈ Finset.Icc 1 B, (1 : ℝ) / n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hs ?_
    intro n _ _
    positivity
  have hh :
      (harmonic B : ℝ) = ∑ n ∈ Finset.Icc 1 B, (1 : ℝ) / n := by
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, one_div]
  simpa [hh] using hsum

end RHLean.Analysis
