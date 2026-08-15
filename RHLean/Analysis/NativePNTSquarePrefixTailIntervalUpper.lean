import RHLean.Analysis.NativePNTSquarePrefixTailReciprocalBound

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- The finite-prefix reciprocal LambdaTwo carry has exact leading logarithmic
variation; all losses are only linear in the upper logarithm. -/
theorem nativeLambdaTwoRecipIntervalMass_upper
    (A B : ℕ) (hA : 3 ≤ A) (hAB : A ≤ B) :
    nativeLambdaTwoRecipIntervalMass A B ≤
      (Real.log B) ^ 2 - (Real.log A) ^ 2 +
        200 * Real.log B + 1000 := by
  have hB3 : 3 ≤ B := hA.trans hAB
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (show 0 < B by omega)
  have hApos : (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast (show 0 < A by omega)
  have hlogB0 : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have hC : 2 * (Real.log 4 + 2) + 172 ≤ (182 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at h ⊢
    linarith
  have hselB := nativeLambdaTwoSummatory_sub_two_mul_log_abs_le B hB3
  rw [abs_le] at hselB
  have hBR0 : 0 ≤ (B : ℝ) := by positivity
  have hrhoB :
      nativeLambdaTwoSummatory B / (B : ℝ) ≤ 2 * Real.log B + 182 := by
    rw [div_le_iff₀ hBpos]
    nlinarith [hselB.2, mul_le_mul_of_nonneg_right hC hBR0]
  have hrhoA0 : 0 ≤ nativeLambdaTwoSummatory A := by
    unfold nativeLambdaTwoSummatory
    apply Finset.sum_nonneg
    intro n hn
    exact nativeLambdaTwo_nonneg n (Finset.mem_Icc.mp hn).1
  have hdivA0 : 0 ≤ nativeLambdaTwoSummatory A / (A : ℝ) :=
    div_nonneg hrhoA0 hApos.le
  have hinterior0 :
      (∑ n ∈ Finset.Ico A B,
        nativeLambdaTwoSummatory n *
          (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) ≤
        ∑ n ∈ Finset.Ico A B,
          (2 * Real.log (n : ℝ) / (n : ℝ) + 182 / (n : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    exact nativeLambdaTwoAbelPoint_upper_three n
      (hA.trans (Finset.mem_Ico.mp hn).1)
  have hlog := nativeLogRecipIco_interval_le A B hA hAB
  have hrecip0 := nativeTailReciprocalIco_le A B (by omega)
  have hrecip :
      (∑ n ∈ Finset.Ico A B, (1 : ℝ) / n) ≤ 1 + Real.log B :=
    hrecip0.trans (harmonic_le_one_add_log B)
  have hinterior :
      (∑ n ∈ Finset.Ico A B,
        nativeLambdaTwoSummatory n *
          (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) ≤
        2 * ((1 / 2 : ℝ) * ((Real.log B) ^ 2 - (Real.log A) ^ 2) +
          Real.log B + 8) + 182 * (1 + Real.log B) := by
    calc
      (∑ n ∈ Finset.Ico A B,
        nativeLambdaTwoSummatory n *
          (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) ≤
          ∑ n ∈ Finset.Ico A B,
            (2 * Real.log (n : ℝ) / (n : ℝ) + 182 / (n : ℝ)) := hinterior0
      _ = 2 * (∑ n ∈ Finset.Ico A B,
            Real.log (n : ℝ) / (n : ℝ)) +
          182 * (∑ n ∈ Finset.Ico A B, (1 : ℝ) / n) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro n _hn <;> ring
      _ ≤ 2 * ((1 / 2 : ℝ) * ((Real.log B) ^ 2 - (Real.log A) ^ 2) +
            Real.log B + 8) + 182 * (1 + Real.log B) := by
        gcongr
  rw [nativeLambdaTwoRecipIntervalMass_abel A B (by omega) hAB]
  calc
    nativeLambdaTwoSummatory B / (B : ℝ) -
          nativeLambdaTwoSummatory A / (A : ℝ) +
          ∑ n ∈ Finset.Ico A B,
            nativeLambdaTwoSummatory n *
              (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ))) ≤
        nativeLambdaTwoSummatory B / (B : ℝ) +
          ∑ n ∈ Finset.Ico A B,
            nativeLambdaTwoSummatory n *
              (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ))) := by
      linarith
    _ ≤ (2 * Real.log B + 182) +
        (2 * ((1 / 2 : ℝ) * ((Real.log B) ^ 2 - (Real.log A) ^ 2) +
          Real.log B + 8) + 182 * (1 + Real.log B)) :=
      add_le_add hrhoB hinterior
    _ ≤ (Real.log B) ^ 2 - (Real.log A) ^ 2 +
        200 * Real.log B + 1000 := by
      nlinarith

end RHLean.Analysis
