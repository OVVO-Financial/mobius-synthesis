import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixTailGeometry

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Reciprocal LambdaTwo interval mass is the difference of the two prefix masses. -/
theorem nativeLambdaTwoRecipMass_sub_eq_interval
    (A B : ℕ) (hAB : A ≤ B) :
    nativeLambdaTwoRecipMass B - nativeLambdaTwoRecipMass A =
      nativeLambdaTwoRecipIntervalMass A B := by
  have hsub : Finset.Icc 1 A ⊆ Finset.Icc 1 B := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnA⟩
    exact Finset.mem_Icc.mpr ⟨hn1, hnA.trans hAB⟩
  have hset : Finset.Icc 1 B \ Finset.Icc 1 A = Finset.Icc (A + 1) B := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    omega
  unfold nativeLambdaTwoRecipMass nativeLambdaTwoRecipIntervalMass
  rw [← Finset.sum_sdiff hsub, hset]
  ring

/-- Abel summation localized to `(A,B]`.  The lower endpoint occurs with a
negative sign, so an upper bound never needs a lower asymptotic for the
summatory LambdaTwo function. -/
theorem nativeLambdaTwoRecipIntervalMass_abel
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    nativeLambdaTwoRecipIntervalMass A B =
      nativeLambdaTwoSummatory B / (B : ℝ) -
        nativeLambdaTwoSummatory A / (A : ℝ) +
        ∑ n ∈ Finset.Ico A B,
          nativeLambdaTwoSummatory n *
            (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ))) := by
  rw [← nativeLambdaTwoRecipMass_sub_eq_interval A B hAB,
    nativeLambdaTwoRecipMass_abel B, nativeLambdaTwoRecipMass_abel A]
  let f : ℕ → ℝ := fun n =>
    nativeLambdaTwoSummatory n *
      (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))
  have hsub : Finset.Ico 1 A ⊆ Finset.Ico 1 B := by
    intro n hn
    rcases Finset.mem_Ico.mp hn with ⟨hn1, hnA⟩
    exact Finset.mem_Ico.mpr ⟨hn1, hnA.trans_le hAB⟩
  have hset : Finset.Ico 1 B \ Finset.Ico 1 A = Finset.Ico A B := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Ico]
    omega
  have hsum :
      (∑ n ∈ Finset.Ico 1 B, f n) -
          ∑ n ∈ Finset.Ico 1 A, f n =
        ∑ n ∈ Finset.Ico A B, f n := by
    rw [← Finset.sum_sdiff hsub, hset]
    ring
  change
    nativeLambdaTwoSummatory B / (B : ℝ) +
          ∑ n ∈ Finset.Ico 1 B, f n -
        (nativeLambdaTwoSummatory A / (A : ℝ) +
          ∑ n ∈ Finset.Ico 1 A, f n) = _
  rw [← hsum]
  ring

private theorem tailInterval_selbergConstant_le :
    2 * (Real.log 4 + 2) + 172 ≤ (182 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  norm_num at h ⊢
  linarith

private theorem tailInterval_recipDiff_eq
    (n : ℕ) (hn : 1 ≤ n) :
    1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)) =
      1 / ((n : ℝ) * (((n + 1 : ℕ) : ℝ))) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hs0 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hn0, hs0]
  push_cast
  ring

/-- On scales at least three, one Abel summand has the sharp leading
`2 log n / n` upper coefficient and only a linear harmonic error. -/
theorem nativeLambdaTwoAbelPoint_upper_three
    (n : ℕ) (hn : 3 ≤ n) :
    nativeLambdaTwoSummatory n *
        (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ))) ≤
      2 * Real.log (n : ℝ) / (n : ℝ) + 182 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hspos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hsel := nativeLambdaTwoSummatory_sub_two_mul_log_abs_le n hn
  rw [abs_le] at hsel
  have hC := tailInterval_selbergConstant_le
  have hNR0 : 0 ≤ (n : ℝ) := by positivity
  have hrho :
      nativeLambdaTwoSummatory n ≤
        2 * (n : ℝ) * Real.log (n : ℝ) + 182 * (n : ℝ) := by
    nlinarith [hsel.2, mul_le_mul_of_nonneg_right hC hNR0]
  have hk := tailInterval_recipDiff_eq n (by omega)
  have hkernel0 :
      0 ≤ 1 / ((n : ℝ) * (((n + 1 : ℕ) : ℝ))) := by positivity
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlogfrac :
      2 * Real.log (n : ℝ) / (((n + 1 : ℕ) : ℝ)) ≤
        2 * Real.log (n : ℝ) / (n : ℝ) := by
    rw [div_le_div_iff₀ hspos hnpos]
    push_cast
    nlinarith
  have hconstfrac :
      (182 : ℝ) / (((n + 1 : ℕ) : ℝ)) ≤ 182 / (n : ℝ) := by
    rw [div_le_div_iff₀ hspos hnpos]
    push_cast
    nlinarith
  rw [hk]
  calc
    nativeLambdaTwoSummatory n *
        (1 / ((n : ℝ) * (((n + 1 : ℕ) : ℝ)))) ≤
      (2 * (n : ℝ) * Real.log (n : ℝ) + 182 * (n : ℝ)) *
        (1 / ((n : ℝ) * (((n + 1 : ℕ) : ℝ)))) :=
      mul_le_mul_of_nonneg_right hrho hkernel0
    _ = 2 * Real.log (n : ℝ) / (((n + 1 : ℕ) : ℝ)) +
        182 / (((n + 1 : ℕ) : ℝ)) := by
      field_simp [ne_of_gt hnpos, ne_of_gt hspos]
    _ ≤ 2 * Real.log (n : ℝ) / (n : ℝ) + 182 / (n : ℝ) := by
      linarith

end RHLean.Analysis
