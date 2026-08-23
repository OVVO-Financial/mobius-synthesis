import RHLean.Analysis.K2CenteredClassicalClosureScratch

noncomputable section

open Filter Finset Set Topology
open scoped BigOperators

namespace RHLean.Analysis

/-- Positive harmonic-floor divisor weight. -/
def k2HarmonicWeight (N d : ℕ) : ℝ :=
  k2H N d - k2H N (d + 1)

/-- Positive logarithmic divisor weight. -/
def k2LogWeight (d : ℕ) : ℝ :=
  Real.log ((d + 1 : ℕ) : ℝ) - Real.log (d : ℝ)

/-- Integer quotient is antitone in a positive divisor. -/
theorem k2Quotient_antitone (N d : ℕ) (hd : 1 ≤ d) :
    N / (d + 1) ≤ N / d := by
  have hdpos : 0 < d := by omega
  apply (Nat.le_div_iff_mul_le hdpos).2
  calc
    (N / (d + 1)) * d ≤ (N / (d + 1)) * (d + 1) := by
      exact Nat.mul_le_mul_left _ (Nat.le_succ d)
    _ ≤ N := Nat.div_mul_le_self N (d + 1)

/-- Harmonic numbers are monotone. -/
theorem k2Harmonic_mono {a b : ℕ} (hab : a ≤ b) :
    (harmonic a : ℝ) ≤ (harmonic b : ℝ) := by
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rcases Finset.mem_Icc.mp hx with ⟨hx1, hxa⟩
    exact Finset.mem_Icc.mpr ⟨hx1, hxa.trans hab⟩
  · intro x hx hnot
    positivity

/-- Harmonic-floor weights are nonnegative. -/
theorem k2HarmonicWeight_nonneg (N d : ℕ) (hd : 1 ≤ d) :
    0 ≤ k2HarmonicWeight N d := by
  unfold k2HarmonicWeight k2H
  exact sub_nonneg.mpr (k2Harmonic_mono (k2Quotient_antitone N d hd))

/-- Logarithmic divisor weights are nonnegative. -/
theorem k2LogWeight_nonneg (d : ℕ) (hd : 1 ≤ d) :
    0 ≤ k2LogWeight d := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hle : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ d
  unfold k2LogWeight
  exact sub_nonneg.mpr (Real.log_le_log hdpos hle)

/-- Harmonic-floor weights telescope. -/
theorem k2HarmonicWeight_sum (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Ico 1 N, k2HarmonicWeight N d) =
      (harmonic N : ℝ) - 1 := by
  have ht := k2H_telescope N hN
  have hNN : k2H N N = 1 := by
    unfold k2H
    rw [Nat.div_self (by omega)]
    norm_num [harmonic]
  unfold k2HarmonicWeight
  rw [hNN] at ht
  linarith

/-- Logarithmic divisor weights telescope to `log N`. -/
theorem k2LogWeight_sum (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Ico 1 N, k2LogWeight d) = Real.log (N : ℝ) := by
  have ht := k2_log_telescope N hN
  unfold k2LogWeight
  calc
    (∑ d ∈ Finset.Ico 1 N,
        (Real.log ((d + 1 : ℕ) : ℝ) - Real.log (d : ℝ))) =
        -(∑ d ∈ Finset.Ico 1 N,
          (Real.log (d : ℝ) - Real.log ((d + 1 : ℕ) : ℝ))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = Real.log (N : ℝ) := by
      rw [ht]
      ring

/-- The total positive comparison mass is at most `2 log N`. -/
theorem k2TotalWeight_sum_le_two_log (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Ico 1 N,
      (k2HarmonicWeight N d + k2LogWeight d)) ≤
        2 * Real.log (N : ℝ) := by
  rw [Finset.sum_add_distrib, k2HarmonicWeight_sum N hN,
    k2LogWeight_sum N hN]
  have hh := harmonic_le_one_add_log N
  linarith

/-- Natural square roots tend to infinity. -/
theorem k2Sqrt_tendsto_atTop : Tendsto Nat.sqrt atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  exact eventually_atTop.2 ⟨b * b, fun N hN => (Nat.le_sqrt).2 hN⟩

end RHLean.Analysis
