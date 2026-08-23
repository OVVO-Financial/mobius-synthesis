import RHLean.Analysis.K2CenteredClassicalKernelScratch

noncomputable section

open Filter Finset Set Topology
open scoped BigOperators

namespace RHLean.Analysis

/-- The square-root scale controls the endpoint logarithm by a fixed factor. -/
theorem k2Log_le_four_log_sqrt (N : ℕ) (hs : 2 ≤ Nat.sqrt N) :
    Real.log (N : ℝ) ≤ 4 * Real.log (Nat.sqrt N : ℝ) := by
  let s := Nat.sqrt N
  have hs2 : 2 ≤ s := by simpa [s] using hs
  have hsposNat : 0 < s := by omega
  have hNposNat : 0 < N := (Nat.sqrt_pos).1 hsposNat
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
  have hsp1 : s + 1 ≤ s * s := by nlinarith
  have hNle : N ≤ s ^ 4 := by
    calc
      N ≤ (s + 1) * (s + 1) := (Nat.lt_succ_sqrt N).le
      _ ≤ (s * s) * (s * s) := Nat.mul_self_le_mul_self hsp1
      _ = s ^ 4 := by ring
  have hcast : (N : ℝ) ≤ (s : ℝ) ^ 4 := by exact_mod_cast hNle
  have hlog := Real.log_le_log hNpos hcast
  rw [Real.log_pow] at hlog
  simpa [s] using hlog

/-- Low-divisor part of the harmonic-floor/logarithmic comparison. -/
def k2KernelComparisonLow (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ico 1 (Nat.sqrt N), k2r d * k2WeightError N d

/-- High-divisor part of the harmonic-floor/logarithmic comparison. -/
def k2KernelComparisonHigh (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ico (Nat.sqrt N) N, k2r d * k2WeightError N d

/-- The low square-root block is bounded by a Cesaro average of `|r|`. -/
theorem k2KernelComparisonLow_abs_le (N : ℕ) (hN : 1 ≤ N) :
    |k2KernelComparisonLow N| ≤
      2 * ((Nat.sqrt N : ℝ)⁻¹ *
        ∑ d ∈ Finset.range (Nat.sqrt N), |k2r d|) := by
  have hsposNat : 0 < Nat.sqrt N := (Nat.sqrt_pos).2 (by omega)
  have hspos : (0 : ℝ) < (Nat.sqrt N : ℝ) := by exact_mod_cast hsposNat
  unfold k2KernelComparisonLow
  calc
    |∑ d ∈ Finset.Ico 1 (Nat.sqrt N), k2r d * k2WeightError N d|
        ≤ ∑ d ∈ Finset.Ico 1 (Nat.sqrt N),
            |k2r d * k2WeightError N d| := by
          simpa only [Real.norm_eq_abs] using
            (norm_sum_le (Finset.Ico 1 (Nat.sqrt N))
              (fun d : ℕ => k2r d * k2WeightError N d))
    _ ≤ ∑ d ∈ Finset.Ico 1 (Nat.sqrt N),
          (2 / (Nat.sqrt N : ℝ)) * |k2r d| := by
        apply Finset.sum_le_sum
        intro d hdmem
        rcases Finset.mem_Ico.mp hdmem with ⟨hd, hds⟩
        rw [abs_mul]
        have herr := k2WeightError_abs_le_sqrt N d hN hd hds
        nlinarith [abs_nonneg (k2r d)]
    _ = (2 / (Nat.sqrt N : ℝ)) *
          ∑ d ∈ Finset.Ico 1 (Nat.sqrt N), |k2r d| := by
        rw [Finset.mul_sum]
    _ ≤ (2 / (Nat.sqrt N : ℝ)) *
          ∑ d ∈ Finset.range (Nat.sqrt N), |k2r d| := by
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro d hdmem
            exact Finset.mem_range.mpr (Finset.mem_Ico.mp hdmem).2
          · intro d hdmem hnot
            exact abs_nonneg _
        · positivity
    _ = 2 * ((Nat.sqrt N : ℝ)⁻¹ *
          ∑ d ∈ Finset.range (Nat.sqrt N), |k2r d|) := by
        field_simp [hspos.ne']

/-- The low square-root comparison block vanishes. -/
theorem k2KernelComparisonLow_tendsto_zero (h : K2ClassicalMomentInput) :
    Tendsto k2KernelComparisonLow atTop (𝓝 0) := by
  have habs : Tendsto (fun n : ℕ => |k2r n|) atTop (𝓝 0) := by
    simpa using h.r_tendsto_zero.abs
  have hces :
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, |k2r i|)
        atTop (𝓝 0) := by
    simpa using habs.cesaro
  have hcesS := hces.comp k2Sqrt_tendsto_atTop
  have hbound :
      Tendsto
        (fun N : ℕ =>
          2 * ((Nat.sqrt N : ℝ)⁻¹ *
            ∑ d ∈ Finset.range (Nat.sqrt N), |k2r d|))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hcesS :
      Tendsto
        (fun N : ℕ =>
          2 * ((Nat.sqrt N : ℝ)⁻¹ *
            ∑ d ∈ Finset.range (Nat.sqrt N), |k2r d|))
        atTop (𝓝 (2 * 0)))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hbound
  filter_upwards [eventually_ge_atTop 1] with N hN
  simpa [Real.norm_eq_abs] using k2KernelComparisonLow_abs_le N hN

end RHLean.Analysis
