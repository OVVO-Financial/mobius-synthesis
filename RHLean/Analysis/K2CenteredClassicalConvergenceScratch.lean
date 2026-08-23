import RHLean.Analysis.K2CenteredClassicalCompareScratch

noncomputable section

open Filter Finset Set Topology
open scoped BigOperators

namespace RHLean.Analysis

local notation "gammaE" => Real.eulerMascheroniConstant

/-- Absolute kernel error is bounded by the sum of the two positive weights. -/
theorem k2WeightError_abs_le_total (N d : ℕ) (hd : 1 ≤ d) :
    |k2WeightError N d| ≤ k2HarmonicWeight N d + k2LogWeight d := by
  have hH := k2HarmonicWeight_nonneg N d hd
  have hL := k2LogWeight_nonneg d hd
  change |k2HarmonicWeight N d - k2LogWeight d| ≤
    k2HarmonicWeight N d + k2LogWeight d
  rw [abs_le]
  constructor <;> linarith

/-- The high square-root block carries at most the full positive comparison mass. -/
theorem k2HighTotalWeight_le_two_log (N : ℕ)
    (hN : 1 ≤ N) (hs : 1 ≤ Nat.sqrt N) :
    (∑ d ∈ Finset.Ico (Nat.sqrt N) N,
      (k2HarmonicWeight N d + k2LogWeight d)) ≤
        2 * Real.log (N : ℝ) := by
  calc
    (∑ d ∈ Finset.Ico (Nat.sqrt N) N,
        (k2HarmonicWeight N d + k2LogWeight d)) ≤
      ∑ d ∈ Finset.Ico 1 N,
        (k2HarmonicWeight N d + k2LogWeight d) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hdmem
        rcases Finset.mem_Ico.mp hdmem with ⟨hds, hdN⟩
        exact Finset.mem_Ico.mpr ⟨hs.trans hds, hdN⟩
      · intro d hdmem _hnot
        have hd : 1 ≤ d := (Finset.mem_Ico.mp hdmem).1
        exact add_nonneg (k2HarmonicWeight_nonneg N d hd)
          (k2LogWeight_nonneg d hd)
    _ ≤ 2 * Real.log (N : ℝ) := k2TotalWeight_sum_le_two_log N hN

/-- If `|r(d) log d|` is uniformly small beyond the square-root cutoff, then
so is the whole high-divisor comparison block. -/
theorem k2KernelComparisonHigh_abs_le
    (N : ℕ) (eta : ℝ) (heta : 0 ≤ eta) (hs : 2 ≤ Nat.sqrt N)
    (hr : ∀ d : ℕ, Nat.sqrt N ≤ d → d < N →
      |k2r d * Real.log (d : ℝ)| ≤ eta) :
    |k2KernelComparisonHigh N| ≤ 8 * eta := by
  have hs1 : 1 ≤ Nat.sqrt N := by omega
  have hN : 1 ≤ N := hs1.trans (Nat.sqrt_le_self N)
  have hspos : (0 : ℝ) < (Nat.sqrt N : ℝ) := by positivity
  have hlogspos : 0 < Real.log (Nat.sqrt N : ℝ) :=
    Real.log_pos (by exact_mod_cast hs)
  have hratio := k2Log_le_four_log_sqrt N hs
  unfold k2KernelComparisonHigh
  calc
    |∑ d ∈ Finset.Ico (Nat.sqrt N) N, k2r d * k2WeightError N d|
        ≤ ∑ d ∈ Finset.Ico (Nat.sqrt N) N,
            |k2r d * k2WeightError N d| := by
          simpa only [Real.norm_eq_abs] using
            (norm_sum_le (Finset.Ico (Nat.sqrt N) N)
              (fun d : ℕ => k2r d * k2WeightError N d))
    _ ≤ ∑ d ∈ Finset.Ico (Nat.sqrt N) N,
          (eta / Real.log (Nat.sqrt N : ℝ)) *
            (k2HarmonicWeight N d + k2LogWeight d) := by
        apply Finset.sum_le_sum
        intro d hdmem
        rcases Finset.mem_Ico.mp hdmem with ⟨hds, hdN⟩
        have hd : 1 ≤ d := hs1.trans hds
        have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
        have hcast : (Nat.sqrt N : ℝ) ≤ (d : ℝ) := by exact_mod_cast hds
        have hlogle := Real.log_le_log hspos hcast
        have hr0 := hr d hds hdN
        have hr1 : |k2r d| * Real.log (d : ℝ) ≤ eta := by
          simpa [abs_mul, abs_of_nonneg hlogd] using hr0
        have hrs : |k2r d| * Real.log (Nat.sqrt N : ℝ) ≤ eta :=
          (mul_le_mul_of_nonneg_left hlogle (abs_nonneg _)).trans hr1
        have hrdiv : |k2r d| ≤ eta / Real.log (Nat.sqrt N : ℝ) :=
          (le_div_iff₀ hlogspos).2 hrs
        have herr := k2WeightError_abs_le_total N d hd
        rw [abs_mul]
        exact mul_le_mul hrdiv herr (abs_nonneg _)
          (div_nonneg heta hlogspos.le)
    _ = (eta / Real.log (Nat.sqrt N : ℝ)) *
          (∑ d ∈ Finset.Ico (Nat.sqrt N) N,
            (k2HarmonicWeight N d + k2LogWeight d)) := by
        rw [Finset.mul_sum]
    _ ≤ (eta / Real.log (Nat.sqrt N : ℝ)) *
          (2 * Real.log (N : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · exact k2HighTotalWeight_le_two_log N hN hs1
        · exact div_nonneg heta hlogspos.le
    _ ≤ (eta / Real.log (Nat.sqrt N : ℝ)) *
          (8 * Real.log (Nat.sqrt N : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith
        · exact div_nonneg heta hlogspos.le
    _ = 8 * eta := by
        field_simp [hlogspos.ne']

/-- The high square-root comparison block vanishes from `r(N) log N -> 0`. -/
theorem k2KernelComparisonHigh_tendsto_zero (h : K2ClassicalMomentInput) :
    Tendsto k2KernelComparisonHigh atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  let eta : ℝ := eps / 16
  have heta : 0 < eta := by
    dsimp [eta]
    linarith
  have hrEv : ∀ᶠ d : ℕ in atTop,
      |k2r d * Real.log (d : ℝ)| < eta := by
    have hraw := (Metric.tendsto_nhds.1 h.r_mul_log_tendsto_zero) eta heta
    simpa [Real.dist_eq] using hraw
  rcases eventually_atTop.1 hrEv with ⟨K, hK⟩
  have hsEv : ∀ᶠ N : ℕ in atTop, max K 2 ≤ Nat.sqrt N :=
    k2Sqrt_tendsto_atTop.eventually (eventually_ge_atTop (max K 2))
  filter_upwards [hsEv] with N hNs
  have hKsqrt : K ≤ Nat.sqrt N := (le_max_left K 2).trans hNs
  have hs : 2 ≤ Nat.sqrt N := (le_max_right K 2).trans hNs
  have hbound := k2KernelComparisonHigh_abs_le N eta heta.le hs (fun d hsd _hdN =>
    (hK d (hKsqrt.trans hsd)).le)
  have hsmall : 8 * eta < eps := by
    dsimp [eta]
    linarith
  simpa [Real.dist_eq] using hbound.trans_lt hsmall

/-- Full harmonic-floor/logarithmic kernel comparison. -/
def k2KernelComparisonSum (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ico 1 N, k2r d * k2WeightError N d

/-- The full comparison splits exactly at the natural square root. -/
theorem k2KernelComparisonSum_split (N : ℕ) (hs : 1 ≤ Nat.sqrt N) :
    k2KernelComparisonLow N + k2KernelComparisonHigh N =
      k2KernelComparisonSum N := by
  unfold k2KernelComparisonLow k2KernelComparisonHigh k2KernelComparisonSum
  exact Finset.sum_Ico_consecutive
    (fun d : ℕ => k2r d * k2WeightError N d)
    hs (Nat.sqrt_le_self N)

/-- The complete harmonic-floor/logarithmic kernel error vanishes. -/
theorem k2KernelComparisonSum_tendsto_zero (h : K2ClassicalMomentInput) :
    Tendsto k2KernelComparisonSum atTop (𝓝 0) := by
  have hsum := (k2KernelComparisonLow_tendsto_zero h).add
    (k2KernelComparisonHigh_tendsto_zero h)
  have heq :
      (fun N : ℕ => k2KernelComparisonLow N + k2KernelComparisonHigh N) =ᶠ[atTop]
        k2KernelComparisonSum := by
    have hsEv : ∀ᶠ N : ℕ in atTop, 1 ≤ Nat.sqrt N :=
      k2Sqrt_tendsto_atTop.eventually (eventually_ge_atTop 1)
    filter_upwards [hsEv] with N hs
    exact k2KernelComparisonSum_split N hs
  have hconv := hsum.congr' heq
  simpa using hconv

/-- Harmonic-floor weighted centered moment sum. -/
def k2HarmonicCenteredWeightSum (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ico 1 N, k2r d * k2HarmonicWeight N d

/-- Harmonic and logarithmic centered sums differ exactly by the comparison
kernel. -/
theorem k2HarmonicCenteredWeightSum_eq (N : ℕ) :
    k2HarmonicCenteredWeightSum N =
      k2LogCenteredWeightSum N + k2KernelComparisonSum N := by
  unfold k2HarmonicCenteredWeightSum k2LogCenteredWeightSum
    k2KernelComparisonSum k2HarmonicWeight k2WeightError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  ring

/-- Harmonic-floor and logarithmic centered sums have the same limit. -/
theorem k2HarmonicCenteredWeightSum_tendsto (h : K2ClassicalMomentInput) :
    ∃ ell : ℝ, Tendsto k2HarmonicCenteredWeightSum atTop (𝓝 ell) := by
  rcases k2LogCenteredWeightSum_tendsto h with ⟨ell, hell⟩
  refine ⟨ell, ?_⟩
  have hsum := hell.add (k2KernelComparisonSum_tendsto_zero h)
  simpa only [add_zero] using hsum.congr' (Eventually.of_forall fun N =>
    (k2HarmonicCenteredWeightSum_eq N).symm)

/-- The finite K2 centered harmonic expression converges. -/
theorem k2CenteredHarmonic_tendsto (h : K2ClassicalMomentInput) :
    ∃ ell : ℝ,
      Tendsto
        (fun N : ℕ =>
          nativePNTSignedSecondSelbergKernelRecipMass N +
            2 * gammaE * (harmonic N : ℝ))
        atTop (𝓝 ell) := by
  rcases k2HarmonicCenteredWeightSum_tendsto h with ⟨ell, hell⟩
  refine ⟨ell, ?_⟩
  have hsum := h.r_tendsto_zero.add hell
  have heq :
      (fun N : ℕ => k2r N + k2HarmonicCenteredWeightSum N) =ᶠ[atTop]
        (fun N : ℕ =>
          nativePNTSignedSecondSelbergKernelRecipMass N +
            2 * gammaE * (harmonic N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hF := k2F_centered_abel N hN
    have hNN : k2H N N = 1 := by
      unfold k2H
      rw [Nat.div_self (by omega)]
      norm_num [harmonic]
    rw [hNN, mul_one] at hF
    unfold k2HarmonicCenteredWeightSum k2HarmonicWeight
    exact hF.symm
  have hconv := hsum.congr' heq
  simpa using hconv

/-- **Classical centered K2 closure.**  The three reciprocal moment limits imply
convergence of the centered reciprocal K2 mass. -/
theorem k2ClassicalMomentInput_to_centered_converges
    (h : K2ClassicalMomentInput) : K2CenteredConverges := by
  rcases k2CenteredHarmonic_tendsto h with ⟨ell, hell⟩
  unfold K2CenteredConverges
  refine ⟨ell - 2 * gammaE * gammaE, ?_⟩
  have hEuler :
      Tendsto
        (fun N : ℕ => (harmonic N : ℝ) - Real.log (N : ℝ))
        atTop (𝓝 gammaE) := Real.tendsto_harmonic_sub_log
  have hcorr :
      Tendsto
        (fun N : ℕ => 2 * gammaE *
          ((harmonic N : ℝ) - Real.log (N : ℝ)))
        atTop (𝓝 (2 * gammaE * gammaE)) := by
    simpa using (tendsto_const_nhds.mul hEuler :
      Tendsto
        (fun N : ℕ => (2 * gammaE) *
          ((harmonic N : ℝ) - Real.log (N : ℝ)))
        atTop (𝓝 ((2 * gammaE) * gammaE)))
  have hfinal := hell.sub hcorr
  apply hfinal.congr'
  exact Eventually.of_forall fun N => by
    unfold k2CenteredRecipValue
    ring

/-- Strong Mertens supplies all moment inputs and therefore closes centered K2. -/
theorem k2CenteredConverges_from_strongMertens : K2CenteredConverges :=
  k2ClassicalMomentInput_to_centered_converges k2ClassicalMomentInput_from_strongMertens

end RHLean.Analysis
