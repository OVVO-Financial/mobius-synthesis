import RHLean.Analysis.K2RecipMomentRateScratch

noncomputable section

open Filter Finset Set Topology
open scoped BigOperators

namespace RHLean.Analysis

local notation "gammaE" => Real.eulerMascheroniConstant

/-- The positive logarithmic Abel weight appearing in the classical K2
closure. -/
def k2LogCenteredWeightSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 N,
    k2r n *
      (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))

/-- The logarithmic weighted sum is exactly the endpoint term minus the cubic
reciprocal moment. -/
theorem k2LogCenteredWeightSum_eq (N : ℕ) (hN : 1 ≤ N) :
    k2LogCenteredWeightSum N =
      k2r N * Real.log (N : ℝ) - k2C3 N := by
  have hC := k2C3_centered_abel N hN
  unfold k2LogCenteredWeightSum
  calc
    (∑ n ∈ Finset.Ico 1 N,
        k2r n *
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) =
        ∑ n ∈ Finset.Ico 1 N,
          -(k2r n *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = -(∑ n ∈ Finset.Ico 1 N,
          k2r n *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))) := by
      rw [Finset.sum_neg_distrib]
    _ = k2r N * Real.log (N : ℝ) - k2C3 N := by
      rw [hC]
      ring

/-- The logarithmic K2 comparison sum converges under precisely the three
moment hypotheses recorded by `K2ClassicalMomentInput`. -/
theorem k2LogCenteredWeightSum_tendsto (h : K2ClassicalMomentInput) :
    ∃ ell : ℝ, Tendsto k2LogCenteredWeightSum atTop (𝓝 ell) := by
  rcases h.c3_tendsto with ⟨ell, hell⟩
  refine ⟨-ell, ?_⟩
  have hlim :
      Tendsto
        (fun N : ℕ => k2r N * Real.log (N : ℝ) - k2C3 N)
        atTop (𝓝 (-ell)) := by
    simpa using h.r_mul_log_tendsto_zero.sub hell
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (k2LogCenteredWeightSum_eq N hN).symm

/-- Euler's harmonic remainder after subtracting `log n + gamma`. -/
def k2HarmonicError (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log (n : ℝ) - gammaE

/-- The harmonic remainder is nonnegative. -/
theorem k2HarmonicError_nonneg (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ k2HarmonicError n := by
  have hn0 : n ≠ 0 := by omega
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  simp [Real.eulerMascheroniSeq', hn0] at h
  unfold k2HarmonicError
  linarith

/-- The harmonic remainder is bounded by one logarithmic mesh step. -/
theorem k2HarmonicError_le_log_step (n : ℕ) (_hn : 1 ≤ n) :
    k2HarmonicError n ≤
      Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  simp [Real.eulerMascheroniSeq] at h
  have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by norm_num
  rw [hcast]
  unfold k2HarmonicError
  linarith

/-- A single positive logarithmic mesh step is at most `1/n`. -/
theorem k2LogStep_le_inv (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
  have hnposNat : 0 < n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposNat
  have hnp1pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  calc
    Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)
        = Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
      rw [Real.log_div hnp1pos.ne' hnpos.ne']
    _ ≤ (((n + 1 : ℕ) : ℝ) / (n : ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hnp1pos hnpos)
    _ = 1 / (n : ℝ) := by
      field_simp [hnpos.ne']
      norm_num

/-- The harmonic remainder has the elementary reciprocal bound `E_n ≤ 1/n`. -/
theorem k2HarmonicError_le_inv (n : ℕ) (hn : 1 ≤ n) :
    k2HarmonicError n ≤ 1 / (n : ℝ) :=
  (k2HarmonicError_le_log_step n hn).trans (k2LogStep_le_inv n hn)

/-- Error from replacing the real quotient `N/d` by its integer floor. -/
def k2QuotientLogError (N d : ℕ) : ℝ :=
  Real.log ((N : ℝ) / (d : ℝ)) - Real.log ((N / d : ℕ) : ℝ)

/-- Flooring a positive quotient can only lower its logarithm. -/
theorem k2QuotientLogError_nonneg (N d : ℕ) (hd : 1 ≤ d) (hdN : d ≤ N) :
    0 ≤ k2QuotientLogError N d := by
  have hdposNat : 0 < d := by omega
  have hqposNat : 0 < N / d := Nat.div_pos hdN hdposNat
  have hqpos : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by exact_mod_cast hqposNat
  have hcast : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
  unfold k2QuotientLogError
  exact sub_nonneg.mpr (Real.log_le_log hqpos hcast)

/-- The logarithmic floor error is at most one reciprocal quotient. -/
theorem k2QuotientLogError_le_inv (N d : ℕ) (hd : 1 ≤ d) (hdN : d ≤ N) :
    k2QuotientLogError N d ≤ 1 / ((N / d : ℕ) : ℝ) := by
  have hdposNat : 0 < d := by omega
  have hNposNat : 0 < N := hdposNat.trans_le hdN
  have hqposNat : 0 < N / d := Nat.div_pos hdN hdposNat
  have hq1 : 1 ≤ N / d := hqposNat
  have hxpos : (0 : ℝ) < (N : ℝ) / (d : ℝ) := by positivity
  have hfloor :
      Nat.floor ((N : ℝ) / (d : ℝ)) = N / d := by
    simpa using (Nat.floor_div_eq_div (K := ℝ) N d)
  have hxlt :
      (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
    have hx := Nat.lt_floor_add_one ((N : ℝ) / (d : ℝ))
    rw [hfloor] at hx
    exact hx
  have hloglt :
      Real.log ((N : ℝ) / (d : ℝ)) <
        Real.log (((N / d : ℕ) : ℝ) + 1) :=
    Real.log_lt_log hxpos hxlt
  have hstep :
      Real.log (((N / d : ℕ) : ℝ) + 1) -
          Real.log ((N / d : ℕ) : ℝ) ≤
        1 / ((N / d : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using k2LogStep_le_inv (N / d) hq1
  unfold k2QuotientLogError
  linarith

/-- Harmonic quotient error after centering by the real quotient logarithm. -/
def k2HarmonicQuotientError (N d : ℕ) : ℝ :=
  (harmonic (N / d) : ℝ) -
    Real.log ((N : ℝ) / (d : ℝ)) - gammaE

/-- The centered harmonic quotient error is the difference of two errors, both
lying in the same reciprocal interval. -/
theorem k2HarmonicQuotientError_eq (N d : ℕ) :
    k2HarmonicQuotientError N d =
      k2HarmonicError (N / d) - k2QuotientLogError N d := by
  unfold k2HarmonicQuotientError k2HarmonicError k2QuotientLogError
  ring

/-- Absolute harmonic quotient error is at most one reciprocal quotient. -/
theorem k2HarmonicQuotientError_abs_le_inv
    (N d : ℕ) (hd : 1 ≤ d) (hdN : d ≤ N) :
    |k2HarmonicQuotientError N d| ≤ 1 / ((N / d : ℕ) : ℝ) := by
  have hdposNat : 0 < d := by omega
  have hqposNat : 0 < N / d := Nat.div_pos hdN hdposNat
  have hq1 : 1 ≤ N / d := hqposNat
  have he0 := k2HarmonicError_nonneg (N / d) hq1
  have he1 := k2HarmonicError_le_inv (N / d) hq1
  have hq0 := k2QuotientLogError_nonneg N d hd hdN
  have hq1' := k2QuotientLogError_le_inv N d hd hdN
  rw [k2HarmonicQuotientError_eq]
  rw [abs_le]
  constructor <;> linarith

/-- Real quotient logarithms telescope to the logarithmic weight in the divisor. -/
theorem k2LogQuotient_diff (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d) :
    Real.log ((N : ℝ) / (d : ℝ)) -
        Real.log ((N : ℝ) / ((d + 1 : ℕ) : ℝ)) =
      Real.log ((d + 1 : ℕ) : ℝ) - Real.log (d : ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hdp10 : (((d + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [Real.log_div hN0 hd0, Real.log_div hN0 hdp10]
  ring

/-- Difference between the harmonic floor weight and its logarithmic model. -/
def k2WeightError (N d : ℕ) : ℝ :=
  (k2H N d - k2H N (d + 1)) -
    (Real.log ((d + 1 : ℕ) : ℝ) - Real.log (d : ℝ))

/-- The kernel error is a first difference of centered harmonic quotient errors. -/
theorem k2WeightError_eq (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d) :
    k2WeightError N d =
      k2HarmonicQuotientError N d -
        k2HarmonicQuotientError N (d + 1) := by
  unfold k2WeightError k2H k2HarmonicQuotientError
  have hlog := k2LogQuotient_diff N d hN hd
  linarith

/-- If a positive scale lies below the quotient, the centered harmonic quotient
error is bounded by the reciprocal scale. -/
theorem k2HarmonicQuotientError_abs_le_scale
    (N d s : ℕ) (hs : 1 ≤ s) (hd : 1 ≤ d) (hdN : d ≤ N)
    (hsq : s ≤ N / d) :
    |k2HarmonicQuotientError N d| ≤ 1 / (s : ℝ) := by
  have hbase := k2HarmonicQuotientError_abs_le_inv N d hd hdN
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have hcast : (s : ℝ) ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast hsq
  exact hbase.trans (one_div_le_one_div_of_le hspos hcast)

/-- Square-root divisors leave at least the square-root scale in the quotient. -/
theorem k2Sqrt_le_quotient (N d : ℕ) (hd : 1 ≤ d)
    (hds : d ≤ Nat.sqrt N) :
    Nat.sqrt N ≤ N / d := by
  have hdpos : 0 < d := by omega
  apply (Nat.le_div_iff_mul_le hdpos).2
  calc
    Nat.sqrt N * d ≤ Nat.sqrt N * Nat.sqrt N :=
      Nat.mul_le_mul_left _ hds
    _ ≤ N := Nat.sqrt_le N

/-- On the low-divisor square-root block, the harmonic floor weight differs
from the logarithmic weight by at most `2/sqrt N`. -/
theorem k2WeightError_abs_le_sqrt
    (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d) (hds : d < Nat.sqrt N) :
    |k2WeightError N d| ≤ 2 / (Nat.sqrt N : ℝ) := by
  have hspos : 0 < Nat.sqrt N := (Nat.sqrt_pos).2 (by omega)
  have hs : 1 ≤ Nat.sqrt N := hspos
  have hdN : d ≤ N := by
    exact (hds.le.trans (Nat.sqrt_le_self N)).trans (Nat.le_refl N)
  have hdp1s : d + 1 ≤ Nat.sqrt N := by omega
  have hdp1N : d + 1 ≤ N := hdp1s.trans (Nat.sqrt_le_self N)
  have hq0 := k2Sqrt_le_quotient N d hd hds.le
  have hq1 := k2Sqrt_le_quotient N (d + 1) (by omega) hdp1s
  have he0 := k2HarmonicQuotientError_abs_le_scale
    N d (Nat.sqrt N) hs hd hdN hq0
  have he1 := k2HarmonicQuotientError_abs_le_scale
    N (d + 1) (Nat.sqrt N) hs (by omega) hdp1N hq1
  rw [k2WeightError_eq N d hN hd]
  calc
    |k2HarmonicQuotientError N d - k2HarmonicQuotientError N (d + 1)|
        ≤ |k2HarmonicQuotientError N d| +
            |k2HarmonicQuotientError N (d + 1)| := abs_sub _ _
    _ ≤ 1 / (Nat.sqrt N : ℝ) + 1 / (Nat.sqrt N : ℝ) :=
      add_le_add he0 he1
    _ = 2 / (Nat.sqrt N : ℝ) := by ring

end RHLean.Analysis
