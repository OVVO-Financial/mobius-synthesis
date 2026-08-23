import RHLean.Analysis.K2RecipMomentAbelUniformScratch
import RHLean.Analysis.K2RecipMomentLSeriesPrefixScratch

noncomputable section

open Filter Finset Set Topology
open scoped ArithmeticFunction.Moebius LSeries.notation BigOperators

namespace RHLean.Analysis

local notation "gammaE" => Real.eulerMascheroniConstant

/-- A convergent order-two Mobius moment has the same right-hand Dirichlet
Abel limit.  The proof is finite: split the centered Abel identity at one
fixed prefix, let the finite head tend to zero, and control the remaining
positive telescoping mass by the tail error of the original prefixes. -/
theorem k2MobiusLogSqLSeries_re_tendsto_of_moment_tendsto
    {A : ℝ}
    (hA : Tendsto (k2MobiusLogMoment 2) atTop (𝓝 A)) :
    Tendsto
      (fun sigma : ℝ =>
        (LSeries (LSeries.logMul^[2] (fun n : ℕ => (μ n : ℂ)))
          (sigma : ℂ)).re)
      (𝓝[>] (1 : ℝ)) (𝓝 A) := by
  rw [Metric.tendsto_nhds] at hA ⊢
  intro eps heps
  let delta : ℝ := eps / 3
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hcloseEv := hA delta hdelta
  rcases eventually_atTop.1 hcloseEv with ⟨N0, hN0⟩
  let N : ℕ := max 1 N0
  have hN : 1 ≤ N := by
    dsimp [N]
    exact le_max_left _ _
  have hN0N : N0 ≤ N := by
    dsimp [N]
    exact le_max_right _ _
  have hcloseN : ∀ n : ℕ, N ≤ n →
      |k2MobiusLogMoment 2 n - A| ≤ delta := by
    intro n hn
    have hnclose := hN0 n (hN0N.trans hn)
    have : |k2MobiusLogMoment 2 n - A| < delta := by
      simpa [Real.dist_eq] using hnclose
    exact this.le
  have hheadNhds := k2A2AbelHead_tendsto_zero A N
  have hheadRight :
      Tendsto
        (fun sigma : ℝ =>
          ∑ n ∈ Finset.Ico 1 N,
            (k2MobiusLogMoment 2 n - A) *
              (k2AbelBoundaryWeight sigma n -
                k2AbelBoundaryWeight sigma (n + 1)))
        (𝓝[>] (1 : ℝ)) (𝓝 0) :=
    hheadNhds.mono_left inf_le_left
  rw [Metric.tendsto_nhds] at hheadRight
  have hheadEv := hheadRight delta hdelta
  filter_upwards [hheadEv, self_mem_nhdsWithin] with sigma hhead hsigma
  have hsigma : 1 < sigma := by simpa using hsigma
  have hheadAbs :
      |∑ n ∈ Finset.Ico 1 N,
        (k2MobiusLogMoment 2 n - A) *
          (k2AbelBoundaryWeight sigma n -
            k2AbelBoundaryWeight sigma (n + 1))| < delta := by
    simpa [Real.dist_eq] using hhead
  have hprefix := k2A2AbelPrefix_tendsto_LSeries_re hsigma
  have habs :
      Tendsto
        (fun M : ℕ => |k2A2AbelPrefix sigma M - A|)
        atTop
        (𝓝 |(LSeries (LSeries.logMul^[2] (fun n : ℕ => (μ n : ℂ)))
          (sigma : ℂ)).re - A|) := by
    simpa using (hprefix.sub tendsto_const_nhds).abs
  have hfinite :
      ∀ᶠ M : ℕ in atTop,
        |k2A2AbelPrefix sigma M - A| ≤ 2 * delta := by
    filter_upwards [eventually_ge_atTop N] with M hNM
    have hu := k2A2AbelPrefix_centered_abs_le_head_add
      hsigma hdelta.le hN hNM
      (fun n hnN _hnM => hcloseN n hnN)
    exact (hu.trans_lt (by linarith)).le
  have hlimit :
      |(LSeries (LSeries.logMul^[2] (fun n : ℕ => (μ n : ℂ)))
        (sigma : ℂ)).re - A| ≤ 2 * delta :=
    le_of_tendsto habs hfinite
  have hstrict :
      |(LSeries (LSeries.logMul^[2] (fun n : ℕ => (μ n : ℂ)))
        (sigma : ℂ)).re - A| < eps := by
    dsimp [delta] at hlimit ⊢
    linarith
  simpa [Real.dist_eq] using hstrict

/-- The order-two Abel constant is exactly the second reciprocal-zeta Taylor
coefficient `-2 * gammaE`. -/
theorem k2MertensAbelTerm_two_tsum_eq_neg_two_gamma :
    (∑' n : ℕ, k2MertensAbelTerm 2 n) = -2 * gammaE := by
  let A : ℝ := ∑' n : ℕ, k2MertensAbelTerm 2 n
  have hmoment : Tendsto (k2MobiusLogMoment 2) atTop (𝓝 A) := by
    dsimp [A]
    exact k2MobiusLogMoment_tendsto_of_summable 2
      k2MertensAbelTerm_two_summable
      (k2StrongMertens_logRecip_endpoint_tendsto_zero 2)
  have habel := k2MobiusLogSqLSeries_re_tendsto_of_moment_tendsto hmoment
  have hgammaComplex := k2MobiusLogSqLSeries_tendsto_right_one
  have hgammaRe :
      Tendsto
        (fun sigma : ℝ =>
          (LSeries (LSeries.logMul^[2] (fun n : ℕ => (μ n : ℂ)))
            (sigma : ℂ)).re)
        (𝓝[>] (1 : ℝ)) (𝓝 (-2 * gammaE)) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp hgammaComplex
    simpa using h
  have hA : A = -2 * gammaE := tendsto_nhds_unique habel hgammaRe
  simpa [A] using hA

/-- The centered second reciprocal moment tends to zero with the analytic
center now identified exactly. -/
theorem k2r_tendsto_zero_from_strongMertens :
    Tendsto k2r atTop (𝓝 0) := by
  have h := k2r_tendsto_of_summable
    k2MertensAbelTerm_two_summable
    (k2StrongMertens_logRecip_endpoint_tendsto_zero 2)
  rw [k2MertensAbelTerm_two_tsum_eq_neg_two_gamma] at h
  simpa using h

/-- The cubic reciprocal moment converges from the same Strong Mertens input. -/
theorem k2C3_tendsto_from_strongMertens :
    ∃ ell : ℝ, Tendsto k2C3 atTop (𝓝 ell) :=
  k2C3_tendsto_of_summable
    k2MertensAbelTerm_three_summable
    (k2StrongMertens_logRecip_endpoint_tendsto_zero 3)

end RHLean.Analysis
