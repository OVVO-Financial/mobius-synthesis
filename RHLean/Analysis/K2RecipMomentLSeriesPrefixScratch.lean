import RHLean.Analysis.K2RecipMomentAbelBoundaryScratch

noncomputable section

open Filter Finset Set Topology
open scoped ArithmeticFunction.Moebius LSeries.notation BigOperators

namespace RHLean.Analysis

private abbrev k2MobiusLogSqCoeff : ℕ → ℂ :=
  LSeries.logMul^[2] (fun n : ℕ => (μ n : ℂ))

/-- For a positive integer index, the real Abel coefficient is exactly the
corresponding term of the log-square Mobius L-series. -/
theorem k2A2AbelCoeff_ofReal_eq_term
    (sigma : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ((((μ n : ℤ) : ℝ) * k2LogRecipWeight 2 n *
        k2AbelBoundaryWeight sigma n : ℝ) : ℂ) =
      LSeries.term k2MobiusLogSqCoeff (sigma : ℂ) n := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hpowpos : 0 < (n : ℝ) ^ sigma := Real.rpow_pos_of_pos hnpos _
  have hweight :
      k2LogRecipWeight 2 n * k2AbelBoundaryWeight sigma n =
        (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ sigma := by
    unfold k2LogRecipWeight k2AbelBoundaryWeight
    rw [Real.rpow_sub hnpos, Real.rpow_one]
    field_simp [ne_of_gt hnpos, ne_of_gt hpowpos]
  rw [mul_assoc, hweight, LSeries.term_of_ne_zero hn0]
  simp only [k2MobiusLogSqCoeff, Function.iterate_succ_apply,
    Function.iterate_zero_apply, LSeries.logMul]
  push_cast
  rw [← Complex.natCast_log, Complex.ofReal_cpow (Nat.cast_nonneg n) sigma]
  have hncast : (((n : ℝ) : ℂ)) = (n : ℂ) := by norm_cast
  rw [hncast]
  ring_nf

/-- Complexifying the finite Abel prefix gives the ordinary finite L-series
partial sum through the same endpoint. -/
theorem k2A2AbelPrefix_ofReal_eq_sum_range (sigma : ℝ) (M : ℕ) :
    ((k2A2AbelPrefix sigma M : ℝ) : ℂ) =
      ∑ n ∈ Finset.range (M + 1),
        LSeries.term k2MobiusLogSqCoeff (sigma : ℂ) n := by
  have hIcc : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
    ext n
    simp
    omega
  unfold k2A2AbelPrefix
  rw [hIcc]
  push_cast
  calc
    ∑ n ∈ Finset.Ico 1 (M + 1),
        (((μ n : ℤ) : ℂ) * (k2LogRecipWeight 2 n : ℂ) *
          (k2AbelBoundaryWeight sigma n : ℂ)) =
      ∑ n ∈ Finset.Ico 1 (M + 1),
        LSeries.term k2MobiusLogSqCoeff (sigma : ℂ) n := by
          apply Finset.sum_congr rfl
          intro n hnmem
          rw [← k2A2AbelCoeff_ofReal_eq_term sigma (Finset.mem_Ico.mp hnmem).1]
          push_cast
          rfl
    _ = ∑ n ∈ Finset.Ico 0 (M + 1),
        LSeries.term k2MobiusLogSqCoeff (sigma : ℂ) n := by
          have hsplit := Finset.sum_Ico_consecutive
            (f := fun n : ℕ => LSeries.term k2MobiusLogSqCoeff (sigma : ℂ) n)
            (show 0 ≤ 1 by omega) (show 1 ≤ M + 1 by omega)
          simpa using hsplit
    _ = ∑ n ∈ Finset.range (M + 1),
        LSeries.term k2MobiusLogSqCoeff (sigma : ℂ) n := by
          simp

/-- At every real `sigma > 1`, the finite Abel prefixes converge to the real
part of the absolutely convergent log-square Mobius L-series. -/
theorem k2A2AbelPrefix_tendsto_LSeries_re
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Tendsto (fun M : ℕ => k2A2AbelPrefix sigma M) atTop
      (𝓝 (LSeries k2MobiusLogSqCoeff (sigma : ℂ)).re) := by
  have hsE : (1 : EReal) < ((sigma : ℂ).re : EReal) := by
    exact_mod_cast hsigma
  have habs :
      LSeries.abscissaOfAbsConv k2MobiusLogSqCoeff < ((sigma : ℂ).re : EReal) := by
    rw [LSeries.absicssaOfAbsConv_logPowMul]
    exact k2Mobius_abscissaOfAbsConv_le_one.trans_lt hsE
  have hsum : LSeriesSummable k2MobiusLogSqCoeff (sigma : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re habs
  have hpartial := hsum.hasSum.tendsto_sum_nat
  have hsucc : Tendsto (fun M : ℕ => M + 1) atTop atTop :=
    tendsto_atTop_mono Nat.le_succ tendsto_id
  have hcomplex :
      Tendsto (fun M : ℕ => ((k2A2AbelPrefix sigma M : ℝ) : ℂ)) atTop
        (𝓝 (LSeries k2MobiusLogSqCoeff (sigma : ℂ))) := by
    apply (hpartial.comp hsucc).congr'
    filter_upwards with M
    exact (k2A2AbelPrefix_ofReal_eq_sum_range sigma M).symm
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  simpa using hre

end RHLean.Analysis
