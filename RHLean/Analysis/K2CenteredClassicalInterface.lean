import Mathlib
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import RHLean.Analysis.NativePNTSignedSecondSelbergDepthFourFubini
import RHLean.Analysis.NativePNTSignedSecondSelbergDepthFourShell
import RHLean.Analysis.K2CenteredFinite
import RHLean.Analysis.StrongMertensRecipMomentTransfer

/-!
# Analytic interface and factor-four corollary for centered K2

The finite Abel identities are already checked in `K2CenteredFinite`.  This file
records the analytic input needed for the classical closure and proves the
factor-four consequence of centered convergence.  The factor-four limit is
independent of the unknown centered constant: it cancels between the two
prefixes.
-/

noncomputable section
open Filter Finset Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

local notation "γE" => Real.eulerMascheroniConstant

/-- The analytic consequences actually needed by the finite argument. -/
structure K2ClassicalMomentInput : Prop where
  r_tendsto_zero : Tendsto k2r atTop (𝓝 0)
  r_mul_log_tendsto_zero :
    Tendsto (fun N : ℕ => k2r N * Real.log (N : ℝ)) atTop (𝓝 0)
  c3_tendsto : ∃ L : ℝ, Tendsto k2C3 atTop (𝓝 L)

/-- The desired centered boundedness statement. -/
def K2CenteredBounded : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 3 ≤ N →
      |nativePNTSignedSecondSelbergKernelRecipMass N +
        2 * γE * Real.log (N : ℝ)| ≤ C

/-- The centered reciprocal K2 prefix. -/
def k2CenteredRecipValue (N : ℕ) : ℝ :=
  nativePNTSignedSecondSelbergKernelRecipMass N +
    2 * γE * Real.log (N : ℝ)

/-- Stronger asymptotic target, with the limiting constant left abstract. -/
def K2CenteredConverges : Prop :=
  ∃ L : ℝ, Tendsto k2CenteredRecipValue atTop (𝓝 L)

/-- Division by the fixed positive integer four preserves escape to infinity. -/
theorem k2_tendsto_nat_div_four_atTop :
    Tendsto (fun N : ℕ => N / 4) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop (4 * b)] with N hN
  omega

/-- The real quotient `N / floor(N/4)` tends to four. -/
theorem k2_tendsto_div_four_ratio :
    Tendsto
      (fun N : ℕ => (N : ℝ) / ((N / 4 : ℕ) : ℝ))
      atTop (𝓝 4) := by
  have hq :
      Tendsto (fun N : ℕ => ((N / 4 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp k2_tendsto_nat_div_four_atTop
  have hinv :
      Tendsto (fun N : ℕ => (((N / 4 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hq
  have hrem :
      Tendsto
        (fun N : ℕ => ((N % 4 : ℕ) : ℝ) * (((N / 4 : ℕ) : ℝ))⁻¹)
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun N => mul_nonneg (by positivity) (by positivity)
    · filter_upwards [eventually_ge_atTop 4] with N hN
      have hmodNat : N % 4 ≤ 3 := by omega
      have hmod : ((N % 4 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hmodNat
      exact mul_le_mul_of_nonneg_right hmod (inv_nonneg.mpr (by positivity))
    · simpa using (tendsto_const_nhds.mul hinv :
        Tendsto (fun N : ℕ => (3 : ℝ) * (((N / 4 : ℕ) : ℝ))⁻¹)
          atTop (𝓝 ((3 : ℝ) * 0)))
  have heq :
      (fun N : ℕ => (N : ℝ) / ((N / 4 : ℕ) : ℝ)) =ᶠ[atTop]
        (fun N : ℕ => 4 +
          ((N % 4 : ℕ) : ℝ) * (((N / 4 : ℕ) : ℝ))⁻¹) := by
    filter_upwards [eventually_ge_atTop 4] with N hN
    have hqpos : 0 < N / 4 := by omega
    have hq0 : (((N / 4 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hnat : N = 4 * (N / 4) + N % 4 := by omega
    have hdiv : (4 * (N / 4) + N % 4) / 4 = N / 4 := by omega
    have hmod : (4 * (N / 4) + N % 4) % 4 = N % 4 := by omega
    rw [hnat]
    simp only [hdiv, hmod]
    push_cast
    field_simp [hq0]
  have htarget :
      Tendsto
        (fun N : ℕ => 4 +
          ((N % 4 : ℕ) : ℝ) * (((N / 4 : ℕ) : ℝ))⁻¹)
        atTop (𝓝 4) := by
    simpa using (tendsto_const_nhds.add hrem :
      Tendsto
        (fun N : ℕ => (4 : ℝ) +
          ((N % 4 : ℕ) : ℝ) * (((N / 4 : ℕ) : ℝ))⁻¹)
        atTop (𝓝 ((4 : ℝ) + 0)))
  exact htarget.congr' heq.symm

/-- The logarithmic scale difference between `N` and `floor(N/4)` tends to
`log 4`. -/
theorem k2_tendsto_log_sub_log_div_four :
    Tendsto
      (fun N : ℕ =>
        Real.log (N : ℝ) - Real.log ((N / 4 : ℕ) : ℝ))
      atTop (𝓝 (Real.log 4)) := by
  have hlog :
      Tendsto
        (fun N : ℕ =>
          Real.log ((N : ℝ) / ((N / 4 : ℕ) : ℝ)))
        atTop (𝓝 (Real.log 4)) :=
    k2_tendsto_div_four_ratio.log (by norm_num)
  have heq :
      (fun N : ℕ =>
        Real.log (N : ℝ) - Real.log ((N / 4 : ℕ) : ℝ)) =ᶠ[atTop]
      (fun N : ℕ =>
        Real.log ((N : ℝ) / ((N / 4 : ℕ) : ℝ))) := by
    filter_upwards [eventually_ge_atTop 4] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hq0 : (((N / 4 : ℕ) : ℝ)) ≠ 0 := by
      have : 0 < N / 4 := by omega
      positivity
    rw [Real.log_div hN0 hq0]
  exact hlog.congr' heq.symm

/-- Exact algebraic expression of the factor-four shell through centered
prefixes. -/
theorem nativePNTSignedK2RecipInterval_four_eq_centered
    (N : ℕ) :
    nativePNTSignedK2RecipInterval N 4 =
      (k2CenteredRecipValue N - k2CenteredRecipValue (N / 4)) -
        2 * γE *
          (Real.log (N : ℝ) - Real.log ((N / 4 : ℕ) : ℝ)) := by
  rw [nativePNTSignedK2RecipInterval_four_eq_prefix_sub]
  unfold k2CenteredRecipValue
  ring

/-- The factor-four reciprocal shell has the exact asymptotic constant once the
centered K2 prefix converges.  The unknown centered prefix limit cancels. -/
theorem K2CenteredConverges.factorFourTendsto
    (h : K2CenteredConverges) :
    Tendsto
      (fun N : ℕ => nativePNTSignedK2RecipInterval N 4)
      atTop (𝓝 (-2 * γE * Real.log 4)) := by
  rcases h with ⟨L, hL⟩
  have hL4 :
      Tendsto (fun N : ℕ => k2CenteredRecipValue (N / 4)) atTop (𝓝 L) :=
    hL.comp k2_tendsto_nat_div_four_atTop
  have hdiff :
      Tendsto
        (fun N : ℕ =>
          k2CenteredRecipValue N - k2CenteredRecipValue (N / 4))
        atTop (𝓝 0) := by
    simpa using hL.sub hL4
  have hlog :
      Tendsto
        (fun N : ℕ =>
          2 * γE *
            (Real.log (N : ℝ) - Real.log ((N / 4 : ℕ) : ℝ)))
        atTop (𝓝 (2 * γE * Real.log 4)) := by
    simpa using
      (tendsto_const_nhds.mul k2_tendsto_log_sub_log_div_four :
        Tendsto
          (fun N : ℕ =>
            (2 * γE) *
              (Real.log (N : ℝ) - Real.log ((N / 4 : ℕ) : ℝ)))
          atTop (𝓝 ((2 * γE) * Real.log 4)))
  have hsub := hdiff.sub hlog
  simpa [nativePNTSignedK2RecipInterval_four_eq_centered] using hsub

/-- Global `O(1)` factor-four reciprocal shell bound, including the finite
initial segment. -/
theorem K2CenteredConverges.factorFourUniformBound
    (h : K2CenteredConverges) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, |nativePNTSignedK2RecipInterval N 4| ≤ C := by
  have hconv := h.factorFourTendsto
  let L : ℝ := -2 * γE * Real.log 4
  have hnear :
      ∀ᶠ N : ℕ in atTop,
        nativePNTSignedK2RecipInterval N 4 ∈ Metric.ball L 1 := by
    exact hconv.eventually (Metric.ball_mem_nhds L (by norm_num))
  have hlarge :
      ∀ᶠ N : ℕ in atTop,
        |nativePNTSignedK2RecipInterval N 4| ≤ |L| + 1 := by
    filter_upwards [hnear] with N hN
    have hd : |nativePNTSignedK2RecipInterval N 4 - L| < 1 := by
      simpa [Real.dist_eq] using hN
    calc
      |nativePNTSignedK2RecipInterval N 4| =
          |(nativePNTSignedK2RecipInterval N 4 - L) + L| := by ring_nf
      _ ≤ |nativePNTSignedK2RecipInterval N 4 - L| + |L| := abs_add_le _ _
      _ ≤ |L| + 1 := by linarith
  rcases eventually_atTop.1 hlarge with ⟨M, hM⟩
  let S : ℝ :=
    ∑ n ∈ Finset.range M, |nativePNTSignedK2RecipInterval n 4|
  refine ⟨|L| + 1 + S, ?_, ?_⟩
  · have hS : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  · intro N
    by_cases hMN : M ≤ N
    · have htail := hM N hMN
      have hS : 0 ≤ S := by
        dsimp [S]
        exact Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    · have hNM : N < M := Nat.lt_of_not_ge hMN
      have hsingle :
          |nativePNTSignedK2RecipInterval N 4| ≤ S := by
        dsimp [S]
        exact Finset.single_le_sum
          (fun n _ => abs_nonneg (nativePNTSignedK2RecipInterval n 4))
          (Finset.mem_range.2 hNM)
      have hbase : 0 ≤ |L| + 1 := by positivity
      linarith

/-!
The mathematical proof in `research/K2_CENTERED_CLASSICAL_PROOF_COMPLETE.md` proves:

* `K2ClassicalMomentInput` from the classical zero-free-region Mertens bound;
* `K2CenteredConverges` from `K2ClassicalMomentInput` by the two finite Abel identities plus the harmonic floor comparison;
* the limiting constant is `4 * γ^2 + 6 * γ₁`.

The remaining goal on this branch is to discharge the analytic input in the
Mathlib-4.24 environment without importing a theorem compiled against a
conflicting Mathlib version.
-/

end RHLean.Analysis