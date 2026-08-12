import Mathlib
import Mathlib.NumberTheory.Harmonic.Bounds
import RHLean.Analysis.NativePNTSelberg
import RHLean.Analysis.NativePNTSummatorySelberg

/-!
# Bounded reciprocal mass of the Chebyshev error

Let `R(N) = psi(N) - N`.  The elementary Erdos step needs the signed reciprocal
mass

`sum_{1 <= n <= N} R(n) / (n(n+1))`

to stay uniformly bounded.  This module proves that fact from the already
formalized Mertens-first-theorem estimate by an exact finite Abel identity.
It also derives the first absolute Selberg error recurrence from the summatory
Selberg theorem.  No prime-distribution asymptotic is used.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Discrete Chebyshev error. -/
def nativePNTError (N : ℕ) : ℝ := nativePsi N - (N : ℝ)

/-- Signed reciprocal mass used in Erdos's good-interval argument. -/
def nativePNTWeightedErrorMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    nativePNTError n / ((n : ℝ) * (n + 1 : ℝ))

/-- One-step increment of the finite Chebyshev mass. -/
theorem nativePsi_succ (N : ℕ) :
    nativePsi (N + 1) = nativePsi N + Λ (N + 1) := by
  unfold nativePsi
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- One-step increment of the reciprocal von Mangoldt mass. -/
theorem nativeLambdaRecip_succ (N : ℕ) :
    nativeLambdaRecip (N + 1) =
      nativeLambdaRecip N + Λ (N + 1) / (N + 1 : ℝ) := by
  unfold nativeLambdaRecip
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
  norm_num [Nat.cast_add, Nat.cast_one]

/-- Exact finite Abel identity for the Chebyshev mass. -/
theorem nativePsi_weighted_abel (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      nativePsi n / ((n : ℝ) * (n + 1 : ℝ))) =
      nativeLambdaRecip N - nativePsi N / (N + 1 : ℝ) := by
  induction N with
  | zero =>
      simp [nativePsi, nativeLambdaRecip]
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih,
        nativeLambdaRecip_succ, nativePsi_succ]
      push_cast
      have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
      field_simp [h1, h2]
      ring_nf

/-- The corresponding linear kernel telescopes to a harmonic number. -/
theorem nativeLinear_weighted_abel (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      (n : ℝ) / ((n : ℝ) * (n + 1 : ℝ))) =
      (harmonic (N + 1) : ℝ) - 1 := by
  induction N with
  | zero => norm_num [harmonic_succ]
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih]
      rw [harmonic_succ (N + 1)]
      push_cast
      have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
      field_simp [h1, h2]
      ring_nf

/-- Exact expression of the signed reciprocal error mass in terms of Mertens'
first theorem, the endpoint Chebyshev mass, and one harmonic number. -/
theorem nativePNTWeightedErrorMass_eq (N : ℕ) :
    nativePNTWeightedErrorMass N =
      nativeLambdaRecip N - nativePsi N / (N + 1 : ℝ) -
        ((harmonic (N + 1) : ℝ) - 1) := by
  unfold nativePNTWeightedErrorMass nativePNTError
  have hsplit :
      (∑ n ∈ Finset.Icc 1 N,
        (nativePsi n - (n : ℝ)) / ((n : ℝ) * (n + 1 : ℝ))) =
        (∑ n ∈ Finset.Icc 1 N,
          nativePsi n / ((n : ℝ) * (n + 1 : ℝ))) -
        ∑ n ∈ Finset.Icc 1 N,
          (n : ℝ) / ((n : ℝ) * (n + 1 : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  rw [hsplit, nativePsi_weighted_abel, nativeLinear_weighted_abel]

/-- Harmonic excess over `log N` is uniformly bounded by `1 + log 2`. -/
theorem nativeHarmonic_succ_sub_log_bounds
    (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ (harmonic (N + 1) : ℝ) - Real.log N ∧
      (harmonic (N + 1) : ℝ) - Real.log N ≤ 1 + Real.log 2 := by
  have hlower : Real.log (N : ℝ) ≤ (harmonic (N + 1) : ℝ) := by
    calc
      Real.log (N : ℝ) ≤ Real.log ((N + 2 : ℕ) : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast hN
        · exact_mod_cast (show N ≤ N + 2 by omega)
      _ ≤ (harmonic (N + 1) : ℝ) := by
        convert (log_add_one_le_harmonic (N + 1)) using 1
  have hupper0 :
      (harmonic (N + 1) : ℝ) ≤ 1 + Real.log (N + 1 : ℝ) := by
    simpa using harmonic_le_one_add_log (N + 1)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hratio : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
    linarith
  have hlogratio : Real.log (N + 1 : ℝ) ≤ Real.log 2 + Real.log N := by
    change Real.log ((N : ℝ) + 1) ≤ Real.log 2 + Real.log (N : ℝ)
    calc
      Real.log ((N : ℝ) + 1) ≤ Real.log (2 * (N : ℝ)) := by
        apply Real.log_le_log
        · positivity
        · exact hratio
      _ = Real.log 2 + Real.log N := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)]
  constructor
  · linarith
  · have hupper0' :
        (harmonic (N + 1) : ℝ) ≤ 1 + Real.log (N : ℝ) + Real.log 2 := by
      calc
        (harmonic (N + 1) : ℝ) ≤ 1 + Real.log (N + 1 : ℝ) := hupper0
        _ ≤ 1 + (Real.log 2 + Real.log N) := by linarith
        _ = 1 + Real.log N + Real.log 2 := by ring
    linarith

/-- Uniform bound for the signed reciprocal Chebyshev-error mass. -/
theorem nativePNTWeightedErrorMass_abs_le
    (N : ℕ) :
    |nativePNTWeightedErrorMass N| ≤
      2 * (Real.log 4 + 2) + Real.log 2 + 3 := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst N
    simp [nativePNTWeightedErrorMass]
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · have hN : 1 ≤ N := hNpos
    have heq := nativePNTWeightedErrorMass_eq N
    have hLambda := nativeLambdaRecip_sub_log_abs_le N hN
    have hpsi0 := nativePsi_nonneg N
    have hpsi := nativePsi_le_const_mul N
    have hden : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hfrac0 : 0 ≤ nativePsi N / ((N : ℝ) + 1) :=
      div_nonneg hpsi0 hden.le
    have hfrac : nativePsi N / ((N : ℝ) + 1) ≤ Real.log 4 + 2 := by
      have hNlt : (N : ℝ) < (N : ℝ) + 1 := by linarith
      have hconst0 : 0 ≤ Real.log 4 + 2 := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
        linarith
      calc
        nativePsi N / ((N : ℝ) + 1) ≤
            ((Real.log 4 + 2) * (N : ℝ)) / ((N : ℝ) + 1) :=
          div_le_div_of_nonneg_right hpsi hden.le
        _ ≤ Real.log 4 + 2 := by
          rw [div_le_iff₀ hden]
          nlinarith
    have hharm := nativeHarmonic_succ_sub_log_bounds N hN
    rw [heq]
    rw [abs_le] at hLambda ⊢
    constructor <;> linarith [hLambda.1, hLambda.2, hfrac0, hfrac,
      hharm.1, hharm.2]

/-! ## Absolute Selberg error recurrence -/

/-- The summatory Selberg pair, after subtracting its main term, splits exactly
into the endpoint Chebyshev error, the reciprocal von Mangoldt weighted error,
and the elementary log-factorial floor term. -/
theorem nativePNTError_selberg_decomposition (N : ℕ) :
    nativeSelbergPair N - 2 * (N : ℝ) * Real.log N =
      nativePNTError N * Real.log N +
        (∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)) +
        (Real.log ((Nat.factorial N : ℕ) : ℝ) -
          (N : ℝ) * Real.log N) := by
  have hsplit :
      (∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)) =
        (∑ d ∈ Finset.Icc 1 N, Λ d * nativePsi (N / d)) -
          ∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ) := by
    unfold nativePNTError
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  unfold nativeSelbergPair
  rw [hsplit, nativeVonMangoldtSummatory]
  unfold nativePNTError
  ring

/-- The elementary factorial bracket gives the cruder linear bound centered
at `N log N`, which is the form used by the absolute Selberg recurrence. -/
theorem nativeLogFactorial_sub_Nlog_abs_le
    (N : ℕ) (hN : 1 ≤ N) :
    |Real.log ((Nat.factorial N : ℕ) : ℝ) -
      (N : ℝ) * Real.log N| ≤ (N : ℝ) := by
  have hlo := nativeLogFactorial_lower N hN
  have hup := nativeLogFactorial_upper N hN
  rw [abs_le]
  constructor <;> linarith

private theorem nativeLambdaErrorSum_abs_le (N : ℕ) :
    |∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)| ≤
      ∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)| := by
  calc
    |∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)| ≤
        ∑ d ∈ Finset.Icc 1 N, |Λ d * nativePNTError (N / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)| := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- **Absolute Selberg recurrence at natural endpoints.**

This is the first genuinely absolute bridge needed by the Erdos contraction:

`|R(N)| log N <= sum_{d<=N} Lambda(d) |R(floor(N/d))| + O(N)`.

The linear constant is explicit and comes only from the summatory Selberg
bound and the elementary log-factorial floor term. -/
theorem nativePNTError_abs_log_le_weighted
    (N : ℕ) (hN : 3 ≤ N) :
    |nativePNTError N| * Real.log N ≤
      (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) +
        (3 * (Real.log 4 + 2) + 173) * (N : ℝ) := by
  have hsel := nativeSelbergPair_sub_two_mul_log_abs_le N hN
  have hfac := nativeLogFactorial_sub_Nlog_abs_le N (by omega)
  have hsum := nativeLambdaErrorSum_abs_le N
  have hdecomp := nativePNTError_selberg_decomposition N
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hAeq :
      nativePNTError N * Real.log N =
        (nativeSelbergPair N - 2 * (N : ℝ) * Real.log N) -
          (∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)) -
          (Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log N) := by
    linarith [hdecomp]
  have htri :
      |nativePNTError N * Real.log N| ≤
        |nativeSelbergPair N - 2 * (N : ℝ) * Real.log N| +
          |∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)| +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log N| := by
    rw [hAeq]
    calc
      |(nativeSelbergPair N - 2 * (N : ℝ) * Real.log N) -
          (∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)) -
          (Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log N)| ≤
        |(nativeSelbergPair N - 2 * (N : ℝ) * Real.log N) -
          (∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d))| +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log N| := abs_sub _ _
      _ ≤
        (|nativeSelbergPair N - 2 * (N : ℝ) * Real.log N| +
          |∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)|) +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log N| := by
        gcongr
        exact abs_sub _ _
  have hmain :
      |nativePNTError N * Real.log N| ≤
        (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) +
          (3 * (Real.log 4 + 2) + 173) * (N : ℝ) := by
    calc
      |nativePNTError N * Real.log N| ≤
        |nativeSelbergPair N - 2 * (N : ℝ) * Real.log N| +
          |∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)| +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log N| := htri
      _ ≤
        (3 * (Real.log 4 + 2) + 172) * (N : ℝ) +
          (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) +
          (N : ℝ) := by
        gcongr
      _ =
        (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) +
          (3 * (Real.log 4 + 2) + 173) * (N : ℝ) := by ring
  simpa [abs_mul, abs_of_nonneg hlog0] using hmain


/-! ## Reciprocal logarithmic von Mangoldt moment -/

/-- Reciprocal log-weighted von Mangoldt mass. -/
def nativeLambdaLogRecip (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (Λ n / (n : ℝ)) * Real.log (n : ℝ)

private theorem nativePNTTelescopeIco
    (b : ℕ → ℝ) : ∀ M : ℕ, 1 ≤ M →
    (∑ n ∈ Finset.Ico 1 M, (b (n + 1) - b n)) = b M - b 1 := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
      rw [Finset.sum_Ico_succ_top hM, ih]
      ring

private theorem nativePNTLogIncrement_nonneg
    (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
  apply sub_nonneg.mpr
  apply Real.log_le_log
  · exact_mod_cast hn
  · exact_mod_cast (show n ≤ n + 1 by omega)

private theorem nativePNTLogIncrement_le_one
    (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 := by
  have hinc := nativeLog_succ_sub_log_le_inv n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hrecip : (1 : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hnpos]
    exact_mod_cast hn
  exact hinc.trans hrecip

private theorem nativePNTLogIncrement_sum
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N,
      (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) = Real.log N := by
  have h := nativePNTTelescopeIco (fun n => Real.log (n : ℝ)) N hN
  simpa using h

private theorem nativePNTLogSquareIncrement_sum
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N,
      ((Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 -
        (Real.log (n : ℝ)) ^ 2)) = (Real.log N) ^ 2 := by
  have h := nativePNTTelescopeIco
    (fun n => (Real.log (n : ℝ)) ^ 2) N hN
  simpa using h

/-- Abel form of the reciprocal log-weighted von Mangoldt mass. -/
theorem nativeLambdaLogRecip_abel (N : ℕ) :
    nativeLambdaLogRecip N =
      nativeLambdaRecip N * Real.log N +
        ∑ n ∈ Finset.Ico 1 N,
          nativeLambdaRecip n *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)) := by
  have h := nativeAbelIccOne
    (fun n => Λ n / (n : ℝ))
    (fun n => Real.log (n : ℝ)) N
  simpa [nativeLambdaLogRecip, nativeLambdaRecip] using h

/-- **Reciprocal log von Mangoldt moment.**  Mertens' first theorem and finite
Abel summation give the coefficient `1/2` without any prime-distribution
asymptotic:

`sum_{n<=N} Lambda(n) log(n) / n = (1/2) log^2 N + O(log N)`.
-/
theorem nativeLambdaLogRecip_sub_half_logSq_abs_le
    (N : ℕ) (hN : 1 ≤ N) :
    |nativeLambdaLogRecip N - (1 / 2 : ℝ) * (Real.log N) ^ 2| ≤
      (2 * (Real.log 4 + 2) + 1) * Real.log N := by
  let delta : ℕ → ℝ := fun n =>
    Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hdelta0 : ∀ n ∈ Finset.Ico 1 N, 0 ≤ delta n := by
    intro n hn
    exact nativePNTLogIncrement_nonneg n (Finset.mem_Ico.mp hn).1
  have hdelta1 : ∀ n ∈ Finset.Ico 1 N, delta n ≤ 1 := by
    intro n hn
    exact nativePNTLogIncrement_le_one n (Finset.mem_Ico.mp hn).1
  have hsumdelta :
      (∑ n ∈ Finset.Ico 1 N, delta n) = Real.log N := by
    simpa [delta] using nativePNTLogIncrement_sum N hN
  have hsquares0 :
      0 ≤ ∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2 := by
    exact Finset.sum_nonneg fun n _hn => sq_nonneg (delta n)
  have hsquares_le :
      (∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2) ≤ Real.log N := by
    calc
      (∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2) ≤
          ∑ n ∈ Finset.Ico 1 N, delta n := by
        apply Finset.sum_le_sum
        intro n hn
        have h0 := hdelta0 n hn
        have h1 := hdelta1 n hn
        have hm := mul_nonneg h0 (sub_nonneg.mpr h1)
        nlinarith
      _ = Real.log N := hsumdelta
  have hsqsplit :
      (∑ n ∈ Finset.Ico 1 N,
        ((Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 -
          (Real.log (n : ℝ)) ^ 2)) =
        2 * (∑ n ∈ Finset.Ico 1 N,
          Real.log (n : ℝ) * delta n) +
          ∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2 := by
    calc
      (∑ n ∈ Finset.Ico 1 N,
        ((Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 -
          (Real.log (n : ℝ)) ^ 2)) =
        ∑ n ∈ Finset.Ico 1 N,
          (2 * (Real.log (n : ℝ) * delta n) + (delta n) ^ 2) := by
        apply Finset.sum_congr rfl
        intro n _hn
        simp only [delta]
        ring
      _ = 2 * (∑ n ∈ Finset.Ico 1 N,
          Real.log (n : ℝ) * delta n) +
          ∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsqid :
      (Real.log N) ^ 2 =
        2 * (∑ n ∈ Finset.Ico 1 N,
          Real.log (n : ℝ) * delta n) +
          ∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2 := by
    calc
      (Real.log N) ^ 2 =
          ∑ n ∈ Finset.Ico 1 N,
            ((Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 -
              (Real.log (n : ℝ)) ^ 2) :=
        (nativePNTLogSquareIncrement_sum N hN).symm
      _ = _ := hsqsplit
  have hmain :
      (Real.log N) ^ 2 +
          (∑ n ∈ Finset.Ico 1 N,
            Real.log (n : ℝ) *
              (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))) =
        (1 / 2 : ℝ) * (Real.log N) ^ 2 +
          (1 / 2 : ℝ) *
            (∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2) := by
    have hneg :
        (∑ n ∈ Finset.Ico 1 N,
          Real.log (n : ℝ) *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))) =
          -(∑ n ∈ Finset.Ico 1 N,
            Real.log (n : ℝ) * delta n) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n _hn
      simp only [delta]
      ring
    rw [hneg]
    nlinarith [hsqid]
  have hsumdecomp :
      (∑ n ∈ Finset.Ico 1 N,
        nativeLambdaRecip n *
          (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))) =
        (∑ n ∈ Finset.Ico 1 N,
          Real.log (n : ℝ) *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))) +
        ∑ n ∈ Finset.Ico 1 N,
          (nativeLambdaRecip n - Real.log n) *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  have hdecomp :
      nativeLambdaLogRecip N - (1 / 2 : ℝ) * (Real.log N) ^ 2 =
        (1 / 2 : ℝ) * (∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2) +
          (nativeLambdaRecip N - Real.log N) * Real.log N +
          ∑ n ∈ Finset.Ico 1 N,
            (nativeLambdaRecip n - Real.log n) *
              (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)) := by
    rw [nativeLambdaLogRecip_abel, hsumdecomp]
    have hend :
        nativeLambdaRecip N * Real.log N =
          (Real.log N) ^ 2 +
            (nativeLambdaRecip N - Real.log N) * Real.log N := by ring
    rw [hend]
    linarith [hmain]
  have hhalf :
      |(1 / 2 : ℝ) * (∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2)| ≤
        (1 / 2 : ℝ) * Real.log N := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hsquares0)]
    exact mul_le_mul_of_nonneg_left hsquares_le (by norm_num)
  have hendpoint :
      |(nativeLambdaRecip N - Real.log N) * Real.log N| ≤
        (Real.log 4 + 2) * Real.log N := by
    rw [abs_mul, abs_of_nonneg hlog0]
    exact mul_le_mul_of_nonneg_right
      (nativeLambdaRecip_sub_log_abs_le N hN) hlog0
  have hinteriorPoint : ∀ n ∈ Finset.Ico 1 N,
      |(nativeLambdaRecip n - Real.log n) *
        (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))| ≤
        (Real.log 4 + 2) * delta n := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
    have hd0 := hdelta0 n hn
    have herr := nativeLambdaRecip_sub_log_abs_le n hn1
    have hneg :
        Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) = -delta n := by
      simp only [delta]
      ring
    rw [hneg, abs_mul, abs_neg, abs_of_nonneg hd0]
    exact mul_le_mul_of_nonneg_right herr hd0
  have hinterior :
      |∑ n ∈ Finset.Ico 1 N,
        (nativeLambdaRecip n - Real.log n) *
          (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))| ≤
        (Real.log 4 + 2) * Real.log N := by
    calc
      |∑ n ∈ Finset.Ico 1 N,
        (nativeLambdaRecip n - Real.log n) *
          (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))| ≤
        ∑ n ∈ Finset.Ico 1 N,
          |(nativeLambdaRecip n - Real.log n) *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ico 1 N, (Real.log 4 + 2) * delta n :=
        Finset.sum_le_sum hinteriorPoint
      _ = (Real.log 4 + 2) *
          (∑ n ∈ Finset.Ico 1 N, delta n) := by
        rw [Finset.mul_sum]
      _ = (Real.log 4 + 2) * Real.log N := by rw [hsumdelta]
  rw [hdecomp]
  calc
    |(1 / 2 : ℝ) * (∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2) +
        (nativeLambdaRecip N - Real.log N) * Real.log N +
        ∑ n ∈ Finset.Ico 1 N,
          (nativeLambdaRecip n - Real.log n) *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))| ≤
      (|(1 / 2 : ℝ) * (∑ n ∈ Finset.Ico 1 N, (delta n) ^ 2)| +
        |(nativeLambdaRecip N - Real.log N) * Real.log N|) +
        |∑ n ∈ Finset.Ico 1 N,
          (nativeLambdaRecip n - Real.log n) *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))| := by
      exact (abs_add_le _ _).trans
        (add_le_add_right (abs_add_le _ _) _)
    _ ≤ (1 / 2 : ℝ) * Real.log N +
        (Real.log 4 + 2) * Real.log N +
        (Real.log 4 + 2) * Real.log N := by
      gcongr
    _ ≤ (2 * (Real.log 4 + 2) + 1) * Real.log N := by
      nlinarith


/-! ## Squared Selberg error recurrence -/

/-- The elementary Chebyshev estimate gives a global linear envelope for the
absolute error. -/
theorem nativePNTError_abs_le_chebyshev (N : ℕ) :
    |nativePNTError N| ≤ (Real.log 4 + 3) * (N : ℝ) := by
  have hpsi0 := nativePsi_nonneg N
  have hpsi := nativePsi_le_const_mul N
  unfold nativePNTError
  calc
    |nativePsi N - (N : ℝ)| ≤ |nativePsi N| + |(N : ℝ)| := abs_sub _ _
    _ = nativePsi N + (N : ℝ) := by
      rw [abs_of_nonneg hpsi0, abs_of_nonneg (by positivity)]
    _ ≤ (Real.log 4 + 2) * (N : ℝ) + (N : ℝ) :=
      add_le_add_right hpsi _
    _ = (Real.log 4 + 3) * (N : ℝ) := by ring

private theorem nativePNTFirstErrorConstant_le_thousand :
    3 * (Real.log 4 + 2) + 173 ≤ (1000 : ℝ) := by
  have hlog4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  norm_num at hlog4 ⊢
  linarith

/-- A deliberately coarse all-endpoint form of the first absolute Selberg
recurrence.  The large constant avoids exceptional cases when this theorem is
applied recursively to floor quotients `N / d`. -/
theorem nativePNTError_abs_log_le_weighted_crude (N : ℕ) :
    |nativePNTError N| * Real.log N ≤
      (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) +
        1000 * (N : ℝ) := by
  by_cases hN3 : 3 ≤ N
  · have h := nativePNTError_abs_log_le_weighted N hN3
    calc
      |nativePNTError N| * Real.log N ≤
          (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) +
            (3 * (Real.log 4 + 2) + 173) * (N : ℝ) := h
      _ ≤ (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) +
            1000 * (N : ℝ) := by
        gcongr
        exact nativePNTFirstErrorConstant_le_thousand
  · have hNle : N ≤ 2 := by omega
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · simp [nativePNTError, nativePsi]
    · have hN1 : 1 ≤ N := hNpos
      have hlog0 : 0 ≤ Real.log (N : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hN1)
      have hlogle0 := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < (N : ℝ) by exact_mod_cast hNpos)
      have hlogle : Real.log (N : ℝ) ≤ (N : ℝ) := by linarith
      have herr := nativePNTError_abs_le_chebyshev N
      have hlog4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      have hC0 : 0 ≤ Real.log 4 + 3 := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
        linarith
      have hC6 : Real.log 4 + 3 ≤ 6 := by
        norm_num at hlog4 ⊢
        linarith
      have hNR0 : 0 ≤ (N : ℝ) := by positivity
      have hNleR : (N : ℝ) ≤ 2 := by exact_mod_cast hNle
      have hNN : (N : ℝ) * (N : ℝ) ≤ 2 * (N : ℝ) := by
        nlinarith
      have hleft :
          |nativePNTError N| * Real.log N ≤ 1000 * (N : ℝ) := by
        calc
          |nativePNTError N| * Real.log N ≤
              ((Real.log 4 + 3) * (N : ℝ)) * Real.log N :=
            mul_le_mul_of_nonneg_right herr hlog0
          _ ≤ ((Real.log 4 + 3) * (N : ℝ)) * (N : ℝ) :=
            mul_le_mul_of_nonneg_left hlogle (mul_nonneg hC0 hNR0)
          _ ≤ (6 * (N : ℝ)) * (N : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hC6 hNR0) hNR0
          _ = 6 * ((N : ℝ) * (N : ℝ)) := by ring
          _ ≤ 6 * (2 * (N : ℝ)) := mul_le_mul_of_nonneg_left hNN (by norm_num)
          _ ≤ 1000 * (N : ℝ) := by nlinarith
      have hsum0 :
          0 ≤ ∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)| := by
        apply Finset.sum_nonneg
        intro d _hd
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (abs_nonneg _)
      exact hleft.trans (le_add_of_nonneg_left hsum0)

/-- The logarithm of an endpoint is bounded by the logarithms of a divisor and
its floor quotient, up to one harmless unit. -/
private theorem nativeLog_le_log_divisor_add_floor_add_one
    (N d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
    Real.log (N : ℝ) ≤
      Real.log (d : ℝ) + Real.log ((N / d : ℕ) : ℝ) + 1 := by
  have hdI := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := by omega
  have hNpos : 0 < N := lt_of_lt_of_le hdpos hdI.2
  have hq1 : 1 ≤ N / d :=
    (Nat.one_le_div_iff hdpos).2 hdI.2
  have hdivmod : d * (N / d) + N % d = N := Nat.div_add_mod N d
  have hrem : N % d < d := Nat.mod_lt N hdpos
  have hlt : N < d * (N / d + 1) := by
    calc
      N = d * (N / d) + N % d := hdivmod.symm
      _ < d * (N / d) + d := Nat.add_lt_add_left hrem _
      _ = d * (N / d + 1) := by ring
  have hlogprod :
      Real.log (N : ℝ) ≤ Real.log ((d * (N / d + 1) : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hNpos
    · exact_mod_cast (Nat.le_of_lt hlt)
  have hdR0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
  have hprodlog :
      Real.log ((d * (N / d + 1) : ℕ) : ℝ) =
        Real.log (d : ℝ) + Real.log ((N / d + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [Real.log_mul hdR0 (by positivity)]
  rw [hprodlog] at hlogprod
  have hinc := nativeLog_succ_sub_log_le_inv (N / d) hq1
  have hqposR : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < N / d by omega)
  have hrecip : (1 : ℝ) / ((N / d : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hqposR]
    exact_mod_cast hq1
  linarith

/-- Log-weighted error mass occurring in the differentiated Selberg kernel. -/
def nativeLambdaLogErrorMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    Λ n * Real.log (n : ℝ) * |nativePNTError (N / n)|

/-- Convolution-weighted error mass. -/
def nativeLambdaConvolutionErrorMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    (Λ * Λ) n * |nativePNTError (N / n)|

/-- The combined second-von-Mangoldt error mass. -/
def nativeLambdaTwoErrorMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    nativeLambdaTwo n * |nativePNTError (N / n)|

/-- The second-von-Mangoldt mass is exactly the sum of its log and convolution
error pieces. -/
theorem nativeLambdaTwoErrorMass_eq_log_add_convolution (N : ℕ) :
    nativeLambdaTwoErrorMass N =
      nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N := by
  unfold nativeLambdaTwoErrorMass nativeLambdaLogErrorMass
    nativeLambdaConvolutionErrorMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [nativeLambdaTwo_eq_logWeight_vonMangoldt_add_convolution]
  simp only [ArithmeticFunction.add_apply, arithmeticLogWeight_apply]
  ring

/-- Cofactor-first Fubini form of the convolution error mass. -/
theorem nativeLambdaConvolutionErrorMass_eq_double (N : ℕ) :
    nativeLambdaConvolutionErrorMass N =
      ∑ d ∈ Finset.Icc 1 N,
        ∑ m ∈ Finset.Icc 1 (N / d),
          Λ d * Λ m * |nativePNTError (N / (d * m))| := by
  unfold nativeLambdaConvolutionErrorMass
  have hmem : ∀ (n d : ℕ),
      n ∈ Finset.Icc 1 N ∧ d ∈ n.divisors ↔
        n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x) ∧ d ∈ Finset.Icc 1 N := by
    intro n d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, hdvd, hn0⟩
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact hn0 (Nat.eq_zero_of_zero_dvd hdvd)
      exact ⟨⟨⟨hn1, hnN⟩, hdvd⟩,
        Nat.one_le_iff_ne_zero.mpr hd0,
        (Nat.le_of_dvd (by omega) hdvd).trans hnN⟩
    · rintro ⟨⟨⟨hn1, hnN⟩, hdvd⟩, _hd1, _hdN⟩
      exact ⟨⟨hn1, hnN⟩, hdvd, Nat.ne_of_gt (by omega : 0 < n)⟩
  calc
    (∑ n ∈ Finset.Icc 1 N,
        (Λ * Λ) n * |nativePNTError (N / n)|) =
        ∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ n.divisors,
            (Λ d * Λ (n / d)) * |nativePNTError (N / n)| := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal (fun a b => Λ a * Λ b), Finset.sum_mul]
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x),
            (Λ d * Λ (n / d)) * |nativePNTError (N / n)| :=
      Finset.sum_comm' hmem
    _ = ∑ d ∈ Finset.Icc 1 N,
        ∑ m ∈ Finset.Icc 1 (N / d),
          Λ d * Λ m * |nativePNTError (N / (d * m))| := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hmap :
          (Finset.Icc 1 N).filter (fun x => d ∣ x) =
            (Finset.Icc 1 (N / d)).image (fun m => d * m) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hn1, hnN⟩, hdvd⟩
          refine ⟨n / d, ?_, Nat.mul_div_cancel' hdvd⟩
          have hq1 : 1 ≤ n / d :=
            (Nat.one_le_div_iff hdpos).2 (Nat.le_of_dvd (by omega) hdvd)
          exact ⟨hq1, Nat.div_le_div_right hnN⟩
        · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
          have hmulN' : m * d ≤ N := (Nat.le_div_iff_mul_le hdpos).1 hmN
          have hmulN : d * m ≤ N := by simpa [Nat.mul_comm] using hmulN'
          have hmpos : 0 < m := by omega
          exact ⟨⟨Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (Nat.mul_pos hdpos hmpos)), hmulN⟩, dvd_mul_right d m⟩
      rw [hmap, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro m _hm
        have hdiv : d * m / d = m := Nat.mul_div_cancel_left m hdpos
        rw [hdiv]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hdpos hab

private theorem nativeLambdaFloorMass_le_Nlog
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ)) ≤
      (N : ℝ) * Real.log N := by
  rw [nativeVonMangoldtSummatory]
  exact nativeLogFactorial_upper N hN

private theorem nativeLambdaErrorMass_le_floorMass
    (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) ≤
      (Real.log 4 + 3) *
        ∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ) := by
  calc
    (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) ≤
        ∑ d ∈ Finset.Icc 1 N,
          Λ d * ((Real.log 4 + 3) * ((N / d : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro d _hd
      exact mul_le_mul_of_nonneg_left
        (nativePNTError_abs_le_chebyshev (N / d))
        ArithmeticFunction.vonMangoldt_nonneg
    _ = (Real.log 4 + 3) *
        ∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      ring

private theorem nativeLambdaErrorMass_mul_log_le_lambdaTwo
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) * Real.log N ≤
      nativeLambdaTwoErrorMass N + 2000 * (N : ℝ) * Real.log N := by
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hC6 : Real.log 4 + 3 ≤ 6 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at h ⊢
    linarith
  have hC0 : 0 ≤ Real.log 4 + 3 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith
  have hsplit :
      (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) * Real.log N ≤
        nativeLambdaLogErrorMass N +
          nativeLambdaConvolutionErrorMass N +
          1006 * (N : ℝ) * Real.log N := by
    rw [Finset.sum_mul]
    have hpoint : ∀ d ∈ Finset.Icc 1 N,
        Λ d * |nativePNTError (N / d)| * Real.log N ≤
          Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
          ∑ m ∈ Finset.Icc 1 (N / d),
            Λ d * Λ m * |nativePNTError (N / (d * m))| +
          (1000 + (Real.log 4 + 3)) *
            (Λ d * ((N / d : ℕ) : ℝ)) := by
      intro d hd
      have hdI := Finset.mem_Icc.mp hd
      have hdpos : 0 < d := by omega
      have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).2 hdI.2
      have hlogd0 : 0 ≤ Real.log (d : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hdI.1)
      have hlogq0 : 0 ≤ Real.log ((N / d : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hq1)
      have hcoef0 : 0 ≤ Λ d * |nativePNTError (N / d)| :=
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (abs_nonneg _)
      have hlogsplit := nativeLog_le_log_divisor_add_floor_add_one N d hd
      have hfirst := nativePNTError_abs_log_le_weighted_crude (N / d)
      have hfirstMul :
          Λ d * (|nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ)) ≤
            Λ d *
              ((∑ m ∈ Finset.Icc 1 (N / d),
                Λ m * |nativePNTError ((N / d) / m)|) +
                1000 * ((N / d : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hfirst ArithmeticFunction.vonMangoldt_nonneg
      have hfirstMul' :
          Λ d * |nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ) ≤
            (∑ m ∈ Finset.Icc 1 (N / d),
              Λ d * Λ m * |nativePNTError (N / (d * m))|) +
              1000 * (Λ d * ((N / d : ℕ) : ℝ)) := by
        calc
          Λ d * |nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ) =
              Λ d * (|nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ)) := by ring
          _ ≤ Λ d *
              ((∑ m ∈ Finset.Icc 1 (N / d),
                Λ m * |nativePNTError ((N / d) / m)|) +
                1000 * ((N / d : ℕ) : ℝ)) := hfirstMul
          _ = (∑ m ∈ Finset.Icc 1 (N / d),
                Λ d * Λ m * |nativePNTError (N / (d * m))|) +
              1000 * (Λ d * ((N / d : ℕ) : ℝ)) := by
            rw [mul_add, Finset.mul_sum]
            apply congrArg₂ (· + ·)
            · apply Finset.sum_congr rfl
              intro m hm
              have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
              rw [Nat.div_div_eq_div_mul]
              ring
            · ring
      have herr := nativePNTError_abs_le_chebyshev (N / d)
      have hcorr :
          Λ d * |nativePNTError (N / d)| ≤
            (Real.log 4 + 3) * (Λ d * ((N / d : ℕ) : ℝ)) := by
        calc
          Λ d * |nativePNTError (N / d)| ≤
              Λ d * ((Real.log 4 + 3) * ((N / d : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left herr ArithmeticFunction.vonMangoldt_nonneg
          _ = (Real.log 4 + 3) * (Λ d * ((N / d : ℕ) : ℝ)) := by ring
      have hlogs :
          Λ d * |nativePNTError (N / d)| * Real.log N ≤
            Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
              Λ d * |nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ) +
              Λ d * |nativePNTError (N / d)| := by
        calc
          Λ d * |nativePNTError (N / d)| * Real.log N ≤
              (Λ d * |nativePNTError (N / d)|) *
                (Real.log (d : ℝ) + Real.log ((N / d : ℕ) : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hlogsplit hcoef0
          _ = Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
              Λ d * |nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ) +
              Λ d * |nativePNTError (N / d)| := by ring
      calc
        Λ d * |nativePNTError (N / d)| * Real.log N ≤
            Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
              Λ d * |nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ) +
              Λ d * |nativePNTError (N / d)| := hlogs
        _ ≤ Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
              ((∑ m ∈ Finset.Icc 1 (N / d),
                Λ d * Λ m * |nativePNTError (N / (d * m))|) +
                1000 * (Λ d * ((N / d : ℕ) : ℝ))) +
              (Real.log 4 + 3) * (Λ d * ((N / d : ℕ) : ℝ)) := by
          gcongr
        _ = Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
              ∑ m ∈ Finset.Icc 1 (N / d),
                Λ d * Λ m * |nativePNTError (N / (d * m))| +
              (1000 + (Real.log 4 + 3)) *
                (Λ d * ((N / d : ℕ) : ℝ)) := by ring
    calc
      (∑ d ∈ Finset.Icc 1 N,
        Λ d * |nativePNTError (N / d)| * Real.log N) ≤
          ∑ d ∈ Finset.Icc 1 N,
            (Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
              ∑ m ∈ Finset.Icc 1 (N / d),
                Λ d * Λ m * |nativePNTError (N / (d * m))| +
              (1000 + (Real.log 4 + 3)) *
                (Λ d * ((N / d : ℕ) : ℝ))) :=
        Finset.sum_le_sum hpoint
      _ = nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          (1000 + (Real.log 4 + 3)) *
            (∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        unfold nativeLambdaLogErrorMass
        rw [← nativeLambdaConvolutionErrorMass_eq_double]
        rw [← Finset.mul_sum]
      _ ≤ nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          (1000 + (Real.log 4 + 3)) * ((N : ℝ) * Real.log N) := by
        have hcoef : 0 ≤ 1000 + (Real.log 4 + 3) :=
          add_nonneg (by norm_num) hC0
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left (nativeLambdaFloorMass_le_Nlog N hN) hcoef)
          (nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N)
      _ ≤ nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          1006 * ((N : ℝ) * Real.log N) := by
        have hcoef : 1000 + (Real.log 4 + 3) ≤ (1006 : ℝ) := by
          linarith [hC6]
        have hNlog0 : 0 ≤ (N : ℝ) * Real.log N :=
          mul_nonneg (by positivity) hlog0
        exact add_le_add_left
          (mul_le_mul_of_nonneg_right hcoef hNlog0)
          (nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N)
      _ = nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          1006 * (N : ℝ) * Real.log N := by ring
  rw [nativeLambdaTwoErrorMass_eq_log_add_convolution]
  calc
    (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) * Real.log N ≤
        nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          1006 * (N : ℝ) * Real.log N := hsplit
    _ ≤ nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          2000 * (N : ℝ) * Real.log N := by
      have hNlog0 : 0 ≤ (N : ℝ) * Real.log N :=
        mul_nonneg (by positivity) hlog0
      have hcoef : 1006 * (N : ℝ) * Real.log N ≤
          2000 * (N : ℝ) * Real.log N := by
        calc
          1006 * (N : ℝ) * Real.log N = 1006 * ((N : ℝ) * Real.log N) := by ring
          _ ≤ 2000 * ((N : ℝ) * Real.log N) :=
            mul_le_mul_of_nonneg_right (by norm_num) hNlog0
          _ = 2000 * (N : ℝ) * Real.log N := by ring
      exact add_le_add_left hcoef
        (nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N)

/-- **Squared absolute Selberg recurrence in the native architecture.**

The one-log recurrence is self-composed on every reciprocal floor fibre.  Its
log-weighted and convolution-weighted pieces combine exactly into
`nativeLambdaTwo`, giving

`|R(N)| log^2 N <= sum Lambda_2(n) |R(floor(N/n))| + O(N log N)`.
-/
theorem nativePNTError_abs_log_sq_le_lambdaTwo
    (N : ℕ) (hN : 3 ≤ N) :
    |nativePNTError N| * (Real.log N) ^ 2 ≤
      nativeLambdaTwoErrorMass N + 3000 * (N : ℝ) * Real.log N := by
  have hfirst := nativePNTError_abs_log_le_weighted_crude N
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hmul := mul_le_mul_of_nonneg_right hfirst hlog0
  have hinner := nativeLambdaErrorMass_mul_log_le_lambdaTwo N (by omega : 1 ≤ N)
  calc
    |nativePNTError N| * (Real.log N) ^ 2 =
        (|nativePNTError N| * Real.log N) * Real.log N := by ring
    _ ≤ ((∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) +
          1000 * (N : ℝ)) * Real.log N := hmul
    _ = (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) * Real.log N +
          1000 * (N : ℝ) * Real.log N := by ring
    _ ≤ nativeLambdaTwoErrorMass N + 2000 * (N : ℝ) * Real.log N +
          1000 * (N : ℝ) * Real.log N := add_le_add_right hinner _
    _ = nativeLambdaTwoErrorMass N + 3000 * (N : ℝ) * Real.log N := by ring

end RHLean.Analysis
