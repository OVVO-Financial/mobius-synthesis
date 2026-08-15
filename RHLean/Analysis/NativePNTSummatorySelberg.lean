import Mathlib
import RHLean.Analysis.NativePNTLogSums
import RHLean.Analysis.NativePNTMobiusSecondMoment

/-!
# Summatory Selberg interface

The pointwise Dirichlet-ring identity

`Lambda_2 = D Lambda + Lambda * Lambda`

is not yet Selberg's summatory formula.  This module performs that missing
finite reindexing in the same reciprocal-fibre coordinates used throughout
`RH_Lean`.

No asymptotic prime-distribution theorem is used here.
-/

noncomputable section

open Finset Nat
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Summatory second von Mangoldt mass. -/
def nativeLambdaTwoSummatory (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, nativeLambdaTwo n

/-- Log-weighted von Mangoldt mass. -/
def nativeLambdaLogMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, Λ n * Real.log n

/-- Summatory Dirichlet self-convolution of von Mangoldt. -/
def nativeLambdaConvolutionMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (Λ * Λ) n

/-- Summing the pointwise Selberg kernel gives the exact decomposition into
its log-weighted and convolution pieces. -/
theorem nativeLambdaTwoSummatory_eq_log_add_convolution (N : ℕ) :
    nativeLambdaTwoSummatory N =
      nativeLambdaLogMass N + nativeLambdaConvolutionMass N := by
  unfold nativeLambdaTwoSummatory nativeLambdaLogMass nativeLambdaConvolutionMass
  rw [nativeLambdaTwo_eq_logWeight_vonMangoldt_add_convolution]
  simp only [ArithmeticFunction.add_apply, arithmeticLogWeight_apply]
  exact Finset.sum_add_distrib

/-- Exact reciprocal-fibre form of the von Mangoldt self-convolution:

`sum_{m <= N} (Lambda * Lambda)(m)
   = sum_{d <= N} Lambda(d) * psi(floor(N/d))`.

This is the finite cofactor-first/endpoint-first Fubini step needed by
Selberg's symmetry formula. -/
theorem nativeLambdaConvolutionMass_eq_reciprocalPsi (N : ℕ) :
    nativeLambdaConvolutionMass N =
      ∑ d ∈ Finset.Icc 1 N, Λ d * nativePsi (N / d) := by
  unfold nativeLambdaConvolutionMass nativePsi
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
    (∑ n ∈ Finset.Icc 1 N, (Λ * Λ) n) =
        ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, Λ d * Λ (n / d) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal (fun a b => Λ a * Λ b)]
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x),
            Λ d * Λ (n / d) :=
      Finset.sum_comm' hmem
    _ = ∑ d ∈ Finset.Icc 1 N,
          Λ d * ∑ m ∈ Finset.Icc 1 (N / d), Λ m := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hmap :
          (Finset.Icc 1 N).filter (fun x => d ∣ x) =
            (Finset.Icc 1 (N / d)).image (fun m => d * m) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hn1, hnN⟩, hdvd⟩
          refine ⟨n / d, ?_, Nat.mul_div_cancel' hdvd⟩
          have hq1 : 1 ≤ n / d := by
            exact (Nat.one_le_div_iff hdpos).2 (Nat.le_of_dvd (by omega) hdvd)
          have hqN : n / d ≤ N / d := Nat.div_le_div_right hnN
          exact ⟨hq1, hqN⟩
        · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
          have hmulN' : m * d ≤ N := (Nat.le_div_iff_mul_le hdpos).1 hmN
          have hmulN : d * m ≤ N := by simpa [Nat.mul_comm] using hmulN'
          have hmpos : 0 < m := by omega
          have hmulpos : 0 < d * m := Nat.mul_pos hdpos hmpos
          exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmulpos), hmulN⟩,
            dvd_mul_right d m⟩
      rw [hmap, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro m _hm
        have hdiv : d * m / d = m := Nat.mul_div_cancel_left m hdpos
        rw [hdiv]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hdpos hab
    _ = ∑ d ∈ Finset.Icc 1 N, Λ d * nativePsi (N / d) := by rfl

/-- Exact Möbius-first reciprocal-fibre form of the summatory second von
Mangoldt mass:

`sum_{n <= N} Lambda_2(n)
  = sum_{d <= N} mu(d) * sum_{m <= N/d} log^2(m)`.

This is the precise finite identity to which the sharp quadratic logarithmic
sum estimate is applied. -/
theorem nativeLambdaTwoSummatory_eq_moebius_logSquare (N : ℕ) :
    nativeLambdaTwoSummatory N =
      ∑ d ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) d * nativeLogSquareMass (N / d) := by
  unfold nativeLambdaTwoSummatory nativeLambdaTwo nativeLogSquareMass
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
        ((μ : ArithmeticFunction ℝ) * arithmeticLogSquare) n) =
        ∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ n.divisors,
            (μ : ArithmeticFunction ℝ) d *
              arithmeticLogSquare (n / d) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal
          (fun a b => (μ : ArithmeticFunction ℝ) a * arithmeticLogSquare b)]
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x),
            (μ : ArithmeticFunction ℝ) d *
              arithmeticLogSquare (n / d) :=
      Finset.sum_comm' hmem
    _ = ∑ d ∈ Finset.Icc 1 N,
          (μ : ArithmeticFunction ℝ) d *
            ∑ m ∈ Finset.Icc 1 (N / d), (Real.log (m : ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hmap :
          (Finset.Icc 1 N).filter (fun x => d ∣ x) =
            (Finset.Icc 1 (N / d)).image (fun m => d * m) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hn1, hnN⟩, hdvd⟩
          refine ⟨n / d, ?_, Nat.mul_div_cancel' hdvd⟩
          have hq1 : 1 ≤ n / d := by
            exact (Nat.one_le_div_iff hdpos).2 (Nat.le_of_dvd (by omega) hdvd)
          have hqN : n / d ≤ N / d := Nat.div_le_div_right hnN
          exact ⟨hq1, hqN⟩
        · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
          have hmulN' : m * d ≤ N := (Nat.le_div_iff_mul_le hdpos).1 hmN
          have hmulN : d * m ≤ N := by simpa [Nat.mul_comm] using hmulN'
          have hmpos : 0 < m := by omega
          have hmulpos : 0 < d * m := Nat.mul_pos hdpos hmpos
          exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmulpos), hmulN⟩,
            dvd_mul_right d m⟩
      rw [hmap, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro m _hm
        have hdiv : d * m / d = m := Nat.mul_div_cancel_left m hdpos
        rw [hdiv]
        rfl
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hdpos hab
    _ = ∑ d ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) d *
          nativeLogSquareMass (N / d) := by rfl

/-- One-step increment of `nativePsi`, placed here so the summatory Selberg
modules do not depend on the later error-mass module. -/
theorem nativePsi_succ_eq (N : ℕ) :
    nativePsi (N + 1) = nativePsi N + Λ (N + 1) := by
  unfold nativePsi
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- Finite Abel summation for the log-weighted von Mangoldt mass. -/
theorem nativeLambdaLogMass_abel (N : ℕ) :
    nativeLambdaLogMass N =
      nativePsi N * Real.log N -
        ∑ n ∈ Finset.Ico 1 N,
          nativePsi n *
            (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) := by
  induction N with
  | zero =>
      simp [nativeLambdaLogMass, nativePsi]
  | succ N ih =>
      by_cases hN0 : N = 0
      · subst N
        simp [nativeLambdaLogMass, nativePsi]
      · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        unfold nativeLambdaLogMass at ih ⊢
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        rw [ih, nativePsi_succ_eq]
        rw [Finset.sum_Ico_succ_top hN1]
        push_cast
        ring

/-- Elementary logarithmic increment bound used in the Abel correction. -/
theorem nativeLog_succ_sub_log_le_inv
    (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsuccpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hratio :
      Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) =
        Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
    rw [Real.log_div (ne_of_gt hsuccpos) (ne_of_gt hnpos)]
  have h := Real.log_le_sub_one_of_pos
    (show 0 < (((n + 1 : ℕ) : ℝ) / (n : ℝ)) by positivity)
  rw [hratio] at h
  have hsub : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) - 1 = 1 / (n : ℝ) := by
    push_cast
    field_simp [ne_of_gt hnpos]
    ring
  rw [hsub] at h
  exact h

/-- The Abel correction is nonnegative. -/
theorem nativeLambdaLogAbelCorrection_nonneg (N : ℕ) :
    0 ≤ ∑ n ∈ Finset.Ico 1 N,
      nativePsi n *
        (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) := by
  apply Finset.sum_nonneg
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
  have hlog : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hn1
    · exact_mod_cast (show n ≤ n + 1 by omega)
  exact mul_nonneg (nativePsi_nonneg n) (sub_nonneg.mpr hlog)

/-- The Abel correction is at most the elementary Chebyshev constant times
`N`.  This is the precise `O(N)` bridge from the pointwise Selberg kernel to
its summatory `psi log` form. -/
theorem nativeLambdaLogAbelCorrection_le (N : ℕ) :
    (∑ n ∈ Finset.Ico 1 N,
      nativePsi n *
        (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) ≤
      (Real.log 4 + 2) * (N : ℝ) := by
  have hpoint : ∀ n ∈ Finset.Ico 1 N,
      nativePsi n *
        (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) ≤ Real.log 4 + 2 := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
    have hpsi := nativePsi_le_const_mul n
    have hinc := nativeLog_succ_sub_log_le_inv n hn1
    have hinc0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
      apply sub_nonneg.mpr
      apply Real.log_le_log
      · exact_mod_cast hn1
      · exact_mod_cast (show n ≤ n + 1 by omega)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hconst0 : 0 ≤ Real.log 4 + 2 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      linarith
    calc
      nativePsi n *
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) ≤
          ((Real.log 4 + 2) * (n : ℝ)) *
            (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hpsi hinc0
      _ ≤ ((Real.log 4 + 2) * (n : ℝ)) * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hinc (mul_nonneg hconst0 (by positivity))
      _ = Real.log 4 + 2 := by
        field_simp [ne_of_gt hnpos]
  calc
    (∑ n ∈ Finset.Ico 1 N,
        nativePsi n *
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) ≤
        ∑ _n ∈ Finset.Ico 1 N, (Real.log 4 + 2) :=
      Finset.sum_le_sum hpoint
    _ = ((Finset.Ico 1 N).card : ℝ) * (Real.log 4 + 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (Real.log 4 + 2) := by
      have hcard : (Finset.Ico 1 N).card ≤ N := by
        rw [Nat.card_Ico]
        omega
      have hcast : ((Finset.Ico 1 N).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard
      have hconst0 : 0 ≤ Real.log 4 + 2 := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
        linarith
      exact mul_le_mul_of_nonneg_right hcast hconst0
    _ = (Real.log 4 + 2) * (N : ℝ) := by ring

/-- Explicit absolute `O(N)` form of the Abel bridge. -/
theorem nativeLambdaLogMass_sub_psiLog_abs_le (N : ℕ) :
    |nativeLambdaLogMass N - nativePsi N * Real.log N| ≤
      (Real.log 4 + 2) * (N : ℝ) := by
  rw [nativeLambdaLogMass_abel]
  have h0 := nativeLambdaLogAbelCorrection_nonneg N
  have h1 := nativeLambdaLogAbelCorrection_le N
  rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg h0]
  exact h1

/-- The exact Selberg summatory pair before its main-term estimate. -/
def nativeSelbergPair (N : ℕ) : ℝ :=
  nativePsi N * Real.log N +
    ∑ d ∈ Finset.Icc 1 N, Λ d * nativePsi (N / d)

/-- `nativeSelbergPair` differs from the summatory `Lambda_2` mass by only the
explicit Abel correction. -/
theorem nativeSelbergPair_sub_lambdaTwoSummatory_abs_le (N : ℕ) :
    |nativeSelbergPair N - nativeLambdaTwoSummatory N| ≤
      (Real.log 4 + 2) * (N : ℝ) := by
  rw [nativeLambdaTwoSummatory_eq_log_add_convolution,
    nativeLambdaConvolutionMass_eq_reciprocalPsi]
  unfold nativeSelbergPair
  have h := nativeLambdaLogMass_sub_psiLog_abs_le N
  simpa [abs_sub_comm, add_sub_add_right_eq_sub] using h

/-! ## Explicit main term -/

private theorem nativeFloorQuotient_cast_eq_sub_fract
    (N d : ℕ) (_hd : 1 ≤ d) :
    ((N / d : ℕ) : ℝ) =
      (N : ℝ) / (d : ℝ) - Int.fract ((N : ℝ) / (d : ℝ)) := by
  have hfloorcast :
      (⌊(N : ℝ) / (d : ℝ)⌋ : ℝ) = ((N / d : ℕ) : ℝ) := by
    have hz :
        ⌊(N : ℝ) / (d : ℝ)⌋ = ((N / d : ℕ) : ℤ) := by
      rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]
    rw [hz]
    norm_cast
  rw [← Int.self_sub_floor, hfloorcast]
  ring

private theorem nativeLogSquare_le_sixteen_sqrt
    {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs1 : 1 ≤ Real.sqrt x := (Real.one_le_sqrt).2 hx
  have hss0 : 0 ≤ Real.sqrt (Real.sqrt x) := Real.sqrt_nonneg _
  have hss1 : 1 ≤ Real.sqrt (Real.sqrt x) := (Real.one_le_sqrt).2 hs1
  have hsspos : 0 < Real.sqrt (Real.sqrt x) := lt_of_lt_of_le (by norm_num) hss1
  have hlogle := Real.log_le_sub_one_of_pos hsspos
  have hlogle' :
      Real.log (Real.sqrt (Real.sqrt x)) ≤ Real.sqrt (Real.sqrt x) := by
    linarith
  have hlogss :
      Real.log (Real.sqrt (Real.sqrt x)) = Real.log x / 4 := by
    rw [Real.log_sqrt hs0, Real.log_sqrt hx0]
    ring
  rw [hlogss] at hlogle'
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hbound : Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
    nlinarith
  have hsq :
      (Real.log x) ^ 2 ≤ 16 * (Real.sqrt (Real.sqrt x)) ^ 2 := by
    nlinarith
  rw [Real.sq_sqrt hs0] at hsq
  exact hsq

private theorem nativeReciprocalSqrtMass_le :
    ∀ N : ℕ,
      (∑ d ∈ Finset.Icc 1 N, 1 / Real.sqrt (d : ℝ)) ≤
        2 * Real.sqrt (N : ℝ) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      by_cases hN0 : N = 0
      · subst N
        norm_num
      · have hNposNat : 0 < N := Nat.pos_of_ne_zero hN0
        have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
        have hSpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
        have hsNpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
        have hsSpos : 0 < Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hSpos
        have hsNle : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) := by
          apply Real.sqrt_le_sqrt
          exact_mod_cast (show N ≤ N + 1 by omega)
        have hdiff0 :
            0 ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ) :=
          sub_nonneg.mpr hsNle
        have hsNSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
          Real.sq_sqrt hNpos.le
        have hsSSq :
            (Real.sqrt ((N + 1 : ℕ) : ℝ)) ^ 2 = ((N + 1 : ℕ) : ℝ) :=
          Real.sq_sqrt hSpos.le
        have hident :
            (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
                (Real.sqrt ((N + 1 : ℕ) : ℝ) + Real.sqrt (N : ℝ)) = 1 := by
          calc
            (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
                (Real.sqrt ((N + 1 : ℕ) : ℝ) + Real.sqrt (N : ℝ)) =
                (Real.sqrt ((N + 1 : ℕ) : ℝ)) ^ 2 -
                  (Real.sqrt (N : ℝ)) ^ 2 := by ring
            _ = ((N + 1 : ℕ) : ℝ) - (N : ℝ) := by rw [hsSSq, hsNSq]
            _ = 1 := by push_cast; ring
        have hsumle :
            Real.sqrt ((N + 1 : ℕ) : ℝ) + Real.sqrt (N : ℝ) ≤
              2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
          linarith
        have honele :
            1 ≤ 2 *
                (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
                  Real.sqrt ((N + 1 : ℕ) : ℝ) := by
          calc
            1 =
                (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
                  (Real.sqrt ((N + 1 : ℕ) : ℝ) + Real.sqrt (N : ℝ)) :=
              hident.symm
            _ ≤
                (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
                  (2 * Real.sqrt ((N + 1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hsumle hdiff0
            _ = 2 *
                (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
                  Real.sqrt ((N + 1 : ℕ) : ℝ) := by ring
        have hstep :
            1 / Real.sqrt ((N + 1 : ℕ) : ℝ) ≤
              2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) := by
          apply (div_le_iff₀ hsSpos).2
          simpa [mul_assoc] using honele
        calc
          (∑ d ∈ Finset.Icc 1 N, 1 / Real.sqrt (d : ℝ)) +
              1 / Real.sqrt ((N + 1 : ℕ) : ℝ) ≤
              2 * Real.sqrt (N : ℝ) +
                1 / Real.sqrt ((N + 1 : ℕ) : ℝ) :=
            add_le_add_right ih _
          _ ≤ 2 * Real.sqrt (N : ℝ) +
                2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) :=
            add_le_add_left hstep _
          _ = 2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by ring

private theorem nativeFloorLogSquareMass_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
      (Real.log ((N / d : ℕ) : ℝ)) ^ 2) ≤ 32 * (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hpoint : ∀ d ∈ Finset.Icc 1 N,
        (Real.log ((N / d : ℕ) : ℝ)) ^ 2 ≤
          (16 * Real.sqrt (N : ℝ)) * (1 / Real.sqrt (d : ℝ)) := by
      intro d hd
      have hdI := Finset.mem_Icc.mp hd
      have hdpos : 0 < d := by omega
      have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).2 hdI.2
      have hqReal : (1 : ℝ) ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast hq1
      have hlog := nativeLogSquare_le_sixteen_sqrt hqReal
      have hcast : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
      have hsqrt := Real.sqrt_le_sqrt hcast
      have hsqrtDiv :
          Real.sqrt ((N : ℝ) / (d : ℝ)) =
            Real.sqrt (N : ℝ) / Real.sqrt (d : ℝ) := by
        exact Real.sqrt_div (show 0 ≤ (N : ℝ) by positivity) (d : ℝ)
      calc
        (Real.log ((N / d : ℕ) : ℝ)) ^ 2 ≤
            16 * Real.sqrt ((N / d : ℕ) : ℝ) := hlog
        _ ≤ 16 * Real.sqrt ((N : ℝ) / (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrt (by norm_num)
        _ = (16 * Real.sqrt (N : ℝ)) * (1 / Real.sqrt (d : ℝ)) := by
          rw [hsqrtDiv]
          ring
    calc
      (∑ d ∈ Finset.Icc 1 N,
          (Real.log ((N / d : ℕ) : ℝ)) ^ 2) ≤
          ∑ d ∈ Finset.Icc 1 N,
            (16 * Real.sqrt (N : ℝ)) * (1 / Real.sqrt (d : ℝ)) :=
        Finset.sum_le_sum hpoint
      _ = (16 * Real.sqrt (N : ℝ)) *
          ∑ d ∈ Finset.Icc 1 N, 1 / Real.sqrt (d : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ (16 * Real.sqrt (N : ℝ)) * (2 * Real.sqrt (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (nativeReciprocalSqrtMass_le N) (by positivity)
      _ = 32 * (N : ℝ) := by
        calc
          (16 * Real.sqrt (N : ℝ)) * (2 * Real.sqrt (N : ℝ)) =
              32 * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by ring
          _ = 32 * (N : ℝ) := by
            rw [Real.mul_self_sqrt (show 0 ≤ (N : ℝ) by positivity)]

private theorem nativeFloorLogMass_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, Real.log ((N / d : ℕ) : ℝ)) ≤ 33 * (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hpoint : ∀ d ∈ Finset.Icc 1 N,
        Real.log ((N / d : ℕ) : ℝ) ≤
          (Real.log ((N / d : ℕ) : ℝ)) ^ 2 + 1 := by
      intro d hd
      have hdI := Finset.mem_Icc.mp hd
      have hdpos : 0 < d := by omega
      have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).2 hdI.2
      have hlog0 : 0 ≤ Real.log ((N / d : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hq1)
      nlinarith [sq_nonneg (Real.log ((N / d : ℕ) : ℝ) - 1)]
    calc
      (∑ d ∈ Finset.Icc 1 N, Real.log ((N / d : ℕ) : ℝ)) ≤
          ∑ d ∈ Finset.Icc 1 N,
            ((Real.log ((N / d : ℕ) : ℝ)) ^ 2 + 1) :=
        Finset.sum_le_sum hpoint
      _ = (∑ d ∈ Finset.Icc 1 N,
            (Real.log ((N / d : ℕ) : ℝ)) ^ 2) +
          ((Finset.Icc 1 N).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = (∑ d ∈ Finset.Icc 1 N,
            (Real.log ((N / d : ℕ) : ℝ)) ^ 2) + (N : ℝ) := by
        rw [Nat.card_Icc]
        norm_num
      _ ≤ 32 * (N : ℝ) + (N : ℝ) :=
        add_le_add_right (nativeFloorLogSquareMass_le N) _
      _ = 33 * (N : ℝ) := by ring

private def nativeMobiusFloorLogSquareCorrection (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) *
      Int.fract ((N : ℝ) / (d : ℝ)) *
        (Real.log ((N / d : ℕ) : ℝ)) ^ 2

private def nativeMobiusFloorLogCorrection (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) *
      Int.fract ((N : ℝ) / (d : ℝ)) *
        Real.log ((N / d : ℕ) : ℝ)

private theorem nativeAbsMobiusReal_le_one (d : ℕ) :
    |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
  have h := ArithmeticFunction.abs_moebius_le_one (n := d)
  calc
    |(ArithmeticFunction.moebius d : ℝ)| =
        ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) := by rw [Int.cast_abs]
    _ ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h
    _ = 1 := by norm_num

private theorem nativeMobiusFloorLogSquareCorrection_abs_le (N : ℕ) :
    |nativeMobiusFloorLogSquareCorrection N| ≤ 32 * (N : ℝ) := by
  unfold nativeMobiusFloorLogSquareCorrection
  calc
    |∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) *
          Int.fract ((N : ℝ) / (d : ℝ)) *
            (Real.log ((N / d : ℕ) : ℝ)) ^ 2| ≤
        ∑ d ∈ Finset.Icc 1 N,
          |(ArithmeticFunction.moebius d : ℝ) *
            Int.fract ((N : ℝ) / (d : ℝ)) *
              (Real.log ((N / d : ℕ) : ℝ)) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
          (Real.log ((N / d : ℕ) : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro d _hd
      have hmu := nativeAbsMobiusReal_le_one d
      have hfr0 := Int.fract_nonneg ((N : ℝ) / (d : ℝ))
      have hfr1 : Int.fract ((N : ℝ) / (d : ℝ)) ≤ 1 :=
        (Int.fract_lt_one _).le
      have hmf :
          |(ArithmeticFunction.moebius d : ℝ)| *
              Int.fract ((N : ℝ) / (d : ℝ)) ≤ 1 := by
        calc
          |(ArithmeticFunction.moebius d : ℝ)| *
              Int.fract ((N : ℝ) / (d : ℝ)) ≤
              1 * Int.fract ((N : ℝ) / (d : ℝ)) :=
            mul_le_mul_of_nonneg_right hmu hfr0
          _ ≤ 1 := by simpa using hfr1
      have hlog2 : 0 ≤ (Real.log ((N / d : ℕ) : ℝ)) ^ 2 :=
        sq_nonneg (Real.log ((N / d : ℕ) : ℝ))
      rw [abs_mul, abs_mul, abs_of_nonneg hfr0, abs_of_nonneg hlog2]
      simpa using mul_le_mul_of_nonneg_right hmf hlog2
    _ ≤ 32 * (N : ℝ) := nativeFloorLogSquareMass_le N

private theorem nativeMobiusFloorLogCorrection_abs_le (N : ℕ) :
    |nativeMobiusFloorLogCorrection N| ≤ 33 * (N : ℝ) := by
  unfold nativeMobiusFloorLogCorrection
  calc
    |∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) *
          Int.fract ((N : ℝ) / (d : ℝ)) *
            Real.log ((N / d : ℕ) : ℝ)| ≤
        ∑ d ∈ Finset.Icc 1 N,
          |(ArithmeticFunction.moebius d : ℝ) *
            Int.fract ((N : ℝ) / (d : ℝ)) *
              Real.log ((N / d : ℕ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
          Real.log ((N / d : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdI := Finset.mem_Icc.mp hd
      have hdpos : 0 < d := by omega
      have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).2 hdI.2
      have hlog0 : 0 ≤ Real.log ((N / d : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hq1)
      have hmu := nativeAbsMobiusReal_le_one d
      have hfr0 := Int.fract_nonneg ((N : ℝ) / (d : ℝ))
      have hfr1 : Int.fract ((N : ℝ) / (d : ℝ)) ≤ 1 :=
        (Int.fract_lt_one _).le
      have hmf :
          |(ArithmeticFunction.moebius d : ℝ)| *
              Int.fract ((N : ℝ) / (d : ℝ)) ≤ 1 := by
        calc
          |(ArithmeticFunction.moebius d : ℝ)| *
              Int.fract ((N : ℝ) / (d : ℝ)) ≤
              1 * Int.fract ((N : ℝ) / (d : ℝ)) :=
            mul_le_mul_of_nonneg_right hmu hfr0
          _ ≤ 1 := by simpa using hfr1
      rw [abs_mul, abs_mul, abs_of_nonneg hfr0, abs_of_nonneg hlog0]
      simpa using mul_le_mul_of_nonneg_right hmf hlog0
    _ ≤ 33 * (N : ℝ) := nativeFloorLogMass_le N

private def nativeMobiusFloorLogSquareMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ) *
      (Real.log ((N / d : ℕ) : ℝ)) ^ 2

private def nativeMobiusFloorLogMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ) *
      Real.log ((N / d : ℕ) : ℝ)

private def nativeMobiusFloorMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ)

private theorem nativeMobiusFloorLogSquareMass_eq (N : ℕ) :
    nativeMobiusFloorLogSquareMass N =
      (N : ℝ) * nativeMobiusLogMomentTwo N -
        nativeMobiusFloorLogSquareCorrection N := by
  unfold nativeMobiusFloorLogSquareMass nativeMobiusLogMomentTwo
    nativeMobiusFloorLogSquareCorrection
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  rw [nativeFloorQuotient_cast_eq_sub_fract N d hd1]
  ring

private theorem nativeMobiusFloorLogMass_eq (N : ℕ) :
    nativeMobiusFloorLogMass N =
      (N : ℝ) * nativeMobiusLogMomentOne N -
        nativeMobiusFloorLogCorrection N := by
  unfold nativeMobiusFloorLogMass nativeMobiusLogMomentOne
    nativeMobiusFloorLogCorrection
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  rw [nativeFloorQuotient_cast_eq_sub_fract N d hd1]
  ring

private theorem nativeMobiusFloorMass_eq_one
    (N : ℕ) (hN : 1 ≤ N) : nativeMobiusFloorMass N = 1 := by
  unfold nativeMobiusFloorMass
  have hz := nativeSumMoebiusMulFloor N hN
  have hcast :
      (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ)) =
        (((∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℤ) * ((N / d : ℕ) : ℤ)) : ℤ) : ℝ) := by
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro d _hd
    rw [Int.cast_mul, Int.cast_natCast]
  rw [hcast, hz]
  norm_num

private def nativeMobiusLogSquareMainMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) * nativeLogSquareMain (N / d)

private theorem nativeMobiusLogSquareMainMass_eq_floorMasses (N : ℕ) :
    nativeMobiusLogSquareMainMass N =
      nativeMobiusFloorLogSquareMass N -
        2 * nativeMobiusFloorLogMass N + 2 * nativeMobiusFloorMass N := by
  unfold nativeMobiusLogSquareMainMass nativeMobiusFloorLogSquareMass
    nativeMobiusFloorLogMass nativeMobiusFloorMass nativeLogSquareMain
  calc
    (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) *
          ((N / d : ℕ) * (Real.log ((N / d : ℕ) : ℝ)) ^ 2 -
            2 * (N / d : ℕ) * Real.log ((N / d : ℕ) : ℝ) + 2 * (N / d : ℕ))) =
        ∑ d ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ) *
              (Real.log ((N / d : ℕ) : ℝ)) ^ 2 -
            2 * ((ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ) *
              Real.log ((N / d : ℕ) : ℝ)) +
            2 * ((ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro d _hd
      ring
    _ =
        (∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ) *
            (Real.log ((N / d : ℕ) : ℝ)) ^ 2) -
          2 * (∑ d ∈ Finset.Icc 1 N,
            (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ) *
              Real.log ((N / d : ℕ) : ℝ)) +
          2 * (∑ d ∈ Finset.Icc 1 N,
            (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]

private def nativeLambdaTwoLogSquareRemainderMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) *
      (nativeLogSquareMass (N / d) - nativeLogSquareMain (N / d))

private theorem nativeLambdaTwoLogSquareRemainderMass_abs_le
    (N : ℕ) :
    |nativeLambdaTwoLogSquareRemainderMass N| ≤ 34 * (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [nativeLambdaTwoLogSquareRemainderMass]
  · unfold nativeLambdaTwoLogSquareRemainderMass
    calc
      |∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) *
            (nativeLogSquareMass (N / d) - nativeLogSquareMain (N / d))| ≤
          ∑ d ∈ Finset.Icc 1 N,
            |(ArithmeticFunction.moebius d : ℝ) *
              (nativeLogSquareMass (N / d) - nativeLogSquareMain (N / d))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 N,
            ((Real.log ((N / d : ℕ) : ℝ)) ^ 2 + 2) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdI := Finset.mem_Icc.mp hd
        have hdpos : 0 < d := by omega
        have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).2 hdI.2
        have herr := nativeLogSquareMass_sub_main_abs_le (N / d) hq1
        have hmu := nativeAbsMobiusReal_le_one d
        rw [abs_mul]
        simpa using
          (mul_le_mul hmu herr (abs_nonneg _)
            (show (0 : ℝ) ≤ 1 by norm_num))
      _ = (∑ d ∈ Finset.Icc 1 N,
            (Real.log ((N / d : ℕ) : ℝ)) ^ 2) +
          2 * ((Finset.Icc 1 N).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
      _ = (∑ d ∈ Finset.Icc 1 N,
            (Real.log ((N / d : ℕ) : ℝ)) ^ 2) + 2 * (N : ℝ) := by
        rw [Nat.card_Icc]
        norm_num
      _ ≤ 32 * (N : ℝ) + 2 * (N : ℝ) :=
        add_le_add_right (nativeFloorLogSquareMass_le N) _
      _ = 34 * (N : ℝ) := by ring

private theorem nativeLambdaTwoSummatory_eq_main_add_remainder (N : ℕ) :
    nativeLambdaTwoSummatory N =
      nativeMobiusLogSquareMainMass N + nativeLambdaTwoLogSquareRemainderMass N := by
  rw [nativeLambdaTwoSummatory_eq_moebius_logSquare]
  unfold nativeMobiusLogSquareMainMass nativeLambdaTwoLogSquareRemainderMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  ring_nf
  exact mul_comm _ _

private theorem nativeMobiusLogSquareMainMass_eq
    (N : ℕ) (hN : 1 ≤ N) :
    nativeMobiusLogSquareMainMass N =
      (N : ℝ) * nativeMobiusLogMomentTwo N -
        2 * (N : ℝ) * nativeMobiusLogMomentOne N + 2 -
        nativeMobiusFloorLogSquareCorrection N +
        2 * nativeMobiusFloorLogCorrection N := by
  rw [nativeMobiusLogSquareMainMass_eq_floorMasses,
    nativeMobiusFloorLogSquareMass_eq, nativeMobiusFloorLogMass_eq,
    nativeMobiusFloorMass_eq_one N hN]
  ring

private theorem nativeMobiusLogSquareMainMass_sub_main_abs_le
    (N : ℕ) (hN : 3 ≤ N) :
    |nativeMobiusLogSquareMainMass N -
        2 * (N : ℝ) * Real.log N| ≤
      (2 * (Real.log 4 + 2) + 138) * (N : ℝ) := by
  rw [nativeMobiusLogSquareMainMass_eq N (by omega)]
  have hM2 := nativeMobiusLogMomentTwo_sub_two_log_abs_le N hN
  have hM1 := nativeMobiusLogMomentOne_abs_le_four N (by omega)
  have hC2 := nativeMobiusFloorLogSquareCorrection_abs_le N
  have hC1 := nativeMobiusFloorLogCorrection_abs_le N
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hrearrange :
      (N : ℝ) * nativeMobiusLogMomentTwo N -
          2 * (N : ℝ) * nativeMobiusLogMomentOne N + 2 -
          nativeMobiusFloorLogSquareCorrection N +
          2 * nativeMobiusFloorLogCorrection N -
          2 * (N : ℝ) * Real.log N =
        (N : ℝ) * (nativeMobiusLogMomentTwo N - 2 * Real.log N) +
          (-2 * (N : ℝ) * nativeMobiusLogMomentOne N) +
          (-nativeMobiusFloorLogSquareCorrection N) +
          (2 * nativeMobiusFloorLogCorrection N) + 2 := by
    ring
  rw [hrearrange]
  have hA :
      |(N : ℝ) * (nativeMobiusLogMomentTwo N - 2 * Real.log N)| ≤
        (N : ℝ) * (2 * (Real.log 4 + 2) + 30) := by
    rw [abs_mul, abs_of_nonneg hN0]
    exact mul_le_mul_of_nonneg_left hM2 hN0
  have hB :
      |-2 * (N : ℝ) * nativeMobiusLogMomentOne N| ≤ 8 * (N : ℝ) := by
    rw [abs_mul, abs_mul]
    norm_num
    nlinarith [abs_nonneg (nativeMobiusLogMomentOne N)]
  have hD :
      |2 * nativeMobiusFloorLogCorrection N| ≤ 66 * (N : ℝ) := by
    rw [abs_mul]
    norm_num
    nlinarith [abs_nonneg (nativeMobiusFloorLogCorrection N)]
  have htri :
      |(N : ℝ) * (nativeMobiusLogMomentTwo N - 2 * Real.log N) +
          (-2 * (N : ℝ) * nativeMobiusLogMomentOne N) +
          (-nativeMobiusFloorLogSquareCorrection N) +
          (2 * nativeMobiusFloorLogCorrection N) + 2| ≤
        |(N : ℝ) * (nativeMobiusLogMomentTwo N - 2 * Real.log N)| +
          |-2 * (N : ℝ) * nativeMobiusLogMomentOne N| +
          |nativeMobiusFloorLogSquareCorrection N| +
          |2 * nativeMobiusFloorLogCorrection N| + 2 := by
    calc
      |_ + 2| ≤
          |(N : ℝ) * (nativeMobiusLogMomentTwo N - 2 * Real.log N) +
            (-2 * (N : ℝ) * nativeMobiusLogMomentOne N) +
            (-nativeMobiusFloorLogSquareCorrection N) +
            (2 * nativeMobiusFloorLogCorrection N)| + |(2 : ℝ)| :=
        abs_add_le _ _
      _ ≤
          (|(N : ℝ) * (nativeMobiusLogMomentTwo N - 2 * Real.log N) +
              (-2 * (N : ℝ) * nativeMobiusLogMomentOne N) +
              (-nativeMobiusFloorLogSquareCorrection N)| +
            |2 * nativeMobiusFloorLogCorrection N|) + |(2 : ℝ)| := by
        gcongr
        exact abs_add_le _ _
      _ ≤
          ((|(N : ℝ) * (nativeMobiusLogMomentTwo N - 2 * Real.log N) +
              (-2 * (N : ℝ) * nativeMobiusLogMomentOne N)| +
            |-nativeMobiusFloorLogSquareCorrection N|) +
            |2 * nativeMobiusFloorLogCorrection N|) + |(2 : ℝ)| := by
        gcongr
        exact abs_add_le _ _
      _ ≤
          (((|(N : ℝ) * (nativeMobiusLogMomentTwo N - 2 * Real.log N)| +
              |-2 * (N : ℝ) * nativeMobiusLogMomentOne N|) +
            |-nativeMobiusFloorLogSquareCorrection N|) +
            |2 * nativeMobiusFloorLogCorrection N|) + |(2 : ℝ)| := by
        gcongr
        exact abs_add_le _ _
      _ =
          |(N : ℝ) * (nativeMobiusLogMomentTwo N - 2 * Real.log N)| +
            |-2 * (N : ℝ) * nativeMobiusLogMomentOne N| +
            |nativeMobiusFloorLogSquareCorrection N| +
            |2 * nativeMobiusFloorLogCorrection N| + 2 := by
        rw [abs_neg]
        norm_num
  calc
    |(N : ℝ) * (nativeMobiusLogMomentTwo N - 2 * Real.log N) +
        (-2 * (N : ℝ) * nativeMobiusLogMomentOne N) +
        (-nativeMobiusFloorLogSquareCorrection N) +
        (2 * nativeMobiusFloorLogCorrection N) + 2| ≤
        |(N : ℝ) * (nativeMobiusLogMomentTwo N - 2 * Real.log N)| +
          |-2 * (N : ℝ) * nativeMobiusLogMomentOne N| +
          |nativeMobiusFloorLogSquareCorrection N| +
          |2 * nativeMobiusFloorLogCorrection N| + 2 := htri
    _ ≤
        (N : ℝ) * (2 * (Real.log 4 + 2) + 30) +
          8 * (N : ℝ) + 32 * (N : ℝ) + 66 * (N : ℝ) + 2 := by
      gcongr
    _ ≤ (2 * (Real.log 4 + 2) + 138) * (N : ℝ) := by
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
      nlinarith

/-- **Summatory Selberg symmetry with an explicit linear error.**

This is the missing finite main-term theorem from the native PNT route:

`sum_{n <= N} Lambda_2(n) = 2 N log N + O(N)`.

The proof uses only the exact Möbius reciprocal-fibre reindex, the first and
second logarithmic Möbius moments, and elementary floor-fibre estimates. -/
theorem nativeLambdaTwoSummatory_sub_two_mul_log_abs_le
    (N : ℕ) (hN : 3 ≤ N) :
    |nativeLambdaTwoSummatory N - 2 * (N : ℝ) * Real.log N| ≤
      (2 * (Real.log 4 + 2) + 172) * (N : ℝ) := by
  rw [nativeLambdaTwoSummatory_eq_main_add_remainder]
  have hmain := nativeMobiusLogSquareMainMass_sub_main_abs_le N hN
  have hrem := nativeLambdaTwoLogSquareRemainderMass_abs_le N
  have hrearrange :
      nativeMobiusLogSquareMainMass N + nativeLambdaTwoLogSquareRemainderMass N -
          2 * (N : ℝ) * Real.log N =
        (nativeMobiusLogSquareMainMass N - 2 * (N : ℝ) * Real.log N) +
          nativeLambdaTwoLogSquareRemainderMass N := by ring
  rw [hrearrange]
  calc
    |(nativeMobiusLogSquareMainMass N - 2 * (N : ℝ) * Real.log N) +
        nativeLambdaTwoLogSquareRemainderMass N| ≤
      |nativeMobiusLogSquareMainMass N - 2 * (N : ℝ) * Real.log N| +
        |nativeLambdaTwoLogSquareRemainderMass N| := abs_add_le _ _
    _ ≤ (2 * (Real.log 4 + 2) + 138) * (N : ℝ) + 34 * (N : ℝ) :=
      add_le_add hmain hrem
    _ = (2 * (Real.log 4 + 2) + 172) * (N : ℝ) := by ring

/-- Selberg's symmetry pair in its conventional `psi log + Lambda * psi`
form, again with an explicit linear error. -/
theorem nativeSelbergPair_sub_two_mul_log_abs_le
    (N : ℕ) (hN : 3 ≤ N) :
    |nativeSelbergPair N - 2 * (N : ℝ) * Real.log N| ≤
      (3 * (Real.log 4 + 2) + 172) * (N : ℝ) := by
  have hpair := nativeSelbergPair_sub_lambdaTwoSummatory_abs_le N
  have hmain := nativeLambdaTwoSummatory_sub_two_mul_log_abs_le N hN
  have hrearrange :
      nativeSelbergPair N - 2 * (N : ℝ) * Real.log N =
        (nativeSelbergPair N - nativeLambdaTwoSummatory N) +
          (nativeLambdaTwoSummatory N - 2 * (N : ℝ) * Real.log N) := by ring
  rw [hrearrange]
  calc
    |(nativeSelbergPair N - nativeLambdaTwoSummatory N) +
        (nativeLambdaTwoSummatory N - 2 * (N : ℝ) * Real.log N)| ≤
      |nativeSelbergPair N - nativeLambdaTwoSummatory N| +
        |nativeLambdaTwoSummatory N - 2 * (N : ℝ) * Real.log N| := abs_add_le _ _
    _ ≤ (Real.log 4 + 2) * (N : ℝ) +
        (2 * (Real.log 4 + 2) + 172) * (N : ℝ) :=
      add_le_add hpair hmain
    _ = (3 * (Real.log 4 + 2) + 172) * (N : ℝ) := by ring

end RHLean.Analysis
