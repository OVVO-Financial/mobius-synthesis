import Mathlib
import Mathlib.NumberTheory.Harmonic.Bounds
import RHLean.Analysis.NativePNTNormalizedReciprocal
import RHLean.Analysis.NativePNTMobiusSecondMoment
import RHLean.Analysis.NativePNTSignedSecondSelberg

/-!
# Reciprocal cancellation in the signed second Selberg kernel

The positive second-von-Mangoldt kernel has reciprocal mass of logarithmic
square size.  The exact signed second-Selberg kernel

`K₂(n) = (Lambda * Lambda)(n) - Lambda(n) log n`

has a different constant mode.  Mertens' first theorem makes the reciprocal
`Lambda` mass `log N + O(1)`.  A finite Abel transform then shows

`sum Lambda(n) log n / n = (1/2) log(N)^2 + O(log N)`.

Reindexing the convolution over reciprocal divisor fibres gives the same
quadratic main term for `(Lambda * Lambda) / n`.  Their difference therefore
has only `O(log N)` reciprocal mass.

This is an unconditional signed cancellation theorem.  It removes one full
logarithm from the constant mode of the second Selberg operator before any
wheel-frontier or error-profile estimate is applied.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Reciprocal log-weighted von Mangoldt mass. -/
def nativePNTLambdaLogRecipMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    Λ n * Real.log (n : ℝ) / (n : ℝ)

/-- Reciprocal mass of the convolution part of the signed second kernel. -/
def nativePNTLambdaConvolutionRecipMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (Λ * Λ) n / (n : ℝ)

/-- Reciprocal mass of the true signed second-Selberg kernel. -/
def nativePNTSignedSecondSelbergKernelRecipMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    nativePNTSignedSecondSelbergKernel n / (n : ℝ)

/-- A version of the finite Abel bound with an arbitrary prefix constant. -/
theorem nativeAbelBoundMonotone_general
    (a b : ℕ → ℝ) (M : ℕ) (hM : 1 ≤ M)
    (P B : ℝ) (hP : 0 ≤ P)
    (hprefix : ∀ n, 1 ≤ n → n ≤ M →
      |∑ k ∈ Finset.Icc 1 n, a k| ≤ P)
    (hmono : ∀ n ∈ Finset.Ico 1 M, b n ≤ b (n + 1))
    (hbound : ∀ n ∈ Finset.Icc 1 M, |b n| ≤ B) :
    |∑ n ∈ Finset.Icc 1 M, a n * b n| ≤ 3 * P * B := by
  rw [nativeAbelIccOne a b M]
  have htail :
      |∑ n ∈ Finset.Ico 1 M,
          (∑ k ∈ Finset.Icc 1 n, a k) * (b n - b (n + 1))| ≤
        P * (b M - b 1) := by
    calc
      |∑ n ∈ Finset.Ico 1 M,
          (∑ k ∈ Finset.Icc 1 n, a k) * (b n - b (n + 1))| ≤
          ∑ n ∈ Finset.Ico 1 M,
            |(∑ k ∈ Finset.Icc 1 n, a k) *
              (b n - b (n + 1))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ico 1 M, P * (b (n + 1) - b n) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnI := Finset.mem_Ico.mp hn
        have hp := hprefix n hnI.1 (Nat.le_of_lt hnI.2)
        have hm := hmono n hn
        have hdiff : 0 ≤ b (n + 1) - b n := sub_nonneg.mpr hm
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hm)]
        have hneg : -(b n - b (n + 1)) = b (n + 1) - b n := by ring
        rw [hneg]
        exact mul_le_mul_of_nonneg_right hp hdiff
      _ = P * ∑ n ∈ Finset.Ico 1 M, (b (n + 1) - b n) := by
        rw [Finset.mul_sum]
      _ = P * (b M - b 1) := by
        rw [nativeTelescopeDiffIco b M hM]
  have hend :
      |(∑ n ∈ Finset.Icc 1 M, a n) * b M| ≤ P * B := by
    rw [abs_mul]
    exact mul_le_mul (hprefix M hM le_rfl)
      (hbound M (Finset.mem_Icc.mpr ⟨hM, le_rfl⟩))
      (abs_nonneg _) hP
  have hdiffBound : b M - b 1 ≤ 2 * B := by
    have hbM := hbound M (Finset.mem_Icc.mpr ⟨hM, le_rfl⟩)
    have hb1 := hbound 1 (Finset.mem_Icc.mpr ⟨le_rfl, hM⟩)
    rw [abs_le] at hbM hb1
    linarith
  calc
    |(∑ n ∈ Finset.Icc 1 M, a n) * b M +
        ∑ n ∈ Finset.Ico 1 M,
          (∑ k ∈ Finset.Icc 1 n, a k) * (b n - b (n + 1))| ≤
      |(∑ n ∈ Finset.Icc 1 M, a n) * b M| +
        |∑ n ∈ Finset.Ico 1 M,
          (∑ k ∈ Finset.Icc 1 n, a k) *
            (b n - b (n + 1))| := abs_add_le _ _
    _ ≤ P * B + P * (b M - b 1) := add_le_add hend htail
    _ ≤ P * B + P * (2 * B) :=
      add_le_add_left (mul_le_mul_of_nonneg_left hdiffBound hP) _
    _ = 3 * P * B := by ring

/-- Reciprocal integer mass equals the harmonic number. -/
theorem nativeRecipIcc_eq_harmonic : ∀ N : ℕ,
    (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)) = (harmonic N : ℝ) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih,
        harmonic_succ]
      push_cast
      ring

/-- Mertens' first theorem and the elementary harmonic estimate imply a
uniform bound for the prefix discrepancy between `Lambda(n)/n` and `1/n`. -/
theorem nativeLambdaRecip_sub_harmonic_abs_le
    (N : ℕ) (hN : 1 ≤ N) :
    |nativeLambdaRecip N - (harmonic N : ℝ)| ≤ Real.log 4 + 3 := by
  have hL := nativeLambdaRecip_sub_log_abs_le N hN
  have hHup : (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := by
    simpa using harmonic_le_one_add_log N
  have hlogNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlogMono : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log hlogNpos
    exact_mod_cast (show N ≤ N + 1 by omega)
  have hHlo : Real.log (N : ℝ) ≤ (harmonic N : ℝ) := by
    exact hlogMono.trans (by
      simpa [show N + 1 = N + 1 by rfl] using log_add_one_le_harmonic N)
  rw [abs_le] at hL ⊢
  constructor
  · have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith [hL.1, hHup]
  · linarith [hL.2, hHlo]

/-- The reciprocal log-weighted von Mangoldt mass differs from the elementary
`sum log(n)/n` mass by only `O(log N)`. -/
theorem nativePNTLambdaLogRecipMass_sub_logRecipMass_abs_le
    (N : ℕ) (hN : 3 ≤ N) :
    |nativePNTLambdaLogRecipMass N - nativeLogRecipMass N| ≤
      3 * (Real.log 4 + 3) * Real.log (N : ℝ) := by
  let a : ℕ → ℝ := fun n => Λ n / (n : ℝ) - 1 / (n : ℝ)
  let b : ℕ → ℝ := fun n => Real.log (n : ℝ)
  have hN1 : 1 ≤ N := by omega
  have hprefix : ∀ n, 1 ≤ n → n ≤ N →
      |∑ k ∈ Finset.Icc 1 n, a k| ≤ Real.log 4 + 3 := by
    intro n hn1 _hnN
    have heq :
        (∑ k ∈ Finset.Icc 1 n, a k) =
          nativeLambdaRecip n - (harmonic n : ℝ) := by
      dsimp [a]
      rw [Finset.sum_sub_distrib]
      unfold nativeLambdaRecip
      rw [nativeRecipIcc_eq_harmonic]
    rw [heq]
    exact nativeLambdaRecip_sub_harmonic_abs_le n hn1
  have hmono : ∀ n ∈ Finset.Ico 1 N, b n ≤ b (n + 1) := by
    intro n hn
    have hnI := Finset.mem_Ico.mp hn
    dsimp [b]
    apply Real.log_le_log
    · exact_mod_cast hnI.1
    · exact_mod_cast (show n ≤ n + 1 by omega)
  have hbound : ∀ n ∈ Finset.Icc 1 N,
      |b n| ≤ Real.log (N : ℝ) := by
    intro n hn
    have hnI := Finset.mem_Icc.mp hn
    have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hnI.1)
    dsimp [b]
    rw [abs_of_nonneg hlogn0]
    exact Real.log_le_log (by exact_mod_cast hnI.1) (by exact_mod_cast hnI.2)
  have hab := nativeAbelBoundMonotone_general a b N hN1
    (Real.log 4 + 3) (Real.log (N : ℝ))
    (by have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith)
    hprefix hmono hbound
  have heq :
      (∑ n ∈ Finset.Icc 1 N, a n * b n) =
        nativePNTLambdaLogRecipMass N - nativeLogRecipMass N := by
    unfold nativePNTLambdaLogRecipMass nativeLogRecipMass
    dsimp [a, b]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  rw [heq] at hab
  exact hab

/-- Hence the log-weighted von Mangoldt reciprocal mass has the expected
`(1/2) log^2 N` main term with only logarithmic error. -/
theorem nativePNTLambdaLogRecipMass_sub_half_log_sq_abs_le
    (N : ℕ) (hN : 3 ≤ N) :
    |nativePNTLambdaLogRecipMass N -
        (1 / 2 : ℝ) * (Real.log (N : ℝ)) ^ 2| ≤
      3 * (Real.log 4 + 3) * Real.log (N : ℝ) + 4 := by
  have hdiff := nativePNTLambdaLogRecipMass_sub_logRecipMass_abs_le N hN
  have hJ := nativeLogRecipDefect_abs_le_four N hN
  unfold nativeLogRecipDefect at hJ
  have hdecomp :
      nativePNTLambdaLogRecipMass N -
          (1 / 2 : ℝ) * (Real.log (N : ℝ)) ^ 2 =
        (nativePNTLambdaLogRecipMass N - nativeLogRecipMass N) +
          (nativeLogRecipMass N -
            (1 / 2 : ℝ) * (Real.log (N : ℝ)) ^ 2) := by ring
  rw [hdecomp]
  exact (abs_add_le _ _).trans (add_le_add hdiff hJ)

/-- Reciprocal convolution reindexing: the `(Lambda * Lambda)` mass is the
fixed reciprocal `Lambda` measure applied to the smaller reciprocal masses. -/
theorem nativePNTLambdaConvolutionRecipMass_eq
    (N : ℕ) :
    nativePNTLambdaConvolutionRecipMass N =
      ∑ d ∈ Finset.Icc 1 N,
        (Λ d / (d : ℝ)) * nativeLambdaRecip (N / d) := by
  unfold nativePNTLambdaConvolutionRecipMass nativeLambdaRecip
  have hmem : ∀ (n d : ℕ),
      n ∈ Finset.Icc 1 N ∧ d ∈ n.divisors ↔
        n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x) ∧
          d ∈ Finset.Icc 1 N := by
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
    (∑ n ∈ Finset.Icc 1 N, (Λ * Λ) n / (n : ℝ)) =
        ∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ n.divisors,
            (Λ d / (d : ℝ)) *
              (Λ (n / d) / ((n / d : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      rw [ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal (fun a b => Λ a * Λ b), Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
      have hqpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hnpos hdvd) hdpos
      have hmulNat : d * (n / d) = n := Nat.mul_div_cancel' hdvd
      have hdR0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
      have hqR0 : (((n / d : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hqpos)
      have hnR0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
      have hmulR : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast hmulNat
      field_simp [hdR0, hqR0, hnR0]
      calc
        Λ d * Λ (n / d) * (d : ℝ) * ((n / d : ℕ) : ℝ) =
            (Λ d * Λ (n / d)) * ((d : ℝ) * ((n / d : ℕ) : ℝ)) := by ring
        _ = (Λ d * Λ (n / d)) * (n : ℝ) := by rw [hmulR]
        _ = Λ d * Λ (n / d) * (n : ℝ) := by ring
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x),
            (Λ d / (d : ℝ)) *
              (Λ (n / d) / ((n / d : ℕ) : ℝ)) := Finset.sum_comm' hmem
    _ = ∑ d ∈ Finset.Icc 1 N,
        (Λ d / (d : ℝ)) *
          ∑ m ∈ Finset.Icc 1 (N / d), Λ m / (m : ℝ) := by
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
          exact ⟨(Nat.one_le_div_iff hdpos).2
              (Nat.le_of_dvd (by omega) hdvd), Nat.div_le_div_right hnN⟩
        · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
          have hmpos : 0 < m := by omega
          have hmulN' : m * d ≤ N := (Nat.le_div_iff_mul_le hdpos).1 hmN
          have hmulN : d * m ≤ N := by simpa [Nat.mul_comm] using hmulN'
          exact ⟨⟨Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (Nat.mul_pos hdpos hmpos)), hmulN⟩,
            dvd_mul_right d m⟩
      rw [hmap, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro m _hm
        rw [Nat.mul_div_cancel_left m hdpos]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hdpos hab

/-- On every active reciprocal fibre the logarithmic floor defect lies between
zero and one. -/
theorem nativePNT_log_floor_defect_bounds
    (N d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
    0 ≤ Real.log (N : ℝ) - Real.log (d : ℝ) -
        Real.log ((N / d : ℕ) : ℝ) ∧
    Real.log (N : ℝ) - Real.log (d : ℝ) -
        Real.log ((N / d : ℕ) : ℝ) ≤ 1 := by
  have hdI := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := by omega
  have hNpos : 0 < N := hdpos.trans_le hdI.2
  have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).2 hdI.2
  have hmulLe : d * (N / d) ≤ N := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self N d
  have hprodPos : (0 : ℝ) < (d * (N / d) : ℕ) := by positivity
  have hlogLe :
      Real.log ((d * (N / d) : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < d * (N / d) by positivity)
    · exact_mod_cast hmulLe
  have hdR0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
  have hqR0 : (((N / d : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show N / d ≠ 0 by omega)
  have hprodlog :
      Real.log ((d * (N / d) : ℕ) : ℝ) =
        Real.log (d : ℝ) + Real.log ((N / d : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hdR0 hqR0]
  rw [hprodlog] at hlogLe
  have hlo : 0 ≤ Real.log (N : ℝ) - Real.log (d : ℝ) -
      Real.log ((N / d : ℕ) : ℝ) := by linarith
  have hlt : N < d * (N / d + 1) := by
    have hdivmod : d * (N / d) + N % d = N := Nat.div_add_mod N d
    have hrem : N % d < d := Nat.mod_lt N hdpos
    calc
      N = d * (N / d) + N % d := hdivmod.symm
      _ < d * (N / d) + d := Nat.add_lt_add_left hrem _
      _ = d * (N / d + 1) := by ring
  have hq2 : N / d + 1 ≤ 2 * (N / d) := by omega
  have hupperNat : N < 2 * (d * (N / d)) := by
    calc
      N < d * (N / d + 1) := hlt
      _ ≤ d * (2 * (N / d)) := Nat.mul_le_mul_left d hq2
      _ = 2 * (d * (N / d)) := by ring
  have hupperR : (N : ℝ) < 2 * ((d * (N / d) : ℕ) : ℝ) := by
    exact_mod_cast hupperNat
  have hlogUpper :
      Real.log (N : ℝ) ≤ Real.log (2 * ((d * (N / d) : ℕ) : ℝ)) := by
    apply Real.log_le_log
    · exact_mod_cast hNpos
    · exact hupperR.le
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hprodR0 : (((d * (N / d) : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show d * (N / d) ≠ 0 by positivity)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hprodR0,
    hprodlog] at hlogUpper
  constructor
  · exact hlo
  · linarith

/-- The convolution reciprocal mass differs from the deterministic expression
`log N * L(N) - D(N)` by only one copy of the reciprocal `Lambda` mass plus
the Mertens error. -/
theorem nativePNTLambdaConvolutionRecipMass_sub_model_abs_le
    (N : ℕ) (_hN : 3 ≤ N) :
    |nativePNTLambdaConvolutionRecipMass N -
        (Real.log (N : ℝ) * nativeLambdaRecip N -
          nativePNTLambdaLogRecipMass N)| ≤
      (Real.log 4 + 3) * nativeLambdaRecip N := by
  rw [nativePNTLambdaConvolutionRecipMass_eq]
  let A : ℝ := Real.log 4 + 2
  have hsumNonneg : 0 ≤ nativeLambdaRecip N := by
    unfold nativeLambdaRecip
    apply Finset.sum_nonneg
    intro d hd
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hpoint : ∀ d ∈ Finset.Icc 1 N,
      |(Λ d / (d : ℝ)) * nativeLambdaRecip (N / d) -
        (Λ d / (d : ℝ)) *
          (Real.log (N : ℝ) - Real.log (d : ℝ))| ≤
        (Real.log 4 + 3) * (Λ d / (d : ℝ)) := by
    intro d hd
    have hdI := Finset.mem_Icc.mp hd
    have hdpos : 0 < d := by omega
    have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).2 hdI.2
    have hM := nativeLambdaRecip_sub_log_abs_le (N / d) hq1
    have hdef := nativePNT_log_floor_defect_bounds N d hd
    have hinner :
        |nativeLambdaRecip (N / d) -
          (Real.log (N : ℝ) - Real.log (d : ℝ))| ≤ Real.log 4 + 3 := by
      have hdecomp :
          nativeLambdaRecip (N / d) -
              (Real.log (N : ℝ) - Real.log (d : ℝ)) =
            (nativeLambdaRecip (N / d) -
              Real.log ((N / d : ℕ) : ℝ)) -
            (Real.log (N : ℝ) - Real.log (d : ℝ) -
              Real.log ((N / d : ℕ) : ℝ)) := by ring
      rw [hdecomp]
      have hdefAbs :
          |Real.log (N : ℝ) - Real.log (d : ℝ) -
            Real.log ((N / d : ℕ) : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg hdef.1]
        exact hdef.2
      exact (abs_sub _ _).trans (by linarith [hM, hdefAbs])
    have hw0 : 0 ≤ Λ d / (d : ℝ) :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    have heq :
        (Λ d / (d : ℝ)) * nativeLambdaRecip (N / d) -
            (Λ d / (d : ℝ)) *
              (Real.log (N : ℝ) - Real.log (d : ℝ)) =
          (Λ d / (d : ℝ)) *
            (nativeLambdaRecip (N / d) -
              (Real.log (N : ℝ) - Real.log (d : ℝ))) := by ring
    rw [heq, abs_mul, abs_of_nonneg hw0]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hinner hw0
  have hmodel :
      ∑ d ∈ Finset.Icc 1 N,
          (Λ d / (d : ℝ)) *
            (Real.log (N : ℝ) - Real.log (d : ℝ)) =
        Real.log (N : ℝ) * nativeLambdaRecip N -
          nativePNTLambdaLogRecipMass N := by
    unfold nativeLambdaRecip nativePNTLambdaLogRecipMass
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  rw [← hmodel, ← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ Finset.Icc 1 N,
        ((Λ d / (d : ℝ)) * nativeLambdaRecip (N / d) -
          (Λ d / (d : ℝ)) *
            (Real.log (N : ℝ) - Real.log (d : ℝ)))| ≤
      ∑ d ∈ Finset.Icc 1 N,
        |(Λ d / (d : ℝ)) * nativeLambdaRecip (N / d) -
          (Λ d / (d : ℝ)) *
            (Real.log (N : ℝ) - Real.log (d : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
        (Real.log 4 + 3) * (Λ d / (d : ℝ)) := Finset.sum_le_sum hpoint
    _ = (Real.log 4 + 3) * nativeLambdaRecip N := by
      unfold nativeLambdaRecip
      rw [Finset.mul_sum]

/-- The reciprocal signed second-kernel mass is convolution minus the
log-weighted reciprocal mass. -/
theorem nativePNTSignedSecondSelbergKernelRecipMass_eq
    (N : ℕ) :
    nativePNTSignedSecondSelbergKernelRecipMass N =
      nativePNTLambdaConvolutionRecipMass N -
        nativePNTLambdaLogRecipMass N := by
  unfold nativePNTSignedSecondSelbergKernelRecipMass
    nativePNTLambdaConvolutionRecipMass nativePNTLambdaLogRecipMass
    nativePNTSignedSecondSelbergKernel
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- Explicit logarithmic bound for the reciprocal constant mode of the true
signed second-Selberg kernel.  In contrast, the positive second kernel carries
quadratic logarithmic reciprocal mass. -/
theorem nativePNTSignedSecondSelbergKernelRecipMass_abs_le
    (N : ℕ) (hN : 3 ≤ N) :
    |nativePNTSignedSecondSelbergKernelRecipMass N| ≤
      (Real.log 4 + 3) * (Real.log (N : ℝ) + (Real.log 4 + 2)) +
      (Real.log 4 + 2) * Real.log (N : ℝ) +
      6 * (Real.log 4 + 3) * Real.log (N : ℝ) + 8 := by
  let A : ℝ := Real.log 4 + 2
  have hN1 : 1 ≤ N := by omega
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN1)
  have hL := nativeLambdaRecip_sub_log_abs_le N hN1
  have hLupper : nativeLambdaRecip N ≤ Real.log (N : ℝ) + A := by
    dsimp [A]
    rw [abs_le] at hL
    linarith
  have hL0 : 0 ≤ nativeLambdaRecip N := by
    unfold nativeLambdaRecip
    apply Finset.sum_nonneg
    intro d _hd
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hconv := nativePNTLambdaConvolutionRecipMass_sub_model_abs_le N hN
  have hD := nativePNTLambdaLogRecipMass_sub_half_log_sq_abs_le N hN
  have hmain :
      |Real.log (N : ℝ) * nativeLambdaRecip N -
          2 * nativePNTLambdaLogRecipMass N| ≤
        A * Real.log (N : ℝ) +
          6 * (Real.log 4 + 3) * Real.log (N : ℝ) + 8 := by
    have hsplit :
        Real.log (N : ℝ) * nativeLambdaRecip N -
            2 * nativePNTLambdaLogRecipMass N =
          Real.log (N : ℝ) *
              (nativeLambdaRecip N - Real.log (N : ℝ)) -
            2 * (nativePNTLambdaLogRecipMass N -
              (1 / 2 : ℝ) * (Real.log (N : ℝ)) ^ 2) := by ring
    rw [hsplit]
    calc
      |Real.log (N : ℝ) *
          (nativeLambdaRecip N - Real.log (N : ℝ)) -
          2 * (nativePNTLambdaLogRecipMass N -
            (1 / 2 : ℝ) * (Real.log (N : ℝ)) ^ 2)| ≤
        |Real.log (N : ℝ) *
          (nativeLambdaRecip N - Real.log (N : ℝ))| +
        |2 * (nativePNTLambdaLogRecipMass N -
          (1 / 2 : ℝ) * (Real.log (N : ℝ)) ^ 2)| := abs_sub _ _
      _ = Real.log (N : ℝ) *
          |nativeLambdaRecip N - Real.log (N : ℝ)| +
        2 * |nativePNTLambdaLogRecipMass N -
          (1 / 2 : ℝ) * (Real.log (N : ℝ)) ^ 2| := by
        rw [abs_mul, abs_of_nonneg hlog0, abs_mul]
        norm_num
      _ ≤ Real.log (N : ℝ) * A +
          2 * (3 * (Real.log 4 + 3) * Real.log (N : ℝ) + 4) := by
        have hLA :
            |nativeLambdaRecip N - Real.log (N : ℝ)| ≤ A := by
          simpa [A] using hL
        exact add_le_add
          (mul_le_mul_of_nonneg_left hLA hlog0)
          (mul_le_mul_of_nonneg_left hD (by norm_num))
      _ = A * Real.log (N : ℝ) +
          6 * (Real.log 4 + 3) * Real.log (N : ℝ) + 8 := by ring
  rw [nativePNTSignedSecondSelbergKernelRecipMass_eq]
  have hdecomp :
      nativePNTLambdaConvolutionRecipMass N -
          nativePNTLambdaLogRecipMass N =
        (nativePNTLambdaConvolutionRecipMass N -
          (Real.log (N : ℝ) * nativeLambdaRecip N -
            nativePNTLambdaLogRecipMass N)) +
        (Real.log (N : ℝ) * nativeLambdaRecip N -
          2 * nativePNTLambdaLogRecipMass N) := by ring
  rw [hdecomp]
  calc
    |(nativePNTLambdaConvolutionRecipMass N -
        (Real.log (N : ℝ) * nativeLambdaRecip N -
          nativePNTLambdaLogRecipMass N)) +
        (Real.log (N : ℝ) * nativeLambdaRecip N -
          2 * nativePNTLambdaLogRecipMass N)| ≤
      |nativePNTLambdaConvolutionRecipMass N -
        (Real.log (N : ℝ) * nativeLambdaRecip N -
          nativePNTLambdaLogRecipMass N)| +
      |Real.log (N : ℝ) * nativeLambdaRecip N -
        2 * nativePNTLambdaLogRecipMass N| := abs_add_le _ _
    _ ≤ (Real.log 4 + 3) * nativeLambdaRecip N +
        (A * Real.log (N : ℝ) +
          6 * (Real.log 4 + 3) * Real.log (N : ℝ) + 8) :=
      add_le_add hconv hmain
    _ ≤ (Real.log 4 + 3) * (Real.log (N : ℝ) + A) +
        (A * Real.log (N : ℝ) +
          6 * (Real.log 4 + 3) * Real.log (N : ℝ) + 8) := by
      gcongr
    _ = (Real.log 4 + 3) *
          (Real.log (N : ℝ) + (Real.log 4 + 2)) +
        (Real.log 4 + 2) * Real.log (N : ℝ) +
        6 * (Real.log 4 + 3) * Real.log (N : ℝ) + 8 := by
      dsimp [A]
      ring

end RHLean.Analysis
