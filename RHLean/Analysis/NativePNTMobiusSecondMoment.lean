import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import RHLean.Analysis.NativePNTMobiusMoments
import RHLean.Analysis.NativePNTSelberg

/-!
# Second Möbius logarithmic moment

This module proves the second reciprocal logarithmic moment needed in the
summatory Selberg formula.  The proof stays finite:

* reindex `Lambda = mu * log` after division by the endpoint;
* compare `sum log(m)/m` with `(1/2) log^2`;
* show the sum-integral defect has bounded variation above `3`;
* apply a finite Abel transform against the uniformly bounded reciprocal
  Möbius prefixes.

No PNT-equivalent asymptotic input is used.
-/

noncomputable section

open Finset Nat
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Reciprocal logarithmic partial sum `J(N) = sum_{m<=N} log(m)/m`. -/
def nativeLogRecipMass (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ) / (m : ℝ)

/-- Defect from the elementary integral main term `(1/2) log^2 N`. -/
def nativeLogRecipDefect (N : ℕ) : ℝ :=
  nativeLogRecipMass N - (1 / 2 : ℝ) * (Real.log N) ^ 2

/-- Exact reciprocal convolution form of `Lambda = mu * log`. -/
theorem nativeLambdaRecip_eq_mobius_logRecip
    (N : ℕ) :
    nativeLambdaRecip N =
      ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
          nativeLogRecipMass (N / d) := by
  unfold nativeLambdaRecip nativeLogRecipMass
  have hLambda :
      (Λ : ArithmeticFunction ℝ) =
        (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log := by
    simp
  rw [hLambda]
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
        (((μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) n) / (n : ℝ)) =
        ∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ n.divisors,
            ((ArithmeticFunction.moebius d : ℝ) /
              (d : ℝ)) *
              (Real.log ((n / d : ℕ) : ℝ) / ((n / d : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      rw [ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal
          (fun a b => (μ : ArithmeticFunction ℝ) a * ArithmeticFunction.log b),
        Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
      have hqpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hnpos hdvd) hdpos
      change
        ((ArithmeticFunction.moebius d : ℝ) * Real.log ((n / d : ℕ) : ℝ)) /
            (n : ℝ) =
          ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) *
            (Real.log ((n / d : ℕ) : ℝ) / ((n / d : ℕ) : ℝ))
      have hmulNat : d * (n / d) = n := Nat.mul_div_cancel' hdvd
      have hmul : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast hmulNat
      have hdR0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
      have hqR0 : (((n / d : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqpos)
      have hnR0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
      field_simp [hdR0, hqR0, hnR0]
      have hscaled := congrArg
        (fun z : ℝ =>
          (ArithmeticFunction.moebius d : ℝ) *
            Real.log ((n / d : ℕ) : ℝ) * z) hmul
      simpa [mul_assoc] using hscaled
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x),
            ((ArithmeticFunction.moebius d : ℝ) /
              (d : ℝ)) *
              (Real.log ((n / d : ℕ) : ℝ) / ((n / d : ℕ) : ℝ)) :=
      Finset.sum_comm' hmem
    _ = ∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
            ∑ m ∈ Finset.Icc 1 (N / d),
              Real.log (m : ℝ) / (m : ℝ) := by
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
              (Nat.le_of_dvd (by omega) hdvd),
            Nat.div_le_div_right hnN⟩
        · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
          have hmpos : 0 < m := by omega
          have hmulpos : 0 < d * m := Nat.mul_pos hdpos hmpos
          have hmulN' : m * d ≤ N := (Nat.le_div_iff_mul_le hdpos).1 hmN
          have hmulN : d * m ≤ N := by simpa [Nat.mul_comm] using hmulN'
          exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmulpos), hmulN⟩,
            dvd_mul_right d m⟩
      rw [hmap, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro m _hm
        have hdiv : d * m / d = m := Nat.mul_div_cancel_left m hdpos
        rw [hdiv]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hdpos hab
    _ = ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
          nativeLogRecipMass (N / d) := by rfl

/-- Primitive for `log x / x`. -/
def nativeLogRecipPrimitive (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.log x) ^ 2

/-- Derivative of the reciprocal-log primitive. -/
theorem nativeLogRecipPrimitive_hasDerivAt
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt nativeLogRecipPrimitive (Real.log x / x) x := by
  have hlog := Real.hasDerivAt_log hx
  have h := (hlog.mul hlog).const_mul (1 / 2 : ℝ)
  convert h using 1
  · funext y
    simp [nativeLogRecipPrimitive, pow_two]
  · field_simp [hx]
    ring

/-- Exact integral of `log x / x` on an integer unit interval. -/
theorem nativeIntegral_log_div_unit
    (q : ℕ) (hq : 1 ≤ q) :
    (∫ x in (q : ℝ)..((q + 1 : ℕ) : ℝ), Real.log x / x) =
      nativeLogRecipPrimitive ((q + 1 : ℕ) : ℝ) -
        nativeLogRecipPrimitive (q : ℝ) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hderiv : ∀ x ∈ Set.uIcc (q : ℝ) ((q + 1 : ℕ) : ℝ),
      HasDerivAt nativeLogRecipPrimitive (Real.log x / x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by exact_mod_cast (show q ≤ q + 1 by omega))] at hx
    exact nativeLogRecipPrimitive_hasDerivAt (by linarith [hx.1])
  have hcont : ContinuousOn (fun x : ℝ => Real.log x / x)
      (Set.uIcc (q : ℝ) ((q + 1 : ℕ) : ℝ)) := by
    intro x hx
    rw [Set.uIcc_of_le (by exact_mod_cast (show q ≤ q + 1 by omega))] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    exact ((Real.hasDerivAt_log hx0).continuousAt.div continuousAt_id hx0).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-- One-step increment of the reciprocal logarithmic mass. -/
theorem nativeLogRecipMass_succ (q : ℕ) :
    nativeLogRecipMass (q + 1) =
      nativeLogRecipMass q + Real.log ((q + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ) := by
  unfold nativeLogRecipMass
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ q + 1)]

private theorem nativeExpOne_le_three : Real.exp 1 ≤ 3 := by
  have h := Real.exp_one_lt_d9
  norm_num at h ⊢
  linarith

/-- `log x / x` is antitone on every interval above `3`. -/
theorem nativeLogDivSelf_antitoneOn_three
    {a b : ℝ} (ha : 3 ≤ a) :
    AntitoneOn (fun x : ℝ => Real.log x / x) (Set.Icc a b) := by
  apply Real.log_div_self_antitoneOn.mono
  intro x hx
  exact nativeExpOne_le_three.trans (ha.trans hx.1)

/-- Above `3`, the discrete sum-integral defect is antitone. -/
theorem nativeLogRecipDefect_succ_le
    (q : ℕ) (hq : 3 ≤ q) :
    nativeLogRecipDefect (q + 1) ≤ nativeLogRecipDefect q := by
  have hanti := nativeLogDivSelf_antitoneOn_three
    (a := (q : ℝ)) (b := ((q + 1 : ℕ) : ℝ)) (by exact_mod_cast hq)
  have hsum := AntitoneOn.sum_le_integral_Ico
    (f := fun x : ℝ => Real.log x / x)
    (show q ≤ q + 1 by omega) hanti
  have hpoint :
      Real.log ((q + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ) ≤
        ∫ x in (q : ℝ)..((q + 1 : ℕ) : ℝ), Real.log x / x := by
    simpa using hsum
  rw [nativeIntegral_log_div_unit q (by omega : 1 ≤ q)] at hpoint
  unfold nativeLogRecipDefect
  rw [nativeLogRecipMass_succ]
  unfold nativeLogRecipPrimitive at hpoint
  nlinarith

/-- Matching lower control on one defect increment. -/
theorem nativeLogRecipDefect_succ_sub_ge
    (q : ℕ) (hq : 3 ≤ q) :
    Real.log ((q + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ) -
        Real.log (q : ℝ) / (q : ℝ) ≤
      nativeLogRecipDefect (q + 1) - nativeLogRecipDefect q := by
  have hanti := nativeLogDivSelf_antitoneOn_three
    (a := (q : ℝ)) (b := ((q + 1 : ℕ) : ℝ)) (by exact_mod_cast hq)
  have hsum := AntitoneOn.integral_le_sum_Ico
    (f := fun x : ℝ => Real.log x / x)
    (show q ≤ q + 1 by omega) hanti
  have hpoint :
      (∫ x in (q : ℝ)..((q + 1 : ℕ) : ℝ), Real.log x / x) ≤
        Real.log (q : ℝ) / (q : ℝ) := by
    simpa using hsum
  rw [nativeIntegral_log_div_unit q (by omega : 1 ≤ q)] at hpoint
  unfold nativeLogRecipDefect
  rw [nativeLogRecipMass_succ]
  unfold nativeLogRecipPrimitive at hpoint
  nlinarith

/-- Antitonicity of the defect on integer endpoints at least `3`. -/
theorem nativeLogRecipDefect_antitone_three
    {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) :
    nativeLogRecipDefect b ≤ nativeLogRecipDefect a := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      exact (nativeLogRecipDefect_succ_le b (ha.trans hab)).trans ih

/-- Telescoped lower drift from endpoint `3`. -/
theorem nativeLogRecipDefect_lower_three
    (q : ℕ) (hq : 3 ≤ q) :
    nativeLogRecipDefect 3 +
        Real.log (q : ℝ) / (q : ℝ) - Real.log (3 : ℝ) / 3 ≤
      nativeLogRecipDefect q := by
  induction q, hq using Nat.le_induction with
  | base =>
      ring_nf
      exact le_rfl
  | succ q hq ih =>
      have hstep := nativeLogRecipDefect_succ_sub_ge q hq
      linarith

private theorem nativeLog_two_bounds :
    0 ≤ Real.log (2 : ℝ) ∧ Real.log (2 : ℝ) ≤ 1 := by
  constructor
  · exact Real.log_nonneg (by norm_num)
  · have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    linarith

private theorem nativeLog_three_bounds :
    0 ≤ Real.log (3 : ℝ) ∧ Real.log (3 : ℝ) ≤ 2 := by
  constructor
  · exact Real.log_nonneg (by norm_num)
  · have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    norm_num at h ⊢
    linarith

/-- Uniform crude bound for the reciprocal-log defect above `3`.  Sharp
constants are irrelevant; bounded variation is the point. -/
theorem nativeLogRecipDefect_abs_le_four
    (q : ℕ) (hq : 3 ≤ q) :
    |nativeLogRecipDefect q| ≤ 4 := by
  have hanti := nativeLogRecipDefect_antitone_three
    (a := 3) (b := q) (by norm_num) hq
  have hlower := nativeLogRecipDefect_lower_three q hq
  have hlog2 := nativeLog_two_bounds
  have hlog3 := nativeLog_three_bounds
  have hlog2lo := hlog2.1
  have hlog2hi := hlog2.2
  have hlog3lo := hlog3.1
  have hlog3hi := hlog3.2
  have hqlog : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (show 0 < q by omega)
  have hmass1 : nativeLogRecipMass 1 = 0 := by
    simp [nativeLogRecipMass]
  have hmass2 : nativeLogRecipMass 2 = Real.log (2 : ℝ) / 2 := by
    rw [nativeLogRecipMass_succ 1, hmass1]
    norm_num
  have hmass3 :
      nativeLogRecipMass 3 =
        Real.log (2 : ℝ) / 2 + Real.log (3 : ℝ) / 3 := by
    rw [nativeLogRecipMass_succ 2, hmass2]
    norm_num
  have hlog3sq : (Real.log (3 : ℝ)) ^ 2 ≤ 4 := by
    have hprod :
        0 ≤ Real.log (3 : ℝ) * (2 - Real.log (3 : ℝ)) :=
      mul_nonneg hlog3lo (sub_nonneg.mpr hlog3hi)
    nlinarith
  have hD3upper : nativeLogRecipDefect 3 ≤ 2 := by
    unfold nativeLogRecipDefect
    rw [hmass3]
    nlinarith [sq_nonneg (Real.log (3 : ℝ))]
  have hD3lower : -2 ≤ nativeLogRecipDefect 3 := by
    unfold nativeLogRecipDefect
    rw [hmass3]
    nlinarith
  have hf3 : Real.log (3 : ℝ) / 3 ≤ 1 := by
    nlinarith
  have hqterm : 0 ≤ Real.log (q : ℝ) / (q : ℝ) := div_nonneg hqlog hqpos.le
  rw [abs_le]
  constructor
  · nlinarith
  · exact (hanti.trans hD3upper).trans (by norm_num)

/-- For quotient `1` or `2` the defect is also uniformly tiny. -/
theorem nativeLogRecipDefect_abs_le_one_of_le_two
    (q : ℕ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    |nativeLogRecipDefect q| ≤ 1 := by
  have hcases : q = 1 ∨ q = 2 := by omega
  rcases hcases with rfl | rfl
  · norm_num [nativeLogRecipDefect, nativeLogRecipMass]
  · have hlog2 := nativeLog_two_bounds
    unfold nativeLogRecipDefect
    rw [nativeLogRecipMass_succ 1]
    simp [nativeLogRecipMass]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (Real.log (2 : ℝ))]

/-! ## A finite Abel bound -/

/-- Exact Abel summation on the positive prefix. -/
theorem nativeAbelIccOne
    (a b : ℕ → ℝ) : ∀ M : ℕ,
    (∑ n ∈ Finset.Icc 1 M, a n * b n) =
      (∑ n ∈ Finset.Icc 1 M, a n) * b M +
        ∑ n ∈ Finset.Ico 1 M,
          (∑ k ∈ Finset.Icc 1 n, a k) * (b n - b (n + 1)) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
      by_cases hM0 : M = 0
      · subst M
        simp
      · have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM0
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), ih,
          Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1),
          Finset.sum_Ico_succ_top hM1]
        ring

private theorem nativeTelescopeDiffIco
    (b : ℕ → ℝ) : ∀ M : ℕ, 1 ≤ M →
    (∑ n ∈ Finset.Ico 1 M, (b (n + 1) - b n)) = b M - b 1 := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
      rw [Finset.sum_Ico_succ_top hM, ih]
      ring

/-- Abel bound for a monotone weight and uniformly bounded positive-prefix
partial sums. -/
theorem nativeAbelBoundMonotone
    (a b : ℕ → ℝ) (M : ℕ) (hM : 1 ≤ M) (B : ℝ) (_hB : 0 ≤ B)
    (hprefix : ∀ n, 1 ≤ n → n ≤ M →
      |∑ k ∈ Finset.Icc 1 n, a k| ≤ 1)
    (hmono : ∀ n ∈ Finset.Ico 1 M, b n ≤ b (n + 1))
    (hbound : ∀ n ∈ Finset.Icc 1 M, |b n| ≤ B) :
    |∑ n ∈ Finset.Icc 1 M, a n * b n| ≤ 3 * B := by
  rw [nativeAbelIccOne a b M]
  calc
    |(∑ n ∈ Finset.Icc 1 M, a n) * b M +
        ∑ n ∈ Finset.Ico 1 M,
          (∑ k ∈ Finset.Icc 1 n, a k) * (b n - b (n + 1))| ≤
      |(∑ n ∈ Finset.Icc 1 M, a n) * b M| +
        |∑ n ∈ Finset.Ico 1 M,
          (∑ k ∈ Finset.Icc 1 n, a k) * (b n - b (n + 1))| := abs_add_le _ _
    _ ≤ B + ∑ n ∈ Finset.Ico 1 M, (b (n + 1) - b n) := by
      apply _root_.add_le_add
      · rw [abs_mul]
        have hp := hprefix M hM le_rfl
        have hb := hbound M (Finset.mem_Icc.mpr ⟨hM, le_rfl⟩)
        nlinarith [abs_nonneg (∑ n ∈ Finset.Icc 1 M, a n), abs_nonneg (b M)]
      · calc
          |∑ n ∈ Finset.Ico 1 M,
              (∑ k ∈ Finset.Icc 1 n, a k) * (b n - b (n + 1))| ≤
            ∑ n ∈ Finset.Ico 1 M,
              |(∑ k ∈ Finset.Icc 1 n, a k) * (b n - b (n + 1))| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ n ∈ Finset.Ico 1 M, (b (n + 1) - b n) := by
            apply Finset.sum_le_sum
            intro n hn
            have hnI := Finset.mem_Ico.mp hn
            have hp := hprefix n hnI.1 (Nat.le_of_lt hnI.2)
            have hm := hmono n hn
            rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hm)]
            have hdiff : 0 ≤ b (n + 1) - b n := sub_nonneg.mpr hm
            have hneg : -(b n - b (n + 1)) = b (n + 1) - b n := by ring
            rw [hneg]
            exact mul_le_of_le_one_left hdiff hp
    _ = B + (b M - b 1) := by rw [nativeTelescopeDiffIco b M hM]
    _ ≤ 3 * B := by
      have hbM := hbound M (Finset.mem_Icc.mpr ⟨hM, le_rfl⟩)
      have hb1 := hbound 1 (Finset.mem_Icc.mpr ⟨le_rfl, hM⟩)
      rw [abs_le] at hbM hb1
      linarith

/-- Second logarithmic reciprocal Möbius moment. -/
def nativeMobiusLogMomentTwo (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
      (Real.log ((N / d : ℕ) : ℝ)) ^ 2

/-- Möbius-weighted reciprocal-log defect. -/
def nativeMobiusLogRecipDefectMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
      nativeLogRecipDefect (N / d)

/-- Exact relation between Mertens' first theorem and the second logarithmic
Möbius moment. -/
theorem nativeLambdaRecip_eq_half_momentTwo_add_defect
    (N : ℕ) :
    nativeLambdaRecip N =
      (1 / 2 : ℝ) * nativeMobiusLogMomentTwo N +
        nativeMobiusLogRecipDefectMass N := by
  rw [nativeLambdaRecip_eq_mobius_logRecip]
  unfold nativeMobiusLogMomentTwo nativeMobiusLogRecipDefectMass
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  unfold nativeLogRecipDefect
  ring

/-- Above the hyperbolic cutoff `N/3`, the reciprocal quotient is `1` or `2`. -/
private theorem nativeDiv_le_two_of_div_three_lt
    (N d : ℕ) (hd : N / 3 < d) : N / d ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ N / d := by omega
  have hdpos : 0 < d := by
    by_contra hd0
    simp_all
  have hmul : 3 * d ≤ N := (Nat.le_div_iff_mul_le hdpos).1 h3
  have hdiv : d ≤ N / 3 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2 (by
    simpa [Nat.mul_comm] using hmul)
  omega

/-- The Möbius-weighted reciprocal-log defect is uniformly bounded. -/
theorem nativeMobiusLogRecipDefectMass_abs_le
    (N : ℕ) (hN : 3 ≤ N) :
    |nativeMobiusLogRecipDefectMass N| ≤ 15 := by
  let M := N / 3
  have hM : 1 ≤ M := (Nat.one_le_div_iff (by norm_num : 0 < 3)).2 hN
  let a : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
  let b : ℕ → ℝ := fun d => nativeLogRecipDefect (N / d)
  have hprefix : ∀ n, 1 ≤ n → n ≤ M →
      |∑ k ∈ Finset.Icc 1 n, a k| ≤ 1 := by
    intro n _hn1 _hnM
    simpa [a, nativeMertensRecip] using nativeMertensRecip_abs_le_one n
  have hmono : ∀ d ∈ Finset.Ico 1 M, b d ≤ b (d + 1) := by
    intro d hd
    have hdI := Finset.mem_Ico.mp hd
    have hdpos : 0 < d := by omega
    have hsuccM : d + 1 ≤ M := by omega
    have hqSucc : 3 ≤ N / (d + 1) :=
      (Nat.le_div_iff_mul_le (by omega : 0 < d + 1)).2 <| by
        have hMmul : 3 * M ≤ N := Nat.mul_div_le N 3
        have hmul : 3 * (d + 1) ≤ 3 * M := Nat.mul_le_mul_left 3 hsuccM
        omega
    have hqmul : (N / (d + 1)) * d ≤ N := by
      calc
        (N / (d + 1)) * d ≤ (N / (d + 1)) * (d + 1) :=
          Nat.mul_le_mul_left (N / (d + 1)) (by omega)
        _ ≤ N := Nat.div_mul_le_self N (d + 1)
    have hquot : N / (d + 1) ≤ N / d :=
      (Nat.le_div_iff_mul_le hdpos).2 hqmul
    exact nativeLogRecipDefect_antitone_three hqSucc hquot
  have hbound : ∀ d ∈ Finset.Icc 1 M, |b d| ≤ 4 := by
    intro d hd
    have hdI := Finset.mem_Icc.mp hd
    have hdpos : 0 < d := by omega
    have hq : 3 ≤ N / d :=
      (Nat.le_div_iff_mul_le hdpos).2 <| by
        have hMmul : 3 * M ≤ N := Nat.mul_div_le N 3
        have hmul : 3 * d ≤ 3 * M := Nat.mul_le_mul_left 3 hdI.2
        omega
    exact nativeLogRecipDefect_abs_le_four (N / d) hq
  have hprefixMass :
      |∑ d ∈ Finset.Icc 1 M, a d * b d| ≤ 12 := by
    have h := nativeAbelBoundMonotone a b M hM 4 (by norm_num) hprefix hmono hbound
    norm_num at h ⊢
    exact h
  have htailMass :
      |∑ d ∈ (Finset.Icc 1 N).filter (fun d => M < d), a d * b d| ≤ 3 := by
    calc
      |∑ d ∈ (Finset.Icc 1 N).filter (fun d => M < d), a d * b d| ≤
          ∑ d ∈ (Finset.Icc 1 N).filter (fun d => M < d), |a d * b d| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ (Finset.Icc 1 N).filter (fun d => M < d), 3 / (N : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdFilter := Finset.mem_filter.mp hd
        have hdI := Finset.mem_Icc.mp hdFilter.1
        have hdposNat : 0 < d := by omega
        have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdposNat
        have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hdposNat).2 hdI.2
        have hq2 : N / d ≤ 2 := nativeDiv_le_two_of_div_three_lt N d hdFilter.2
        have hb := nativeLogRecipDefect_abs_le_one_of_le_two (N / d) hq1 hq2
        have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
          have h := ArithmeticFunction.abs_moebius_le_one (n := d)
          calc
            |(ArithmeticFunction.moebius d : ℝ)| =
                ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) := by rw [Int.cast_abs]
            _ ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h
            _ = 1 := by norm_num
        have hMlt : N / 3 < d := hdFilter.2
        have hthreeN : (N : ℝ) < 3 * (d : ℝ) := by
          have hNat : N < 3 * d := by
            have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).1 hMlt
            simpa [Nat.mul_comm] using this
          exact_mod_cast hNat
        have hrecip : 1 / (d : ℝ) ≤ 3 / (N : ℝ) := by
          have hNNatPos : 0 < N := by omega
          have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNNatPos
          rw [div_le_div_iff₀ hdpos hNpos]
          nlinarith
        rw [abs_mul]
        have ha : |a d| ≤ 3 / (N : ℝ) := by
          simp only [a, abs_div, abs_of_pos hdpos]
          exact (div_le_div_of_nonneg_right hmu hdpos.le).trans hrecip
        exact mul_le_of_le_one_right (by positivity) hb |>.trans (by simpa using ha)
      _ ≤ (N : ℝ) * (3 / (N : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Finset.Icc 1 N).filter (fun d => M < d)).card ≤ N := by
          calc
            _ ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
            _ = N := by rw [Nat.card_Icc]; omega
        have hcast : (((Finset.Icc 1 N).filter (fun d => M < d)).card : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right hcast (by positivity)
      _ = 3 := by field_simp
  have hsplit :
      nativeMobiusLogRecipDefectMass N =
        (∑ d ∈ Finset.Icc 1 M, a d * b d) +
          ∑ d ∈ (Finset.Icc 1 N).filter (fun d => M < d), a d * b d := by
    have hlow :
        (Finset.Icc 1 N).filter (fun d => d ≤ M) = Finset.Icc 1 M := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hd1, _hdN⟩, hdM⟩
        exact ⟨hd1, hdM⟩
      · rintro ⟨hd1, hdM⟩
        exact ⟨⟨hd1, hdM.trans (Nat.div_le_self N 3)⟩, hdM⟩
    have hhigh :
        (Finset.Icc 1 N).filter (fun d => ¬ d ≤ M) =
          (Finset.Icc 1 N).filter (fun d => M < d) := by
      ext d
      simp [not_le]
    unfold nativeMobiusLogRecipDefectMass
    change (∑ d ∈ Finset.Icc 1 N, a d * b d) = _
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.Icc 1 N) (p := fun d => d ≤ M) (f := fun d => a d * b d),
      hlow, hhigh]
  rw [hsplit]
  exact (abs_add_le _ _).trans (by linarith)

/-- **Second logarithmic Möbius moment.**

The coefficient `2` is obtained from Mertens' first theorem and the finite
bounded-variation defect above; no PNT input occurs. -/
theorem nativeMobiusLogMomentTwo_sub_two_log_abs_le
    (N : ℕ) (hN : 3 ≤ N) :
    |nativeMobiusLogMomentTwo N - 2 * Real.log N| ≤
      2 * (Real.log 4 + 2) + 30 := by
  have hrel := nativeLambdaRecip_eq_half_momentTwo_add_defect N
  have hMertens := nativeLambdaRecip_sub_log_abs_le N (by omega : 1 ≤ N)
  have hdef := nativeMobiusLogRecipDefectMass_abs_le N hN
  have hrearrange :
      nativeMobiusLogMomentTwo N - 2 * Real.log N =
        2 * (nativeLambdaRecip N - Real.log N) -
          2 * nativeMobiusLogRecipDefectMass N := by
    linarith
  rw [hrearrange]
  calc
    |2 * (nativeLambdaRecip N - Real.log N) -
        2 * nativeMobiusLogRecipDefectMass N| ≤
      |2 * (nativeLambdaRecip N - Real.log N)| +
        |2 * nativeMobiusLogRecipDefectMass N| := abs_sub _ _
    _ = 2 * |nativeLambdaRecip N - Real.log N| +
        2 * |nativeMobiusLogRecipDefectMass N| := by
      simp [abs_mul]
    _ ≤ 2 * (Real.log 4 + 2) + 2 * 15 := by nlinarith
    _ = 2 * (Real.log 4 + 2) + 30 := by ring

end RHLean.Analysis
