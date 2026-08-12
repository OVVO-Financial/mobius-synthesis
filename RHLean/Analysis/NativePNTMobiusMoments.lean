import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import RHLean.Analysis.NativePNTMertens

/-!
# Möbius logarithmic moments for the native Selberg route

The summatory identity

`sum_{n <= N} Lambda_2(n) = sum_{d <= N} mu(d) * S₂(floor(N/d))`

reduces Selberg's main term to reciprocal Möbius moments.  This module develops
those moments directly from finite convolution identities.  No PNT input or
zero-free argument is used.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Harmonic numbers as a positive-prefix real sum. -/
theorem nativeHarmonicReal_eq_sum_Icc (N : ℕ) :
    (harmonic N : ℝ) = ∑ m ∈ Finset.Icc 1 N, 1 / (m : ℝ) := by
  induction N with
  | zero => simp [harmonic_zero]
  | succ N ih =>
      rw [harmonic_succ, Rat.cast_add, ih,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      push_cast
      simp [one_div]

/-- Exact reciprocal convolution `mu * 1 = epsilon`, after dividing by the
endpoint.  This is the harmonic identity behind the first logarithmic Möbius
moment. -/
theorem nativeMobiusRecipHarmonic_eq_one
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
        (harmonic (N / d) : ℝ)) = 1 := by
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
    (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
          (harmonic (N / d) : ℝ)) =
        ∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x),
            (ArithmeticFunction.moebius d : ℝ) / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [nativeHarmonicReal_eq_sum_Icc, Finset.mul_sum]
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdpos : 0 < d := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hd1)
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
          have hmpos : 0 < m := by omega
          have hmulpos : 0 < d * m := Nat.mul_pos hdpos hmpos
          have hmulN' : m * d ≤ N := (Nat.le_div_iff_mul_le hdpos).1 hmN
          have hmulN : d * m ≤ N := by simpa [Nat.mul_comm] using hmulN'
          exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmulpos), hmulN⟩,
            dvd_mul_right d m⟩
      rw [hmap, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro m hm
        have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
        have hdR0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
        have hmR0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
        push_cast
        field_simp [hdR0, hmR0]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hdpos hab
    _ = ∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ n.divisors,
            (ArithmeticFunction.moebius d : ℝ) / (n : ℝ) :=
      (Finset.sum_comm' hmem).symm
    _ = ∑ n ∈ Finset.Icc 1 N,
          (if n = 1 then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnNatPos : 0 < n := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn1)
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnNatPos
      calc
        (∑ d ∈ n.divisors,
            (ArithmeticFunction.moebius d : ℝ) / (n : ℝ)) =
            (∑ d ∈ n.divisors,
              (ArithmeticFunction.moebius d : ℝ)) / (n : ℝ) := by
          rw [Finset.sum_div]
        _ = ((if n = 1 then (1 : ℤ) else 0 : ℤ) : ℝ) / (n : ℝ) := by
          rw [← Int.cast_sum, nativeSumMoebiusDivisors n hn1]
        _ = if n = 1 then (1 : ℝ) else 0 := by
          split_ifs with h
          · subst n
            norm_num
          · simp
    _ = 1 := by
      simp [Finset.sum_ite_eq', Finset.mem_Icc, hN]

/-- First logarithmic reciprocal Möbius moment. -/
def nativeMobiusLogMomentOne (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
      Real.log ((N / d : ℕ) : ℝ)

/-- Euler--Mascheroni remainder at an integer endpoint. -/
def nativeHarmonicLogError (q : ℕ) : ℝ :=
  (harmonic q : ℝ) - Real.log q - Real.eulerMascheroniConstant

private theorem nativeLogSucc_sub_log_le_inv
    (q : ℕ) (hq : 1 ≤ q) :
    Real.log ((q + 1 : ℕ) : ℝ) - Real.log (q : ℝ) ≤ 1 / (q : ℝ) := by
  have hqNatPos : 0 < q := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hq)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqNatPos
  have hsuccpos : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  have hratio :
      Real.log (((q + 1 : ℕ) : ℝ) / (q : ℝ)) =
        Real.log ((q + 1 : ℕ) : ℝ) - Real.log (q : ℝ) := by
    rw [Real.log_div (ne_of_gt hsuccpos) (ne_of_gt hqpos)]
  have h := Real.log_le_sub_one_of_pos
    (show 0 < (((q + 1 : ℕ) : ℝ) / (q : ℝ)) by positivity)
  rw [hratio] at h
  have hsub : (((q + 1 : ℕ) : ℝ) / (q : ℝ)) - 1 = 1 / (q : ℝ) := by
    push_cast
    field_simp [ne_of_gt hqpos]
    ring
  rw [hsub] at h
  exact h

/-- Explicit Euler--Mascheroni remainder bound
`0 <= H_q - log q - gamma <= 1/q`. -/
theorem nativeHarmonicLogError_bounds
    (q : ℕ) (hq : 1 ≤ q) :
    0 ≤ nativeHarmonicLogError q ∧
      nativeHarmonicLogError q ≤ 1 / (q : ℝ) := by
  have hupperGamma := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' q
  have hlowerGamma := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant q
  have hq0 : q ≠ 0 := Nat.one_le_iff_ne_zero.mp hq
  simp only [Real.eulerMascheroniSeq', hq0, if_false] at hupperGamma
  simp only [Real.eulerMascheroniSeq] at hlowerGamma
  have hinc := nativeLogSucc_sub_log_le_inv q hq
  have hinc' :
      Real.log ((q : ℝ) + 1) - Real.log (q : ℝ) ≤ 1 / (q : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using hinc
  unfold nativeHarmonicLogError
  constructor
  · linarith
  · have hstrict :
        (harmonic q : ℝ) - Real.log q - Real.eulerMascheroniConstant <
          Real.log ((q : ℝ) + 1) - Real.log (q : ℝ) := by
      linarith
    exact hstrict.le.trans hinc'

/-- Weighted Euler--Mascheroni remainder in the reciprocal Möbius identity. -/
def nativeMobiusHarmonicErrorMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
      nativeHarmonicLogError (N / d)

private theorem nativeReciprocalDivisorProduct_le_two_over
    (N d : ℕ) (hN : 1 ≤ N) (hd : d ∈ Finset.Icc 1 N) :
    (1 / (d : ℝ)) * (1 / ((N / d : ℕ) : ℝ)) ≤ 2 / (N : ℝ) := by
  have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hdpos : 0 < d := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hd1)
  have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).2 hdN
  have hrem : N % d < d := Nat.mod_lt N hdpos
  have hdle : d ≤ d * (N / d) := by
    simpa using Nat.mul_le_mul_left d hq1
  have hremle : N % d ≤ d * (N / d) :=
    (Nat.le_of_lt hrem).trans hdle
  have hdecomp := Nat.mod_add_div N d
  have hNat : N ≤ 2 * (d * (N / d)) := by
    calc
      N = N % d + d * (N / d) := hdecomp.symm
      _ ≤ d * (N / d) + d * (N / d) := Nat.add_le_add_right hremle _
      _ = 2 * (d * (N / d)) := by omega
  have hReal : (N : ℝ) ≤ 2 * ((d : ℝ) * ((N / d : ℕ) : ℝ)) := by
    exact_mod_cast hNat
  have hNNatPos : 0 < N := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNNatPos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hqNatPos : 0 < N / d := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hq1)
  have hqR : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by exact_mod_cast hqNatPos
  calc
    (1 / (d : ℝ)) * (1 / ((N / d : ℕ) : ℝ)) =
        1 / ((d : ℝ) * ((N / d : ℕ) : ℝ)) := by
      field_simp [ne_of_gt hdR, ne_of_gt hqR]
    _ ≤ 2 / (N : ℝ) := by
      rw [div_le_div_iff₀ (mul_pos hdR hqR) hNpos]
      nlinarith [hReal]

/-- The accumulated harmonic remainder remains uniformly bounded despite the
hyperbolic reciprocal fibres. -/
theorem nativeMobiusHarmonicErrorMass_abs_le_two
    (N : ℕ) (hN : 1 ≤ N) :
    |nativeMobiusHarmonicErrorMass N| ≤ 2 := by
  unfold nativeMobiusHarmonicErrorMass
  calc
    |∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
          nativeHarmonicLogError (N / d)| ≤
        ∑ d ∈ Finset.Icc 1 N,
          |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
            nativeHarmonicLogError (N / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 N, 2 / (N : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdNatPos : 0 < d := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hd1)
      have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdNatPos
      have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hdNatPos).2 hdN
      have herr := nativeHarmonicLogError_bounds (N / d) hq1
      have hmu0 : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := d)
        calc
          |(ArithmeticFunction.moebius d : ℝ)| =
              ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) := by rw [Int.cast_abs]
          _ ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h
          _ = 1 := by norm_num
      have hterm :
          |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
              nativeHarmonicLogError (N / d)| ≤
            (1 / (d : ℝ)) * (1 / ((N / d : ℕ) : ℝ)) := by
        rw [abs_mul, abs_div, abs_of_nonneg herr.1,
          abs_of_pos hdpos]
        have hdiv : |(ArithmeticFunction.moebius d : ℝ)| / (d : ℝ) ≤
            1 / (d : ℝ) := div_le_div_of_nonneg_right hmu0 hdpos.le
        exact mul_le_mul hdiv herr.2 herr.1 (by positivity)
      exact hterm.trans (nativeReciprocalDivisorProduct_le_two_over N d hN hd)
    _ = ((Finset.Icc 1 N).card : ℝ) * (2 / (N : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 := by
      rw [Nat.card_Icc]
      have hcard : N + 1 - 1 = N := by omega
      rw [hcard]
      have hNNatPos : 0 < N := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN)
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNNatPos)
      field_simp

/-- Exact decomposition of the first logarithmic Möbius moment. -/
theorem nativeMobiusLogMomentOne_eq
    (N : ℕ) (hN : 1 ≤ N) :
    nativeMobiusLogMomentOne N =
      1 - Real.eulerMascheroniConstant * nativeMertensRecip N -
        nativeMobiusHarmonicErrorMass N := by
  have hexact := nativeMobiusRecipHarmonic_eq_one N hN
  unfold nativeMobiusLogMomentOne nativeMertensRecip
  unfold nativeMobiusHarmonicErrorMass nativeHarmonicLogError
  have hsplit :
      (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
          (harmonic (N / d) : ℝ)) =
      (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
          Real.log ((N / d : ℕ) : ℝ)) +
      Real.eulerMascheroniConstant *
        (∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) +
      (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
          ((harmonic (N / d) : ℝ) - Real.log ((N / d : ℕ) : ℝ) -
            Real.eulerMascheroniConstant)) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  rw [hsplit] at hexact
  linarith

/-- Uniform first logarithmic Möbius moment. -/
theorem nativeMobiusLogMomentOne_abs_le_four
    (N : ℕ) (hN : 1 ≤ N) :
    |nativeMobiusLogMomentOne N| ≤ 4 := by
  rw [nativeMobiusLogMomentOne_eq N hN]
  have hM := nativeMertensRecip_abs_le_one N
  have hE := nativeMobiusHarmonicErrorMass_abs_le_two N hN
  have hgammaPos : 0 ≤ Real.eulerMascheroniConstant :=
    (Real.one_half_lt_eulerMascheroniConstant).le.trans' (by norm_num)
  have hgamma : Real.eulerMascheroniConstant ≤ 1 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  calc
    |1 - Real.eulerMascheroniConstant * nativeMertensRecip N -
        nativeMobiusHarmonicErrorMass N| ≤
      |(1 : ℝ)| +
        |Real.eulerMascheroniConstant * nativeMertensRecip N| +
        |nativeMobiusHarmonicErrorMass N| := by
      calc
        |1 - Real.eulerMascheroniConstant * nativeMertensRecip N -
            nativeMobiusHarmonicErrorMass N| ≤
          |1 - Real.eulerMascheroniConstant * nativeMertensRecip N| +
            |nativeMobiusHarmonicErrorMass N| := abs_sub _ _
        _ ≤ (|(1 : ℝ)| +
            |Real.eulerMascheroniConstant * nativeMertensRecip N|) +
            |nativeMobiusHarmonicErrorMass N| := by
          gcongr
          exact abs_sub _ _
    _ ≤ 1 + 1 + 2 := by
      rw [abs_one, abs_mul, abs_of_nonneg hgammaPos]
      nlinarith [abs_nonneg (nativeMertensRecip N)]
    _ = 4 := by norm_num

end RHLean.Analysis
