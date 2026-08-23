import Mathlib
import RHLean.Analysis.NativePNTAxer
import RHLean.Analysis.NativePNTLambdaRecipInterval
import RHLean.Analysis.NativePNTMobiusMoments
import RHLean.Analysis.NativePNTSignedSecondSelbergFactorFourDyadic

/-!
# Low-degree reciprocal Mobius moments for the factor-four K2 fold

After the exact prime-two fold, the correction channel contains only degree-zero
and degree-one logarithmic Mobius weights. This file identifies the degree-one
harmonic prefix exactly with the negative reciprocal von-Mangoldt prefix.

No PNT input is used in this identity.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- First logarithmic Mobius weight against a harmonic reciprocal fibre. -/
def nativeMobiusLogRecipHarmonic (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (μ : ArithmeticFunction ℝ) d * Real.log (d : ℝ) / (d : ℝ) *
      (harmonic (N / d) : ℝ)

/-- Logarithmic differentiation of `mu * zeta = 1`, followed by multiplication
by zeta, gives `(D mu) * zeta = -Lambda`. -/
theorem arithmeticLogWeight_moebius_mul_zeta_eq_neg_vonMangoldt :
    arithmeticLogWeight (μ : ArithmeticFunction ℝ) *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) =
      -(Λ : ArithmeticFunction ℝ) := by
  rw [arithmeticLogWeight_moebius]
  calc
    -((μ : ArithmeticFunction ℝ) * Λ) *
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) =
        -(((μ : ArithmeticFunction ℝ) *
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) * Λ) := by
      ring
    _ = -(Λ : ArithmeticFunction ℝ) := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
      simp

/-- Exact coefficient form of `(D mu) * zeta = -Lambda`. -/
theorem sum_moebius_log_divisors_eq_neg_vonMangoldt
    (n : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ n.divisors,
      (μ : ArithmeticFunction ℝ) d * Real.log (d : ℝ)) = -Λ n := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have h := congrArg
    (fun f : ArithmeticFunction ℝ => f n)
    arithmeticLogWeight_moebius_mul_zeta_eq_neg_vonMangoldt
  change
    (arithmeticLogWeight (μ : ArithmeticFunction ℝ) *
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) n =
        (-(Λ : ArithmeticFunction ℝ)) n at h
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun a b =>
        arithmeticLogWeight (μ : ArithmeticFunction ℝ) a *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) b))] at h
  simp [arithmeticLogWeight_apply] at h
  calc
    (∑ x ∈ n.divisors,
        (μ : ArithmeticFunction ℝ) x * Real.log (x : ℝ)) =
      ∑ x ∈ n.divisors,
        if x = 0 ∨ n < x then 0
        else (μ : ArithmeticFunction ℝ) x * Real.log (x : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxmem := Nat.mem_divisors.mp hx
      have hxdiv : x ∣ n := hxmem.1
      have hx0 : x ≠ 0 := by
        intro hxz
        subst x
        have hnz : n = 0 := Nat.eq_zero_of_zero_dvd hxdiv
        exact hn0 hnz
      have hxle : x ≤ n := Nat.le_of_dvd (by omega) hxdiv
      simp [hx0, not_lt_of_ge hxle]
    _ = -Λ n := by simpa using h

/-- **First logarithmic reciprocal Mobius harmonic identity.**

`sum_{d<=N} mu(d) log(d)/d * H_floor(N/d) = -sum_{n<=N} Lambda(n)/n`.
-/
theorem nativeMobiusLogRecipHarmonic_eq_neg_lambdaRecip
    (N : ℕ) :
    nativeMobiusLogRecipHarmonic N = -nativeLambdaRecip N := by
  unfold nativeMobiusLogRecipHarmonic nativeLambdaRecip
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
    (∑ d ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) d * Real.log (d : ℝ) / (d : ℝ) *
          (harmonic (N / d) : ℝ)) =
      ∑ d ∈ Finset.Icc 1 N,
        ∑ n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x),
          ((μ : ArithmeticFunction ℝ) d * Real.log (d : ℝ)) / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [nativeHarmonicReal_eq_sum_Icc, Finset.mul_sum]
      have hdpos : 0 < d := by
        have hd1 := (Finset.mem_Icc.mp hd).1
        omega
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
          ((μ : ArithmeticFunction ℝ) d * Real.log (d : ℝ)) / (n : ℝ) :=
      (Finset.sum_comm' hmem).symm
    _ = ∑ n ∈ Finset.Icc 1 N, (-Λ n) / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 := (Finset.mem_Icc.mp hn).1
      rw [← Finset.sum_div, sum_moebius_log_divisors_eq_neg_vonMangoldt n hn1]
    _ = -(∑ n ∈ Finset.Icc 1 N, Λ n / (n : ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n _hn
      ring

end RHLean.Analysis
