import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelbergDepthFourInterval

/-!
# Reciprocal Fubini coordinate for the depth-four K2 interval

This module rewrites reciprocal prefix and interval sums of the true signed
second-Selberg kernel in the exact Möbius log-square divisor coordinate.  It is
the coordinate in which the depth-four wheel acts on the divisor variable.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Reciprocal Möbius log-square weight. -/
def nativeMobiusLogSquareRecipWeight (d : ℕ) : ℝ :=
  (μ : ArithmeticFunction ℝ) d * (Real.log (d : ℝ)) ^ 2 / (d : ℝ)

/-- Signed `K2/n` mass on the multiplicative interval `(N/M, N]`. -/
def nativePNTSignedK2RecipInterval (N M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc (N / M) N,
    nativePNTSignedSecondSelbergKernel n / (n : ℝ)

/-- Exact reciprocal Fubini formula for the signed second-Selberg prefix. -/
theorem nativePNTSignedSecondSelbergKernelRecipMass_eq_mobius_harmonic
    (N : ℕ) :
    nativePNTSignedSecondSelbergKernelRecipMass N =
      ∑ d ∈ Finset.Icc 1 N,
        nativeMobiusLogSquareRecipWeight d * (harmonic (N / d) : ℝ) := by
  unfold nativePNTSignedSecondSelbergKernelRecipMass
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
    (∑ n ∈ Finset.Icc 1 N,
        nativePNTSignedSecondSelbergKernel n / (n : ℝ)) =
      ∑ n ∈ Finset.Icc 1 N,
        ∑ d ∈ n.divisors,
          ((μ : ArithmeticFunction ℝ) d *
              (Real.log (d : ℝ)) ^ 2) / (n : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        rw [nativePNTSignedSecondSelbergKernel_eq_mobiusLogSquareDivisorSum n hn1,
          Finset.sum_div]
    _ = ∑ d ∈ Finset.Icc 1 N,
        ∑ n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x),
          ((μ : ArithmeticFunction ℝ) d *
              (Real.log (d : ℝ)) ^ 2) / (n : ℝ) := Finset.sum_comm' hmem
    _ = ∑ d ∈ Finset.Icc 1 N,
        nativeMobiusLogSquareRecipWeight d *
          ∑ m ∈ Finset.Icc 1 (N / d), 1 / (m : ℝ) := by
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
      · unfold nativeMobiusLogSquareRecipWeight
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
        have hdR0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
        have hmR0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
        rw [Nat.cast_mul]
        field_simp [hdR0, hmR0]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hdpos hab
    _ = ∑ d ∈ Finset.Icc 1 N,
        nativeMobiusLogSquareRecipWeight d * (harmonic (N / d) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [nativeRecipIcc_eq_harmonic]

end RHLean.Analysis
