import Mathlib
import RHLean.Analysis.RamanujanDivisorBoundaryBulk

/-!
# Upper-divisor Möbius cancellation

For positive divisors `d | D`, the interval of divisors `d | q | D` is
canonically the divisor set of `D / d`.  Reindexing the Möbius sum through this
bijection gives the upper-divisor Kronecker delta

`sum_{d | q | D} mu(q / d) = 1_(d = D)`.

This is the finite cancellation needed to Möbius-reindex the full conductor
family before taking any norm.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Divisors of `D` that are multiples of `d` are exactly `d` times the
divisors of `D / d`. -/
private theorem upperDivisors_eq_image
    {d D : ℕ} (hd : d ∣ D) (hD : D ≠ 0) :
    D.divisors.filter (fun q => d ∣ q) =
      (D / d).divisors.image (fun r => d * r) := by
  classical
  ext q
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
  constructor
  · rintro ⟨⟨hqD, _⟩, hdq⟩
    have hquotD : D / d ≠ 0 := by
      intro hzero
      have hprod : d * (D / d) = D := Nat.mul_div_cancel' hd
      rw [hzero, mul_zero] at hprod
      exact hD hprod.symm
    refine ⟨q / d, ⟨?_, hquotD⟩, ?_⟩
    · apply (Nat.dvd_div_iff_mul_dvd hd).2
      simpa [Nat.mul_div_cancel' hdq] using hqD
    · exact Nat.mul_div_cancel' hdq
  · rintro ⟨r, ⟨hr, _⟩, rfl⟩
    exact ⟨⟨(Nat.dvd_div_iff_mul_dvd hd).1 hr, hD⟩, dvd_mul_right d r⟩

/-- Upper-divisor Möbius inversion in integer form. -/
theorem sum_moebius_upper_divisors_eq_one_or_zero
    {d D : ℕ} (hd : d ∣ D) (hdpos : 0 < d) (hD : D ≠ 0) :
    (∑ q ∈ D.divisors, if d ∣ q then μ (q / d) else 0) =
      if d = D then 1 else 0 := by
  classical
  rw [← Finset.sum_filter]
  rw [upperDivisors_eq_image hd hD]
  have hinj :
      Set.InjOn (fun r : ℕ => d * r) ((D / d).divisors : Set ℕ) := by
    intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hdpos hab
  rw [Finset.sum_image hinj]
  simp_rw [Nat.mul_div_cancel_left _ hdpos]
  rw [sum_moebius_divisors_eq_one_or_zero]
  by_cases hEq : d = D
  · subst D
    rw [Nat.div_self hdpos]
    simp
  · have hquot : D / d ≠ 1 := by
      intro h
      have hprod : d * (D / d) = D := Nat.mul_div_cancel' hd
      rw [h] at hprod
      have : d = D := by simpa using hprod
      exact hEq this
    simp [hEq, hquot]

/-- The same upper-divisor Möbius delta after casting to `ℂ`, ready for the
Fourier-side conductor coefficients. -/
theorem sum_complex_moebius_upper_divisors_eq_one_or_zero
    {d D : ℕ} (hd : d ∣ D) (hdpos : 0 < d) (hD : D ≠ 0) :
    (∑ q ∈ D.divisors,
      if d ∣ q then (((μ (q / d) : ℤ) : ℂ)) else 0) =
        if d = D then 1 else 0 := by
  exact_mod_cast sum_moebius_upper_divisors_eq_one_or_zero hd hdpos hD

/-- Ambient-modulus form used by conductor tails.  If `D | N`, restricting the
sum over divisors of `N` to those that also divide `D` recovers the same
upper-divisor Möbius delta. -/
theorem sum_complex_moebius_upper_divisors_ambient_eq_one_or_zero
    {d D N : ℕ} (hDN : D ∣ N) (hN : N ≠ 0) (hdpos : 0 < d) :
    (∑ q ∈ N.divisors,
      if d ∣ q then
        if q ∣ D then (((μ (q / d) : ℤ) : ℂ)) else 0
      else 0) =
        if d = D then 1 else 0 := by
  classical
  by_cases hdD : d ∣ D
  · have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hN hDN
    calc
      (∑ q ∈ N.divisors,
        if d ∣ q then
          if q ∣ D then (((μ (q / d) : ℤ) : ℂ)) else 0
        else 0) =
        ∑ q ∈ N.divisors,
          if q ∣ D then
            (if d ∣ q then (((μ (q / d) : ℤ) : ℂ)) else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            by_cases hdq : d ∣ q <;> by_cases hqD : q ∣ D <;>
              simp [hdq, hqD]
      _ =
        ∑ q ∈ N.divisors.filter (fun q => q ∣ D),
          if d ∣ q then (((μ (q / d) : ℤ) : ℂ)) else 0 := by
            rw [Finset.sum_filter]
      _ =
        ∑ q ∈ D.divisors,
          if d ∣ q then (((μ (q / d) : ℤ) : ℂ)) else 0 := by
            rw [Nat.divisors_filter_dvd_of_dvd hN hDN]
      _ = if d = D then 1 else 0 :=
        sum_complex_moebius_upper_divisors_eq_one_or_zero hdD hdpos hD
  · have hne : d ≠ D := by
      intro h
      exact hdD (h ▸ dvd_rfl)
    rw [if_neg hne]
    apply Finset.sum_eq_zero
    intro q hq
    by_cases hdq : d ∣ q
    · have hnqD : ¬q ∣ D := by
        intro hqD
        exact hdD (dvd_trans hdq hqD)
      simp [hdq, hnqD]
    · simp [hdq]

end RHLean.Analysis
