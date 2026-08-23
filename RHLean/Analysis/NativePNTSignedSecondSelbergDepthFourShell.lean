import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelbergDepthFourFubini
import RHLean.Arithmetic.PrimeWheelFiniteDepthFrontier

/-!
# Exact factor-four shell for the signed second-Selberg reciprocal mass

The target interval `(N/4,N]` is first expressed as a difference of reciprocal
prefixes.  In the Möbius log-square coordinate this becomes a harmonic shell.
Under `N < 4 y^2`, every nonzero partial-wheel error divisor lies above `y^2`,
so it cannot occur in the lower prefix through `N/4`; at the upper endpoint its
reciprocal quotient is one of `1,2,3`.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Exact difference between the factor-four interval and reciprocal prefixes. -/
theorem nativePNTSignedK2RecipInterval_four_eq_prefix_sub
    (N : ℕ) :
    nativePNTSignedK2RecipInterval N 4 =
      nativePNTSignedSecondSelbergKernelRecipMass N -
        nativePNTSignedSecondSelbergKernelRecipMass (N / 4) := by
  unfold nativePNTSignedK2RecipInterval
    nativePNTSignedSecondSelbergKernelRecipMass
  have hsub : Finset.Icc 1 (N / 4) ⊆ Finset.Icc 1 N := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hn4⟩
    exact Finset.mem_Icc.mpr ⟨hn1, hn4.trans (Nat.div_le_self N 4)⟩
  have hset :
      Finset.Icc 1 N \ Finset.Icc 1 (N / 4) = Finset.Ioc (N / 4) N := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hs := Finset.sum_sdiff hsub
    (f := fun n => nativePNTSignedSecondSelbergKernel n / (n : ℝ))
  rw [hset] at hs
  linarith

/-- Harmonic shell attached to one Möbius divisor at factor four. -/
def nativePNTDepthFourHarmonicShell (N d : ℕ) : ℝ :=
  (harmonic (N / d) : ℝ) - (harmonic ((N / 4) / d) : ℝ)

/-- The lower-prefix harmonic sum can be extended through the upper endpoint:
all new terms vanish because their lower reciprocal quotient is zero. -/
theorem nativePNTDepthFour_lower_harmonic_sum_extend
    (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 (N / 4),
      nativeMobiusLogSquareRecipWeight d *
        (harmonic ((N / 4) / d) : ℝ)) =
      ∑ d ∈ Finset.Icc 1 N,
        nativeMobiusLogSquareRecipWeight d *
          (harmonic ((N / 4) / d) : ℝ) := by
  have hsub : Finset.Icc 1 (N / 4) ⊆ Finset.Icc 1 N := by
    intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hd1, hd4⟩
    exact Finset.mem_Icc.mpr ⟨hd1, hd4.trans (Nat.div_le_self N 4)⟩
  have hset :
      Finset.Icc 1 N \ Finset.Icc 1 (N / 4) = Finset.Ioc (N / 4) N := by
    ext d
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hzero :
      (∑ d ∈ Finset.Ioc (N / 4) N,
        nativeMobiusLogSquareRecipWeight d *
          (harmonic ((N / 4) / d) : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hgt : N / 4 < d := (Finset.mem_Ioc.mp hd).1
    have hdiv : (N / 4) / d = 0 := Nat.div_eq_of_lt hgt
    simp [hdiv]
  have hs := Finset.sum_sdiff hsub
    (f := fun d => nativeMobiusLogSquareRecipWeight d *
      (harmonic ((N / 4) / d) : ℝ))
  rw [hset, hzero, zero_add] at hs
  exact hs

/-- **Exact factor-four Fubini shell.** -/
theorem nativePNTSignedK2RecipInterval_four_eq_mobius_harmonic_shell
    (N : ℕ) :
    nativePNTSignedK2RecipInterval N 4 =
      ∑ d ∈ Finset.Icc 1 N,
        nativeMobiusLogSquareRecipWeight d *
          nativePNTDepthFourHarmonicShell N d := by
  rw [nativePNTSignedK2RecipInterval_four_eq_prefix_sub,
    nativePNTSignedSecondSelbergKernelRecipMass_eq_mobius_harmonic,
    nativePNTSignedSecondSelbergKernelRecipMass_eq_mobius_harmonic,
    nativePNTDepthFour_lower_harmonic_sum_extend]
  unfold nativePNTDepthFourHarmonicShell
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  ring_nf

/-- At depth four, a nonzero wheel-error divisor is absent from the lower
endpoint and has upper reciprocal quotient in `{1,2,3}`. -/
theorem partialPrimeWheel_nonzero_error_depth_four_shell
    (y N d : ℕ)
    (hscale : N < 4 * y ^ 2)
    (hd : d ∈ Finset.Icc 1 N)
    (herr : μ d - partialPrimeWheelSite y N d ≠ 0) :
    N / 4 < d ∧ 1 ≤ N / d ∧ N / d < 4 := by
  have hdI := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := by omega
  have hdepth := partialPrimeWheel_nonzero_error_div_lt_depth
    4 y N (by omega) hscale hdpos hdI.2 herr
  have hquot1 : 1 ≤ N / d :=
    (Nat.one_le_div_iff hdpos).2 hdI.2
  have hysq : y ^ 2 < d :=
    partialPrimeWheel_nonzero_error_unresolved_gt_sq
      y N hdpos hdI.2 herr |>.trans_le (by
        have ha0 : primeWheelResolvedPart y d ≠ 0 :=
          primeWheelResolvedPart_ne_zero y d
        have ha1 : 1 ≤ primeWheelResolvedPart y d :=
          Nat.one_le_iff_ne_zero.mpr ha0
        have hab := primeWheelResolvedPart_mul_unresolvedPart y (Nat.ne_of_gt hdpos)
        calc
          primeWheelUnresolvedPart y d =
              1 * primeWheelUnresolvedPart y d := by simp
          _ ≤ primeWheelResolvedPart y d * primeWheelUnresolvedPart y d :=
            Nat.mul_le_mul_right (primeWheelUnresolvedPart y d) ha1
          _ = d := hab)
  have hquarter : N / 4 < y ^ 2 := by
    exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 4)).2 (by
      simpa [Nat.mul_comm] using hscale)
  exact ⟨hquarter.trans hysq, hquot1, hdepth⟩

end RHLean.Analysis
