import Mathlib
import RHLean.Analysis.NativePNTAxer
import RHLean.Analysis.NativePNTSignedSecondSelbergReciprocal
import RHLean.Analysis.NativePNTSignedSecondSelbergWheelFrontier
import RHLean.Arithmetic.PrimeWheelFiniteDepthSemiprime

/-!
# Depth-four interval attack for the signed second Selberg kernel

This module targets the scale-local estimate

`|sum_{N/M < n <= N} K2(n)/n| <= C log M`

with the physical depth specialized first to `M = 4`.  The target is not
asserted until it is proved.  The lemmas below expose the exact Möbius
log-square derivative and the finite-depth wheel support needed by the proof.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

private def zetaR : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)

/-- Pointwise log-square derivative of Möbius. -/
def nativeMobiusLogSquareWeight : ArithmeticFunction ℝ :=
  arithmeticLogWeight (arithmeticLogWeight (μ : ArithmeticFunction ℝ))

@[simp] theorem nativeMobiusLogSquareWeight_apply (n : ℕ) :
    nativeMobiusLogSquareWeight n =
      (μ : ArithmeticFunction ℝ) n * (Real.log (n : ℝ)) ^ 2 := by
  simp [nativeMobiusLogSquareWeight, arithmeticLogWeight_apply]
  ring_nf

private theorem arithmeticLogWeight_neg_local (f : ArithmeticFunction ℝ) :
    arithmeticLogWeight (-f) = -arithmeticLogWeight f := by
  ext n
  change (-f n) * Real.log (n : ℝ) = -(f n * Real.log (n : ℝ))
  ring_nf

/-- The second logarithmic derivative of Möbius, after multiplying by zeta,
is exactly the true signed second-Selberg kernel as an arithmetic function. -/
theorem nativeMobiusLogSquareWeight_mul_zeta_eq_signedKernel :
    nativeMobiusLogSquareWeight * zetaR =
      Λ * Λ - arithmeticLogWeight Λ := by
  have hD2 :
      nativeMobiusLogSquareWeight =
        (μ : ArithmeticFunction ℝ) *
          (Λ * Λ - arithmeticLogWeight Λ) := by
    unfold nativeMobiusLogSquareWeight
    rw [arithmeticLogWeight_moebius,
      arithmeticLogWeight_neg_local,
      arithmeticLogWeight_mul,
      arithmeticLogWeight_moebius]
    ring_nf
  rw [hD2]
  calc
    (μ : ArithmeticFunction ℝ) *
          (Λ * Λ - arithmeticLogWeight Λ) * zetaR =
        ((μ : ArithmeticFunction ℝ) * zetaR) *
          (Λ * Λ - arithmeticLogWeight Λ) := by ring_nf
    _ = Λ * Λ - arithmeticLogWeight Λ := by
      dsimp [zetaR]
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
      simp

/-- **Exact Möbius-square form of the signed kernel.**  For positive `n`,

`K2(n) = sum_{d|n} mu(d) log(d)^2`.

This is the finite coefficient identity behind the depth-four interval
reindexing. -/
theorem nativePNTSignedSecondSelbergKernel_eq_mobiusLogSquareDivisorSum
    (n : ℕ) (hn : 1 ≤ n) :
    nativePNTSignedSecondSelbergKernel n =
      ∑ d ∈ n.divisors,
        (μ : ArithmeticFunction ℝ) d * (Real.log (d : ℝ)) ^ 2 := by
  have hfun := congrArg (fun f : ArithmeticFunction ℝ => f n)
    nativeMobiusLogSquareWeight_mul_zeta_eq_signedKernel
  have hn0 : n ≠ 0 := by omega
  change
    (nativeMobiusLogSquareWeight * zetaR) n =
      (Λ * Λ - arithmeticLogWeight Λ) n at hfun
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun a b => nativeMobiusLogSquareWeight a * zetaR b)] at hfun
  have hlhs :
      (∑ d ∈ n.divisors,
        nativeMobiusLogSquareWeight d * zetaR (n / d)) =
      ∑ d ∈ n.divisors,
        (μ : ArithmeticFunction ℝ) d * (Real.log (d : ℝ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro d hd
    have hq0 : n / d ≠ 0 := by
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hdpos)
    rw [nativeMobiusLogSquareWeight_apply]
    change
      (μ : ArithmeticFunction ℝ) d * (Real.log (d : ℝ)) ^ 2 *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
            (n / d)) = _
    rw [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hq0]
    ring_nf
  rw [hlhs] at hfun
  have hrhs :
      (Λ * Λ - arithmeticLogWeight Λ) n =
        nativePNTSignedSecondSelbergKernel n := by
    change (Λ * Λ) n - Λ n * Real.log (n : ℝ) =
      nativePNTSignedSecondSelbergKernel n
    rfl
  rw [hrhs] at hfun
  exact hfun.symm

end RHLean.Analysis
