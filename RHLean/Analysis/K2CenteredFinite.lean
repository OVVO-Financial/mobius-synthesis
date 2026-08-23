import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import RHLean.Analysis.NativePNTSignedSecondSelbergDepthFourFubini

/-!
# Finite core of the centered reciprocal signed K2 theorem

This file contains only finite identities. It uses this package for the discovered
coefficient and the Fubini identity, but none of the RH proof architecture. The
subsequent analytic proof is classical.

There are no `sorry`s and no axioms in this file.
-/

noncomputable section
open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

local notation "γE" => Real.eulerMascheroniConstant

/-- Raw second reciprocal Möbius logarithmic prefix. -/
def k2A2 (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, nativeMobiusLogSquareRecipWeight d

/-- Raw third reciprocal Möbius logarithmic prefix. -/
def k2C3 (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    nativeMobiusLogSquareRecipWeight d * Real.log (d : ℝ)

/-- Centered second reciprocal Möbius prefix. -/
def k2r (N : ℕ) : ℝ := k2A2 N + 2 * γE

/-- Generic Abel summation on `Icc 1 N`. -/
theorem k2_abel_Icc_one
    (a b : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, a n * b n) =
      (∑ n ∈ Finset.Icc 1 N, a n) * b N +
        ∑ n ∈ Finset.Ico 1 N,
          (∑ k ∈ Finset.Icc 1 n, a k) * (b n - b (n + 1)) := by
  simpa using nativeAbelIccOne a b N

/-- The raw cube prefix is `Σ μ(n) log(n)^3 / n`. -/
theorem k2C3_eq (N : ℕ) :
    k2C3 N =
      ∑ d ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) d * (Real.log (d : ℝ)) ^ 3 / (d : ℝ) := by
  unfold k2C3 nativeMobiusLogSquareRecipWeight
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Finite logarithmic telescope. -/
theorem k2_log_telescope (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N,
      (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))) =
      -Real.log (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN, ih]
      ring

/-- First centered Abel identity:

`C3(N) = r(N) log N + Σ_{n<N} r(n)(log n - log(n+1))`.
-/
theorem k2C3_centered_abel (N : ℕ) (hN : 1 ≤ N) :
    k2C3 N =
      k2r N * Real.log (N : ℝ) +
        ∑ n ∈ Finset.Ico 1 N,
          k2r n *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)) := by
  unfold k2C3 k2r k2A2
  rw [k2_abel_Icc_one]
  have htel := k2_log_telescope N hN
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, htel]
  ring

/-- The harmonic reciprocal quotient kernel. -/
def k2H (N d : ℕ) : ℝ := (harmonic (N / d) : ℝ)

/-- Exact K2 reciprocal prefix as the discovered Möbius-harmonic hyperbola sum. -/
theorem k2F_eq_hyperbola (N : ℕ) :
    nativePNTSignedSecondSelbergKernelRecipMass N =
      ∑ d ∈ Finset.Icc 1 N,
        nativeMobiusLogSquareRecipWeight d * k2H N d := by
  simpa [k2H] using
    nativePNTSignedSecondSelbergKernelRecipMass_eq_mobius_harmonic N

/-- Generic finite difference telescope on `Ico 1 N`. -/
theorem k2_diff_telescope (b : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Ico 1 N, (b d - b (d + 1))) = b 1 - b N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN, ih]
      ring

/-- Harmonic quotient telescope. -/
theorem k2H_telescope (N : ℕ) (hN : 1 ≤ N) :
    k2H N N +
      ∑ d ∈ Finset.Ico 1 N, (k2H N d - k2H N (d + 1)) =
      (harmonic N : ℝ) := by
  rw [k2_diff_telescope (k2H N) N hN]
  simp [k2H]

/-- Second centered Abel identity:

`F(N)+2γH_N = r(N) + Σ_{d<N} r(d)(H_{N/d}-H_{N/(d+1)})`.
-/
theorem k2F_centered_abel (N : ℕ) (hN : 1 ≤ N) :
    nativePNTSignedSecondSelbergKernelRecipMass N +
        2 * γE * (harmonic N : ℝ) =
      k2r N * k2H N N +
        ∑ d ∈ Finset.Ico 1 N,
          k2r d * (k2H N d - k2H N (d + 1)) := by
  rw [k2F_eq_hyperbola]
  unfold k2r k2A2
  rw [k2_abel_Icc_one]
  have ht := k2H_telescope N hN
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  rw [← ht]
  rw [mul_add, Finset.mul_sum]
  ring

end RHLean.Analysis
