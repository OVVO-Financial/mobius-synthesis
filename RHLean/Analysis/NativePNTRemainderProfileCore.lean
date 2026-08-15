import Mathlib
import RHLean.Analysis.NativePNTErrorMass

/-!
# Exact remainder profiles for the native PNT recurrence

The quantitative contraction should not freeze finite Selberg losses into one
universal constant before iteration.  This module keeps the first recurrence
in profile form: the endpoint Selberg defect and factorial defect remain the
actual remainder at the current scale.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- First-von-Mangoldt absolute error mass. -/
def nativeLambdaErrorMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|

/-- Push an arbitrary endpoint remainder profile through the reciprocal
von-Mangoldt fibres.  This is the term produced by self-composition. -/
def nativeLambdaRemainderMass (R : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, Λ d * R (N / d)

/-- A scale-dependent remainder profile for the one-log Selberg recurrence. -/
def NativePNTOneLogRemainderProfile (R : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    |nativePNTError N| * Real.log (N : ℝ) ≤
      nativeLambdaErrorMass N + R N

/-- The exact non-recursive remainder left by the signed Selberg decomposition.
No universal numerical majorant has yet been applied. -/
def nativePNTFirstRemainder (N : ℕ) : ℝ :=
  |nativeSelbergPair N - 2 * (N : ℝ) * Real.log (N : ℝ)| +
    |Real.log ((Nat.factorial N : ℕ) : ℝ) -
      (N : ℝ) * Real.log (N : ℝ)|

/-- The native one-log PNT recurrence with its actual scale-dependent
remainder.  This is the non-frozen version of the existing constant-coefficient
Selberg recurrence. -/
theorem nativePNTError_abs_log_le_firstRemainder
    (N : ℕ) (hN : 1 ≤ N) :
    |nativePNTError N| * Real.log (N : ℝ) ≤
      nativeLambdaErrorMass N + nativePNTFirstRemainder N := by
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hdecomp := nativePNTError_selberg_decomposition N
  have hsum :
      |∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)| ≤
        nativeLambdaErrorMass N := by
    unfold nativeLambdaErrorMass
    calc
      |∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)| ≤
          ∑ d ∈ Finset.Icc 1 N,
            |Λ d * nativePNTError (N / d)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ d ∈ Finset.Icc 1 N,
            Λ d * |nativePNTError (N / d)| := by
        apply Finset.sum_congr rfl
        intro d _hd
        rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hAeq :
      nativePNTError N * Real.log (N : ℝ) =
        (nativeSelbergPair N - 2 * (N : ℝ) * Real.log (N : ℝ)) -
          (∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)) -
          (Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log (N : ℝ)) := by
    linarith [hdecomp]
  have htri :
      |nativePNTError N * Real.log (N : ℝ)| ≤
        |nativeSelbergPair N - 2 * (N : ℝ) * Real.log (N : ℝ)| +
          |∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)| +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log (N : ℝ)| := by
    rw [hAeq]
    calc
      |(nativeSelbergPair N - 2 * (N : ℝ) * Real.log (N : ℝ)) -
          (∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)) -
          (Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log (N : ℝ))| ≤
        |(nativeSelbergPair N - 2 * (N : ℝ) * Real.log (N : ℝ)) -
          (∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d))| +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log (N : ℝ)| := abs_sub _ _
      _ ≤
        (|nativeSelbergPair N - 2 * (N : ℝ) * Real.log (N : ℝ)| +
          |∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)|) +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log (N : ℝ)| := by
        gcongr
        exact abs_sub _ _
  have hmain :
      |nativePNTError N * Real.log (N : ℝ)| ≤
        nativeLambdaErrorMass N + nativePNTFirstRemainder N := by
    calc
      |nativePNTError N * Real.log (N : ℝ)| ≤
        |nativeSelbergPair N - 2 * (N : ℝ) * Real.log (N : ℝ)| +
          |∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)| +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log (N : ℝ)| := htri
      _ ≤
        |nativeSelbergPair N - 2 * (N : ℝ) * Real.log (N : ℝ)| +
          nativeLambdaErrorMass N +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log (N : ℝ)| := by
        gcongr
      _ = nativeLambdaErrorMass N + nativePNTFirstRemainder N := by
        unfold nativePNTFirstRemainder
        ring
  simpa [abs_mul, abs_of_nonneg hlog0] using hmain

/-- The canonical exact first remainder is itself a valid recurrence profile. -/
theorem nativePNTFirstRemainder_profile :
    NativePNTOneLogRemainderProfile nativePNTFirstRemainder := by
  intro N hN
  exact nativePNTError_abs_log_le_firstRemainder N hN

/-- The old fixed linear coefficient is only a majorant of the exact first
remainder.  It is retained as a specialization, not built into the profile
recurrence itself. -/
theorem nativePNTFirstRemainder_le_linear
    (N : ℕ) (hN : 3 ≤ N) :
    nativePNTFirstRemainder N ≤
      (3 * (Real.log 4 + 2) + 173) * (N : ℝ) := by
  have hsel := nativeSelbergPair_sub_two_mul_log_abs_le N hN
  have hfac := nativeLogFactorial_sub_Nlog_abs_le N (by omega)
  unfold nativePNTFirstRemainder
  calc
    |nativeSelbergPair N - 2 * (N : ℝ) * Real.log (N : ℝ)| +
        |Real.log ((Nat.factorial N : ℕ) : ℝ) -
          (N : ℝ) * Real.log (N : ℝ)| ≤
      (3 * (Real.log 4 + 2) + 172) * (N : ℝ) + (N : ℝ) :=
        add_le_add hsel hfac
    _ = (3 * (Real.log 4 + 2) + 173) * (N : ℝ) := by ring

end RHLean.Analysis
