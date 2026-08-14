import Mathlib
import RHLean.Analysis.NativePNTRemainderProfileCore

/-!
# Self-composition of native PNT remainder profiles

This module performs the second Selberg composition without replacing the
current remainder by a universal linear constant.  The new remainder is the
sum of three evolving terms: the first-von-Mangoldt error mass, the reciprocal
pushforward of the previous remainder profile, and the endpoint remainder
multiplied by the current logarithm.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Exact logarithmic splitting needed on one reciprocal floor fibre. -/
theorem nativePNTProfile_log_le_log_divisor_add_floor_add_one
    (N d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
    Real.log (N : ℝ) ≤
      Real.log (d : ℝ) + Real.log ((N / d : ℕ) : ℝ) + 1 := by
  have hdI := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := by omega
  have hNpos : 0 < N := lt_of_lt_of_le hdpos hdI.2
  have hq1 : 1 ≤ N / d :=
    (Nat.one_le_div_iff hdpos).2 hdI.2
  have hdivmod : d * (N / d) + N % d = N := Nat.div_add_mod N d
  have hrem : N % d < d := Nat.mod_lt N hdpos
  have hlt : N < d * (N / d + 1) := by
    calc
      N = d * (N / d) + N % d := hdivmod.symm
      _ < d * (N / d) + d := Nat.add_lt_add_left hrem _
      _ = d * (N / d + 1) := by ring
  have hlogprod :
      Real.log (N : ℝ) ≤ Real.log ((d * (N / d + 1) : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hNpos
    · exact_mod_cast (Nat.le_of_lt hlt)
  have hdR0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
  have hprodlog :
      Real.log ((d * (N / d + 1) : ℕ) : ℝ) =
        Real.log (d : ℝ) + Real.log ((N / d + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [Real.log_mul hdR0 (by positivity)]
  rw [hprodlog] at hlogprod
  have hinc := nativeLog_succ_sub_log_le_inv (N / d) hq1
  have hqposR : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < N / d by omega)
  have hrecip : (1 : ℝ) / ((N / d : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hqposR]
    exact_mod_cast hq1
  linarith

/-- Self-composition of an arbitrary one-log remainder profile.  No Chebyshev
constant and no frozen Selberg constant is used: every finite loss remains an
explicit current-scale mass. -/
theorem nativeLambdaErrorMass_mul_log_le_lambdaTwo_add_profile
    (R : ℕ → ℝ) (hR : NativePNTOneLogRemainderProfile R)
    (N : ℕ) :
    nativeLambdaErrorMass N * Real.log (N : ℝ) ≤
      nativeLambdaTwoErrorMass N + nativeLambdaErrorMass N +
        nativeLambdaRemainderMass R N := by
  have hpoint : ∀ d ∈ Finset.Icc 1 N,
      Λ d * |nativePNTError (N / d)| * Real.log (N : ℝ) ≤
        Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
          (∑ m ∈ Finset.Icc 1 (N / d),
            Λ d * Λ m * |nativePNTError (N / (d * m))|) +
          Λ d * |nativePNTError (N / d)| +
          Λ d * R (N / d) := by
    intro d hd
    have hdI := Finset.mem_Icc.mp hd
    have hdpos : 0 < d := by omega
    have hq1 : 1 ≤ N / d :=
      (Nat.one_le_div_iff hdpos).2 hdI.2
    have hcoef0 : 0 ≤ Λ d * |nativePNTError (N / d)| :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (abs_nonneg _)
    have hlogsplit :=
      nativePNTProfile_log_le_log_divisor_add_floor_add_one N d hd
    have hfirst := hR (N / d) hq1
    have hfirstMul :
        Λ d * (|nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ)) ≤
          Λ d * (nativeLambdaErrorMass (N / d) + R (N / d)) :=
      mul_le_mul_of_nonneg_left hfirst ArithmeticFunction.vonMangoldt_nonneg
    have hfirstMul' :
        Λ d * |nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ) ≤
          (∑ m ∈ Finset.Icc 1 (N / d),
            Λ d * Λ m * |nativePNTError (N / (d * m))|) +
            Λ d * R (N / d) := by
      calc
        Λ d * |nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ) =
            Λ d * (|nativePNTError (N / d)| *
              Real.log ((N / d : ℕ) : ℝ)) := by ring
        _ ≤ Λ d * (nativeLambdaErrorMass (N / d) + R (N / d)) :=
          hfirstMul
        _ = (∑ m ∈ Finset.Icc 1 (N / d),
              Λ d * Λ m * |nativePNTError (N / (d * m))|) +
              Λ d * R (N / d) := by
          unfold nativeLambdaErrorMass
          rw [mul_add, Finset.mul_sum]
          apply congrArg₂ (· + ·)
          · apply Finset.sum_congr rfl
            intro m hm
            have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
            rw [Nat.div_div_eq_div_mul]
            ring
          · ring
    have hlogs :
        Λ d * |nativePNTError (N / d)| * Real.log (N : ℝ) ≤
          Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
            Λ d * |nativePNTError (N / d)| *
              Real.log ((N / d : ℕ) : ℝ) +
            Λ d * |nativePNTError (N / d)| := by
      calc
        Λ d * |nativePNTError (N / d)| * Real.log (N : ℝ) ≤
            (Λ d * |nativePNTError (N / d)|) *
              (Real.log (d : ℝ) + Real.log ((N / d : ℕ) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hlogsplit hcoef0
        _ = Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
            Λ d * |nativePNTError (N / d)| *
              Real.log ((N / d : ℕ) : ℝ) +
            Λ d * |nativePNTError (N / d)| := by ring
    calc
      Λ d * |nativePNTError (N / d)| * Real.log (N : ℝ) ≤
          Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
            Λ d * |nativePNTError (N / d)| *
              Real.log ((N / d : ℕ) : ℝ) +
            Λ d * |nativePNTError (N / d)| := hlogs
      _ ≤ Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
            ((∑ m ∈ Finset.Icc 1 (N / d),
              Λ d * Λ m * |nativePNTError (N / (d * m))|) +
              Λ d * R (N / d)) +
            Λ d * |nativePNTError (N / d)| := by
        gcongr
      _ = Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
            (∑ m ∈ Finset.Icc 1 (N / d),
              Λ d * Λ m * |nativePNTError (N / (d * m))|) +
            Λ d * |nativePNTError (N / d)| +
            Λ d * R (N / d) := by ring
  have hsum :
      nativeLambdaErrorMass N * Real.log (N : ℝ) ≤
        nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          nativeLambdaErrorMass N + nativeLambdaRemainderMass R N := by
    change
      (∑ d ∈ Finset.Icc 1 N,
        Λ d * |nativePNTError (N / d)|) * Real.log (N : ℝ) ≤ _
    rw [Finset.sum_mul]
    calc
      (∑ d ∈ Finset.Icc 1 N,
        Λ d * |nativePNTError (N / d)| * Real.log (N : ℝ)) ≤
          ∑ d ∈ Finset.Icc 1 N,
            (Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
              (∑ m ∈ Finset.Icc 1 (N / d),
                Λ d * Λ m * |nativePNTError (N / (d * m))|) +
              Λ d * |nativePNTError (N / d)| +
              Λ d * R (N / d)) :=
        Finset.sum_le_sum hpoint
      _ = nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          nativeLambdaErrorMass N + nativeLambdaRemainderMass R N := by
        simp only [Finset.sum_add_distrib]
        unfold nativeLambdaLogErrorMass nativeLambdaErrorMass
          nativeLambdaRemainderMass
        rw [← nativeLambdaConvolutionErrorMass_eq_double]
  calc
    nativeLambdaErrorMass N * Real.log (N : ℝ) ≤
        nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          nativeLambdaErrorMass N + nativeLambdaRemainderMass R N := hsum
    _ = nativeLambdaTwoErrorMass N + nativeLambdaErrorMass N +
          nativeLambdaRemainderMass R N := by
      rw [nativeLambdaTwoErrorMass_eq_log_add_convolution]

/-- Remainder profile produced by one self-composition. -/
def nativePNTSecondRemainderFrom (R : ℕ → ℝ) (N : ℕ) : ℝ :=
  nativeLambdaErrorMass N + nativeLambdaRemainderMass R N +
    R N * Real.log (N : ℝ)

/-- Generic squared Selberg recurrence.  All lower-order terms remain explicit
profiles instead of being frozen to `3000 * N * log N`. -/
theorem nativePNTError_abs_log_sq_le_lambdaTwo_profile
    (R : ℕ → ℝ) (hR : NativePNTOneLogRemainderProfile R)
    (N : ℕ) (hN : 1 ≤ N) :
    |nativePNTError N| * (Real.log (N : ℝ)) ^ 2 ≤
      nativeLambdaTwoErrorMass N + nativePNTSecondRemainderFrom R N := by
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hfirst := hR N hN
  have hmul := mul_le_mul_of_nonneg_right hfirst hlog0
  have hinner := nativeLambdaErrorMass_mul_log_le_lambdaTwo_add_profile
    R hR N
  calc
    |nativePNTError N| * (Real.log (N : ℝ)) ^ 2 =
        (|nativePNTError N| * Real.log (N : ℝ)) * Real.log (N : ℝ) := by ring
    _ ≤ (nativeLambdaErrorMass N + R N) * Real.log (N : ℝ) := hmul
    _ = nativeLambdaErrorMass N * Real.log (N : ℝ) +
          R N * Real.log (N : ℝ) := by ring
    _ ≤ (nativeLambdaTwoErrorMass N + nativeLambdaErrorMass N +
          nativeLambdaRemainderMass R N) +
          R N * Real.log (N : ℝ) := add_le_add_right hinner _
    _ = nativeLambdaTwoErrorMass N + nativePNTSecondRemainderFrom R N := by
      unfold nativePNTSecondRemainderFrom
      ring

/-- Canonical second remainder obtained by composing the exact first remainder,
with no numerical majorant inserted between the two Selberg layers. -/
def nativePNTSecondRemainder (N : ℕ) : ℝ :=
  nativePNTSecondRemainderFrom nativePNTFirstRemainder N

/-- The squared recurrence driven by the canonical evolving remainder. -/
theorem nativePNTError_abs_log_sq_le_lambdaTwo_firstRemainder
    (N : ℕ) (hN : 1 ≤ N) :
    |nativePNTError N| * (Real.log (N : ℝ)) ^ 2 ≤
      nativeLambdaTwoErrorMass N + nativePNTSecondRemainder N := by
  simpa [nativePNTSecondRemainder] using
    nativePNTError_abs_log_sq_le_lambdaTwo_profile
      nativePNTFirstRemainder nativePNTFirstRemainder_profile N hN

end RHLean.Analysis
