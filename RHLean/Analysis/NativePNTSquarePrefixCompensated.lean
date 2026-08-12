import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixMobiusError

/-!
# Fully rederived compensated Selberg recurrence

This module self-composes the Möbius-native one-log recurrence proved in
`NativePNTSquarePrefixMobiusError`.  The recursive floor-fibre step is rebuilt
here, the log-weighted and convolution-weighted pieces are recombined into the
second von Mangoldt kernel, and the affine good-fibre compensation is then
reproved from that new squared recurrence.

The downstream cubic contraction can therefore consume a compensated recurrence
whose first-order input was obtained by exact `mu * log = Lambda` reciprocal
Fubini reindexing and fresh-prime Möbius cancellation.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.vonMangoldt BigOperators Topology

namespace RHLean.Analysis

/-! ## All-endpoint form of the Möbius-rederived first recurrence -/

private theorem nativePNTSquarePrefix_firstErrorConstant_le_thousand :
    3 * (Real.log 4 + 2) + 173 ≤ (1000 : ℝ) := by
  have hlog4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  norm_num at hlog4 ⊢
  linarith

/-- Coarse all-endpoint form of the newly rederived one-log recurrence.  The
large constant is used only to make recursive floor quotients uniform. -/
theorem nativePNTError_abs_log_le_mobius_rederived_crude (N : ℕ) :
    |nativePNTError N| * Real.log N ≤
      (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) +
        1000 * (N : ℝ) := by
  by_cases hN3 : 3 ≤ N
  · have h := nativePNTError_abs_log_le_mobiusReciprocal N hN3
    rw [← nativeLambdaAbsoluteErrorMass_eq_mobiusReciprocal] at h
    calc
      |nativePNTError N| * Real.log N ≤
          (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) +
            (3 * (Real.log 4 + 2) + 173) * (N : ℝ) := h
      _ ≤ (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) +
            1000 * (N : ℝ) := by
        gcongr
        exact nativePNTSquarePrefix_firstErrorConstant_le_thousand
  · have hNle : N ≤ 2 := by omega
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · simp [nativePNTError, nativePsi]
    · have hN1 : 1 ≤ N := hNpos
      have hlog0 : 0 ≤ Real.log (N : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hN1)
      have hlogle0 := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < (N : ℝ) by exact_mod_cast hNpos)
      have hlogle : Real.log (N : ℝ) ≤ (N : ℝ) := by linarith
      have herr := nativePNTError_abs_le_chebyshev N
      have hlog4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      have hC0 : 0 ≤ Real.log 4 + 3 := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
        linarith
      have hC6 : Real.log 4 + 3 ≤ 6 := by
        norm_num at hlog4 ⊢
        linarith
      have hNR0 : 0 ≤ (N : ℝ) := by positivity
      have hNleR : (N : ℝ) ≤ 2 := by exact_mod_cast hNle
      have hNN : (N : ℝ) * (N : ℝ) ≤ 2 * (N : ℝ) := by
        nlinarith
      have hleft :
          |nativePNTError N| * Real.log N ≤ 1000 * (N : ℝ) := by
        calc
          |nativePNTError N| * Real.log N ≤
              ((Real.log 4 + 3) * (N : ℝ)) * Real.log N :=
            mul_le_mul_of_nonneg_right herr hlog0
          _ ≤ ((Real.log 4 + 3) * (N : ℝ)) * (N : ℝ) :=
            mul_le_mul_of_nonneg_left hlogle (mul_nonneg hC0 hNR0)
          _ ≤ (6 * (N : ℝ)) * (N : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hC6 hNR0) hNR0
          _ = 6 * ((N : ℝ) * (N : ℝ)) := by ring
          _ ≤ 6 * (2 * (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hNN (by norm_num)
          _ ≤ 1000 * (N : ℝ) := by nlinarith
      have hsum0 :
          0 ≤ ∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)| := by
        apply Finset.sum_nonneg
        intro d _hd
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (abs_nonneg _)
      exact hleft.trans (le_add_of_nonneg_left hsum0)

/-! ## Self-composition into the second Selberg kernel -/

private theorem nativePNTSquarePrefix_log_le_log_divisor_add_floor_add_one
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

private theorem nativePNTSquarePrefix_lambdaFloorMass_le_Nlog
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ)) ≤
      (N : ℝ) * Real.log N := by
  rw [nativeVonMangoldtSummatory]
  exact nativeLogFactorial_upper N hN

/-- The recursively rederived one-log inequality combines with the exact
`Lambda * Lambda` Fubini form into the second-von-Mangoldt error mass. -/
theorem nativePNTSquarePrefix_lambdaErrorMass_mul_log_le_lambdaTwo
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) * Real.log N ≤
      nativeLambdaTwoErrorMass N + 2000 * (N : ℝ) * Real.log N := by
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hC6 : Real.log 4 + 3 ≤ 6 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at h ⊢
    linarith
  have hC0 : 0 ≤ Real.log 4 + 3 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith
  have hsplit :
      (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) * Real.log N ≤
        nativeLambdaLogErrorMass N +
          nativeLambdaConvolutionErrorMass N +
          1006 * (N : ℝ) * Real.log N := by
    rw [Finset.sum_mul]
    have hpoint : ∀ d ∈ Finset.Icc 1 N,
        Λ d * |nativePNTError (N / d)| * Real.log N ≤
          Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
          ∑ m ∈ Finset.Icc 1 (N / d),
            Λ d * Λ m * |nativePNTError (N / (d * m))| +
          (1000 + (Real.log 4 + 3)) *
            (Λ d * ((N / d : ℕ) : ℝ)) := by
      intro d hd
      have hdI := Finset.mem_Icc.mp hd
      have hdpos : 0 < d := by omega
      have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).2 hdI.2
      have hcoef0 : 0 ≤ Λ d * |nativePNTError (N / d)| :=
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (abs_nonneg _)
      have hlogsplit :=
        nativePNTSquarePrefix_log_le_log_divisor_add_floor_add_one N d hd
      have hfirst := nativePNTError_abs_log_le_mobius_rederived_crude (N / d)
      have hfirstMul :
          Λ d * (|nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ)) ≤
            Λ d *
              ((∑ m ∈ Finset.Icc 1 (N / d),
                Λ m * |nativePNTError ((N / d) / m)|) +
                1000 * ((N / d : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hfirst ArithmeticFunction.vonMangoldt_nonneg
      have hfirstMul' :
          Λ d * |nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ) ≤
            (∑ m ∈ Finset.Icc 1 (N / d),
              Λ d * Λ m * |nativePNTError (N / (d * m))|) +
              1000 * (Λ d * ((N / d : ℕ) : ℝ)) := by
        calc
          Λ d * |nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ) =
              Λ d * (|nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ)) := by
            ring
          _ ≤ Λ d *
              ((∑ m ∈ Finset.Icc 1 (N / d),
                Λ m * |nativePNTError ((N / d) / m)|) +
                1000 * ((N / d : ℕ) : ℝ)) := hfirstMul
          _ = (∑ m ∈ Finset.Icc 1 (N / d),
                Λ d * Λ m * |nativePNTError (N / (d * m))|) +
              1000 * (Λ d * ((N / d : ℕ) : ℝ)) := by
            rw [mul_add, Finset.mul_sum]
            apply congrArg₂ (· + ·)
            · apply Finset.sum_congr rfl
              intro m hm
              have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
              rw [Nat.div_div_eq_div_mul]
              ring
            · ring
      have herr := nativePNTError_abs_le_chebyshev (N / d)
      have hcorr :
          Λ d * |nativePNTError (N / d)| ≤
            (Real.log 4 + 3) * (Λ d * ((N / d : ℕ) : ℝ)) := by
        calc
          Λ d * |nativePNTError (N / d)| ≤
              Λ d * ((Real.log 4 + 3) * ((N / d : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left herr ArithmeticFunction.vonMangoldt_nonneg
          _ = (Real.log 4 + 3) * (Λ d * ((N / d : ℕ) : ℝ)) := by ring
      have hlogs :
          Λ d * |nativePNTError (N / d)| * Real.log N ≤
            Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
              Λ d * |nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ) +
              Λ d * |nativePNTError (N / d)| := by
        calc
          Λ d * |nativePNTError (N / d)| * Real.log N ≤
              (Λ d * |nativePNTError (N / d)|) *
                (Real.log (d : ℝ) + Real.log ((N / d : ℕ) : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hlogsplit hcoef0
          _ = Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
              Λ d * |nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ) +
              Λ d * |nativePNTError (N / d)| := by ring
      calc
        Λ d * |nativePNTError (N / d)| * Real.log N ≤
            Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
              Λ d * |nativePNTError (N / d)| * Real.log ((N / d : ℕ) : ℝ) +
              Λ d * |nativePNTError (N / d)| := hlogs
        _ ≤ Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
              ((∑ m ∈ Finset.Icc 1 (N / d),
                Λ d * Λ m * |nativePNTError (N / (d * m))|) +
                1000 * (Λ d * ((N / d : ℕ) : ℝ))) +
              (Real.log 4 + 3) * (Λ d * ((N / d : ℕ) : ℝ)) := by
          gcongr
        _ = Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
              ∑ m ∈ Finset.Icc 1 (N / d),
                Λ d * Λ m * |nativePNTError (N / (d * m))| +
              (1000 + (Real.log 4 + 3)) *
                (Λ d * ((N / d : ℕ) : ℝ)) := by ring
    calc
      (∑ d ∈ Finset.Icc 1 N,
        Λ d * |nativePNTError (N / d)| * Real.log N) ≤
          ∑ d ∈ Finset.Icc 1 N,
            (Λ d * Real.log (d : ℝ) * |nativePNTError (N / d)| +
              ∑ m ∈ Finset.Icc 1 (N / d),
                Λ d * Λ m * |nativePNTError (N / (d * m))| +
              (1000 + (Real.log 4 + 3)) *
                (Λ d * ((N / d : ℕ) : ℝ))) :=
        Finset.sum_le_sum hpoint
      _ = nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          (1000 + (Real.log 4 + 3)) *
            (∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        unfold nativeLambdaLogErrorMass
        rw [← nativeLambdaConvolutionErrorMass_eq_double]
        rw [← Finset.mul_sum]
      _ ≤ nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          (1000 + (Real.log 4 + 3)) * ((N : ℝ) * Real.log N) := by
        have hcoef : 0 ≤ 1000 + (Real.log 4 + 3) :=
          add_nonneg (by norm_num) hC0
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left
            (nativePNTSquarePrefix_lambdaFloorMass_le_Nlog N hN) hcoef)
          (nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N)
      _ ≤ nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          1006 * ((N : ℝ) * Real.log N) := by
        have hcoef : 1000 + (Real.log 4 + 3) ≤ (1006 : ℝ) := by
          linarith [hC6]
        have hNlog0 : 0 ≤ (N : ℝ) * Real.log N :=
          mul_nonneg (by positivity) hlog0
        exact add_le_add_left
          (mul_le_mul_of_nonneg_right hcoef hNlog0)
          (nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N)
      _ = nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          1006 * (N : ℝ) * Real.log N := by ring
  rw [nativeLambdaTwoErrorMass_eq_log_add_convolution]
  calc
    (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) * Real.log N ≤
        nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          1006 * (N : ℝ) * Real.log N := hsplit
    _ ≤ nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N +
          2000 * (N : ℝ) * Real.log N := by
      have hNlog0 : 0 ≤ (N : ℝ) * Real.log N :=
        mul_nonneg (by positivity) hlog0
      have hcoef : 1006 * (N : ℝ) * Real.log N ≤
          2000 * (N : ℝ) * Real.log N := by
        calc
          1006 * (N : ℝ) * Real.log N = 1006 * ((N : ℝ) * Real.log N) := by ring
          _ ≤ 2000 * ((N : ℝ) * Real.log N) :=
            mul_le_mul_of_nonneg_right (by norm_num) hNlog0
          _ = 2000 * (N : ℝ) * Real.log N := by ring
      exact add_le_add_left hcoef
        (nativeLambdaLogErrorMass N + nativeLambdaConvolutionErrorMass N)

/-- Squared absolute Selberg recurrence obtained by self-composing the
Möbius-rederived first recurrence on every reciprocal floor fibre. -/
theorem nativePNTError_abs_log_sq_le_lambdaTwo_mobius_rederived
    (N : ℕ) (hN : 3 ≤ N) :
    |nativePNTError N| * (Real.log N) ^ 2 ≤
      nativeLambdaTwoErrorMass N + 3000 * (N : ℝ) * Real.log N := by
  have hfirst := nativePNTError_abs_log_le_mobius_rederived_crude N
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hmul := mul_le_mul_of_nonneg_right hfirst hlog0
  have hinner :=
    nativePNTSquarePrefix_lambdaErrorMass_mul_log_le_lambdaTwo N (by omega : 1 ≤ N)
  calc
    |nativePNTError N| * (Real.log N) ^ 2 =
        (|nativePNTError N| * Real.log N) * Real.log N := by ring
    _ ≤ ((∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) +
          1000 * (N : ℝ)) * Real.log N := hmul
    _ = (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) * Real.log N +
          1000 * (N : ℝ) * Real.log N := by ring
    _ ≤ nativeLambdaTwoErrorMass N + 2000 * (N : ℝ) * Real.log N +
          1000 * (N : ℝ) * Real.log N := add_le_add_right hinner _
    _ = nativeLambdaTwoErrorMass N + 3000 * (N : ℝ) * Real.log N := by ring

/-! ## Rebuilt compensation and affine improvement -/

private theorem nativePNTSquarePrefix_selbergLinearConstant_le_182 :
    2 * (Real.log 4 + 2) + 172 ≤ (182 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  norm_num at h ⊢
  linarith

/-- Compensated squared recurrence whose squared input is the newly rederived
Möbius self-composition above. -/
theorem nativePNTError_abs_log_sq_le_affine_compensated_mobius_rederived
    (N : ℕ) (hN : 3 ≤ N)
    (alpha beta D : ℝ)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hba : beta ≤ alpha)
    (hD : 0 ≤ D)
    (henv : ∀ q : ℕ,
      |nativePNTError q| ≤ alpha * (q : ℝ) + D) :
    |nativePNTError N| * (Real.log N) ^ 2 ≤
      alpha * (N : ℝ) *
          ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) -
        (alpha - beta) * (N : ℝ) *
          nativeLambdaTwoGoodRecipMass N beta +
        D * (2 * (N : ℝ) * Real.log N + 182 * (N : ℝ) + 600) +
        3000 * (N : ℝ) * Real.log N := by
  have hall : ∀ n ∈ Finset.Icc 1 N,
      |nativePNTError (N / n)| ≤
        alpha * ((N : ℝ) / (n : ℝ)) + D := by
    intro n hn
    exact nativePNTAffineEnvelope_on_fiber alpha D halpha henv N n hn
  have hsq := nativePNTError_abs_log_sq_le_lambdaTwo_mobius_rederived N hN
  have hcomp := nativeLambdaTwoErrorMass_compensation
    N alpha beta D halpha hbeta hba hD hall
  have hrec := nativeLambdaTwoRecipMass_upper N hN
  have hsel := nativeLambdaTwoSummatory_sub_two_mul_log_abs_le N hN
  rw [abs_le] at hsel
  have hC := nativePNTSquarePrefix_selbergLinearConstant_le_182
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hCR := mul_le_mul_of_nonneg_right hC hN0
  have hrho :
      nativeLambdaTwoSummatory N ≤
        2 * (N : ℝ) * Real.log N + 182 * (N : ℝ) + 600 := by
    nlinarith [hsel.2, hCR]
  have hrecMul :
      alpha * (N : ℝ) * nativeLambdaTwoRecipMass N ≤
        alpha * (N : ℝ) *
          ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) := by
    exact mul_le_mul_of_nonneg_left hrec (mul_nonneg halpha hN0)
  have hrhoMul :
      D * nativeLambdaTwoSummatory N ≤
        D * (2 * (N : ℝ) * Real.log N + 182 * (N : ℝ) + 600) :=
    mul_le_mul_of_nonneg_left hrho hD
  have hmass :
      nativeLambdaTwoErrorMass N ≤
        alpha * (N : ℝ) *
            ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) -
          (alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodRecipMass N beta +
          D * (2 * (N : ℝ) * Real.log N + 182 * (N : ℝ) + 600) := by
    exact hcomp.trans
      (add_le_add
        (sub_le_sub_right hrecMul
          ((alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta))
        hrhoMul)
  calc
    |nativePNTError N| * (Real.log N) ^ 2 ≤
        nativeLambdaTwoErrorMass N +
          3000 * (N : ℝ) * Real.log N := hsq
    _ ≤
        (alpha * (N : ℝ) *
            ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) -
          (alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodRecipMass N beta +
          D * (2 * (N : ℝ) * Real.log N + 182 * (N : ℝ) + 600)) +
          3000 * (N : ℝ) * Real.log N :=
      add_le_add_right hmass _
    _ = _ := by ring

/-- Strict affine-envelope improvement rebuilt from the newly rederived
compensated recurrence. -/
theorem nativePNTSquarePrefixHasAffineEnvelope_improve_of_goodMass
    (alpha beta c : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 ≤ beta) (hba : beta < alpha)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hgood : ∀ᶠ N : ℕ in atTop,
      c * (Real.log (N : ℝ)) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N beta)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
      (alpha - (alpha - beta) * c / 4) := by
  rcases henv with ⟨D, hD, henv⟩
  let delta : ℝ := (alpha - beta) * c / 4
  have habpos : 0 < alpha - beta := sub_pos.mpr hba
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hable : alpha - beta ≤ alpha := by linarith
  have hmul : (alpha - beta) * c ≤ alpha := by
    have := mul_le_mul hable hc1 hc.le halpha.le
    simpa using this
  have hdeltale : delta ≤ alpha / 4 := by
    dsimp [delta]
    nlinarith
  have hnewnonneg : 0 ≤ alpha - delta := by
    nlinarith
  let C0 : ℝ := 3000 * alpha + 784 * D + 3000
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hlogTop :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog1 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (N : ℝ) :=
    hlogTop.eventually_ge_atTop 1
  have hlogC : ∀ᶠ N : ℕ in atTop,
      C0 / (3 * delta) ≤ Real.log (N : ℝ) :=
    hlogTop.eventually_ge_atTop (C0 / (3 * delta))
  have hlarge : ∀ᶠ N : ℕ in atTop,
      |nativePNTError N| ≤ (alpha - delta) * (N : ℝ) := by
    filter_upwards [eventually_ge_atTop 3, hgood, hlog1, hlogC]
      with N hN hgoodN hL1 hLC
    have hN1 : 1 ≤ N := by omega
    have hNR0 : 0 ≤ (N : ℝ) := by positivity
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    let L : ℝ := Real.log (N : ℝ)
    have hL1' : (1 : ℝ) ≤ L := by simpa [L] using hL1
    have hL0 : 0 ≤ L := le_trans (by norm_num) hL1'
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL1'
    have hden : 0 < 3 * delta := by positivity
    have hCLe0 : C0 ≤ L * (3 * delta) := by
      apply (div_le_iff₀ hden).mp
      simpa [L] using hLC
    have hCLe : C0 ≤ 3 * delta * L := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hCLe0
    have hB0 : 0 ≤ 2000 * alpha + 782 * D := by positivity
    have hBLe :
        2000 * alpha + 782 * D ≤
          (2000 * alpha + 782 * D) * L := by
      have h := mul_le_mul_of_nonneg_left hL1' hB0
      simpa using h
    have hleft :
        alpha * (1000 * L + 2000) +
            D * (2 * L + 782) + 3000 * L ≤ C0 * L := by
      dsimp [C0]
      nlinarith [hBLe]
    have hCLmul : C0 * L ≤ (3 * delta * L) * L :=
      mul_le_mul_of_nonneg_right hCLe hL0
    have hinner :
        alpha * (1000 * L + 2000) +
            D * (2 * L + 782) + 3000 * L ≤
          3 * delta * L ^ 2 := by
      calc
        alpha * (1000 * L + 2000) +
              D * (2 * L + 782) + 3000 * L ≤ C0 * L := hleft
        _ ≤ (3 * delta * L) * L := hCLmul
        _ = 3 * delta * L ^ 2 := by ring
    have hD600 : D * 600 ≤ D * 600 * (N : ℝ) := by
      have h600D : 0 ≤ D * 600 := by positivity
      have h := mul_le_mul_of_nonneg_left hN1R h600D
      simpa [mul_assoc] using h
    have hinnerN := mul_le_mul_of_nonneg_left hinner hNR0
    have hoverhead :
        alpha * (N : ℝ) * (1000 * L + 2000) +
            D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
            3000 * (N : ℝ) * L ≤
          3 * delta * (N : ℝ) * L ^ 2 := by
      have hreshape :
          alpha * (N : ℝ) * (1000 * L + 2000) +
              D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
              3000 * (N : ℝ) * L ≤
            (N : ℝ) *
              (alpha * (1000 * L + 2000) +
                D * (2 * L + 782) + 3000 * L) := by
        nlinarith [hD600]
      calc
        alpha * (N : ℝ) * (1000 * L + 2000) +
              D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
              3000 * (N : ℝ) * L ≤
            (N : ℝ) *
              (alpha * (1000 * L + 2000) +
                D * (2 * L + 782) + 3000 * L) := hreshape
        _ ≤ (N : ℝ) * (3 * delta * L ^ 2) := hinnerN
        _ = 3 * delta * (N : ℝ) * L ^ 2 := by ring
    have hcoef0 : 0 ≤ (alpha - beta) * (N : ℝ) :=
      mul_nonneg habpos.le hNR0
    have hgoodN' : c * L ^ 2 ≤ nativeLambdaTwoGoodRecipMass N beta := by
      simpa [L] using hgoodN
    have hgoodMul := mul_le_mul_of_nonneg_left hgoodN' hcoef0
    have hdeficit :
        -(alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta ≤
          -4 * delta * (N : ℝ) * L ^ 2 := by
      calc
        -(alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta =
            -((alpha - beta) * (N : ℝ) *
              nativeLambdaTwoGoodRecipMass N beta) := by ring
        _ ≤ -((alpha - beta) * (N : ℝ) * (c * L ^ 2)) :=
          neg_le_neg hgoodMul
        _ = -4 * delta * (N : ℝ) * L ^ 2 := by
          dsimp [delta]
          ring
    have htail :
        (alpha * (N : ℝ) * (1000 * L + 2000) +
            D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
            3000 * (N : ℝ) * L) +
          (-(alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodRecipMass N beta) ≤
          -delta * (N : ℝ) * L ^ 2 := by
      nlinarith [hoverhead, hdeficit]
    have hrec := nativePNTError_abs_log_sq_le_affine_compensated_mobius_rederived
      N hN alpha beta D halpha.le hbeta hba.le hD henv
    have hrearrange :
        alpha * (N : ℝ) *
              (L ^ 2 + 1000 * L + 2000) -
            (alpha - beta) * (N : ℝ) *
              nativeLambdaTwoGoodRecipMass N beta +
            D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
            3000 * (N : ℝ) * L =
          alpha * (N : ℝ) * L ^ 2 +
            ((alpha * (N : ℝ) * (1000 * L + 2000) +
                D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
                3000 * (N : ℝ) * L) +
              (-(alpha - beta) * (N : ℝ) *
                nativeLambdaTwoGoodRecipMass N beta)) := by
      ring
    have hsq :
        |nativePNTError N| * L ^ 2 ≤
          (alpha - delta) * (N : ℝ) * L ^ 2 := by
      have hrec' :
          |nativePNTError N| * L ^ 2 ≤
            alpha * (N : ℝ) * L ^ 2 +
              ((alpha * (N : ℝ) * (1000 * L + 2000) +
                  D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
                  3000 * (N : ℝ) * L) +
                (-(alpha - beta) * (N : ℝ) *
                  nativeLambdaTwoGoodRecipMass N beta)) := by
        simpa [L, hrearrange] using hrec
      calc
        |nativePNTError N| * L ^ 2 ≤
            alpha * (N : ℝ) * L ^ 2 +
              ((alpha * (N : ℝ) * (1000 * L + 2000) +
                  D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
                  3000 * (N : ℝ) * L) +
                (-(alpha - beta) * (N : ℝ) *
                  nativeLambdaTwoGoodRecipMass N beta)) := hrec'
        _ ≤ alpha * (N : ℝ) * L ^ 2 - delta * (N : ℝ) * L ^ 2 := by
          simpa [sub_eq_add_neg] using
            (add_le_add_left htail (alpha * (N : ℝ) * L ^ 2))
        _ = (alpha - delta) * (N : ℝ) * L ^ 2 := by ring
    have hLsq : 0 < L ^ 2 := sq_pos_of_pos hLpos
    have hsq' :
        |nativePNTError N| * L ^ 2 ≤
          ((alpha - delta) * (N : ℝ)) * L ^ 2 := by
      simpa [mul_assoc] using hsq
    exact (mul_le_mul_iff_left₀ hLsq).mp hsq'
  rcases (eventually_atTop.1 hlarge) with ⟨M, hM⟩
  refine ⟨D + delta * (M : ℝ), ?_, ?_⟩
  · positivity
  · intro N
    by_cases hMN : M ≤ N
    · exact (hM N hMN).trans
        (le_add_of_nonneg_right (by positivity))
    · have hNM : N ≤ M := Nat.le_of_lt (lt_of_not_ge hMN)
      have hNMR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
      have hdeltaNM := mul_le_mul_of_nonneg_left hNMR hdelta.le
      have hold := henv N
      have htarget :
          alpha * (N : ℝ) + D ≤
            (alpha - delta) * (N : ℝ) +
              (D + delta * (M : ℝ)) := by
        nlinarith
      exact hold.trans htarget

end RHLean.Analysis
