import Mathlib
import RHLean.Analysis.NativePNTChebyshev
import RHLean.Analysis.NativePNTMertens

/-!
# Native Selberg preparation

This module turns the exact floor identities into the bounded reciprocal
von-Mangoldt estimate needed by Selberg's symmetry formula.

The key exact identity is

`N * sum_{n<=N} Lambda(n)/n = log(N!) + sum Lambda(n) * fract(N/n)`.

The fractional part is between zero and one, so the correction is bounded by
`psi(N)`.  Together with the architecture-native Chebyshev bound and the
simple inequality

`N log N - N + 1 <= log(N!) <= N log N`,

this gives Mertens' first theorem in the precise form needed later:
`sum Lambda(n)/n - log N` is uniformly bounded.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Reciprocal von Mangoldt partial sum. -/
def nativeLambdaRecip (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, Λ n / (n : ℝ)

/-- Fractional-part error in replacing `N/n` by `floor(N/n)`. -/
def nativeLambdaFloorError (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    Λ n * Int.fract ((N : ℝ) / (n : ℝ))

/-- Exact floor/fractional-part identity for the reciprocal von Mangoldt sum. -/
theorem nativeMulLambdaRecip_eq_logFactorial_add_error (N : ℕ) :
    (N : ℝ) * nativeLambdaRecip N =
      Real.log ((Nat.factorial N : ℕ) : ℝ) + nativeLambdaFloorError N := by
  unfold nativeLambdaRecip nativeLambdaFloorError
  rw [Finset.mul_sum, ← nativeVonMangoldtSummatory]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnpos : 0 < n := by omega
  have hfloorcast :
      (⌊(N : ℝ) / (n : ℝ)⌋ : ℝ) = ((N / n : ℕ) : ℝ) := by
    have hz :
        ⌊(N : ℝ) / (n : ℝ)⌋ = ((N / n : ℕ) : ℤ) := by
      rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]
    rw [hz]
    norm_cast
  have hfract :
      Int.fract ((N : ℝ) / (n : ℝ)) =
        (N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ) := by
    rw [← Int.self_sub_floor, hfloorcast]
  rw [hfract]
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hnpos)]
  ring

/-- The fractional von-Mangoldt floor error is nonnegative. -/
theorem nativeLambdaFloorError_nonneg (N : ℕ) :
    0 ≤ nativeLambdaFloorError N := by
  unfold nativeLambdaFloorError
  apply Finset.sum_nonneg
  intro n _hn
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Int.fract_nonneg _)

/-- The fractional floor error is bounded by the full Chebyshev mass. -/
theorem nativeLambdaFloorError_le_psi (N : ℕ) :
    nativeLambdaFloorError N ≤ nativePsi N := by
  unfold nativeLambdaFloorError nativePsi
  apply Finset.sum_le_sum
  intro n _hn
  have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hfract : Int.fract ((N : ℝ) / (n : ℝ)) ≤ 1 :=
    (Int.fract_lt_one _).le
  calc
    Λ n * Int.fract ((N : ℝ) / (n : ℝ)) ≤ Λ n * 1 :=
      mul_le_mul_of_nonneg_left hfract hΛ
    _ = Λ n := by ring

/-- Elementary upper bound `log(N!) <= N log N`. -/
theorem nativeLogFactorial_upper
    (N : ℕ) (hN : 1 ≤ N) :
    Real.log ((Nat.factorial N : ℕ) : ℝ) ≤
      (N : ℝ) * Real.log N := by
  rw [nativeLogFactorial_eq_sum_log]
  have hpoint :
      ∀ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) ≤ Real.log (N : ℝ) := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnN⟩
    exact Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnN)
  calc
    (∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ)) ≤
        ∑ _n ∈ Finset.Icc 1 N, Real.log (N : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = ((Finset.Icc 1 N).card : ℝ) * Real.log N := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (N : ℝ) * Real.log N := by
      rw [Nat.card_Icc]
      have hcard : N + 1 - 1 = N := by omega
      rw [hcard]

/-- Elementary lower bound `N log N - N + 1 <= log(N!)`.

The induction step is exactly `log(1+t) <= t`. -/
theorem nativeLogFactorial_lower :
    ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) * Real.log N - (N : ℝ) + 1 ≤
        Real.log ((Nat.factorial N : ℕ) : ℝ) := by
  intro N hN
  induction N with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have ih' := ih hn1
        have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
        have hsuccR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        have hratioPos :
            0 < (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := div_pos hsuccR hnR
        have hlogRatio := Real.log_le_sub_one_of_pos hratioPos
        have hlogDiv :
            Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) =
              Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
          rw [Real.log_div (ne_of_gt hsuccR) (ne_of_gt hnR)]
        have hratioSub :
            (((n + 1 : ℕ) : ℝ) / (n : ℝ)) - 1 = 1 / (n : ℝ) := by
          push_cast
          field_simp [ne_of_gt hnR]
          ring
        rw [hlogDiv, hratioSub] at hlogRatio
        have hmul := mul_le_mul_of_nonneg_left hlogRatio hnR.le
        have hcancel : (n : ℝ) * (1 / (n : ℝ)) = 1 := by
          field_simp [ne_of_gt hnR]
        rw [hcancel] at hmul
        have hstep :
            (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) - (n : ℝ) ≤
              (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + 1 := by
          nlinarith [hmul]
        have hfac :
            Real.log ((Nat.factorial (n + 1) : ℕ) : ℝ) =
              Real.log ((n + 1 : ℕ) : ℝ) +
                Real.log ((Nat.factorial n : ℕ) : ℝ) := by
          rw [Nat.factorial_succ, Nat.cast_mul,
            Real.log_mul (by positivity)
              (by exact_mod_cast (Nat.factorial_ne_zero n))]
        calc
          ((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) -
                ((n + 1 : ℕ) : ℝ) + 1 =
              Real.log ((n + 1 : ℕ) : ℝ) +
                ((n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) - (n : ℝ)) := by
            push_cast
            ring
          _ ≤ Real.log ((n + 1 : ℕ) : ℝ) +
                ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + 1) :=
            add_le_add_left hstep _
          _ ≤ Real.log ((n + 1 : ℕ) : ℝ) +
                Real.log ((Nat.factorial n : ℕ) : ℝ) :=
            add_le_add_left ih' _
          _ = Real.log ((Nat.factorial (n + 1) : ℕ) : ℝ) := hfac.symm

/-- Mertens' first theorem in bounded-error form, proved only from the finite
floor identity and the architecture-native Chebyshev estimate. -/
theorem nativeLambdaRecip_sub_log_bounds
    (N : ℕ) (hN : 1 ≤ N) :
    -1 ≤ nativeLambdaRecip N - Real.log N ∧
      nativeLambdaRecip N - Real.log N ≤ Real.log 4 + 2 := by
  have hNposNat : 0 < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
  have hexact := nativeMulLambdaRecip_eq_logFactorial_add_error N
  have herr0 := nativeLambdaFloorError_nonneg N
  have herrPsi := nativeLambdaFloorError_le_psi N
  have hpsi := nativePsi_le_const_mul N
  have hfacLow := nativeLogFactorial_lower N hN
  have hfacUp := nativeLogFactorial_upper N hN
  constructor
  · nlinarith
  · nlinarith

/-- Uniform absolute form of Mertens' first theorem. -/
theorem nativeLambdaRecip_sub_log_abs_le
    (N : ℕ) (hN : 1 ≤ N) :
    |nativeLambdaRecip N - Real.log N| ≤ Real.log 4 + 2 := by
  have hb := nativeLambdaRecip_sub_log_bounds N hN
  rw [abs_le]
  constructor
  · have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · exact hb.2

end RHLean.Analysis
