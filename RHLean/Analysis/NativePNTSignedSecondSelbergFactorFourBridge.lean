import Mathlib
import RHLean.Analysis.NativePNTErrorMass
import RHLean.Analysis.NativePNTSummatorySelberg
import RHLean.Analysis.NativePNTSignedSecondSelbergDepthFourShell
import RHLean.Analysis.NativePNTSquarePrefixContraction

/-!
# Factor-four signed K2 bridge

This module isolates two exact facts needed by the factor-four reciprocal-shell
attack.

First, fresh-prime cancellation has to be performed at a fixed physical product:
the prime may move between the Möbius divisor and the reciprocal quotient.  In
that coordinate the two denominators agree, the leading `log^2 m` term cancels
exactly, and only the lower-degree fresh-prime correction remains.

Second, the tempting summatory shortcut is calibrated exactly.  The summatory
signed second-Selberg kernel differs from `-2 * E(N) * log N` by only `O(N)`,
with the `O(N)` constant already proved in the native Selberg layer.  Thus a
linear summatory K2 bound would require precisely the logarithmic improvement of
the physical PNT error that the current onset analysis does not yet provide.

No absolute value is taken inside the signed kernel and no new analytic
hypothesis is introduced.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Summatory mass of the true signed second-Selberg kernel. -/
def nativePNTSignedK2Summatory (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, nativePNTSignedSecondSelbergKernel n

/-- The summatory signed kernel is exactly `Lambda_2 - 2 Lambda log`. -/
theorem nativePNTSignedK2Summatory_eq_lambdaTwo_sub_two_log
    (N : ℕ) :
    nativePNTSignedK2Summatory N =
      nativeLambdaTwoSummatory N - 2 * nativeLambdaLogMass N := by
  unfold nativePNTSignedK2Summatory nativeLambdaTwoSummatory nativeLambdaLogMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [nativePNTSignedSecondSelbergKernel_eq_lambdaTwo_sub_two_log]

/-- Explicit linear remainder in the identity
`sum K2 = -2 * E(N) * log N + O(N)`.

This theorem is deliberately signed: it does not estimate the positive and
negative faces of `K2` separately. -/
theorem nativePNTSignedK2Summatory_add_two_error_log_abs_le
    (N : ℕ) (hN : 3 ≤ N) :
    |nativePNTSignedK2Summatory N +
        2 * nativePNTError N * Real.log (N : ℝ)| ≤
      (4 * (Real.log 4 + 2) + 172) * (N : ℝ) := by
  have htwo := nativeLambdaTwoSummatory_sub_two_mul_log_abs_le N hN
  have hlog := nativeLambdaLogMass_sub_psiLog_abs_le N
  rw [nativePNTSignedK2Summatory_eq_lambdaTwo_sub_two_log]
  unfold nativePNTError
  have hrearrange :
      nativeLambdaTwoSummatory N - 2 * nativeLambdaLogMass N +
          2 * (nativePsi N - (N : ℝ)) * Real.log (N : ℝ) =
        (nativeLambdaTwoSummatory N -
            2 * (N : ℝ) * Real.log (N : ℝ)) -
          2 * (nativeLambdaLogMass N -
            nativePsi N * Real.log (N : ℝ)) := by
    ring
  rw [hrearrange]
  calc
    |(nativeLambdaTwoSummatory N -
          2 * (N : ℝ) * Real.log (N : ℝ)) -
        2 * (nativeLambdaLogMass N -
          nativePsi N * Real.log (N : ℝ))| ≤
      |nativeLambdaTwoSummatory N -
          2 * (N : ℝ) * Real.log (N : ℝ)| +
        |2 * (nativeLambdaLogMass N -
          nativePsi N * Real.log (N : ℝ))| := abs_sub _ _
    _ = |nativeLambdaTwoSummatory N -
          2 * (N : ℝ) * Real.log (N : ℝ)| +
        2 * |nativeLambdaLogMass N -
          nativePsi N * Real.log (N : ℝ)| := by
      rw [abs_mul]
      norm_num
    _ ≤ (2 * (Real.log 4 + 2) + 172) * (N : ℝ) +
        2 * ((Real.log 4 + 2) * (N : ℝ)) := by
      exact add_le_add htwo
        (mul_le_mul_of_nonneg_left hlog (by norm_num))
    _ = (4 * (Real.log 4 + 2) + 172) * (N : ℝ) := by ring

/-- One reciprocal Fubini atom for the signed K2 shell.  The physical product
is `d*k`; keeping that product fixed is essential for fresh-prime pairing. -/
def nativePNTSignedK2RecipFubiniAtom (d k : ℕ) : ℝ :=
  (μ : ArithmeticFunction ℝ) d * (Real.log (d : ℝ)) ^ 2 /
    ((d * k : ℕ) : ℝ)

/-- **Same-product fresh-prime cancellation.**  Move a fresh prime `p` from the
reciprocal quotient to the Möbius divisor.  The two atoms have the same physical
product `m*p*k`, so the `log^2 m` term cancels exactly.  Only the lower-degree
correction `(log p)^2 + 2 log p log m` survives.

This is the reciprocal-shell analogue of the repository's same-endpoint
log-square cell identity. -/
theorem nativePNTSignedK2RecipFubiniAtom_freshPrime_sameProduct
    (m p k : ℕ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hp : p.Prime) (hcop : Nat.Coprime m p) :
    nativePNTSignedK2RecipFubiniAtom (m * p) k +
        nativePNTSignedK2RecipFubiniAtom m (p * k) =
      -(μ : ArithmeticFunction ℝ) m *
        ((Real.log (p : ℝ)) ^ 2 +
          2 * Real.log (p : ℝ) * Real.log (m : ℝ)) /
        (((m * p) * k : ℕ) : ℝ) := by
  have hmu :
      (μ : ArithmeticFunction ℝ) (m * p) =
        -(μ : ArithmeticFunction ℝ) m := by
    change (((μ (m * p) : ℤ) : ℝ)) = -(((μ m : ℤ) : ℝ))
    rw [nativeMobius_adjoin_prime m p hp hcop]
    push_cast
    rfl
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by omega)
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (show k ≠ 0 by omega)
  have hlog :
      Real.log ((m * p : ℕ) : ℝ) =
        Real.log (m : ℝ) + Real.log (p : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hm0 hp0]
  unfold nativePNTSignedK2RecipFubiniAtom
  rw [hmu, hlog]
  push_cast
  field_simp [hm0, hp0, hk0]
  ring

end RHLean.Analysis
