import Mathlib
import RHLean.Analysis.NativePNTSignedWheelRemainder
import RHLean.Analysis.NativePNTSignedLogSquarePositiveDyadicKernel
import RHLean.Analysis.NativePNTSignedLogSquareSquareStage

/-!
# Exact signed second Selberg recurrence

The usual absolute self-composition replaces the second Selberg layer by the
positive kernel `Lambda_2` and pays an additive current-scale remainder.  This
file records the exact algebra before that loss of sign.

Writing

`S(N) = nativePNTSignedSelbergRemainder N`,

one first has exactly

`E(N) log N + sum_d Lambda(d) E(N/d) = S(N)`.

Multiplying by `log N`, splitting

`log N = log d + log floor(N/d) + floorDefect(N,d)`,

and applying the same signed recurrence on the lower quotient gives an exact
second recurrence.  Its error kernel is

`(Lambda * Lambda)(d) - Lambda(d) log d
   = Lambda_2(d) - 2 Lambda(d) log d`,

not the positive `Lambda_2` kernel.  The first signed Selberg remainder remains
inside the same identity as

`S(N) log N - sum_d Lambda(d) S(N/d)`.

This is the algebraic seam needed by the square-stage signed-cell attack: no
`O(N)` Selberg remainder is inserted and no termwise absolute value is taken.
The final theorems expose the exact dyadic-cell ownership of the `Lambda_2`
piece and specialize the identity to the repository's complete-square endpoint.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Signed log-weighted first-kernel error mass. -/
def nativePNTLambdaLogSignedErrorMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    Λ d * Real.log (d : ℝ) * nativePNTError (N / d)

/-- The lower-quotient logarithm in the exact second composition. -/
def nativePNTLambdaFloorLogSignedErrorMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    Λ d * nativePNTError (N / d) *
      Real.log ((N / d : ℕ) : ℝ)

/-- Exact defect in `log N = log d + log floor(N/d) + defect`.  It is kept
signed and is not replaced by the coarse upper bound `1`. -/
def nativePNTLambdaFloorLogSignedDefectMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    Λ d * nativePNTError (N / d) *
      (Real.log (N : ℝ) - Real.log (d : ℝ) -
        Real.log ((N / d : ℕ) : ℝ))

/-- The first signed Selberg remainder pushed down the same reciprocal
`Lambda` fibres. -/
def nativePNTLambdaSignedSelbergRemainderMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    Λ d * nativePNTSignedSelbergRemainder (N / d)

/-- Signed convolution part of the second Selberg kernel. -/
def nativePNTLambdaConvolutionSignedErrorMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    (Λ * Λ) n * nativePNTError (N / n)

/-- Cofactor-first finite form of the signed convolution mass. -/
def nativePNTLambdaConvolutionSignedErrorDoubleMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    ∑ m ∈ Finset.Icc 1 (N / d),
      Λ d * Λ m * nativePNTError (N / (d * m))

/-- The signed convolution coefficient reindexes exactly over reciprocal
cofactor pairs. -/
theorem nativePNTLambdaConvolutionSignedErrorMass_eq_double
    (N : ℕ) :
    nativePNTLambdaConvolutionSignedErrorMass N =
      nativePNTLambdaConvolutionSignedErrorDoubleMass N := by
  unfold nativePNTLambdaConvolutionSignedErrorMass
    nativePNTLambdaConvolutionSignedErrorDoubleMass
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
        (Λ * Λ) n * nativePNTError (N / n)) =
        ∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ n.divisors,
            (Λ d * Λ (n / d)) * nativePNTError (N / n) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal (fun a b => Λ a * Λ b), Finset.sum_mul]
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x),
            (Λ d * Λ (n / d)) * nativePNTError (N / n) :=
      Finset.sum_comm' hmem
    _ = ∑ d ∈ Finset.Icc 1 N,
        ∑ m ∈ Finset.Icc 1 (N / d),
          Λ d * Λ m * nativePNTError (N / (d * m)) := by
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
          have hq1 : 1 ≤ n / d :=
            (Nat.one_le_div_iff hdpos).2 (Nat.le_of_dvd (by omega) hdvd)
          exact ⟨hq1, Nat.div_le_div_right hnN⟩
        · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
          have hmulN' : m * d ≤ N :=
            (Nat.le_div_iff_mul_le hdpos).1 hmN
          have hmulN : d * m ≤ N := by
            simpa [Nat.mul_comm] using hmulN'
          have hmpos : 0 < m := by omega
          exact ⟨⟨Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (Nat.mul_pos hdpos hmpos)), hmulN⟩,
            dvd_mul_right d m⟩
      rw [hmap, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro m _hm
        have hdiv : d * m / d = m := Nat.mul_div_cancel_left m hdpos
        rw [hdiv]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hdpos hab

/-- Exact logarithm split of the signed first-kernel error mass. -/
theorem nativePNTLambdaSignedErrorMass_mul_log_eq_components
    (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
        Λ d * nativePNTError (N / d)) * Real.log (N : ℝ) =
      nativePNTLambdaLogSignedErrorMass N +
        nativePNTLambdaFloorLogSignedErrorMass N +
        nativePNTLambdaFloorLogSignedDefectMass N := by
  unfold nativePNTLambdaLogSignedErrorMass
    nativePNTLambdaFloorLogSignedErrorMass
    nativePNTLambdaFloorLogSignedDefectMass
  rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  ring

/-- Applying the exact first signed Selberg recurrence on every reciprocal
quotient converts the lower-log piece into a signed remainder pushforward minus
the signed `Lambda * Lambda` convolution. -/
theorem nativePNTLambdaFloorLogSignedErrorMass_eq_remainder_sub_convolution
    (N : ℕ) :
    nativePNTLambdaFloorLogSignedErrorMass N =
      nativePNTLambdaSignedSelbergRemainderMass N -
        nativePNTLambdaConvolutionSignedErrorMass N := by
  rw [nativePNTLambdaConvolutionSignedErrorMass_eq_double]
  unfold nativePNTLambdaFloorLogSignedErrorMass
    nativePNTLambdaSignedSelbergRemainderMass
    nativePNTLambdaConvolutionSignedErrorDoubleMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  have hrec := nativePNTError_mul_log_add_mobiusSigned_eq_remainder (N / d)
  rw [← nativeLambdaSignedErrorMass_eq_mobiusReciprocal] at hrec
  have hquot :
      (∑ m ∈ Finset.Icc 1 (N / d),
        Λ m * nativePNTError ((N / d) / m)) =
      ∑ m ∈ Finset.Icc 1 (N / d),
        Λ m * nativePNTError (N / (d * m)) := by
    apply Finset.sum_congr rfl
    intro m _hm
    rw [Nat.div_div_eq_div_mul]
  rw [hquot] at hrec
  have hpoint :
      nativePNTError (N / d) * Real.log ((N / d : ℕ) : ℝ) =
        nativePNTSignedSelbergRemainder (N / d) -
          ∑ m ∈ Finset.Icc 1 (N / d),
            Λ m * nativePNTError (N / (d * m)) := by
    linarith [hrec]
  calc
    Λ d * nativePNTError (N / d) * Real.log ((N / d : ℕ) : ℝ) =
        Λ d * (nativePNTError (N / d) * Real.log ((N / d : ℕ) : ℝ)) := by ring
    _ = Λ d * (nativePNTSignedSelbergRemainder (N / d) -
        ∑ m ∈ Finset.Icc 1 (N / d),
          Λ m * nativePNTError (N / (d * m))) := by rw [hpoint]
    _ = Λ d * nativePNTSignedSelbergRemainder (N / d) -
        Λ d * (∑ m ∈ Finset.Icc 1 (N / d),
          Λ m * nativePNTError (N / (d * m))) := by ring
    _ = Λ d * nativePNTSignedSelbergRemainder (N / d) -
        ∑ m ∈ Finset.Icc 1 (N / d),
          Λ d * (Λ m * nativePNTError (N / (d * m))) := by
      rw [Finset.mul_sum]
    _ = Λ d * nativePNTSignedSelbergRemainder (N / d) -
        ∑ m ∈ Finset.Icc 1 (N / d),
          Λ d * Λ m * nativePNTError (N / (d * m)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro m _hm
      ring

/-- The actual signed second-Selberg error kernel. -/
def nativePNTSignedSecondSelbergKernel (n : ℕ) : ℝ :=
  (Λ * Λ) n - Λ n * Real.log (n : ℝ)

/-- Signed second-kernel error mass. -/
def nativePNTSignedSecondSelbergKernelErrorMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    nativePNTSignedSecondSelbergKernel n * nativePNTError (N / n)

/-- The signed kernel is the positive second von Mangoldt kernel minus twice its
log-weighted prime-power part. -/
theorem nativePNTSignedSecondSelbergKernel_eq_lambdaTwo_sub_two_log
    (n : ℕ) :
    nativePNTSignedSecondSelbergKernel n =
      nativeLambdaTwo n - 2 * (Λ n * Real.log (n : ℝ)) := by
  unfold nativePNTSignedSecondSelbergKernel
  rw [nativeLambdaTwo_eq_logWeight_vonMangoldt_add_convolution]
  simp only [ArithmeticFunction.add_apply, arithmeticLogWeight_apply]
  ring

/-- The signed second-kernel mass is exactly convolution minus differentiated
first-kernel mass. -/
theorem nativePNTSignedSecondSelbergKernelErrorMass_eq
    (N : ℕ) :
    nativePNTSignedSecondSelbergKernelErrorMass N =
      nativePNTLambdaConvolutionSignedErrorMass N -
        nativePNTLambdaLogSignedErrorMass N := by
  unfold nativePNTSignedSecondSelbergKernelErrorMass
    nativePNTSignedSecondSelbergKernel
    nativePNTLambdaConvolutionSignedErrorMass
    nativePNTLambdaLogSignedErrorMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- The same signed kernel written in the `Lambda_2` coordinate. -/
theorem nativePNTSignedSecondSelbergKernelErrorMass_eq_lambdaTwo_sub_two_log
    (N : ℕ) :
    nativePNTSignedSecondSelbergKernelErrorMass N =
      nativeLambdaTwoSignedErrorMass N -
        2 * nativePNTLambdaLogSignedErrorMass N := by
  unfold nativePNTSignedSecondSelbergKernelErrorMass
    nativeLambdaTwoSignedErrorMass nativePNTLambdaLogSignedErrorMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [nativePNTSignedSecondSelbergKernel_eq_lambdaTwo_sub_two_log]
  ring

/-- **Cell ownership inside the true signed kernel.**  The `Lambda_2` portion of
the exact second-Selberg kernel is the dyadic-cell mass plus its explicit top
boundary.  The differentiated first-kernel term is retained with its sign. -/
theorem nativePNTSignedSecondSelbergKernelErrorMass_eq_cells_boundary_log
    (N : ℕ) :
    nativePNTSignedSecondSelbergKernelErrorMass N =
      nativePNTLambdaTwoOddKernelDyadicCellMass N +
        nativePNTLambdaTwoOddKernelTopBoundaryMass N -
        2 * nativePNTLambdaLogSignedErrorMass N := by
  rw [nativePNTSignedSecondSelbergKernelErrorMass_eq_lambdaTwo_sub_two_log,
    nativeLambdaTwoSignedErrorMass_eq_dyadicCells_add_boundary]

/-- **Exact signed second Selberg recurrence.**  No current-scale remainder is
bounded separately and no `Lambda_2` term is replaced by its absolute mass. -/
theorem nativePNTError_mul_log_sq_eq_signedSecondSelberg
    (N : ℕ) :
    nativePNTError N * (Real.log (N : ℝ)) ^ 2 =
      nativePNTSignedSelbergRemainder N * Real.log (N : ℝ) -
        nativePNTLambdaSignedSelbergRemainderMass N +
        nativePNTSignedSecondSelbergKernelErrorMass N -
        nativePNTLambdaFloorLogSignedDefectMass N := by
  have hfirst := nativePNTError_mul_log_add_mobiusSigned_eq_remainder N
  rw [← nativeLambdaSignedErrorMass_eq_mobiusReciprocal] at hfirst
  have hbase :
      nativePNTError N * (Real.log (N : ℝ)) ^ 2 +
          (∑ d ∈ Finset.Icc 1 N,
            Λ d * nativePNTError (N / d)) * Real.log (N : ℝ) =
        nativePNTSignedSelbergRemainder N * Real.log (N : ℝ) := by
    calc
      nativePNTError N * (Real.log (N : ℝ)) ^ 2 +
          (∑ d ∈ Finset.Icc 1 N,
            Λ d * nativePNTError (N / d)) * Real.log (N : ℝ) =
        (nativePNTError N * Real.log (N : ℝ) +
          ∑ d ∈ Finset.Icc 1 N,
            Λ d * nativePNTError (N / d)) * Real.log (N : ℝ) := by ring
      _ = nativePNTSignedSelbergRemainder N * Real.log (N : ℝ) := by
        rw [hfirst]
  have hsplit := nativePNTLambdaSignedErrorMass_mul_log_eq_components N
  have hfloor :=
    nativePNTLambdaFloorLogSignedErrorMass_eq_remainder_sub_convolution N
  have hkernel := nativePNTSignedSecondSelbergKernelErrorMass_eq N
  rw [hsplit, hfloor] at hbase
  rw [hkernel]
  linarith [hbase]

/-- The exact recurrence with the dyadic cells exposed and every remaining term
visible.  This is the acceptance coordinate for the square-stage cubic-gain
attack: any claimed local surplus must cancel against these exact leftovers,
not against an auxiliary absolute remainder. -/
theorem nativePNTError_mul_log_sq_eq_dyadicCells_signedSecondSelberg
    (N : ℕ) :
    nativePNTError N * (Real.log (N : ℝ)) ^ 2 =
      nativePNTSignedSelbergRemainder N * Real.log (N : ℝ) -
        nativePNTLambdaSignedSelbergRemainderMass N +
        nativePNTLambdaTwoOddKernelDyadicCellMass N +
        nativePNTLambdaTwoOddKernelTopBoundaryMass N -
        2 * nativePNTLambdaLogSignedErrorMass N -
        nativePNTLambdaFloorLogSignedDefectMass N := by
  rw [nativePNTError_mul_log_sq_eq_signedSecondSelberg,
    nativePNTSignedSecondSelbergKernelErrorMass_eq_cells_boundary_log]
  ring

/-- Complete-square specialization of the exact signed second recurrence. -/
theorem nativePNTError_squareStage_mul_log_sq_eq_signedSecondSelberg
    (t : ℕ) :
    nativePNTError (squarePrefixEndpoint t) *
        (Real.log ((squarePrefixEndpoint t : ℕ) : ℝ)) ^ 2 =
      nativePNTSignedSelbergRemainder (squarePrefixEndpoint t) *
          Real.log ((squarePrefixEndpoint t : ℕ) : ℝ) -
        nativePNTLambdaSignedSelbergRemainderMass (squarePrefixEndpoint t) +
        nativePNTSignedSecondSelbergKernelErrorMass (squarePrefixEndpoint t) -
        nativePNTLambdaFloorLogSignedDefectMass (squarePrefixEndpoint t) := by
  exact nativePNTError_mul_log_sq_eq_signedSecondSelberg (squarePrefixEndpoint t)

/-- Complete-square specialization with the exact dyadic-cell ownership exposed. -/
theorem nativePNTError_squareStage_mul_log_sq_eq_dyadicCells
    (t : ℕ) :
    nativePNTError (squarePrefixEndpoint t) *
        (Real.log ((squarePrefixEndpoint t : ℕ) : ℝ)) ^ 2 =
      nativePNTSignedSelbergRemainder (squarePrefixEndpoint t) *
          Real.log ((squarePrefixEndpoint t : ℕ) : ℝ) -
        nativePNTLambdaSignedSelbergRemainderMass (squarePrefixEndpoint t) +
        nativePNTLambdaTwoOddKernelDyadicCellMass (squarePrefixEndpoint t) +
        nativePNTLambdaTwoOddKernelTopBoundaryMass (squarePrefixEndpoint t) -
        2 * nativePNTLambdaLogSignedErrorMass (squarePrefixEndpoint t) -
        nativePNTLambdaFloorLogSignedDefectMass (squarePrefixEndpoint t) := by
  exact nativePNTError_mul_log_sq_eq_dyadicCells_signedSecondSelberg
    (squarePrefixEndpoint t)

end RHLean.Analysis
