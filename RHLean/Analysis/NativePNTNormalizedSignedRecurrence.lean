import Mathlib
import RHLean.Analysis.NativePNTErdosContraction

/-!
# Scale-free normalized signed Selberg recurrence

The affine-envelope proof globalizes a tail bound by inserting an additive
intercept.  That is convenient for proving the qualitative PNT, but it hides
the physical scale at which a small normalized error becomes valid.

This module instead divides the exact signed first Selberg recurrence by the
current endpoint.  The resulting remainder is an absolute constant, not a
term growing like `N` or `N * log N`.  This is the normalization needed for a
quantitative modulus attack and for later square-stage or wheel-frontier
smoothing.

The reciprocal term is then rewritten as a nonnegative barycentric transform
of the smaller normalized errors.  Its total weight is exactly `log(N!) / N`,
so the sharp factorial estimate identifies the transform mass with
`log N - 1 + O(log N / N)`.  Thus the signed relation is a scale-free
near-averaging law rather than an affine recurrence with a growing intercept.

No new analytic premise is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Normalized Chebyshev error `E(N) / N`.  The value at zero is harmless and
is never used by the positive-endpoint theorems below. -/
def nativePNTNormalizedError (N : ℕ) : ℝ :=
  nativePNTError N / (N : ℝ)

/-- The signed reciprocal-floor Selberg transform after division by the
current endpoint `N`. -/
def nativePNTNormalizedFloorSelbergMass (N : ℕ) : ℝ :=
  (∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)) / (N : ℝ)

/-- Nonnegative weight attached to the reciprocal quotient `floor(N/d)` after
normalization.  The floor factor is retained exactly. -/
def nativePNTNormalizedFloorWeight (N d : ℕ) : ℝ :=
  Λ d * ((N / d : ℕ) : ℝ) / (N : ℝ)

/-- The normalized reciprocal transform written directly as a weighted average
of normalized errors on smaller quotient fibres. -/
def nativePNTNormalizedFloorAverage (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    nativePNTNormalizedFloorWeight N d * nativePNTNormalizedError (N / d)

/-- Explicit scale-free constant inherited from the signed first Selberg
recurrence. -/
def nativePNTNormalizedSelbergConstant : ℝ :=
  3 * (Real.log 4 + 2) + 173

/-- Public finite telescope used by the normalized Abel and signed-kernel
layers. -/
theorem nativeTelescopeDiffIco
    (b : ℕ → ℝ) : ∀ M : ℕ, 1 ≤ M →
    (∑ n ∈ Finset.Ico 1 M, (b (n + 1) - b n)) = b M - b 1 := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
      rw [Finset.sum_Ico_succ_top hM, ih]
      ring

/-- On positive endpoints, normalized error is exactly `psi(N) / N - 1`. -/
theorem nativePNTNormalizedError_eq_psi_div_sub_one
    (N : ℕ) (hN : 1 ≤ N) :
    nativePNTNormalizedError N = nativePsi N / (N : ℝ) - 1 := by
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  unfold nativePNTNormalizedError nativePNTError
  field_simp [hNne]

/-- The elementary Chebyshev estimate gives a uniform bound for the normalized
error.  This is used later to control local scale changes without introducing
an affine intercept. -/
theorem nativePNTNormalizedError_abs_le_const
    (N : ℕ) (hN : 1 ≤ N) :
    |nativePNTNormalizedError N| ≤ Real.log 4 + 3 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have h := nativePNTError_abs_le_const_mul N
  unfold nativePNTNormalizedError
  rw [abs_div, abs_of_pos hNpos]
  apply (div_le_iff₀ hNpos).2
  simpa [mul_assoc] using h

/-- The exact normalized reciprocal term is the barycentric transform of the
normalized quotient errors.  No floor approximation is made. -/
theorem nativePNTNormalizedFloorSelbergMass_eq_average
    (N : ℕ) (hN : 1 ≤ N) :
    nativePNTNormalizedFloorSelbergMass N =
      nativePNTNormalizedFloorAverage N := by
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  unfold nativePNTNormalizedFloorSelbergMass
    nativePNTNormalizedFloorAverage
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdI := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := by omega
  have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).2 hdI.2
  have hqne : (((N / d : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show N / d ≠ 0 by omega)
  unfold nativePNTNormalizedFloorWeight nativePNTNormalizedError
  field_simp [hNne, hqne]

/-- Every normalized floor weight is nonnegative. -/
theorem nativePNTNormalizedFloorWeight_nonneg
    (N d : ℕ) :
    0 ≤ nativePNTNormalizedFloorWeight N d := by
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  unfold nativePNTNormalizedFloorWeight
  exact div_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)) hN0

/-- The total barycentric weight is exactly `log(N!) / N`. -/
theorem nativePNTNormalizedFloorWeight_sum_eq_logFactorial_div
    (N : ℕ) (_hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, nativePNTNormalizedFloorWeight N d) =
      Real.log ((Nat.factorial N : ℕ) : ℝ) / (N : ℝ) := by
  unfold nativePNTNormalizedFloorWeight
  rw [← Finset.sum_div, nativeVonMangoldtSummatory]

/-- The total normalized weight differs from
`log N - 1 + 1/N` by at most `log N / N`.  This is the sharp finite form of
the fact that the signed recurrence is a near-averaging law of logarithmic
mass. -/
theorem nativePNTNormalizedFloorWeight_sum_sub_main_abs_le
    (N : ℕ) (hN : 1 ≤ N) :
    |(∑ d ∈ Finset.Icc 1 N, nativePNTNormalizedFloorWeight N d) -
        (Real.log (N : ℝ) - 1 + 1 / (N : ℝ))| ≤
      Real.log (N : ℝ) / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hfac := nativeLogFactorial_sub_main_abs_le N hN
  rw [nativePNTNormalizedFloorWeight_sum_eq_logFactorial_div N hN]
  have hrearrange :
      Real.log ((Nat.factorial N : ℕ) : ℝ) / (N : ℝ) -
          (Real.log (N : ℝ) - 1 + 1 / (N : ℝ)) =
        (Real.log ((Nat.factorial N : ℕ) : ℝ) -
          ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1)) / (N : ℝ) := by
    field_simp [ne_of_gt hNpos]
  rw [hrearrange, abs_div, abs_of_pos hNpos]
  exact (div_le_div_iff_of_pos_right hNpos).2 hfac

/-- **Scale-free normalized signed Selberg recurrence.**

For every `N >= 3`,

`| e(N) log N + N^(-1) * sum_{d<=N} Lambda(d) E(floor(N/d)) | <= C`,

where `e(N) = E(N)/N` and `C` is an absolute explicit constant.  The crucial
point is that the right side no longer grows with `N`: the linear signed
Selberg remainder disappears after normalization rather than being propagated
as an affine intercept. -/
theorem nativePNTNormalized_signed_first_recurrence_abs_le
    (N : ℕ) (hN : 3 ≤ N) :
    |nativePNTNormalizedError N * Real.log (N : ℝ) +
        nativePNTNormalizedFloorSelbergMass N| ≤
      nativePNTNormalizedSelbergConstant := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hsigned := nativePNTError_signed_log_sum_abs_le N hN
  have hrearrange :
      nativePNTNormalizedError N * Real.log (N : ℝ) +
          nativePNTNormalizedFloorSelbergMass N =
        (nativePNTError N * Real.log (N : ℝ) +
          ∑ d ∈ Finset.Icc 1 N,
            Λ d * nativePNTError (N / d)) / (N : ℝ) := by
    unfold nativePNTNormalizedError nativePNTNormalizedFloorSelbergMass
    ring
  rw [hrearrange, abs_div, abs_of_pos hNpos]
  apply (div_le_iff₀ hNpos).2
  simpa [nativePNTNormalizedSelbergConstant] using hsigned

/-- Barycentric form of the scale-free signed recurrence.  The entire recursive
term is now a nonnegative weighted average of normalized quotient errors. -/
theorem nativePNTNormalized_signed_first_recurrence_average_abs_le
    (N : ℕ) (hN : 3 ≤ N) :
    |nativePNTNormalizedError N * Real.log (N : ℝ) +
        nativePNTNormalizedFloorAverage N| ≤
      nativePNTNormalizedSelbergConstant := by
  rw [← nativePNTNormalizedFloorSelbergMass_eq_average N (by omega)]
  exact nativePNTNormalized_signed_first_recurrence_abs_le N hN

end RHLean.Analysis
