import Mathlib
import RHLean.Analysis.NativePNTNormalizedContinuity

/-!
# Fixed reciprocal form of the normalized signed Selberg recurrence

The exact normalized recurrence naturally carries the floor weight

`Lambda(d) * floor(N/d) / N`.

For smoothing it is better to work against the fixed logarithmic measure
`Lambda(d) / d`.  The two weights differ only by the fractional part of
`N/d`.  Summed over `d`, this defect is bounded by `psi(N) / N`, hence by an
absolute constant.  Consequently the normalized signed recurrence can be
written with the fixed reciprocal measure and still has an absolute,
scale-free remainder.

This is the finite architecture-native analogue of the normalized Selberg
relation used in quantitative elementary PNT remainder arguments.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Fixed reciprocal von-Mangoldt weight. -/
def nativePNTNormalizedRecipWeight (d : ℕ) : ℝ :=
  Λ d / (d : ℝ)

/-- Fixed reciprocal transform of the normalized error. -/
def nativePNTNormalizedRecipAverage (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    nativePNTNormalizedRecipWeight d * nativePNTNormalizedError (N / d)

/-- Total fixed reciprocal weight on the positive prefix. -/
def nativePNTNormalizedRecipMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, nativePNTNormalizedRecipWeight d

/-- The exact floor weight is bounded above by the fixed reciprocal weight. -/
theorem nativePNTNormalizedFloorWeight_le_recipWeight
    (N d : ℕ) (hN : 1 ≤ N) (hd : d ∈ Finset.Icc 1 N) :
    nativePNTNormalizedFloorWeight N d ≤
      nativePNTNormalizedRecipWeight d := by
  have hdI := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hdRpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hcast : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hscaled := (div_le_div_iff_of_pos_right hNpos).2 hcast
  unfold nativePNTNormalizedFloorWeight nativePNTNormalizedRecipWeight
  calc
    Λ d * ((N / d : ℕ) : ℝ) / (N : ℝ) =
        Λ d * (((N / d : ℕ) : ℝ) / (N : ℝ)) := by ring
    _ ≤ Λ d * (((N : ℝ) / (d : ℝ)) / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hscaled ArithmeticFunction.vonMangoldt_nonneg
    _ = Λ d / (d : ℝ) := by
      field_simp [ne_of_gt hNpos, ne_of_gt hdRpos]

/-- The reciprocal-weight excess over the exact floor weight is at most
`Lambda(d) / N`.  This is the pointwise fractional-floor correction. -/
theorem nativePNTNormalizedRecipWeight_le_floorWeight_add
    (N d : ℕ) (hN : 1 ≤ N) (hd : d ∈ Finset.Icc 1 N) :
    nativePNTNormalizedRecipWeight d ≤
      nativePNTNormalizedFloorWeight N d + Λ d / (N : ℝ) := by
  have hdI := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hdRpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hdivmod : d * (N / d) + N % d = N := Nat.div_add_mod N d
  have hrem : N % d < d := Nat.mod_lt N hdpos
  have hNlt : N < (N / d + 1) * d := by
    calc
      N = d * (N / d) + N % d := hdivmod.symm
      _ < d * (N / d) + d := Nat.add_lt_add_left hrem _
      _ = (N / d + 1) * d := by ring
  have hNltR : (N : ℝ) < (((N / d : ℕ) : ℝ) + 1) * (d : ℝ) := by
    exact_mod_cast hNlt
  have hratio :
      1 / (d : ℝ) ≤ (((N / d : ℕ) : ℝ) + 1) / (N : ℝ) := by
    have hlt : 1 / (d : ℝ) < (((N / d : ℕ) : ℝ) + 1) / (N : ℝ) := by
      rw [div_lt_div_iff₀ hdRpos hNpos]
      simpa [mul_comm] using hNltR
    exact hlt.le
  have hLambda0 : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  have hmul :
      Λ d * (1 / (d : ℝ)) ≤
        Λ d * ((((N / d : ℕ) : ℝ) + 1) / (N : ℝ)) :=
    mul_le_mul_of_nonneg_left hratio hLambda0
  change Λ d / (d : ℝ) ≤
    Λ d * ((N / d : ℕ) : ℝ) / (N : ℝ) + Λ d / (N : ℝ)
  calc
    Λ d / (d : ℝ) = Λ d * (1 / (d : ℝ)) := by ring
    _ ≤ Λ d * ((((N / d : ℕ) : ℝ) + 1) / (N : ℝ)) := hmul
    _ = Λ d * ((N / d : ℕ) : ℝ) / (N : ℝ) + Λ d / (N : ℝ) := by ring

/-- The total floor-to-reciprocal weight defect is nonnegative and at most
`psi(N) / N`. -/
theorem nativePNTNormalizedRecipMass_sub_floor_sum_bounds
    (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ nativePNTNormalizedRecipMass N -
        ∑ d ∈ Finset.Icc 1 N, nativePNTNormalizedFloorWeight N d ∧
    nativePNTNormalizedRecipMass N -
        ∑ d ∈ Finset.Icc 1 N, nativePNTNormalizedFloorWeight N d ≤
      nativePsi N / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hlo :
      (∑ d ∈ Finset.Icc 1 N, nativePNTNormalizedFloorWeight N d) ≤
        nativePNTNormalizedRecipMass N := by
    unfold nativePNTNormalizedRecipMass
    apply Finset.sum_le_sum
    intro d hd
    exact nativePNTNormalizedFloorWeight_le_recipWeight N d hN hd
  have hupPoint :
      ∑ d ∈ Finset.Icc 1 N, nativePNTNormalizedRecipWeight d ≤
        ∑ d ∈ Finset.Icc 1 N,
          (nativePNTNormalizedFloorWeight N d + Λ d / (N : ℝ)) := by
    apply Finset.sum_le_sum
    intro d hd
    exact nativePNTNormalizedRecipWeight_le_floorWeight_add N d hN hd
  have hup :
      nativePNTNormalizedRecipMass N ≤
        (∑ d ∈ Finset.Icc 1 N, nativePNTNormalizedFloorWeight N d) +
          nativePsi N / (N : ℝ) := by
    unfold nativePNTNormalizedRecipMass at hupPoint ⊢
    rw [Finset.sum_add_distrib] at hupPoint
    have hLambda :
        (∑ d ∈ Finset.Icc 1 N, Λ d / (N : ℝ)) =
          nativePsi N / (N : ℝ) := by
      rw [← Finset.sum_div]
      rfl
    simpa [hLambda] using hupPoint
  constructor
  · linarith
  · linarith

/-- The total floor-to-reciprocal defect is bounded by the same absolute
Chebyshev constant that controls `psi(N) / N`. -/
theorem nativePNTNormalizedRecipMass_sub_floor_sum_le_const
    (N : ℕ) (hN : 1 ≤ N) :
    nativePNTNormalizedRecipMass N -
        ∑ d ∈ Finset.Icc 1 N, nativePNTNormalizedFloorWeight N d ≤
      Real.log 4 + 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hdef := (nativePNTNormalizedRecipMass_sub_floor_sum_bounds N hN).2
  have hpsi := nativePsi_le_const_mul N
  have hpsiDiv : nativePsi N / (N : ℝ) ≤ Real.log 4 + 2 := by
    apply (div_le_iff₀ hNpos).2
    simpa [mul_assoc] using hpsi
  exact hdef.trans hpsiDiv

/-- Replacing exact floor weights by fixed reciprocal weights changes the
normalized transform by only an absolute constant. -/
theorem nativePNTNormalizedRecipAverage_sub_floorAverage_abs_le
    (N : ℕ) (hN : 1 ≤ N) :
    |nativePNTNormalizedRecipAverage N -
        nativePNTNormalizedFloorAverage N| ≤
      (Real.log 4 + 3) * (Real.log 4 + 2) := by
  have hrewrite :
      nativePNTNormalizedRecipAverage N -
          nativePNTNormalizedFloorAverage N =
        ∑ d ∈ Finset.Icc 1 N,
          (nativePNTNormalizedRecipWeight d -
            nativePNTNormalizedFloorWeight N d) *
              nativePNTNormalizedError (N / d) := by
    unfold nativePNTNormalizedRecipAverage nativePNTNormalizedFloorAverage
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  rw [hrewrite]
  calc
    |∑ d ∈ Finset.Icc 1 N,
        (nativePNTNormalizedRecipWeight d -
          nativePNTNormalizedFloorWeight N d) *
            nativePNTNormalizedError (N / d)| ≤
      ∑ d ∈ Finset.Icc 1 N,
        |(nativePNTNormalizedRecipWeight d -
          nativePNTNormalizedFloorWeight N d) *
            nativePNTNormalizedError (N / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
        (nativePNTNormalizedRecipWeight d -
          nativePNTNormalizedFloorWeight N d) * (Real.log 4 + 3) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdI := Finset.mem_Icc.mp hd
      have hdpos : 0 < d := by omega
      have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).2 hdI.2
      have hcoef := nativePNTNormalizedFloorWeight_le_recipWeight N d hN hd
      have hcoef0 :
          0 ≤ nativePNTNormalizedRecipWeight d -
            nativePNTNormalizedFloorWeight N d := sub_nonneg.mpr hcoef
      have he := nativePNTNormalizedError_abs_le_const (N / d) hq1
      rw [abs_mul, abs_of_nonneg hcoef0]
      exact mul_le_mul_of_nonneg_left he hcoef0
    _ = (nativePNTNormalizedRecipMass N -
          ∑ d ∈ Finset.Icc 1 N, nativePNTNormalizedFloorWeight N d) *
            (Real.log 4 + 3) := by
      unfold nativePNTNormalizedRecipMass
      rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    _ ≤ (Real.log 4 + 2) * (Real.log 4 + 3) := by
      have hdef := nativePNTNormalizedRecipMass_sub_floor_sum_le_const N hN
      have hC0 : 0 ≤ Real.log 4 + 3 := by
        have hlog4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
        linarith
      exact mul_le_mul_of_nonneg_right hdef hC0
    _ = (Real.log 4 + 3) * (Real.log 4 + 2) := by ring

/-- Absolute scale-free constant for the fixed-reciprocal normalized recurrence. -/
def nativePNTNormalizedRecipSelbergConstant : ℝ :=
  nativePNTNormalizedSelbergConstant +
    (Real.log 4 + 3) * (Real.log 4 + 2)

/-- **Fixed-reciprocal normalized signed Selberg recurrence.**  The recursive
operator now uses the endpoint-independent logarithmic measure `Lambda(d)/d`,
while all floor effects remain in one absolute constant. -/
theorem nativePNTNormalized_signed_recip_recurrence_abs_le
    (N : ℕ) (hN : 3 ≤ N) :
    |nativePNTNormalizedError N * Real.log (N : ℝ) +
        nativePNTNormalizedRecipAverage N| ≤
      nativePNTNormalizedRecipSelbergConstant := by
  have hfloor := nativePNTNormalized_signed_first_recurrence_average_abs_le N hN
  have hdiff := nativePNTNormalizedRecipAverage_sub_floorAverage_abs_le N (by omega)
  have hdecomp :
      nativePNTNormalizedError N * Real.log (N : ℝ) +
          nativePNTNormalizedRecipAverage N =
        (nativePNTNormalizedError N * Real.log (N : ℝ) +
          nativePNTNormalizedFloorAverage N) +
        (nativePNTNormalizedRecipAverage N -
          nativePNTNormalizedFloorAverage N) := by ring
  rw [hdecomp]
  exact (abs_add_le _ _).trans (add_le_add hfloor hdiff)

end RHLean.Analysis
