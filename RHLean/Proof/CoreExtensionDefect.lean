import RHLean.Proof.ComplementaryMainGram

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Analysis

/-- Real local inner product on a translated square-prefix window. -/
def localWindowInner (f g : ℕ → ℝ) (N H : ℕ) : ℝ :=
  ∑ h ∈ Finset.range H, f (N + h) * g (N + h)

/-- Local square energy on a translated window. -/
def localWindowEnergy (f : ℕ → ℝ) (N H : ℕ) : ℝ :=
  localWindowInner f f N H

/-- Finite Möbius-weighted cofactor baseline. -/
def mobiusBaseline
    (cores : Finset ℕ) (baselineIncrement : ℕ → ℕ → ℝ) : ℕ → ℝ :=
  fun t => ∑ c ∈ cores, (μ c : ℝ) * baselineIncrement c t

/-- Dynamic core-extension weight induced by a complementary-main sequence. -/
def dynamicCoreExtensionWeight
    (complementaryMain : ℕ → ℝ)
    (baselineIncrement : ℕ → ℕ → ℝ)
    (N H c : ℕ) : ℝ :=
  localWindowInner complementaryMain (baselineIncrement c) N H

/-- Möbius sum of the dynamic core-extension weights. -/
def weightedCoreExtensionDefect
    (cores : Finset ℕ)
    (complementaryMain : ℕ → ℝ)
    (baselineIncrement : ℕ → ℕ → ℝ)
    (N H : ℕ) : ℝ :=
  ∑ c ∈ cores, (μ c : ℝ) *
    dynamicCoreExtensionWeight complementaryMain baselineIncrement N H c

/--
The complementary-main defect is exactly a finite weighted Möbius sum whenever
the prediction baseline is expanded cofactor by cofactor.
-/
theorem localWindowInner_mobiusBaseline
    (cores : Finset ℕ)
    (complementaryMain : ℕ → ℝ)
    (baselineIncrement : ℕ → ℕ → ℝ)
    (N H : ℕ) :
    localWindowInner complementaryMain
        (mobiusBaseline cores baselineIncrement) N H =
      weightedCoreExtensionDefect cores complementaryMain
        baselineIncrement N H := by
  simp [localWindowInner, mobiusBaseline, weightedCoreExtensionDefect,
    dynamicCoreExtensionWeight, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro h hh
  ring

/-- Complementary main for the numerically identified pair `L` and `P = -Hhat`. -/
def complementaryMainSequence (L prediction : ℕ → ℝ) : ℕ → ℝ :=
  fun t => L t - prediction t

/-- Exact scalar identity behind the coefficient-gap reduction. -/
theorem coefficientGap_numerator_eq_neg_defect
    (L prediction : ℕ → ℝ) (N H : ℕ) :
    localWindowEnergy prediction N H -
        localWindowInner L prediction N H =
      -localWindowInner (complementaryMainSequence L prediction)
        prediction N H := by
  simp only [localWindowEnergy, localWindowInner, complementaryMainSequence]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  ring

/--
If `prediction = -Hhat` has the exact cofactor expansion, the coefficient-gap
numerator is the negative weighted dynamic core-extension sum.
-/
theorem coefficientGap_numerator_eq_weightedCoreExtension
    (cores : Finset ℕ)
    (L : ℕ → ℝ)
    (baselineIncrement : ℕ → ℕ → ℝ)
    (N H : ℕ) :
    localWindowEnergy (mobiusBaseline cores baselineIncrement) N H -
        localWindowInner L (mobiusBaseline cores baselineIncrement) N H =
      -weightedCoreExtensionDefect cores
        (complementaryMainSequence L
          (mobiusBaseline cores baselineIncrement))
        baselineIncrement N H := by
  rw [coefficientGap_numerator_eq_neg_defect]
  rw [localWindowInner_mobiusBaseline]

/--
Exact normalized coefficient-gap formula.  This is the direct bridge from the
orthogonal coefficient in `ComplementaryMainGram` to the weighted Möbius sum.
-/
theorem one_sub_optimalCoefficient_eq_weightedCoreExtension
    (cores : Finset ℕ)
    (L : ℕ → ℝ)
    (baselineIncrement : ℕ → ℕ → ℝ)
    (N H : ℕ)
    (henergy :
      localWindowEnergy (mobiusBaseline cores baselineIncrement) N H ≠ 0) :
    1 - twoVectorOptimalCoefficient
        (localWindowEnergy (mobiusBaseline cores baselineIncrement) N H)
        (localWindowInner L (mobiusBaseline cores baselineIncrement) N H) =
      -weightedCoreExtensionDefect cores
          (complementaryMainSequence L
            (mobiusBaseline cores baselineIncrement))
          baselineIncrement N H /
        localWindowEnergy (mobiusBaseline cores baselineIncrement) N H := by
  unfold twoVectorOptimalCoefficient
  rw [← coefficientGap_numerator_eq_weightedCoreExtension]
  field_simp [henergy]

/-- Explicit decomposition of a dynamic weight into geometric core-extension and error. -/
structure DynamicCoreExtensionApproximation
    (cores : Finset ℕ)
    (dynamic geometric error : ℕ → ℝ) where
  weight_eq : ∀ c ∈ cores, dynamic c = geometric c + error c

/-- Weighted defect splits exactly into geometric and approximation-error sums. -/
theorem weightedDefect_split_geometric_error
    (cores : Finset ℕ)
    (dynamic geometric error : ℕ → ℝ)
    (approx : DynamicCoreExtensionApproximation cores dynamic geometric error) :
    (∑ c ∈ cores, (μ c : ℝ) * dynamic c) =
      (∑ c ∈ cores, (μ c : ℝ) * geometric c) +
        ∑ c ∈ cores, (μ c : ℝ) * error c := by
  calc
    (∑ c ∈ cores, (μ c : ℝ) * dynamic c) =
        ∑ c ∈ cores, (μ c : ℝ) * (geometric c + error c) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [approx.weight_eq c hc]
    _ = (∑ c ∈ cores, (μ c : ℝ) * geometric c) +
        ∑ c ∈ cores, (μ c : ℝ) * error c := by
      simp only [mul_add, Finset.sum_add_distrib]

end RHLean.Analysis
