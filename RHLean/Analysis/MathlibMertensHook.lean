import RHLean.Analysis.ConcreteSquarePrefixGeometry
import RHLean.Analysis.DeterministicTGreenKuboComparison

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/--
The zero-friction integration point for a future mathlib Mertens theorem.

A caller supplies the classical equivalence itself; no project-specific bridge,
realization, indexing adapter, or structure constructor appears in the theorem
signature.
-/
theorem squarePrefix_highUniformLocalBounded_iff_riemannHypothesis_of_classical_iff
    (partition : SquarePrefixGeometricPartition)
    (criterion : MertensEnergyBoundedStatement ↔ RiemannHypothesisStatement) :
    SquarePrefixHighUniformLocalBoundedStatement partition ↔
      RiemannHypothesisStatement := by
  exact squarePrefix_highUniformLocalBounded_iff_riemannHypothesis
    partition ⟨criterion⟩

/-! ## Exact Möbius-zero covariance threshold -/

/-- Exact number of physical sites `1 <= n <= x` on which Möbius vanishes. -/
def realMertensZeroCount (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter fun n => μ n = 0).card

/-- Real-valued zero indicator for one physical Möbius site. -/
def realMoebiusZeroIndicator (n : ℕ) : ℝ :=
  if μ n = 0 then 1 else 0

/-- Squared Möbius mass plus the zero indicator is exactly one. -/
theorem realMoebiusStep_sq_add_zeroIndicator_eq_one (n : ℕ) :
    realMoebiusStep n ^ 2 + realMoebiusZeroIndicator n = 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [realMoebiusStep, realMoebiusZeroIndicator, h]

/-- The real sum of zero indicators is the exact finite zero count. -/
theorem sum_realMoebiusZeroIndicator_eq_zeroCount (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, realMoebiusZeroIndicator n) =
      (realMertensZeroCount x : ℝ) := by
  classical
  unfold realMertensZeroCount realMoebiusZeroIndicator
  simp

/-- The Green--Kubo diagonal at endpoint `x` is exactly the number of nonzero
Möbius sites in `1,...,x`. The `n = 0` site contributes zero and disappears. -/
theorem realMertensDiagonal_add_zeroCount_eq_endpoint (x : ℕ) :
    realMertensDiagonal (x + 1) + (realMertensZeroCount x : ℝ) = (x : ℝ) := by
  have hdiag :
      realMertensDiagonal (x + 1) =
        ∑ n ∈ Finset.Icc 1 x, realMoebiusStep n ^ 2 := by
    unfold realMertensDiagonal
    rw [show Finset.range (x + 1) = {0} ∪ Finset.Icc 1 x by
      ext n
      simp
      omega]
    rw [Finset.sum_union]
    · simp [realMoebiusStep]
    · rw [Finset.disjoint_left]
      intro n hn0 hnIcc
      simp at hn0
      subst n
      simp at hnIcc
  rw [hdiag, ← sum_realMoebiusZeroIndicator_eq_zeroCount]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ n ∈ Finset.Icc 1 x,
        (realMoebiusStep n ^ 2 + realMoebiusZeroIndicator n)) =
      ∑ _n ∈ Finset.Icc 1 x, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro n _hn
        exact realMoebiusStep_sq_add_zeroIndicator_eq_one n
    _ = (x : ℝ) := by simp

/-- Exact endpoint Green--Kubo identity with the Möbius-zero population exposed
instead of hidden inside the diagonal. -/
theorem norm_mertensSummatory_sq_eq_endpoint_sub_zeroCount_add_two_covariance
    (x : ℕ) :
    ‖mertensSummatory x‖ ^ 2 =
      (x : ℝ) - (realMertensZeroCount x : ℝ) +
        2 * realMertensPositiveLagPairSum (x + 1) := by
  rw [norm_mertensSummatory_sq_eq_realMertensLength_sq,
    realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum]
  have hdiag := realMertensDiagonal_add_zeroCount_eq_endpoint x
  nlinarith

/-- **Crossing the square-root boundary forces positive covariance.** -/
theorem half_zeroCount_lt_positiveLagPairSum_of_sqrt_lt_norm_mertens
    {x : ℕ} (h : Real.sqrt (x : ℝ) < ‖mertensSummatory x‖) :
    ((realMertensZeroCount x : ℝ) / 2) <
      realMertensPositiveLagPairSum (x + 1) := by
  have hx : 0 ≤ (x : ℝ) := by positivity
  have hsqrt : 0 ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
  have hsqroot :
      Real.sqrt (x : ℝ) ^ 2 < ‖mertensSummatory x‖ ^ 2 :=
    (sq_lt_sq₀ hsqrt (norm_nonneg (mertensSummatory x))).2 h
  have hsq : (x : ℝ) < ‖mertensSummatory x‖ ^ 2 := by
    simpa [Real.sq_sqrt hx] using hsqroot
  have hid :=
    norm_mertensSummatory_sq_eq_endpoint_sub_zeroCount_add_two_covariance x
  nlinarith

/-- Non-strict version at the square-root boundary. -/
theorem half_zeroCount_le_positiveLagPairSum_of_sqrt_le_norm_mertens
    {x : ℕ} (h : Real.sqrt (x : ℝ) ≤ ‖mertensSummatory x‖) :
    ((realMertensZeroCount x : ℝ) / 2) ≤
      realMertensPositiveLagPairSum (x + 1) := by
  have hx : 0 ≤ (x : ℝ) := by positivity
  have hsqrt : 0 ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
  have hsqroot :
      Real.sqrt (x : ℝ) ^ 2 ≤ ‖mertensSummatory x‖ ^ 2 :=
    (sq_le_sq₀ hsqrt (norm_nonneg (mertensSummatory x))).2 h
  have hsq : (x : ℝ) ≤ ‖mertensSummatory x‖ ^ 2 := by
    simpa [Real.sq_sqrt hx] using hsqroot
  have hid :=
    norm_mertensSummatory_sq_eq_endpoint_sub_zeroCount_add_two_covariance x
  nlinarith

/-- Quantitative amplitude form: if `|M(x)| >= A*sqrt(x)`, then the required
positive covariance is at least `(A^2*x - x + Z(x))/2`. -/
theorem positiveLagPairSum_lower_of_mul_sqrt_le_norm_mertens
    {x : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (h : A * Real.sqrt (x : ℝ) ≤ ‖mertensSummatory x‖) :
    (A ^ 2 * (x : ℝ) - (x : ℝ) + (realMertensZeroCount x : ℝ)) / 2 ≤
      realMertensPositiveLagPairSum (x + 1) := by
  have hx : 0 ≤ (x : ℝ) := by positivity
  have hsqrt : 0 ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
  have hsq : A ^ 2 * (x : ℝ) ≤ ‖mertensSummatory x‖ ^ 2 := by
    have hnonneg : 0 ≤ A * Real.sqrt (x : ℝ) := mul_nonneg hA hsqrt
    have hsqraw := (sq_le_sq₀ hnonneg (norm_nonneg (mertensSummatory x))).2 h
    simpa [mul_pow, Real.sq_sqrt hx] using hsqraw
  have hid :=
    norm_mertensSummatory_sq_eq_endpoint_sub_zeroCount_add_two_covariance x
  nlinarith

end RHLean.Analysis
