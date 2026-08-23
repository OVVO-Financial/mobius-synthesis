import Mathlib
import RHLean.Analysis.ThreeSlotMertensDegreeOneProjection
import RHLean.Arithmetic.MobiusFourCellEndpointTransfer

/-!
# Degree-one energy criterion for the three-slot route

This module names the quantitative target of the three-slot degree-one route
and wires it into the protected analytic chain.

`ThreeSlotDegreeOneEnergyBoundedStatement` is the squared `K^(1/2+ε)`
cancellation demand for the combined signed degree-one mode
`W_a(K) + W_b(K) + W_c(K)`, stated exactly as the repository states its other
energy criteria.  The theorems below prove it **equivalent** to
`SqrtWheelRecoveredEnergyBoundedStatement`, hence to the protected Mertens- and
square-prefix-energy criteria, hence sufficient for `RiemannHypothesis`.

The only arithmetic inputs are the exact degree-one identity
`mertensSummatory (4K) = W_a + W_b + W_c` and the bounded endpoint transfer
`|M(X) - M(4⌊X/4⌋)| ≤ 3`.  No estimate on any individual slot, state count, or
transition frequency appears anywhere: the statement quantifies the combined
signed mode only.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- **The named contraction target of the three-slot route.**  The combined
signed degree-one mode has square-root-scale energy at complete-cell cutoffs.
This is the exact statement whose proof is the open problem of the route. -/
def ThreeSlotDegreeOneEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ K : ℕ,
        ‖(((threeSlotWa K + threeSlotWb K + threeSlotWc K : ℤ)) : ℂ)‖ ^ 2 ≤
          C * Real.rpow ((K + 1 : ℕ) : ℝ) (1 + ε)

/-- The analytic Mertens summatory function is the complex cast of the integer
Möbius prefix. -/
theorem mertensSummatory_eq_moebiusPrefix_cast (X : ℕ) :
    mertensSummatory X = ((moebiusPrefix X : ℤ) : ℂ) := by
  rw [← sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory,
    sqrtWheelRecoveredPrefix_eq_moebiusPrefix]
  rfl

/-- Squared complex norm of an integer cast, as a real integer quadratic. -/
private theorem threeSlot_norm_intCast_complex_sq (z : ℤ) :
    ‖((z : ℤ) : ℂ)‖ ^ 2 = ((z * z : ℤ) : ℝ) := by
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply]

/-- **Analytic endpoint transfer.**  The Mertens summatory function moves by at
most `3` between an arbitrary cutoff and its complete-cell endpoint. -/
theorem norm_mertensSummatory_sub_fourCell_le (X : ℕ) :
    ‖mertensSummatory X - mertensSummatory (4 * (X / 4))‖ ≤ 3 := by
  have hz := abs_moebiusPrefix_sub_fourCell_le X
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  have hzz : (((moebiusPrefix X - moebiusPrefix (4 * (X / 4))) *
      (moebiusPrefix X - moebiusPrefix (4 * (X / 4))) : ℤ) : ℝ) ≤ 9 := by
    have h9 : (moebiusPrefix X - moebiusPrefix (4 * (X / 4))) *
        (moebiusPrefix X - moebiusPrefix (4 * (X / 4))) ≤ 9 := by nlinarith
    exact_mod_cast h9
  have hsqn : ‖mertensSummatory X - mertensSummatory (4 * (X / 4))‖ ^ 2 ≤ 9 := by
    rw [mertensSummatory_eq_moebiusPrefix_cast,
      mertensSummatory_eq_moebiusPrefix_cast, ← Int.cast_sub,
      threeSlot_norm_intCast_complex_sq]
    exact hzz
  nlinarith [norm_nonneg (mertensSummatory X - mertensSummatory (4 * (X / 4))),
    hsqn,
    sq_nonneg (‖mertensSummatory X - mertensSummatory (4 * (X / 4))‖ - 3)]

/-- **The assigned bridge.**  The degree-one energy statement at complete-cell
cutoffs is sufficient for the recovered square-root-wheel energy criterion at
every physical cutoff.  Constants: `C ↦ 2C + 18`, with no reparameterization
of `ε` required since `K = ⌊X/4⌋ ≤ X`. -/
theorem sqrtWheelRecoveredEnergyBounded_of_threeSlotDegreeOneEnergy
    (h : ThreeSlotDegreeOneEnergyBoundedStatement) :
    SqrtWheelRecoveredEnergyBoundedStatement := by
  intro ε hε
  rcases h ε hε with ⟨C, hC, hbound⟩
  refine ⟨2 * C + 18, by positivity, ?_⟩
  intro X
  have hεexp : (0 : ℝ) ≤ 1 + ε := by linarith
  -- complete-cell value controls the physical value up to the endpoint defect
  have htri : ‖mertensSummatory X‖ ≤ ‖mertensSummatory (4 * (X / 4))‖ + 3 := by
    have hsplit : mertensSummatory X =
        mertensSummatory (4 * (X / 4)) +
          (mertensSummatory X - mertensSummatory (4 * (X / 4))) := by ring
    calc ‖mertensSummatory X‖
        = ‖mertensSummatory (4 * (X / 4)) +
            (mertensSummatory X - mertensSummatory (4 * (X / 4)))‖ := by
          rw [← hsplit]
      _ ≤ ‖mertensSummatory (4 * (X / 4))‖ +
            ‖mertensSummatory X - mertensSummatory (4 * (X / 4))‖ :=
          norm_add_le _ _
      _ ≤ ‖mertensSummatory (4 * (X / 4))‖ + 3 := by
          have := norm_mertensSummatory_sub_fourCell_le X
          linarith
  -- the complete-cell energy is the degree-one energy
  have hcell : ‖mertensSummatory (4 * (X / 4))‖ ^ 2 ≤
      C * Real.rpow ((X / 4 + 1 : ℕ) : ℝ) (1 + ε) := by
    rw [mertensSummatory_four_mul_eq_degreeOne]
    exact hbound (X / 4)
  -- squared triangle absorption: (a + 3)^2 ≤ 2 a^2 + 18
  have hsq : ‖mertensSummatory X‖ ^ 2 ≤
      2 * ‖mertensSummatory (4 * (X / 4))‖ ^ 2 + 18 := by
    have hplus : (0 : ℝ) ≤
        ‖mertensSummatory (4 * (X / 4))‖ + 3 + ‖mertensSummatory X‖ := by
      positivity
    nlinarith [htri, hplus,
      sq_nonneg (‖mertensSummatory (4 * (X / 4))‖ - 3),
      norm_nonneg (mertensSummatory X),
      norm_nonneg (mertensSummatory (4 * (X / 4)))]
  -- monotone transport of the scale factor from K + 1 to X + 1
  have hmono : Real.rpow ((X / 4 + 1 : ℕ) : ℝ) (1 + ε) ≤
      Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε) := by
    apply Real.rpow_le_rpow (by positivity) _ hεexp
    exact_mod_cast Nat.succ_le_succ (Nat.div_le_self X 4)
  have hone : (1 : ℝ) ≤ Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε) := by
    have hbase : (1 : ℝ) ≤ ((X + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left 1 X
    have h1 := Real.rpow_le_rpow zero_le_one hbase hεexp
    simpa [Real.one_rpow] using h1
  rw [sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory]
  calc ‖mertensSummatory X‖ ^ 2
      ≤ 2 * ‖mertensSummatory (4 * (X / 4))‖ ^ 2 + 18 := hsq
    _ ≤ 2 * (C * Real.rpow ((X / 4 + 1 : ℕ) : ℝ) (1 + ε)) + 18 := by
        linarith
    _ ≤ 2 * (C * Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε)) + 18 := by
        have := mul_le_mul_of_nonneg_left hmono hC
        linarith
    _ ≤ 2 * (C * Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε)) +
          18 * Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε) := by
        linarith
    _ = (2 * C + 18) * Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε) := by ring

/-- **Converse direction.**  The recovered-wheel energy criterion restricts to
the complete-cell family, so the degree-one statement is not merely sufficient
but exactly equivalent.  Constants: `C ↦ C · 4^(1+ε)`. -/
theorem threeSlotDegreeOneEnergy_of_sqrtWheelRecoveredEnergy
    (h : SqrtWheelRecoveredEnergyBoundedStatement) :
    ThreeSlotDegreeOneEnergyBoundedStatement := by
  intro ε hε
  rcases h ε hε with ⟨C, hC, hbound⟩
  have hεexp : (0 : ℝ) ≤ 1 + ε := by linarith
  refine ⟨C * Real.rpow 4 (1 + ε), ?_, ?_⟩
  · have : (0 : ℝ) ≤ Real.rpow 4 (1 + ε) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    positivity
  intro K
  have hX := hbound (4 * K)
  rw [sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory,
    mertensSummatory_four_mul_eq_degreeOne] at hX
  have hscale : Real.rpow ((4 * K + 1 : ℕ) : ℝ) (1 + ε) ≤
      Real.rpow 4 (1 + ε) * Real.rpow ((K + 1 : ℕ) : ℝ) (1 + ε) := by
    have hle : ((4 * K + 1 : ℕ) : ℝ) ≤ 4 * ((K + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    calc Real.rpow ((4 * K + 1 : ℕ) : ℝ) (1 + ε)
        ≤ Real.rpow (4 * ((K + 1 : ℕ) : ℝ)) (1 + ε) :=
          Real.rpow_le_rpow (by positivity) hle hεexp
      _ = Real.rpow 4 (1 + ε) * Real.rpow ((K + 1 : ℕ) : ℝ) (1 + ε) :=
          Real.mul_rpow (by norm_num) (by positivity)
  calc ‖(((threeSlotWa K + threeSlotWb K + threeSlotWc K : ℤ)) : ℂ)‖ ^ 2
      ≤ C * Real.rpow ((4 * K + 1 : ℕ) : ℝ) (1 + ε) := hX
    _ ≤ C * (Real.rpow 4 (1 + ε) * Real.rpow ((K + 1 : ℕ) : ℝ) (1 + ε)) :=
        mul_le_mul_of_nonneg_left hscale hC
    _ = C * Real.rpow 4 (1 + ε) * Real.rpow ((K + 1 : ℕ) : ℝ) (1 + ε) := by
        ring

/-- The degree-one energy statement is exactly the recovered square-root-wheel
energy criterion: no cancellation is lost in either direction. -/
theorem threeSlotDegreeOneEnergyBounded_iff_sqrtWheelRecoveredEnergyBounded :
    ThreeSlotDegreeOneEnergyBoundedStatement ↔
      SqrtWheelRecoveredEnergyBoundedStatement :=
  ⟨sqrtWheelRecoveredEnergyBounded_of_threeSlotDegreeOneEnergy,
    threeSlotDegreeOneEnergy_of_sqrtWheelRecoveredEnergy⟩

/-- **Chain closure.**  A proof of the degree-one contraction statement yields
the Riemann Hypothesis through the existing protected route; nothing else is
missing between the three-slot target and `RiemannHypothesis`. -/
theorem riemannHypothesis_of_threeSlotDegreeOneEnergy
    (h : ThreeSlotDegreeOneEnergyBoundedStatement) :
    RiemannHypothesis :=
  riemannHypothesis_of_sqrtWheelRecoveredEnergy
    (sqrtWheelRecoveredEnergyBounded_of_threeSlotDegreeOneEnergy h)

end RHLean.Analysis

end
