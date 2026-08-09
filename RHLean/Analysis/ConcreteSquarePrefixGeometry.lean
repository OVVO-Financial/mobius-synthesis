import Mathlib
import RHLean.Analysis.SquarePrefixMertensBridge

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Uniform local energy control for the concrete square-prefix Mertens sequence. -/
def SquarePrefixUniformLocalBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        localSequenceEnergy squarePrefixMertens N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- An exact low/high geometric partition of the concrete square-prefix sequence. -/
structure SquarePrefixGeometricPartition where
  low : ℕ → ℂ
  high : ℕ → ℂ
  lowConstant : ℝ
  lowConstant_nonneg : 0 ≤ lowConstant
  recombine : ∀ n, squarePrefixMertens n = low n + high n
  low_energy_pointwise :
    ∀ n, ‖low n‖ ^ 2 ≤ lowConstant * (n : ℝ) ^ 2

/-- Local low-sector energy for a concrete square-prefix geometric partition. -/
def squarePrefixLocalLowEnergy
    (partition : SquarePrefixGeometricPartition) (N H : ℕ) : ℝ :=
  localSequenceEnergy partition.low N H

/-- Local high-sector energy for a concrete square-prefix geometric partition. -/
def squarePrefixLocalHighEnergy
    (partition : SquarePrefixGeometricPartition) (N H : ℕ) : ℝ :=
  localSequenceEnergy partition.high N H

/-- The concrete geometric high-sector local criterion. -/
def SquarePrefixHighUniformLocalBoundedStatement
    (partition : SquarePrefixGeometricPartition) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        squarePrefixLocalHighEnergy partition N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

private theorem concrete_norm_sq_add_le_two (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm := norm_add_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x + y‖ := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private theorem concrete_norm_sq_sub_le_two (x y : ℂ) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  simpa [sub_eq_add_neg] using concrete_norm_sq_add_le_two x (-y)

/-- The concrete low sector has the elementary translated-window `H N^2` bound. -/
theorem squarePrefix_localLowEnergy_le
    (partition : SquarePrefixGeometricPartition)
    (N H : ℕ) (hHN : H ≤ N) :
    squarePrefixLocalLowEnergy partition N H ≤
      4 * partition.lowConstant * (H : ℝ) * (N : ℝ) ^ 2 := by
  unfold squarePrefixLocalLowEnergy localSequenceEnergy
  calc
    (∑ h ∈ Finset.range H, ‖partition.low (N + h)‖ ^ 2) ≤
        ∑ _h ∈ Finset.range H,
          4 * partition.lowConstant * (N : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro h hh
      have hlt : h < H := Finset.mem_range.mp hh
      have hindexNat : N + h ≤ 2 * N := by omega
      have hindex : ((N + h : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
        exact_mod_cast hindexNat
      have hsq : ((N + h : ℕ) : ℝ) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by
        have hleft : 0 ≤ ((N + h : ℕ) : ℝ) := by positivity
        have hright : 0 ≤ (N : ℝ) := by positivity
        nlinarith
      calc
        ‖partition.low (N + h)‖ ^ 2 ≤
            partition.lowConstant * ((N + h : ℕ) : ℝ) ^ 2 :=
          partition.low_energy_pointwise (N + h)
        _ ≤ partition.lowConstant * (4 * (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq partition.lowConstant_nonneg
        _ = 4 * partition.lowConstant * (N : ℝ) ^ 2 := by ring
    _ = (H : ℝ) * (4 * partition.lowConstant * (N : ℝ) ^ 2) := by simp
    _ = 4 * partition.lowConstant * (H : ℝ) * (N : ℝ) ^ 2 := by ring

/-- The concrete low sector automatically satisfies the RH-scale local bound. -/
theorem squarePrefix_lowUniformLocalBounded
    (partition : SquarePrefixGeometricPartition) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ N H : ℕ, 1 ≤ H → H ≤ N →
          squarePrefixLocalLowEnergy partition N H ≤
            C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) := by
  intro ε hε
  refine ⟨4 * partition.lowConstant,
    mul_nonneg (by norm_num) partition.lowConstant_nonneg, ?_⟩
  intro N H hH hHN
  have hN1 : 1 ≤ N := hH.trans hHN
  have hbase : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hexponent : (2 : ℝ) ≤ 2 + ε := by linarith
  have hpow : (N : ℝ) ^ 2 ≤ Real.rpow (N : ℝ) (2 + ε) := by
    rw [← Real.rpow_natCast]
    exact (Real.monotone_rpow_of_base_ge_one hbase) hexponent
  have hcoefficient : 0 ≤ 4 * partition.lowConstant * (H : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) partition.lowConstant_nonneg)
      (Nat.cast_nonneg H)
  calc
    squarePrefixLocalLowEnergy partition N H ≤
        4 * partition.lowConstant * (H : ℝ) * (N : ℝ) ^ 2 :=
      squarePrefix_localLowEnergy_le partition N H hHN
    _ ≤ 4 * partition.lowConstant * (H : ℝ) *
          Real.rpow (N : ℝ) (2 + ε) :=
      mul_le_mul_of_nonneg_left hpow hcoefficient

/-- Total concrete energy is controlled by twice the low and high energies. -/
theorem squarePrefix_localEnergy_le_two_low_add_high
    (partition : SquarePrefixGeometricPartition) (N H : ℕ) :
    localSequenceEnergy squarePrefixMertens N H ≤
      2 * squarePrefixLocalLowEnergy partition N H +
        2 * squarePrefixLocalHighEnergy partition N H := by
  unfold squarePrefixLocalLowEnergy squarePrefixLocalHighEnergy localSequenceEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hh
  rw [partition.recombine]
  exact concrete_norm_sq_add_le_two _ _

/-- High concrete energy is controlled by twice the total and low energies. -/
theorem squarePrefix_localHighEnergy_le_two_total_add_low
    (partition : SquarePrefixGeometricPartition) (N H : ℕ) :
    squarePrefixLocalHighEnergy partition N H ≤
      2 * localSequenceEnergy squarePrefixMertens N H +
        2 * squarePrefixLocalLowEnergy partition N H := by
  unfold squarePrefixLocalLowEnergy squarePrefixLocalHighEnergy localSequenceEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hh
  have hhigh : partition.high (N + h) =
      squarePrefixMertens (N + h) - partition.low (N + h) := by
    rw [partition.recombine]
    simp
  rw [hhigh]
  exact concrete_norm_sq_sub_le_two _ _

/-- The concrete total and high-sector local criteria are equivalent. -/
theorem squarePrefix_uniformLocalBounded_iff_highUniformLocalBounded
    (partition : SquarePrefixGeometricPartition) :
    SquarePrefixUniformLocalBoundedStatement ↔
      SquarePrefixHighUniformLocalBoundedStatement partition := by
  constructor
  · intro htotal ε hε
    rcases htotal ε hε with ⟨Ctotal, hCtotal, htotalBound⟩
    rcases squarePrefix_lowUniformLocalBounded partition ε hε with
      ⟨Clow, hClow, hlowBound⟩
    refine ⟨2 * Ctotal + 2 * Clow, by nlinarith, ?_⟩
    intro N H hH hHN
    have htotalNH := htotalBound N H hH hHN
    have hlowNH := hlowBound N H hH hHN
    calc
      squarePrefixLocalHighEnergy partition N H ≤
          2 * localSequenceEnergy squarePrefixMertens N H +
            2 * squarePrefixLocalLowEnergy partition N H :=
        squarePrefix_localHighEnergy_le_two_total_add_low partition N H
      _ ≤ 2 * (Ctotal * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) +
            2 * (Clow * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) := by
        nlinarith
      _ = (2 * Ctotal + 2 * Clow) * (H : ℝ) *
            Real.rpow (N : ℝ) (2 + ε) := by ring
  · intro hhigh ε hε
    rcases hhigh ε hε with ⟨Chigh, hChigh, hhighBound⟩
    rcases squarePrefix_lowUniformLocalBounded partition ε hε with
      ⟨Clow, hClow, hlowBound⟩
    refine ⟨2 * Clow + 2 * Chigh, by nlinarith, ?_⟩
    intro N H hH hHN
    have hlowNH := hlowBound N H hH hHN
    have hhighNH := hhighBound N H hH hHN
    calc
      localSequenceEnergy squarePrefixMertens N H ≤
          2 * squarePrefixLocalLowEnergy partition N H +
            2 * squarePrefixLocalHighEnergy partition N H :=
        squarePrefix_localEnergy_le_two_low_add_high partition N H
      _ ≤ 2 * (Clow * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) +
            2 * (Chigh * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) := by
        nlinarith
      _ = (2 * Clow + 2 * Chigh) * (H : ℝ) *
            Real.rpow (N : ℝ) (2 + ε) := by ring

/-- The concrete local criterion implies the current pointwise square-prefix criterion. -/
theorem squarePrefix_currentPointwise_of_uniformLocalBounded
    (hlocal : SquarePrefixUniformLocalBoundedStatement) :
    SquarePrefixCurrentPointwiseBoundedStatement := by
  intro ε hε
  rcases hlocal ε hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N hN
  have h := hbound N 1 (by simp) hN
  simpa [localSequenceEnergy] using h

/-- The current pointwise square-prefix criterion implies the concrete local criterion. -/
theorem squarePrefix_uniformLocalBounded_of_currentPointwise
    (hpoint : SquarePrefixCurrentPointwiseBoundedStatement) :
    SquarePrefixUniformLocalBoundedStatement := by
  intro ε hε
  rcases hpoint ε hε with ⟨C, hC, hbound⟩
  let K := Real.rpow 2 (2 + ε)
  refine ⟨C * K, mul_nonneg hC (Real.rpow_nonneg (by norm_num) _), ?_⟩
  intro N H hH hHN
  have hN : 1 ≤ N := hH.trans hHN
  unfold localSequenceEnergy
  calc
    (∑ h ∈ Finset.range H, ‖squarePrefixMertens (N + h)‖ ^ 2) ≤
        ∑ _h ∈ Finset.range H,
          (C * K) * Real.rpow (N : ℝ) (2 + ε) := by
      apply Finset.sum_le_sum
      intro h hh
      have hhlt : h < H := Finset.mem_range.mp hh
      have hindex : 1 ≤ N + h := le_add_right hN
      have hboundIndex := hbound (N + h) hindex
      have hindexNat : N + h ≤ 2 * N := by omega
      have hindexR : ((N + h : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hindexNat
      have hexp : 0 ≤ 2 + ε := by linarith
      have hp := Real.rpow_le_rpow (by positivity) hindexR hexp
      have hmul :
          Real.rpow (2 * (N : ℝ)) (2 + ε) =
            Real.rpow 2 (2 + ε) * Real.rpow (N : ℝ) (2 + ε) :=
        Real.mul_rpow (by norm_num) (by positivity)
      calc
        ‖squarePrefixMertens (N + h)‖ ^ 2 ≤
            C * Real.rpow ((N + h : ℕ) : ℝ) (2 + ε) := hboundIndex
        _ ≤ C * Real.rpow (2 * (N : ℝ)) (2 + ε) :=
          mul_le_mul_of_nonneg_left hp hC
        _ = (C * K) * Real.rpow (N : ℝ) (2 + ε) := by
          rw [hmul]
          simp only [K, mul_assoc]
    _ = (H : ℝ) * ((C * K) * Real.rpow (N : ℝ) (2 + ε)) := by simp
    _ = (C * K) * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) := by ring

/-- The concrete local and current pointwise criteria are equivalent. -/
theorem squarePrefix_uniformLocalBounded_iff_currentPointwise :
    SquarePrefixUniformLocalBoundedStatement ↔
      SquarePrefixCurrentPointwiseBoundedStatement := by
  exact ⟨squarePrefix_currentPointwise_of_uniformLocalBounded,
    squarePrefix_uniformLocalBounded_of_currentPointwise⟩

/-- The concrete local criterion is exactly the standard Mertens energy criterion. -/
theorem squarePrefix_uniformLocalBounded_iff_mertensEnergyBounded :
    SquarePrefixUniformLocalBoundedStatement ↔
      MertensEnergyBoundedStatement := by
  calc
    SquarePrefixUniformLocalBoundedStatement ↔
        SquarePrefixCurrentPointwiseBoundedStatement :=
      squarePrefix_uniformLocalBounded_iff_currentPointwise
    _ ↔ SquarePrefixEnergyBoundedStatement :=
      squarePrefixEnergyBounded_iff_currentPointwise.symm
    _ ↔ MertensEnergyBoundedStatement :=
      mertensEnergyBounded_iff_squarePrefixEnergyBounded.symm

/--
The direct geometric equivalence. Once mathlib supplies the standard Mertens
criterion, no project-specific start-sequence realization or RH bridge adapter
remains in this theorem's signature.
-/
theorem squarePrefix_highUniformLocalBounded_iff_riemannHypothesis
    (partition : SquarePrefixGeometricPartition)
    (criterion : ClassicalMertensRHCriterion) :
    SquarePrefixHighUniformLocalBoundedStatement partition ↔
      RiemannHypothesisStatement := by
  calc
    SquarePrefixHighUniformLocalBoundedStatement partition ↔
        SquarePrefixUniformLocalBoundedStatement :=
      (squarePrefix_uniformLocalBounded_iff_highUniformLocalBounded partition).symm
    _ ↔ MertensEnergyBoundedStatement :=
      squarePrefix_uniformLocalBounded_iff_mertensEnergyBounded
    _ ↔ RiemannHypothesisStatement := criterion.iff_riemannHypothesis

end RHLean.Analysis
