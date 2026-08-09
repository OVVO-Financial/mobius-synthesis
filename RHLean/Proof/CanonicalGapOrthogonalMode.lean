import Mathlib
import RHLean.Proof.CanonicalGapPrefixGram

open scoped BigOperators

namespace RHLean.Proof

namespace CanonicalGapOrthogonalMode

open CanonicalGapPrefixGram

/-!
# Orthogonal coherent/residual split of canonical-gap prefixes

The numerical scan showed that raw balanced/extreme anti-alignment contains a dominant
linear prefix mode and, on long windows, a second anti-alignment in the orthogonal
residual. This file records the exact finite algebra without introducing division.
-/

/-- Squared norm of the linear prefix vector `(1,2,...,H)`. -/
def timeNormSq (H : ℕ) : ℤ :=
  ∑ r ∈ Finset.range H, (((r + 1 : ℕ) : ℤ) ^ 2)

/-- Inner product of a prefix vector with `(1,2,...,H)`. -/
def timePrefixInner (H : ℕ) (a : ℕ → ℤ) : ℤ :=
  ∑ r ∈ Finset.range H, ((r + 1 : ℕ) : ℤ) * prefixSum H a r

/-- Division-free numerator of the cross energy after orthogonal projection away
from the linear prefix vector. -/
def orthogonalResidualCrossNumerator
    (H : ℕ) (a b : ℕ → ℤ) : ℤ :=
  timeNormSq H * prefixCrossEnergy H a b -
    timePrefixInner H a * timePrefixInner H b

/-- Division-free numerator of the orthogonal residual energy. -/
def orthogonalResidualEnergyNumerator
    (H : ℕ) (a : ℕ → ℤ) : ℤ :=
  timeNormSq H * prefixEnergy H a - timePrefixInner H a ^ 2

/-- The coherent inner product is additive. -/
theorem timePrefixInner_add (H : ℕ) (a b : ℕ → ℤ) :
    timePrefixInner H (fun i => a i + b i) =
      timePrefixInner H a + timePrefixInner H b := by
  unfold timePrefixInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [prefixSum_add]
  ring

/-- Exact Pythagorean numerator identity for one sequence. -/
theorem timeNormSq_mul_prefixEnergy_eq_coherent_add_residual
    (H : ℕ) (a : ℕ → ℤ) :
    timeNormSq H * prefixEnergy H a =
      timePrefixInner H a ^ 2 + orthogonalResidualEnergyNumerator H a := by
  unfold orthogonalResidualEnergyNumerator
  ring

/-- The residual numerator has the same balanced/extreme Gram ledger. -/
theorem orthogonalResidualEnergyNumerator_add
    (H : ℕ) (a b : ℕ → ℤ) :
    orthogonalResidualEnergyNumerator H (fun i => a i + b i) =
      orthogonalResidualEnergyNumerator H a +
        2 * orthogonalResidualCrossNumerator H a b +
          orthogonalResidualEnergyNumerator H b := by
  unfold orthogonalResidualEnergyNumerator orthogonalResidualCrossNumerator
  rw [prefixEnergy_add, timePrefixInner_add]
  ring

/-- Exact two-mode decomposition of the combined prefix energy: coherent linear mode
plus the coupled orthogonal residual. -/
theorem combined_prefix_energy_two_mode_decomposition
    (H : ℕ) (a b : ℕ → ℤ) :
    timeNormSq H * prefixEnergy H (fun i => a i + b i) =
      (timePrefixInner H a + timePrefixInner H b) ^ 2 +
        orthogonalResidualEnergyNumerator H a +
        2 * orthogonalResidualCrossNumerator H a b +
        orthogonalResidualEnergyNumerator H b := by
  rw [timeNormSq_mul_prefixEnergy_eq_coherent_add_residual,
    timePrefixInner_add, orthogonalResidualEnergyNumerator_add]
  ring

/-- Arithmetic balanced/extreme instantiation of the exact two-mode decomposition. -/
theorem balanced_extreme_two_mode_decomposition
    (H N K : ℕ) :
    timeNormSq H *
        prefixEnergy H
          (fun r =>
            BalancedCanonicalGap.balancedHighBandBlockIncrement (N + r) K +
            BalancedCanonicalGap.extremeHighBandBlockIncrement (N + r) K) =
      (timePrefixInner H
          (fun r => BalancedCanonicalGap.balancedHighBandBlockIncrement (N + r) K) +
        timePrefixInner H
          (fun r => BalancedCanonicalGap.extremeHighBandBlockIncrement (N + r) K)) ^ 2 +
      orthogonalResidualEnergyNumerator H
          (fun r => BalancedCanonicalGap.balancedHighBandBlockIncrement (N + r) K) +
      2 * orthogonalResidualCrossNumerator H
          (fun r => BalancedCanonicalGap.balancedHighBandBlockIncrement (N + r) K)
          (fun r => BalancedCanonicalGap.extremeHighBandBlockIncrement (N + r) K) +
      orthogonalResidualEnergyNumerator H
          (fun r => BalancedCanonicalGap.extremeHighBandBlockIncrement (N + r) K) := by
  exact combined_prefix_energy_two_mode_decomposition H
    (fun r => BalancedCanonicalGap.balancedHighBandBlockIncrement (N + r) K)
    (fun r => BalancedCanonicalGap.extremeHighBandBlockIncrement (N + r) K)

end CanonicalGapOrthogonalMode

end RHLean.Proof
