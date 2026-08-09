import Mathlib
import RHLean.Arithmetic.PrimeWheelMobiusRecovery
import RHLean.Arithmetic.PrimeWheelMobiusDensity
import RHLean.Analysis.SquarePrefixMertensBridge

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- Exact integer-valued prefix identity on the `k`th primorial block. -/
theorem primorialWheel_residual_eq_moebiusInterval
    (k : ℕ) {x : ℕ}
    (hupper : x ≤ primorialBlockUpper k) :
    (primorialWheelSystem k).residual x =
      ∑ n ∈ Finset.Ioc (primorialBlockLower k) x, μ n := by
  exact (primorialWheelSystem k).residual_eq_moebius_sum
    (primorialWheelArithmeticCertificate k) hupper

/-- An interval Möbius sum is the difference of the two ordinary Mertens
prefixes. -/
theorem moebius_Ioc_cast_eq_mertens_sub
    {a x : ℕ} (hax : a ≤ x) :
    (∑ n ∈ Finset.Ioc a x, (((μ n : ℤ) : ℂ))) =
      RHLean.Analysis.mertensSummatory x -
        RHLean.Analysis.mertensSummatory a := by
  have hle : a + 1 ≤ x + 1 := Nat.succ_le_succ hax
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun n : ℕ => (((μ n : ℤ) : ℂ))) hle
  unfold RHLean.Analysis.mertensSummatory
  have hinterval : Finset.Ioc a x = Finset.Ico (a + 1) (x + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hinterval]
  apply (eq_sub_iff_add_eq).2
  simpa [add_comm] using hsplit

/-- Exact complex prefix residual identity in the form used by the harmonic
reduction. -/
theorem primorialWheel_residual_cast_eq_mertens_sub
    (k : ℕ) {x : ℕ}
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    (((primorialWheelSystem k).residual x : ℤ) : ℂ) =
      RHLean.Analysis.mertensSummatory x -
        RHLean.Analysis.mertensSummatory (primorialBlockLower k) := by
  rw [primorialWheel_residual_eq_moebiusInterval k hupper]
  push_cast
  exact moebius_Ioc_cast_eq_mertens_sub (Nat.le_of_lt hlower)

/-- Endpoint specialization. -/
theorem primorialWheel_endpointResidual_cast_eq_mertens_sub
    (k : ℕ) :
    (((primorialWheelSystem k).residual (primorialBlockUpper k) : ℤ) : ℂ) =
      RHLean.Analysis.mertensSummatory (primorialBlockUpper k) -
        RHLean.Analysis.mertensSummatory (primorialBlockLower k) := by
  apply primorialWheel_residual_cast_eq_mertens_sub
  · exact (primorialWheelSystem k).lower_lt_upper
  · exact le_rfl

end RHLean.Arithmetic
