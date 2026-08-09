import Mathlib

open scoped ArithmeticFunction.Moebius

namespace RHLean.Arithmetic

/-- Exact Möbius doubling on odd inputs. -/
theorem moebius_two_mul_of_odd (a : ℕ) (ha : Odd a) :
    μ (2 * a) = -μ a := by
  have hcop : Nat.Coprime 2 a := ha.coprime_two_left
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
  rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  simp

end RHLean.Arithmetic
