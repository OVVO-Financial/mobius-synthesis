import Mathlib

namespace RHLean.Analysis

/-- Difference-of-squares factorization for the quadratic phase numerator. -/
theorem quadratic_numerator_sub_factor
    (a u v : ℤ) :
    a * u ^ 2 - a * v ^ 2 = a * (u - v) * (u + v) := by
  ring

/-- Any divisor of the input displacement also divides the quadratic numerator displacement. -/
theorem quadratic_numerator_dvd_of_dvd
    {m a u v : ℤ}
    (h : m ∣ u - v) :
    m ∣ a * u ^ 2 - a * v ^ 2 := by
  rcases h with ⟨k, hk⟩
  refine ⟨a * k * (u + v), ?_⟩
  calc
    a * u ^ 2 - a * v ^ 2 = a * (u - v) * (u + v) :=
      quadratic_numerator_sub_factor a u v
    _ = a * (m * k) * (u + v) := by rw [hk]
    _ = m * (a * k * (u + v)) := by ring

/-- Congruence modulo `2*r` is preserved by the quadratic numerator. -/
theorem two_mul_r_dvd_quadratic_numerator_sub
    {a r u v : ℤ}
    (h : 2 * r ∣ u - v) :
    2 * r ∣ a * u ^ 2 - a * v ^ 2 :=
  quadratic_numerator_dvd_of_dvd h

/-- Shifting by `r` isolates the parity-sensitive multiplier. -/
theorem quadratic_numerator_shift_r
    (a r u : ℤ) :
    a * (u + r) ^ 2 - a * u ^ 2 =
      r * (2 * a * u + a * r) := by
  ring

/-- The shift multiplier has the same parity as `a*r`. -/
theorem two_dvd_shift_multiplier_sub
    (a r u : ℤ) :
    2 ∣ (2 * a * u + a * r) - a * r := by
  refine ⟨a * u, ?_⟩
  ring

/-- Shifting by `2*r` changes the numerator by an explicit multiple of `2*r`. -/
theorem quadratic_numerator_shift_two_mul_r
    (a r u : ℤ) :
    a * (u + 2 * r) ^ 2 - a * u ^ 2 =
      (2 * r) * (2 * a * u + 2 * a * r) := by
  ring

/-- The quadratic numerator is periodic modulo `2*r`. -/
theorem two_mul_r_dvd_quadratic_numerator_shift
    (a r u : ℤ) :
    2 * r ∣ a * (u + 2 * r) ^ 2 - a * u ^ 2 := by
  refine ⟨2 * a * u + 2 * a * r, ?_⟩
  exact quadratic_numerator_shift_two_mul_r a r u

end RHLean.Analysis
