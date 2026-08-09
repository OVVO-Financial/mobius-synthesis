import RHLean.Analysis.QuadraticExponentCongruence

namespace RHLean.Analysis

/-- The quadratic exponent changes by half the modulus between two inputs. -/
def QuadraticExponentHalfShifted (a r u v : ℤ) : Prop :=
  2 * r ∣ (a * u ^ 2 - a * v ^ 2) - r

/-- If `a*r` is even, shifting the input by `r` preserves the exponent modulo `2*r`. -/
theorem quadraticExponentCongruent_shift_r_of_two_dvd
    {a r u : ℤ}
    (h : 2 ∣ a * r) :
    QuadraticExponentCongruent a r (u + r) u := by
  unfold QuadraticExponentCongruent
  rcases h with ⟨k, hk⟩
  refine ⟨a * u + k, ?_⟩
  calc
    a * (u + r) ^ 2 - a * u ^ 2 =
        r * (2 * a * u + a * r) := quadratic_numerator_shift_r a r u
    _ = r * (2 * a * u + 2 * k) := by rw [hk]
    _ = (2 * r) * (a * u + k) := by ring

/-- If `a*r` is odd, shifting the input by `r` changes the exponent by `r` modulo `2*r`. -/
theorem quadraticExponentHalfShifted_shift_r_of_two_dvd_sub_one
    {a r u : ℤ}
    (h : 2 ∣ a * r - 1) :
    QuadraticExponentHalfShifted a r (u + r) u := by
  unfold QuadraticExponentHalfShifted
  rcases h with ⟨k, hk⟩
  have har : a * r = 2 * k + 1 := by omega
  refine ⟨a * u + k, ?_⟩
  calc
    (a * (u + r) ^ 2 - a * u ^ 2) - r =
        r * (2 * a * u + a * r) - r := by
          rw [quadratic_numerator_shift_r]
    _ = r * (2 * a * u + (2 * k + 1)) - r := by rw [har]
    _ = (2 * r) * (a * u + k) := by ring

/-- Every integer product is either even or congruent to `1` modulo `2`. -/
theorem two_dvd_mul_or_sub_one
    (a r : ℤ) :
    2 ∣ a * r ∨ 2 ∣ a * r - 1 := by
  omega

/-- A shift by `r` either preserves the exponent or moves it by half the modulus. -/
theorem quadratic_shift_r_dichotomy
    (a r u : ℤ) :
    QuadraticExponentCongruent a r (u + r) u ∨
      QuadraticExponentHalfShifted a r (u + r) u := by
  rcases two_dvd_mul_or_sub_one a r with heven | hodd
  · exact Or.inl (quadraticExponentCongruent_shift_r_of_two_dvd heven)
  · exact Or.inr (quadraticExponentHalfShifted_shift_r_of_two_dvd_sub_one hodd)

end RHLean.Analysis
