import Mathlib.Analysis.Complex.Trigonometric
import RHLean.Analysis.ComplexQuadraticPhase

namespace RHLean.QuadraticPrimePhase

/-- An integer number of half turns has complex exponential `(-1)^n`. -/
theorem exp_int_mul_pi_mul_I_eq_neg_one_pow
    (n : ℤ) :
    Complex.exp
        (((n : ℂ) * (Real.pi : ℂ)) * Complex.I) =
      (-1 : ℂ) ^ n := by
  rw [mul_assoc, Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- Adding `r * k` to a numerator modulo `2*r` contributes exactly `(-1)^k`. -/
theorem additiveCharacter_add_half_modulus
    {r x k : ℤ}
    (hr : r ≠ 0) :
    additiveCharacter (2 * r) (x + r * k) =
      (-1 : ℂ) ^ k * additiveCharacter (2 * r) x := by
  have hrC : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr
  have hquot :
      ((x + r * k : ℤ) : ℂ) / ((2 * r : ℤ) : ℂ) =
        (x : ℂ) / ((2 * r : ℤ) : ℂ) + (k : ℂ) / 2 := by
    push_cast
    field_simp [hrC]
  have hturn :
      ((k : ℂ) / 2) *
          (2 * (Real.pi : ℂ) * Complex.I) =
        ((k : ℂ) * (Real.pi : ℂ)) * Complex.I := by
    ring
  unfold additiveCharacter
  rw [hquot, add_mul, Complex.exp_add, hturn,
    exp_int_mul_pi_mul_I_eq_neg_one_pow]
  ring

/-- Shifting the quadratic input by `r` contributes the parity sign `(-1)^(a*r)`. -/
theorem quadraticPhase_shift_r
    (a r u : ℤ) :
    quadraticPhase a r (u + r) =
      (-1 : ℂ) ^ (a * r) * quadraticPhase a r u := by
  by_cases hr : r = 0
  · subst r
    simp [quadraticPhase, additiveCharacter]
  · calc
      quadraticPhase a r (u + r) =
          additiveCharacter (2 * r)
            (a * u ^ 2 + (2 * r) * (a * u) + r * (a * r)) := by
              unfold quadraticPhase
              congr 1
              ring
      _ = additiveCharacter (2 * r)
          (a * u ^ 2 + r * (a * r)) := by
            apply additiveCharacter_eq_of_sub_dvd
            refine ⟨a * u, ?_⟩
            ring
      _ = (-1 : ℂ) ^ (a * r) *
          additiveCharacter (2 * r) (a * u ^ 2) := by
            exact additiveCharacter_add_half_modulus hr
      _ = (-1 : ℂ) ^ (a * r) * quadraticPhase a r u := by
            rfl

end RHLean.QuadraticPrimePhase
