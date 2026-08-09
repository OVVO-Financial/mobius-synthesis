import RHLean.Analysis.QuadraticExponentCongruence

namespace RHLean.QuadraticPrimePhase

open RHLean.Analysis

/-- The complex additive character with integer numerator and modulus.

The definition is totalized at modulus zero by the ambient field convention. The
number-theoretic application uses modulus `2 * r` with nonzero `r`.
-/
noncomputable def additiveCharacter (modulus numerator : ℤ) : ℂ :=
  Complex.exp
    (((numerator : ℂ) / (modulus : ℂ)) *
      (2 * (Real.pi : ℂ) * Complex.I))

/-- The corrected quadratic phase uses modulus `2 * r`, not modulus `r`. -/
noncomputable def quadraticPhase (a r u : ℤ) : ℂ :=
  additiveCharacter (2 * r) (a * u ^ 2)

/-- Adding a multiple of the modulus to the numerator does not change the additive character. -/
theorem additiveCharacter_eq_of_sub_dvd
    {modulus x y : ℤ}
    (h : modulus ∣ x - y) :
    additiveCharacter modulus x = additiveCharacter modulus y := by
  by_cases hm : modulus = 0
  · subst modulus
    have hsub : x - y = 0 := by simpa using h
    have hxy : x = y := sub_eq_zero.mp hsub
    subst x
    rfl
  · rcases h with ⟨k, hk⟩
    have hxy : x = y + modulus * k := by
      linarith
    have hmC : (modulus : ℂ) ≠ 0 := by
      exact_mod_cast hm
    have hquot :
        (x : ℂ) / (modulus : ℂ) =
          (y : ℂ) / (modulus : ℂ) + (k : ℂ) := by
      rw [hxy]
      push_cast
      field_simp [hmC]
    unfold additiveCharacter
    rw [hquot, add_mul, Complex.exp_add,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Congruent quadratic exponents give exactly the same complex phase. -/
theorem quadraticPhase_eq_of_congruent
    {a r u v : ℤ}
    (h : QuadraticExponentCongruent a r u v) :
    quadraticPhase a r u = quadraticPhase a r v := by
  unfold quadraticPhase
  apply additiveCharacter_eq_of_sub_dvd
  simpa [QuadraticExponentCongruent] using h

/-- Inputs congruent modulo `2 * r` give the same quadratic phase. -/
theorem quadraticPhase_eq_of_input_dvd
    {a r u v : ℤ}
    (h : 2 * r ∣ u - v) :
    quadraticPhase a r u = quadraticPhase a r v := by
  exact quadraticPhase_eq_of_congruent
    (quadraticExponentCongruent_of_input_dvd h)

/-- The complex quadratic phase is periodic under the basic shift by `2 * r`. -/
theorem quadraticPhase_shift_two_mul_r
    (a r u : ℤ) :
    quadraticPhase a r (u + 2 * r) = quadraticPhase a r u := by
  exact quadraticPhase_eq_of_congruent
    (quadraticExponentCongruent_shift_two_mul_r a r u)

/-- The complex quadratic phase is periodic under every integer multiple of `2 * r`. -/
theorem quadraticPhase_shift_multiple_two_mul_r
    (a r u k : ℤ) :
    quadraticPhase a r (u + k * (2 * r)) = quadraticPhase a r u := by
  apply quadraticPhase_eq_of_input_dvd
  refine ⟨k, ?_⟩
  ring

/-- The zero numerator has phase one. -/
theorem additiveCharacter_zero
    (modulus : ℤ) :
    additiveCharacter modulus 0 = 1 := by
  simp [additiveCharacter]

/-- The quadratic phase at the zero input is one. -/
theorem quadraticPhase_zero
    (a r : ℤ) :
    quadraticPhase a r 0 = 1 := by
  simp [quadraticPhase, additiveCharacter]

end RHLean.QuadraticPrimePhase
