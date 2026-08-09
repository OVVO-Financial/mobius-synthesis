import RHLean.Analysis.QuadraticPhasePeriod

namespace RHLean.Analysis

/-- Two integer inputs give the same quadratic phase exponent modulo `2*r`. -/
def QuadraticExponentCongruent (a r u v : ℤ) : Prop :=
  2 * r ∣ a * u ^ 2 - a * v ^ 2

/-- Quadratic exponent congruence is reflexive. -/
theorem quadraticExponentCongruent_refl
    (a r u : ℤ) :
    QuadraticExponentCongruent a r u u := by
  unfold QuadraticExponentCongruent
  simp

/-- Quadratic exponent congruence is symmetric. -/
theorem quadraticExponentCongruent_symm
    {a r u v : ℤ}
    (h : QuadraticExponentCongruent a r u v) :
    QuadraticExponentCongruent a r v u := by
  unfold QuadraticExponentCongruent at h ⊢
  rcases h with ⟨k, hk⟩
  refine ⟨-k, ?_⟩
  calc
    a * v ^ 2 - a * u ^ 2 = -(a * u ^ 2 - a * v ^ 2) := by ring
    _ = -((2 * r) * k) := by rw [hk]
    _ = (2 * r) * (-k) := by ring

/-- Quadratic exponent congruence is transitive. -/
theorem quadraticExponentCongruent_trans
    {a r u v w : ℤ}
    (huv : QuadraticExponentCongruent a r u v)
    (hvw : QuadraticExponentCongruent a r v w) :
    QuadraticExponentCongruent a r u w := by
  unfold QuadraticExponentCongruent at huv hvw ⊢
  rcases huv with ⟨k, hk⟩
  rcases hvw with ⟨l, hl⟩
  refine ⟨k + l, ?_⟩
  calc
    a * u ^ 2 - a * w ^ 2 =
        (a * u ^ 2 - a * v ^ 2) + (a * v ^ 2 - a * w ^ 2) := by ring
    _ = (2 * r) * k + (2 * r) * l := by rw [hk, hl]
    _ = (2 * r) * (k + l) := by ring

/-- Congruent inputs modulo `2*r` give congruent quadratic exponents. -/
theorem quadraticExponentCongruent_of_input_dvd
    {a r u v : ℤ}
    (h : 2 * r ∣ u - v) :
    QuadraticExponentCongruent a r u v := by
  unfold QuadraticExponentCongruent
  exact two_mul_r_dvd_quadratic_numerator_sub h

/-- The quadratic exponent is periodic under a shift by `2*r`. -/
theorem quadraticExponentCongruent_shift_two_mul_r
    (a r u : ℤ) :
    QuadraticExponentCongruent a r (u + 2 * r) u := by
  unfold QuadraticExponentCongruent
  exact two_mul_r_dvd_quadratic_numerator_shift a r u

end RHLean.Analysis
