import RHLean.Geometry.ComplexSquareRecovery

open scoped ArithmeticFunction.Moebius

namespace RHLean.Geometry

/-- The first-hit squared-complex height attached to the factor pair `(p,r)`. -/
noncomputable def firstHitHeight (p r : ℝ) : ℝ :=
  2 * fermatA p r * fermatB p r

/-- The first-hit height is exactly the imaginary coordinate of the squared Fermat point. -/
theorem firstHitHeight_eq (p r : ℝ) :
    firstHitHeight p r = (r ^ 2 - p ^ 2) / 2 := by
  simpa [firstHitHeight] using square_imaginary_coordinate p r

/-- Fixed least factor `p` gives the first-hit parabola in the product coordinate `n = p*r`. -/
theorem firstHitHeight_eq_parabola (p r n : ℝ) (hp : p ≠ 0) (hn : n = p * r) :
    firstHitHeight p r = n ^ 2 / (2 * p ^ 2) - p ^ 2 / 2 := by
  subst n
  rw [firstHitHeight_eq]
  field_simp [hp]

/-- The first-hit Fermat point squares to the vertical fibre at the product `p*r`. -/
theorem firstHitPoint_sq (p r : ℝ) :
    (fermatPoint p r) ^ 2 = ⟨p * r, firstHitHeight p r⟩ := by
  rw [fermatPoint_sq, firstHitHeight_eq]

/-- Removing two prime endpoints preserves the Möbius sign of the middle core. -/
theorem moebius_endpoint_pair_preserves
    (p c q : ℕ)
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpc : Nat.Coprime p c)
    (hpcq : Nat.Coprime (p * c) q) :
    μ (p * c * q) = μ c := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hpcq]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hpc]
  rw [ArithmeticFunction.moebius_apply_prime hp]
  rw [ArithmeticFunction.moebius_apply_prime hq]
  simp

/-- The abstract parity sign attached to a factor count. -/
def factorParitySign (k : ℕ) : ℤ :=
  (-1 : ℤ) ^ k

/-- Endpoint stripping changes the factor count by two and preserves its parity sign. -/
theorem factorParitySign_add_two (k : ℕ) :
    factorParitySign (k + 2) = factorParitySign k := by
  simp [factorParitySign, pow_add]

end RHLean.Geometry
