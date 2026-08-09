import RHLean.Analysis.ComplexQuadraticPhase
import RHLean.Arithmetic.PrimeSquareMod40

namespace RHLean.QuadraticPrimePhase

open RHLean.Arithmetic

/-- The two reduced square classes supported by units modulo `40`. -/
def IsReducedSquareClassMod40 (s : ℕ) : Prop :=
  s = 1 ∨ s = 9

/-- The canonical square residue of a natural input modulo `40`. -/
def squareResidueMod40 (q : ℕ) : ℕ :=
  q ^ 2 % 40

/-- A complex phase mode indexed by a reduced square class modulo `40`. -/
noncomputable def squareClassModeMod40 (a : ℤ) (s : ℕ) : ℂ :=
  additiveCharacter 40 (a * (s : ℤ))

/-- The quadratic phase written directly at modulus `40`. -/
noncomputable def quadraticPhaseMod40 (a : ℤ) (q : ℕ) : ℂ :=
  additiveCharacter 40 (a * (q : ℤ) ^ 2)

/-- Every eligible prime has reduced square class `1` or `9` modulo `40`. -/
theorem prime_squareResidueMod40_isReduced
    {q : ℕ}
    (hq : q.Prime)
    (hq2 : q ≠ 2)
    (hq5 : q ≠ 5) :
    IsReducedSquareClassMod40 (squareResidueMod40 q) := by
  rcases prime_sq_modEq_one_or_nine_40 hq hq2 hq5 with h1 | h9
  · exact Or.inl (by simpa [squareResidueMod40, Nat.ModEq] using h1)
  · exact Or.inr (by simpa [squareResidueMod40, Nat.ModEq] using h9)

/-- A square congruence modulo `40` gives exact equality with its complex class mode. -/
theorem quadraticPhaseMod40_eq_squareClassMode_of_modEq
    (a : ℤ) {q s : ℕ}
    (h : Nat.ModEq 40 (q ^ 2) s) :
    quadraticPhaseMod40 a q = squareClassModeMod40 a s := by
  unfold quadraticPhaseMod40 squareClassModeMod40
  apply additiveCharacter_eq_of_sub_dvd
  have hdvd :
      (40 : ℤ) ∣ ((q ^ 2 : ℕ) : ℤ) - (s : ℤ) := by
    simpa only [neg_sub] using h.dvd.neg_right
  simpa only [Nat.cast_pow, mul_sub] using hdvd.mul_left a

/-- Reducing the square numerator modulo `40` leaves the complex phase unchanged. -/
theorem quadraticPhaseMod40_eq_squareResidueMode
    (a : ℤ) (q : ℕ) :
    quadraticPhaseMod40 a q =
      squareClassModeMod40 a (squareResidueMod40 q) := by
  apply quadraticPhaseMod40_eq_squareClassMode_of_modEq
  exact (Nat.mod_modEq (q ^ 2) 40).symm

/-- The canonical quadratic phase at `r = 20` is exactly the modulus-`40` phase. -/
theorem quadraticPhase_twenty_eq_mod40
    (a : ℤ) (q : ℕ) :
    quadraticPhase a 20 (q : ℤ) = quadraticPhaseMod40 a q := by
  rfl

/-- Every eligible prime phase at modulus `40` lies in one of exactly two square-class modes.

This is a support statement only. It makes no claim about mode coefficients,
multiplicities, cancellation, or reinforcement.
-/
theorem prime_quadraticPhase_twenty_eq_mode_one_or_nine
    {q : ℕ}
    (a : ℤ)
    (hq : q.Prime)
    (hq2 : q ≠ 2)
    (hq5 : q ≠ 5) :
    quadraticPhase a 20 (q : ℤ) = squareClassModeMod40 a 1 ∨
      quadraticPhase a 20 (q : ℤ) = squareClassModeMod40 a 9 := by
  rw [quadraticPhase_twenty_eq_mod40]
  rcases prime_sq_modEq_one_or_nine_40 hq hq2 hq5 with h1 | h9
  · exact Or.inl (quadraticPhaseMod40_eq_squareClassMode_of_modEq a h1)
  · exact Or.inr (quadraticPhaseMod40_eq_squareClassMode_of_modEq a h9)

end RHLean.QuadraticPrimePhase
