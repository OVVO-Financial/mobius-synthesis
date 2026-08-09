import RHLean.Proof.NormalizedCofactorExpansion

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace RHLean.Proof

/-- Möbius changes sign when a new prime factor `3` is introduced. -/
theorem moebius_three_mul
    (c : ℕ) (h3 : ¬ 3 ∣ c) :
    (((μ (3 * c) : ℤ) : ℚ)) = -(((μ c : ℤ) : ℚ)) := by
  have hcop : Nat.Coprime 3 c :=
    Nat.prime_three.coprime_iff_not_dvd.mpr h3
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
  rw [ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  push_cast
  ring

/-- The dyadic multiplicity weight is halved when a new prime factor `3` is introduced. -/
theorem alphaWeightRat_three_mul
    (n : ℕ) (h3 : ¬ 3 ∣ n) :
    alphaWeightRat (3 * n) = (1 / 2 : ℚ) * alphaWeightRat n := by
  unfold alphaWeightRat
  rw [distinctPrimeCount_three_mul n h3, pow_succ]
  field_simp

/-- Tripling the lower cofactor scales the normalized arithmetic coefficient by `-1/2`. -/
theorem normalized_tripling_scaling_rat
    (c q : ℕ) (h3 : ¬ 3 ∣ c * q) :
    normalizedCofactorWeightRat (3 * c) q =
      -(1 / 2 : ℚ) * normalizedCofactorWeightRat c q := by
  have h3c : ¬ 3 ∣ c := by
    intro hc
    exact h3 (dvd_mul_of_dvd_left hc q)
  unfold normalizedCofactorWeightRat
  rw [mul_assoc 3 c q]
  rw [alphaWeightRat_three_mul (c * q) h3, moebius_three_mul c h3c]
  ring

/-- Complex-valued form of the exact normalized tripling scaling law. -/
theorem normalized_tripling_scaling
    (c q : ℕ) (h3 : ¬ 3 ∣ c * q) :
    normalizedCofactorWeight (3 * c) q =
      -(1 / 2 : ℂ) * normalizedCofactorWeight c q := by
  simpa [normalizedCofactorWeight] using
    congrArg (fun x : ℚ => (x : ℂ))
      (normalized_tripling_scaling_rat c q h3)

/-- Exact normalized cancellation identity in `ℚ`: child plus twice parent is zero. -/
theorem normalized_cancellation_identity_rat
    (c q : ℕ) (h3 : ¬ 3 ∣ c * q) :
    normalizedCofactorWeightRat c q +
        2 * normalizedCofactorWeightRat (3 * c) q = 0 := by
  rw [normalized_tripling_scaling_rat c q h3]
  ring

/-- Exact normalized cancellation identity in `ℂ`: child plus twice parent is zero. -/
theorem normalized_cancellation_identity
    (c q : ℕ) (h3 : ¬ 3 ∣ c * q) :
    normalizedCofactorWeight c q +
        2 * normalizedCofactorWeight (3 * c) q = 0 := by
  simpa [normalizedCofactorWeight] using
    congrArg (fun x : ℚ => (x : ℂ))
      (normalized_cancellation_identity_rat c q h3)

end RHLean.Proof
