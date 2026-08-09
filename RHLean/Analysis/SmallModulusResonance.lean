import RHLean.Analysis.ReducedQuadraticGauss

namespace RHLean.QuadraticPrimePhase

/-- Every unit modulo `6` has square `1`. -/
theorem unit_sq_eq_one_mod_six :
    ∀ u : (ZMod 6)ˣ, (u : ZMod 6) ^ 2 = 1 := by
  native_decide

/-- Every unit modulo `24` has square `1`. -/
theorem unit_sq_eq_one_mod_twenty_four :
    ∀ u : (ZMod 24)ˣ, (u : ZMod 24) ^ 2 = 1 := by
  native_decide

/-- If a unit squares to one modulo `2 * r`, its quadratic phase is the
single additive-character value with numerator `a`. -/
theorem quadraticUnitPhase_eq_additiveCharacter_of_sq_eq_one
    {a : ℤ} {r : ℕ} [NeZero (2 * r)]
    (u : (ZMod (2 * r))ˣ)
    (hu : (u : ZMod (2 * r)) ^ 2 = 1) :
    quadraticUnitPhase a r u =
      additiveCharacter (2 * (r : ℤ)) a := by
  unfold quadraticUnitPhase quadraticPhase
  apply additiveCharacter_eq_of_sub_dvd
  have hz :
      ((a * (u.val.val : ℤ) ^ 2 - a : ℤ) : ZMod (2 * r)) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, hu]
    ring
  have hdvd :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (a * (u.val.val : ℤ) ^ 2 - a) (2 * r)).mp hz
  simpa using hdvd

/-- When all units modulo `2 * r` square to one, the reduced sum is the
totient times one coherent additive-character phase. -/
theorem reducedQuadraticGauss_eq_totient_mul_phase_of_unit_sq
    (a : ℤ) (r : ℕ) (hr : 0 < r)
    (hsq : ∀ u : (ZMod (2 * r))ˣ,
      (u : ZMod (2 * r)) ^ 2 = 1) :
    reducedQuadraticGauss a r hr =
      (Nat.totient (2 * r) : ℂ) *
        additiveCharacter (2 * (r : ℤ)) a := by
  classical
  letI : NeZero (2 * r) :=
    ⟨Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hr)⟩
  have hphase : ∀ u : (ZMod (2 * r))ˣ,
      quadraticUnitPhase a r u =
        additiveCharacter (2 * (r : ℤ)) a :=
    fun u => quadraticUnitPhase_eq_additiveCharacter_of_sq_eq_one u (hsq u)
  simp [reducedQuadraticGauss, hphase, ZMod.card_units_eq_totient]

/-- Under the same square-one hypothesis, normalization removes the exact
unit count and leaves the coherent phase. -/
theorem normalizedReducedQuadraticGauss_eq_phase_of_unit_sq
    (a : ℤ) (r : ℕ) (hr : 0 < r)
    (hsq : ∀ u : (ZMod (2 * r))ˣ,
      (u : ZMod (2 * r)) ^ 2 = 1) :
    normalizedReducedQuadraticGauss a r hr =
      additiveCharacter (2 * (r : ℤ)) a := by
  rw [normalizedReducedQuadraticGauss,
    reducedQuadraticGauss_eq_totient_mul_phase_of_unit_sq a r hr hsq]
  have htotNat : Nat.totient (2 * r) ≠ 0 :=
    (Nat.totient_pos.mpr (Nat.mul_pos (by norm_num) hr)).ne'
  have htot : (Nat.totient (2 * r) : ℂ) ≠ 0 := by
    exact_mod_cast htotNat
  field_simp [htot]

/-- Exact coherent normalized phase for modulus `6`. -/
theorem normalizedReducedQuadraticGauss_mod_six
    (a : ℤ) :
    normalizedReducedQuadraticGauss a 3 (by norm_num) =
      additiveCharacter 6 a := by
  simpa using
    normalizedReducedQuadraticGauss_eq_phase_of_unit_sq
      a 3 (by norm_num) unit_sq_eq_one_mod_six

/-- Exact coherent normalized phase for modulus `24`. -/
theorem normalizedReducedQuadraticGauss_mod_twenty_four
    (a : ℤ) :
    normalizedReducedQuadraticGauss a 12 (by norm_num) =
      additiveCharacter 24 a := by
  simpa using
    normalizedReducedQuadraticGauss_eq_phase_of_unit_sq
      a 12 (by norm_num) unit_sq_eq_one_mod_twenty_four

/-- The corrected normalized factor at `(a, r) = (1, 3)` is exactly `e(1/6)`. -/
theorem normalizedReducedQuadraticGauss_one_three :
    normalizedReducedQuadraticGauss 1 3 (by norm_num) =
      additiveCharacter 6 1 := by
  exact normalizedReducedQuadraticGauss_mod_six 1

/-- Every integer additive-character value lies on the complex unit circle. -/
theorem norm_additiveCharacter
    (modulus numerator : ℤ) :
    ‖additiveCharacter modulus numerator‖ = 1 := by
  simp [additiveCharacter, Complex.norm_exp]

/-- The prime-3 quadratic factor has exact norm one; it is not the rational
cell-mask energy `1/9`. -/
theorem norm_normalizedReducedQuadraticGauss_one_three :
    ‖normalizedReducedQuadraticGauss 1 3 (by norm_num)‖ = 1 := by
  rw [normalizedReducedQuadraticGauss_one_three]
  exact norm_additiveCharacter 6 1

end RHLean.QuadraticPrimePhase
