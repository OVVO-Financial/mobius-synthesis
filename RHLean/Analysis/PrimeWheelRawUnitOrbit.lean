import Mathlib
import RHLean.Arithmetic.PrimeProductLowerBound
import RHLean.Analysis.PrimeWheelPeriodicRawBridge

/-!
# Unit-orbit invariance of the periodic raw wheel

The complete seeded raw comb only records, for each selected prime `p`, whether
an integer is divisible by `p` and by `p^2`.  Multiplication by a unit modulo any
common multiple of all `p^2` therefore preserves the raw field exactly.

Fourier duality then transports this physical unit invariance to unit-orbit
invariance of the complete periodic raw spectrum.  This is the structural input
needed to prove that the actual raw Fourier coefficient is constant on each
reduced-conductor shell.

No estimate is used in this file.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Divisibility of the least representative by `d` is equivalent to vanishing
after canonical reduction modulo `d`. -/
private theorem dvd_val_iff_cast_eq_zero
    {N d : ℕ} [NeZero N] (z : ZMod N) :
    d ∣ z.val ↔ (z.cast : ZMod d) = 0 := by
  rw [ZMod.cast_eq_val]
  exact (ZMod.natCast_eq_zero_iff z.val d).symm

/-- Multiplication by a unit modulo `N` preserves divisibility of least
representatives by every divisor `d` of `N`. -/
private theorem dvd_unit_mul_val_iff
    {N d : ℕ} [NeZero N] (hd : d ∣ N)
    (u : (ZMod N)ˣ) (z : ZMod N) :
    d ∣ ((u : ZMod N) * z).val ↔ d ∣ z.val := by
  rw [dvd_val_iff_cast_eq_zero ((u : ZMod N) * z),
    dvd_val_iff_cast_eq_zero z]
  rw [ZMod.cast_mul hd]
  have hu : IsUnit (((u : ZMod N).cast : ZMod d)) :=
    ZMod.isUnit_cast_of_dvd hd u
  rcases hu with ⟨v, hv⟩
  rw [← hv]
  simp

/-- One local square-sensitive prime comb is unchanged by a unit multiplication
whenever `p^2` divides the ambient modulus. -/
theorem localPrimeComb_unit_mul_val
    {N p : ℕ} [NeZero N] (hp2 : p ^ 2 ∣ N)
    (u : (ZMod N)ˣ) (z : ZMod N) :
    localPrimeComb p (((u : ZMod N) * z).val) =
      localPrimeComb p z.val := by
  have hp : p ∣ N :=
    dvd_trans (dvd_pow_self p (by norm_num)) hp2
  have hpIff :
      p ∣ (((u : ZMod N) * z).val) ↔ p ∣ z.val :=
    dvd_unit_mul_val_iff hp u z
  have hp2Iff :
      p ^ 2 ∣ (((u : ZMod N) * z).val) ↔ p ^ 2 ∣ z.val :=
    dvd_unit_mul_val_iff hp2 u z
  unfold localPrimeComb
  simp only [hpIff, hp2Iff]

/-- The complete seeded prime comb is invariant under unit multiplication on any
ambient modulus divisible by every selected local period `p^2`. -/
theorem seededPrimeComb_unit_mul_val
    {N : ℕ} [NeZero N]
    (S : Finset ℕ)
    (hperiod : ∀ p ∈ S, p ^ 2 ∣ N)
    (u : (ZMod N)ˣ) (z : ZMod N) :
    seededPrimeComb S (((u : ZMod N) * z).val) =
      seededPrimeComb S z.val := by
  classical
  unfold seededPrimeComb
  apply congrArg Neg.neg
  apply Finset.prod_congr rfl
  intro p hp
  exact localPrimeComb_unit_mul_val (hperiod p hp) u z

/-- Every selected local square period divides the minimal primorial torus. -/
theorem primorialPrimeSquare_dvd_minimalTorusModulus
    (k p : ℕ) (hp : p ∈ primorialWheelPrimes k) :
    p ^ 2 ∣ primorialMinimalTorusModulus k := by
  have hpRaw : p ^ 2 ∣ primorialSquareSensitiveModulus k := by
    unfold primorialSquareSensitiveModulus
    exact Finset.dvd_prod_of_mem (fun q : ℕ => q ^ 2) hp
  exact dvd_trans hpRaw
    (primorialSquareSensitiveModulus_dvd_minimalTorusModulus k)

/-- The actual untruncated periodic raw torus field is invariant under
multiplication by every unit of its ambient torus. -/
theorem primorialPeriodicRawTorusField_unit_mul
    (k : ℕ)
    (u : (ZMod (primorialMinimalWheelSystem k).modulus)ˣ)
    (z : ZMod (primorialMinimalWheelSystem k).modulus) :
    primorialPeriodicRawTorusField k
        ((u : ZMod (primorialMinimalWheelSystem k).modulus) * z) =
      primorialPeriodicRawTorusField k z := by
  letI : NeZero (primorialMinimalTorusModulus k) :=
    ⟨Nat.ne_of_gt (primorialMinimalTorusModulus_pos k)⟩
  unfold primorialPeriodicRawTorusField
    PrimeWheelFiniteSystem.rawSite
  change
    (((seededPrimeComb (primorialWheelPrimes k)
      (((u : ZMod (primorialMinimalWheelSystem k).modulus) * z).val) : ℤ) : ℂ)) =
      (((seededPrimeComb (primorialWheelPrimes k) z.val : ℤ) : ℂ))
  exact congrArg (fun a : ℤ => (a : ℂ))
    (seededPrimeComb_unit_mul_val
      (S := primorialWheelPrimes k)
      (fun p hp => primorialPrimeSquare_dvd_minimalTorusModulus k p hp)
      u z)

/-- Physical unit invariance as an equality of functions. -/
theorem primorialPeriodicRawTorusField_comp_unitMul
    (k : ℕ)
    (u : (ZMod (primorialMinimalWheelSystem k).modulus)ˣ) :
    (fun z : ZMod (primorialMinimalWheelSystem k).modulus =>
      primorialPeriodicRawTorusField k
        ((u : ZMod (primorialMinimalWheelSystem k).modulus) * z)) =
      primorialPeriodicRawTorusField k := by
  funext z
  exact primorialPeriodicRawTorusField_unit_mul k u z

/-- The complete periodic raw DFT is constant on multiplicative unit orbits of
frequency.  This is an exact Fourier consequence of physical unit invariance. -/
theorem primorialPeriodicRawSpectrum_unit_mul
    (k : ℕ)
    (u : (ZMod (primorialMinimalWheelSystem k).modulus)ˣ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus) :
    primorialPeriodicRawSpectrum k
        ((u : ZMod (primorialMinimalWheelSystem k).modulus) * r) =
      primorialPeriodicRawSpectrum k r := by
  have h := ZMod.dft_comp_unitMul
    (primorialPeriodicRawTorusField k) u⁻¹ r
  rw [primorialPeriodicRawTorusField_comp_unitMul k u⁻¹] at h
  unfold primorialPeriodicRawSpectrum
  simpa using h.symm

end RHLean.Analysis
