import Mathlib
import RHLean.Arithmetic.PrimeWheelMobiusRecovery
import RHLean.Arithmetic.PrimorialWheelPrefixIdentity

open scoped ArithmeticFunction.Moebius BigOperators

/-!
# Minimal common torus for one primorial wheel block

The historical concrete wheel chooses the easy common modulus

`(upper + 1) * rawPeriod`.

For harmonic work this is much larger than necessary.  The manuscript's
periodic-lift model only needs a positive multiple of the complete square-
sensitive raw period that is strictly larger than the arithmetic endpoint.
The Euclidean-division choice

`(upper / rawPeriod + 1) * rawPeriod`

is the first such multiple after `upper`.

This file builds the corresponding finite wheel system and proves that it has
exactly the same Möbius recovery on the arithmetic block.  No analytic or
prime-distribution estimate is used.
-/

noncomputable section

namespace RHLean.Arithmetic

/-- Number of complete raw periods needed to pass the arithmetic endpoint. -/
def primorialMinimalLiftMultiplier (k : ℕ) : ℕ :=
  primorialBlockUpper k / primorialSquareSensitiveModulus k + 1

/-- Minimal positive multiple of the complete raw period strictly above the
right endpoint of the primorial block. -/
def primorialMinimalTorusModulus (k : ℕ) : ℕ :=
  primorialMinimalLiftMultiplier k * primorialSquareSensitiveModulus k

/-- The raw square-sensitive period divides the minimal common torus modulus. -/
theorem primorialSquareSensitiveModulus_dvd_minimalTorusModulus
    (k : ℕ) :
    primorialSquareSensitiveModulus k ∣ primorialMinimalTorusModulus k := by
  unfold primorialMinimalTorusModulus
  exact dvd_mul_left _ _

/-- The minimal lift multiplier is positive. -/
theorem primorialMinimalLiftMultiplier_pos (k : ℕ) :
    0 < primorialMinimalLiftMultiplier k := by
  unfold primorialMinimalLiftMultiplier
  exact Nat.succ_pos _

/-- The minimal common torus modulus is positive. -/
theorem primorialMinimalTorusModulus_pos (k : ℕ) :
    0 < primorialMinimalTorusModulus k := by
  unfold primorialMinimalTorusModulus
  exact Nat.mul_pos
    (primorialMinimalLiftMultiplier_pos k)
    (primorialSquareSensitiveModulus_pos k)

/-- Euclidean division proves that the chosen multiple lies strictly above the
arithmetic endpoint. -/
theorem primorialBlockUpper_lt_minimalTorusModulus (k : ℕ) :
    primorialBlockUpper k < primorialMinimalTorusModulus k := by
  let U := primorialBlockUpper k
  let P := primorialSquareSensitiveModulus k
  have hP : 0 < P := by
    dsimp [P]
    exact primorialSquareSensitiveModulus_pos k
  have hmod : U % P < P := Nat.mod_lt U hP
  have hdiv : U = U / P * P + U % P := by
    calc
      U = P * (U / P) + U % P := (Nat.div_add_mod U P).symm
      _ = U / P * P + U % P := by rw [Nat.mul_comm P (U / P)]
  change U < (U / P + 1) * P
  calc
    U = U / P * P + U % P := hdiv
    _ < U / P * P + P := Nat.add_lt_add_left hmod _
    _ = (U / P + 1) * P := by simp [Nat.add_mul]

/-- The minimal common modulus never exceeds `upper + rawPeriod`. -/
theorem primorialMinimalTorusModulus_le_upper_add_rawPeriod (k : ℕ) :
    primorialMinimalTorusModulus k ≤
      primorialBlockUpper k + primorialSquareSensitiveModulus k := by
  let U := primorialBlockUpper k
  let P := primorialSquareSensitiveModulus k
  change (U / P + 1) * P ≤ U + P
  calc
    (U / P + 1) * P = U / P * P + P := by simp [Nat.add_mul]
    _ ≤ U + P := Nat.add_le_add_right (Nat.div_mul_le_self U P) P

/-- Concrete primorial wheel on the minimal common torus.  Its arithmetic block,
prime coordinates, and corrected site field are identical to the historical
`primorialWheelSystem`; only the ambient torus modulus is reduced. -/
def primorialMinimalWheelSystem (k : ℕ) : PrimeWheelFiniteSystem where
  lower := primorialBlockLower k
  upper := primorialBlockUpper k
  modulus := primorialMinimalTorusModulus k
  lower_lt_upper := primorialEndpoint_strictMono (Nat.lt_succ_self k)
  modulus_pos := primorialMinimalTorusModulus_pos k
  upper_lt_modulus := primorialBlockUpper_lt_minimalTorusModulus k
  primeCoordinates := primorialWheelPrimes k
  primeCoordinates_prime := by
    intro p hp
    exact prime_of_mem_primesUpTo hp

/-- The minimal-torus system has the same exact pointwise Möbius recovery on the
whole synchronized arithmetic block. -/
theorem primorialMinimalWheel_correctedSite_eq_moebius
    (k n : ℕ)
    (hlower : (primorialMinimalWheelSystem k).lower < n)
    (hupper : n ≤ (primorialMinimalWheelSystem k).upper) :
    (primorialMinimalWheelSystem k).correctedSite n = μ n := by
  unfold PrimeWheelFiniteSystem.correctedSite primorialMinimalWheelSystem
  apply correctedPrimeWheelSite_eq_moebius
  · intro p hp
    exact prime_of_mem_primesUpTo hp
  · exact primorialWheelSqrtCoverage k
  · exact Nat.zero_lt_of_lt hlower
  · exact hupper

/-- Canonical arithmetic certificate for the minimal-torus wheel. -/
def primorialMinimalWheelArithmeticCertificate (k : ℕ) :
    (primorialMinimalWheelSystem k).ArithmeticCertificate where
  corrected_eq_moebius := by
    intro n hlower hupper
    exact primorialMinimalWheel_correctedSite_eq_moebius k n hlower hupper

/-- Exact integer-valued Möbius prefix identity on the minimal torus. -/
theorem primorialMinimalWheel_residual_eq_moebiusInterval
    (k : ℕ) {x : ℕ}
    (hupper : x ≤ primorialBlockUpper k) :
    (primorialMinimalWheelSystem k).residual x =
      ∑ n ∈ Finset.Ioc (primorialBlockLower k) x, μ n := by
  exact (primorialMinimalWheelSystem k).residual_eq_moebius_sum
    (primorialMinimalWheelArithmeticCertificate k) hupper

/-- The historical and minimal-torus wheel residuals are exactly the same
integer on every admissible arithmetic prefix. -/
theorem primorialMinimalWheel_residual_eq_primorialWheel_residual
    (k : ℕ) {x : ℕ}
    (hupper : x ≤ primorialBlockUpper k) :
    (primorialMinimalWheelSystem k).residual x =
      (primorialWheelSystem k).residual x := by
  rw [primorialMinimalWheel_residual_eq_moebiusInterval k hupper]
  rw [primorialWheel_residual_eq_moebiusInterval k hupper]

/-- Minimal-torus wheel family. -/
def primorialMinimalWheelFamily : ℕ → PrimeWheelFiniteSystem :=
  primorialMinimalWheelSystem

end RHLean.Arithmetic
