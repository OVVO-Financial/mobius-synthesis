import Mathlib
import RHLean.Analysis.ElevenWeightOneFirstMoment

/-!
# Exact weight-one layers at primes 13 and 17

The abstract finite-prime T-sector law already gives the generic Walsh factor

`lambda_p(1) = 1 - 2*(p-1)/(p^2-6)`.

This file supplies the direct finite residue certificates and deterministic CRT
tensor theorems for the next two generic primes.  As at prime 11, the
complementary field is arbitrary on a coprime modulus; no probabilistic
independence assumption is used.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Generic zero-free indicator on the six transition forms at a fixed prime. -/
def genericPrimeZeroFreeIndicatorZMod
    (p : ℕ) (z : ZMod (p ^ 2)) : ℚ :=
  if tSquareZeroFreeAt p z.val then 1 else 0

/-- Generic signed weight-one coordinate multiplier, with square-zero residues
killed. -/
def genericPrimeZeroFreeCoordinateMultiplierZMod
    (p : ℕ) (i : Fin 6) (z : ZMod (p ^ 2)) : ℚ :=
  if tSquareZeroFreeAt p z.val then
    if p ∣ tTransitionForm i z.val then -1 else 1
  else 0

/-- Direct prime-13 certificate: six square-zero residues are removed. -/
theorem sum_thirteenZeroFreeIndicatorZMod :
    (∑ z : ZMod (13 ^ 2), genericPrimeZeroFreeIndicatorZMod 13 z) = 163 := by
  native_decide

/-- At prime 13 each weight-one coordinate flips on exactly twelve retained
residues, so its signed mass is `163 - 2*12 = 139`. -/
theorem sum_thirteenZeroFreeCoordinateMultiplierZMod (i : Fin 6) :
    (∑ z : ZMod (13 ^ 2),
      genericPrimeZeroFreeCoordinateMultiplierZMod 13 i z) = 139 := by
  fin_cases i <;> native_decide

/-- Direct prime-17 certificate: six square-zero residues are removed. -/
theorem sum_seventeenZeroFreeIndicatorZMod :
    (∑ z : ZMod (17 ^ 2), genericPrimeZeroFreeIndicatorZMod 17 z) = 283 := by
  native_decide

/-- At prime 17 each weight-one coordinate flips on exactly sixteen retained
residues, so its signed mass is `283 - 2*16 = 251`. -/
theorem sum_seventeenZeroFreeCoordinateMultiplierZMod (i : Fin 6) :
    (∑ z : ZMod (17 ^ 2),
      genericPrimeZeroFreeCoordinateMultiplierZMod 17 i z) = 251 := by
  fin_cases i <;> native_decide

@[simp] theorem onePrimeWalshFactor_thirteen_one :
    onePrimeWalshFactor 13 1 = (139 : ℚ) / 163 := by
  norm_num [onePrimeWalshFactor, onePrimeNoFlipProb, onePrimeSingleFlipProb,
    onePrimeNoFlipWeight, onePrimeSingleFlipWeight, onePrimeZeroFreeWeight]

@[simp] theorem onePrimeWalshFactor_seventeen_one :
    onePrimeWalshFactor 17 1 = (251 : ℚ) / 283 := by
  norm_num [onePrimeWalshFactor, onePrimeNoFlipProb, onePrimeSingleFlipProb,
    onePrimeNoFlipWeight, onePrimeSingleFlipWeight, onePrimeZeroFreeWeight]

/-- **Deterministic complete-fibre prime-13 first moment.**  Any complementary
field on a modulus coprime to `13^2` is multiplied by exactly `139/163`. -/
theorem thirteen_coprimeTensor_firstMoment
    (M : ℕ) [NeZero M] (hcop : Nat.Coprime (13 ^ 2) M)
    (i : Fin 6) (g : ZMod M → ℚ) :
    (∑ z : ZMod ((13 ^ 2) * M),
      genericPrimeZeroFreeCoordinateMultiplierZMod 13 i
          ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) =
      onePrimeWalshFactor 13 1 *
        (∑ z : ZMod ((13 ^ 2) * M),
          genericPrimeZeroFreeIndicatorZMod 13
              ((ZMod.chineseRemainder hcop) z).1 *
            g ((ZMod.chineseRemainder hcop) z).2) := by
  have hsigned := coprimeZMod_sum_tensor (13 ^ 2) M hcop
    (genericPrimeZeroFreeCoordinateMultiplierZMod 13 i) g
  have hzero := coprimeZMod_sum_tensor (13 ^ 2) M hcop
    (genericPrimeZeroFreeIndicatorZMod 13) g
  rw [sum_thirteenZeroFreeCoordinateMultiplierZMod] at hsigned
  rw [sum_thirteenZeroFreeIndicatorZMod] at hzero
  rw [hsigned, hzero, onePrimeWalshFactor_thirteen_one]
  ring

/-- Prime-13 rank-one energy multiplier. -/
theorem thirteen_coprimeTensor_firstMoment_sq
    (M : ℕ) [NeZero M] (hcop : Nat.Coprime (13 ^ 2) M)
    (i : Fin 6) (g : ZMod M → ℚ) :
    (∑ z : ZMod ((13 ^ 2) * M),
      genericPrimeZeroFreeCoordinateMultiplierZMod 13 i
          ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) ^ 2 =
      (onePrimeWalshFactor 13 1) ^ 2 *
        (∑ z : ZMod ((13 ^ 2) * M),
          genericPrimeZeroFreeIndicatorZMod 13
              ((ZMod.chineseRemainder hcop) z).1 *
            g ((ZMod.chineseRemainder hcop) z).2) ^ 2 := by
  rw [thirteen_coprimeTensor_firstMoment M hcop i g]
  ring

/-- **Deterministic complete-fibre prime-17 first moment.**  Any complementary
field on a modulus coprime to `17^2` is multiplied by exactly `251/283`. -/
theorem seventeen_coprimeTensor_firstMoment
    (M : ℕ) [NeZero M] (hcop : Nat.Coprime (17 ^ 2) M)
    (i : Fin 6) (g : ZMod M → ℚ) :
    (∑ z : ZMod ((17 ^ 2) * M),
      genericPrimeZeroFreeCoordinateMultiplierZMod 17 i
          ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) =
      onePrimeWalshFactor 17 1 *
        (∑ z : ZMod ((17 ^ 2) * M),
          genericPrimeZeroFreeIndicatorZMod 17
              ((ZMod.chineseRemainder hcop) z).1 *
            g ((ZMod.chineseRemainder hcop) z).2) := by
  have hsigned := coprimeZMod_sum_tensor (17 ^ 2) M hcop
    (genericPrimeZeroFreeCoordinateMultiplierZMod 17 i) g
  have hzero := coprimeZMod_sum_tensor (17 ^ 2) M hcop
    (genericPrimeZeroFreeIndicatorZMod 17) g
  rw [sum_seventeenZeroFreeCoordinateMultiplierZMod] at hsigned
  rw [sum_seventeenZeroFreeIndicatorZMod] at hzero
  rw [hsigned, hzero, onePrimeWalshFactor_seventeen_one]
  ring

/-- Prime-17 rank-one energy multiplier. -/
theorem seventeen_coprimeTensor_firstMoment_sq
    (M : ℕ) [NeZero M] (hcop : Nat.Coprime (17 ^ 2) M)
    (i : Fin 6) (g : ZMod M → ℚ) :
    (∑ z : ZMod ((17 ^ 2) * M),
      genericPrimeZeroFreeCoordinateMultiplierZMod 17 i
          ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) ^ 2 =
      (onePrimeWalshFactor 17 1) ^ 2 *
        (∑ z : ZMod ((17 ^ 2) * M),
          genericPrimeZeroFreeIndicatorZMod 17
              ((ZMod.chineseRemainder hcop) z).1 *
            g ((ZMod.chineseRemainder hcop) z).2) ^ 2 := by
  rw [seventeen_coprimeTensor_firstMoment M hcop i g]
  ring

/-- Exact arithmetic threshold advertised by the exceptional-owner triangle:
prime 11 alone is not enough after the factor-four affine cost. -/
theorem exceptionalTriangle_eleven_coefficient_gt_one :
    (1 : ℚ) <
      4 * (onePrimeWalshFactor 11 1) ^ 2 * ((71 : ℚ) / 105) ^ 2 := by
  rw [onePrimeWalshFactor_eleven_one]
  norm_num

/-- Adding prime 13 crosses the subcritical threshold. -/
theorem exceptionalTriangle_eleven_thirteen_coefficient_lt_one :
    4 * ((onePrimeWalshFactor 11 1) *
          (onePrimeWalshFactor 13 1)) ^ 2 *
        ((71 : ℚ) / 105) ^ 2 < 1 := by
  rw [onePrimeWalshFactor_eleven_one,
    onePrimeWalshFactor_thirteen_one]
  norm_num

/-- Adding prime 17 gives further numerical slack. -/
theorem exceptionalTriangle_eleven_thirteen_seventeen_coefficient_lt_three_quarters :
    4 * ((onePrimeWalshFactor 11 1) *
          (onePrimeWalshFactor 13 1) *
          (onePrimeWalshFactor 17 1)) ^ 2 *
        ((71 : ℚ) / 105) ^ 2 < (3 : ℚ) / 4 := by
  rw [onePrimeWalshFactor_eleven_one,
    onePrimeWalshFactor_thirteen_one,
    onePrimeWalshFactor_seventeen_one]
  norm_num

end RHLean.Analysis
