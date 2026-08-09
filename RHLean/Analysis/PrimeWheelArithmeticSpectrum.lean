import Mathlib
import RHLean.Analysis.PrimeWheelJointSpectrum
import RHLean.Arithmetic.PrimeWheelMobiusRecovery

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Product of the distinct prime coordinates carried by one finite wheel. -/
def primeWheelCoordinateProduct (S : Finset ℕ) : ℕ :=
  S.prod id

/-- For a finite set of genuine prime coordinates, smooth squarefree integers
are exactly the squarefree divisors of the coordinate product. -/
theorem isPrimeWheelSmooth_iff_squarefree_dvd_coordinateProduct
    (S : Finset ℕ) (n : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    IsPrimeWheelSmooth S n ↔
      Squarefree n ∧ n ∣ primeWheelCoordinateProduct S := by
  classical
  constructor
  · intro hsmooth
    refine ⟨hsmooth.1, ?_⟩
    rw [← Nat.prod_primeFactors_of_squarefree hsmooth.1]
    exact Finset.prod_dvd_prod_of_subset n.primeFactors S id hsmooth.2
  · rintro ⟨hsq, hdvd⟩
    refine ⟨hsq, ?_⟩
    intro p hp
    have hpData := Nat.mem_primeFactors.mp hp
    have hpDvdProduct : p ∣ primeWheelCoordinateProduct S :=
      dvd_trans hpData.2.1 hdvd
    unfold primeWheelCoordinateProduct at hpDvdProduct
    rcases (Prime.dvd_finset_prod_iff hpData.1.prime id).mp hpDvdProduct with
      ⟨q, hqS, hpq⟩
    rcases (hprime q hqS).eq_one_or_self_of_dvd p hpq with hpOne | hpEq
    · exact (hpData.1.ne_one hpOne).elim
    · simpa [hpEq] using hqS

/-- Explicit unnormalized raw arithmetic coefficient on the common torus. -/
def primeWheelRawArithmeticCoefficient
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) : ℂ :=
  ∑ z : ZMod W.modulus,
    ZMod.stdAddChar (-(z * r)) *
      if W.lower < z.val ∧ z.val ≤ W.upper then
        ((seededPrimeComb W.primeCoordinates z.val : ℤ) : ℂ)
      else 0

/-- The named raw block spectrum is definitionally the explicit arithmetic
additive-character coefficient. -/
theorem rawBlockSpectrum_eq_arithmeticCoefficient
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    W.rawBlockSpectrum r = primeWheelRawArithmeticCoefficient W r := by
  unfold PrimeWheelFiniteSystem.rawBlockSpectrum
    PrimeWheelFiniteSystem.torusRawBlockField
    primeWheelRawArithmeticCoefficient PrimeWheelFiniteSystem.rawSite
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]

/-- Explicit unnormalized smooth-core coefficient: a finite additive-character
sum over squarefree divisors of the prime-coordinate product lying in the
arithmetic block. -/
def primeWheelSmoothDivisorCoefficient
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) : ℂ :=
  ∑ z : ZMod W.modulus,
    ZMod.stdAddChar (-(z * r)) *
      if W.lower < z.val ∧ z.val ≤ W.upper ∧
          Squarefree z.val ∧
          z.val ∣ primeWheelCoordinateProduct W.primeCoordinates then
        -(((μ z.val : ℤ) : ℂ))
      else 0

/-- The zero-padded smooth-core DFT is exactly the truncated squarefree-divisor
coefficient.  No empirical certificate or asymptotic input is used. -/
theorem smoothCoreBlockSpectrum_eq_smoothDivisorCoefficient
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    W.smoothCoreBlockSpectrum r = primeWheelSmoothDivisorCoefficient W r := by
  classical
  unfold PrimeWheelFiniteSystem.smoothCoreBlockSpectrum
    PrimeWheelFiniteSystem.torusSmoothCoreBlockField
    primeWheelSmoothDivisorCoefficient
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hblock : W.lower < z.val ∧ z.val ≤ W.upper
  · have hsmoothIff :=
      isPrimeWheelSmooth_iff_squarefree_dvd_coordinateProduct
        W.primeCoordinates z.val W.primeCoordinates_prime
    by_cases hsmooth : IsPrimeWheelSmooth W.primeCoordinates z.val
    · have hraw := seededPrimeComb_eq_neg_moebius_of_smooth
        W.primeCoordinates W.primeCoordinates_prime hsmooth
      have hcriterion :
          Squarefree z.val ∧
            z.val ∣ primeWheelCoordinateProduct W.primeCoordinates :=
        hsmoothIff.mp hsmooth
      simp [PrimeWheelFiniteSystem.smoothCoreSite,
        primeWheelSmoothCoreSite, hblock, hsmooth, hcriterion, hraw]
    · have hcriterion :
          ¬(Squarefree z.val ∧
            z.val ∣ primeWheelCoordinateProduct W.primeCoordinates) := by
        exact fun h => hsmooth (hsmoothIff.mpr h)
      simp [PrimeWheelFiniteSystem.smoothCoreSite,
        primeWheelSmoothCoreSite, hblock, hsmooth, hcriterion]
  · have hnot :
        ¬(W.lower < z.val ∧ z.val ≤ W.upper ∧
          Squarefree z.val ∧
          z.val ∣ primeWheelCoordinateProduct W.primeCoordinates) := by
      intro h
      exact hblock ⟨h.1, h.2.1⟩
    simp [hblock, hnot]

/-- Exact arithmetic realization of the complete joint spectrum. -/
theorem jointSpectrum_eq_rawArithmetic_sub_two_smoothDivisor
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    W.jointSpectrum r =
      primeWheelRawArithmeticCoefficient W r -
        2 * primeWheelSmoothDivisorCoefficient W r := by
  rw [W.jointSpectrum_eq_raw_sub_two_smooth,
    rawBlockSpectrum_eq_arithmeticCoefficient,
    smoothCoreBlockSpectrum_eq_smoothDivisorCoefficient]

end RHLean.Analysis
