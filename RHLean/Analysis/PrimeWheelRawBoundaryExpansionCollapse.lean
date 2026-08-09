import Mathlib
import RHLean.Analysis.PrimeWheelFullConductorMobiusReindexedResidual
import RHLean.Analysis.PrimeWheelRawConductorWeight

/-!
# Collapse the reindexed raw boundary pairing to expansion points

After upper-divisor Möbius inversion, the raw part of the full conductor
recombination is still written as a sum over boundary divisors.  The exact
upper-Möbius transform is supported only when the boundary divisor is the
expansion divisor of a ternary prime-comb exponent pattern.  This file performs
that last finite collapse before any norm is taken.

For primorial blocks `k >= 2`, the minimal torus modulus is the natural product
of the local square periods, so every ternary expansion divisor is an actual
divisor of the ambient modulus.  Consequently the raw boundary family becomes
one finite sum over genuine expansion points and no conductor or boundary-
divisor summation remains.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Every ternary expansion divisor divides the product of the local square
periods.  This uses only the coordinatewise exponent bound `e_p <= 2`. -/
private theorem rawExpansionDivisor_dvd_naturalModulus'
    (S : Finset ℕ) (e : PrimeWheelRawExpansionPoint S) :
    primeWheelRawExpansionDivisor S e ∣ primeWheelRawNaturalModulus S := by
  refine ⟨∏ p : {p // p ∈ S}, p.val ^ (2 - (e p).val), ?_⟩
  unfold primeWheelRawExpansionDivisor primeWheelRawNaturalModulus
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← pow_add]
  congr 1
  omega

/-- In every primorial block from `k = 2` onward, each raw expansion divisor is
a divisor of the actual minimal torus modulus. -/
theorem primorialRawExpansionDivisor_dvd_minimalModulus
    (k : ℕ) (hk : 2 ≤ k)
    (e : PrimeWheelRawExpansionPoint (primorialWheelPrimes k)) :
    primeWheelRawExpansionDivisor (primorialWheelPrimes k) e ∣
      (primorialMinimalWheelSystem k).modulus := by
  have hmod :
      (primorialMinimalWheelSystem k).modulus =
        primeWheelRawNaturalModulus (primorialWheelPrimes k) := by
    change primorialMinimalTorusModulus k =
      primeWheelRawNaturalModulus (primorialWheelPrimes k)
    rw [primorialMinimalTorusModulus_eq_squareSensitiveModulus hk]
    exact (primeWheelRawNaturalModulus_primorial k).symm
  rw [hmod]
  exact rawExpansionDivisor_dvd_naturalModulus' (primorialWheelPrimes k) e

/-- Once the upper-Möbius transform has collapsed each raw conductor tail, the
remaining boundary-divisor pairing itself collapses to the exact expansion
divisors. -/
theorem sum_rawUpperMobiusTransform_mul_eq_exactExpansionPairing
    (S : Finset ℕ) (N : ℕ) (hN : N ≠ 0)
    (hdiv : ∀ e : PrimeWheelRawExpansionPoint S,
      primeWheelRawExpansionDivisor S e ∣ N)
    (B : ℕ → ℂ) :
    (∑ d ∈ N.divisors,
      primeWheelRawUpperMobiusTransform S N d * B d) =
      -∑ e : PrimeWheelRawExpansionPoint S,
        primeWheelRawExpansionWeight S e *
          (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ)) *
          B (primeWheelRawExpansionDivisor S e) := by
  classical
  calc
    (∑ d ∈ N.divisors,
      primeWheelRawUpperMobiusTransform S N d * B d) =
      ∑ d ∈ N.divisors,
        (-∑ e : PrimeWheelRawExpansionPoint S,
          primeWheelRawExpansionWeight S e *
            (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ)) *
            (if d = primeWheelRawExpansionDivisor S e then 1 else 0)) *
          B d := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [primeWheelRawUpperMobiusTransform_eq_exactExpansionDivisor
              S N d hN (Nat.pos_of_mem_divisors hd) hdiv]
    _ =
      -∑ d ∈ N.divisors,
        ∑ e : PrimeWheelRawExpansionPoint S,
          primeWheelRawExpansionWeight S e *
            (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ)) *
            (if d = primeWheelRawExpansionDivisor S e then 1 else 0) *
            B d := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro d hd
              rw [neg_mul, Finset.sum_mul]
    _ =
      -∑ e : PrimeWheelRawExpansionPoint S,
        ∑ d ∈ N.divisors,
          primeWheelRawExpansionWeight S e *
            (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ)) *
            (if d = primeWheelRawExpansionDivisor S e then 1 else 0) *
            B d := by
              congr 1
              rw [Finset.sum_comm]
    _ =
      -∑ e : PrimeWheelRawExpansionPoint S,
        primeWheelRawExpansionWeight S e *
          (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ)) *
          B (primeWheelRawExpansionDivisor S e) := by
            congr 1
            apply Fintype.sum_congr
            intro e
            have hmem :
                primeWheelRawExpansionDivisor S e ∈ N.divisors :=
              Nat.mem_divisors.mpr ⟨hdiv e, hN⟩
            calc
              (∑ d ∈ N.divisors,
                primeWheelRawExpansionWeight S e *
                  (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ)) *
                  (if d = primeWheelRawExpansionDivisor S e then 1 else 0) *
                  B d) =
                ∑ d ∈ N.divisors,
                  if d = primeWheelRawExpansionDivisor S e then
                    primeWheelRawExpansionWeight S e *
                      (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ)) *
                      B d
                  else 0 := by
                    apply Finset.sum_congr rfl
                    intro d hd
                    by_cases hde : d = primeWheelRawExpansionDivisor S e <;>
                      simp [hde]
              _ =
                primeWheelRawExpansionWeight S e *
                  (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ)) *
                  B (primeWheelRawExpansionDivisor S e) := by
                    simp [hmem]

/-- The primorial raw boundary term after complete conductor reindexing, now
written directly on the ternary expansion points. -/
def primorialRawExpansionBoundaryPairing (k x : ℕ) : ℂ :=
  -∑ e : PrimeWheelRawExpansionPoint (primorialWheelPrimes k),
    primeWheelRawExpansionWeight (primorialWheelPrimes k) e *
      (((((primorialMinimalWheelSystem k).modulus /
        primeWheelRawExpansionDivisor (primorialWheelPrimes k) e : ℕ) : ℂ))) *
      (((divisorIntervalBoundary
        (primeWheelRawExpansionDivisor (primorialWheelPrimes k) e) 0
        (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))

/-- The divisor-indexed raw collapsed pairing in the full residual is exactly
the expansion-point pairing. -/
theorem primorialRawCollapsedBoundaryPairing_eq_expansion
    (k x : ℕ) (hk : 2 ≤ k) :
    primorialRawCollapsedBoundaryPairing k x =
      primorialRawExpansionBoundaryPairing k x := by
  unfold primorialRawCollapsedBoundaryPairing
    primorialRawExpansionBoundaryPairing
  exact sum_rawUpperMobiusTransform_mul_eq_exactExpansionPairing
    (primorialWheelPrimes k)
    (primorialMinimalWheelSystem k).modulus
    (Nat.ne_of_gt (primorialMinimalWheelSystem k).modulus_pos)
    (fun e => primorialRawExpansionDivisor_dvd_minimalModulus k hk e)
    (fun d => (((divisorIntervalBoundary d 0
      (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ)))

/-- Stronger exact residual formula: from block `k >= 2`, every conductor sum
and every raw boundary-divisor sum has disappeared before norms.  The raw term
is indexed only by the genuine ternary expansion points; the smooth term is
already collapsed to its top boundary plus the retained conductor-one bulk. -/
theorem primorialPeriodicRawResidual_eq_expansionReindexed
    (k : ℕ) (hk : 2 ≤ k) {x : ℕ}
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    ((((primorialWheelSystem k).residual x : ℤ) : ℂ)) =
      (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        (primorialRawExpansionBoundaryPairing k x +
          primorialRawRetainedBulk k x -
          2 * (((primorialSmoothCollapsedBoundaryBulk k x : ℤ) : ℂ))) := by
  rw [primorialPeriodicRawResidual_eq_mobiusReindexed k hlower hupper]
  rw [primorialRawCollapsedBoundaryPairing_eq_expansion k x hk]

end RHLean.Analysis
