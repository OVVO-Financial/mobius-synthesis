import Mathlib
import RHLean.Arithmetic.PrimorialWheelMinimalTorus

/-!
# Natural square-sensitive period of the seeded prime comb

Each local prime comb depends only on divisibility by `p` and `p^2`, hence has
period `p^2`.  Any common multiple of the local square periods is therefore a
period of the complete seeded comb.  In particular the product of the local
`p^2` periods is an exact period of the raw primorial wheel field.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- One local prime comb is periodic with period `p^2`. -/
theorem localPrimeComb_periodic_square (p : ℕ) :
    Function.Periodic (localPrimeComb p) (p ^ 2) := by
  intro n
  have hpSq : p ^ 2 ∣ p ^ 2 := dvd_refl _
  have hp : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
  have hsqIff : p ^ 2 ∣ n + p ^ 2 ↔ p ^ 2 ∣ n := by
    symm
    exact Nat.dvd_add_iff_left hpSq
  have hpIff : p ∣ n + p ^ 2 ↔ p ∣ n := by
    symm
    exact Nat.dvd_add_iff_left hp
  simp [localPrimeComb, hsqIff, hpIff]

/-- Every multiple of `p^2` is also a period of the local prime comb. -/
theorem localPrimeComb_periodic_of_square_dvd
    (p P : ℕ) (hdiv : p ^ 2 ∣ P) :
    Function.Periodic (localPrimeComb p) P := by
  rcases hdiv with ⟨c, hc⟩
  have hper := (localPrimeComb_periodic_square p).nsmul c
  simpa [hc, nsmul_eq_mul, Nat.mul_comm] using hper

/-- If a common period is divisible by every local square period, the complete
seeded prime comb has that common period. -/
theorem seededPrimeComb_periodic_of_squarePeriods_dvd
    (S : Finset ℕ) (P : ℕ)
    (hdiv : ∀ p ∈ S, p ^ 2 ∣ P) :
    Function.Periodic (seededPrimeComb S) P := by
  intro n
  unfold seededPrimeComb
  apply congrArg Neg.neg
  apply Finset.prod_congr rfl
  intro p hp
  exact localPrimeComb_periodic_of_square_dvd p P (hdiv p hp) n

/-- Every local square period divides the complete square-sensitive primorial
period. -/
theorem primeSquare_dvd_primorialSquareSensitiveModulus
    (k p : ℕ) (hp : p ∈ primorialWheelPrimes k) :
    p ^ 2 ∣ primorialSquareSensitiveModulus k := by
  unfold primorialSquareSensitiveModulus
  exact Finset.dvd_prod_of_mem (fun q : ℕ => q ^ 2) hp

/-- The natural raw primorial period is an actual period of the seeded comb. -/
theorem primorialSeededPrimeComb_periodic (k : ℕ) :
    Function.Periodic
      (seededPrimeComb (primorialWheelPrimes k))
      (primorialSquareSensitiveModulus k) := by
  apply seededPrimeComb_periodic_of_squarePeriods_dvd
  intro p hp
  exact primeSquare_dvd_primorialSquareSensitiveModulus k p hp

/-- The raw site field of the minimal wheel has the same natural period. -/
theorem primorialMinimalRawSite_periodic (k : ℕ) :
    Function.Periodic
      (primorialMinimalWheelSystem k).rawSite
      (primorialSquareSensitiveModulus k) := by
  simpa [PrimeWheelFiniteSystem.rawSite, primorialMinimalWheelSystem] using
    (primorialSeededPrimeComb_periodic k)

/-- The historical wheel raw site has the same natural period as well. -/
theorem primorialRawSite_periodic (k : ℕ) :
    Function.Periodic
      (primorialWheelSystem k).rawSite
      (primorialSquareSensitiveModulus k) := by
  simpa [PrimeWheelFiniteSystem.rawSite, primorialWheelSystem] using
    (primorialSeededPrimeComb_periodic k)

end RHLean.Analysis
