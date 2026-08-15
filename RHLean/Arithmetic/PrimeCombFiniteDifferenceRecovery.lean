import Mathlib
import RHLean.Arithmetic.MoebiusPrefixFrontierIdentity
import RHLean.Arithmetic.PrimeCombFiniteDifference
import RHLean.Arithmetic.PrimeWheelMobiusRecovery

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-!
# Square-root prime-wheel recovery through the canonical divisor difference

This module connects the exact square-root prime-wheel recovery theorem to the
canonical finite Möbius divisor-difference operator.  The smooth-core correction
is kept intact throughout: the object presented to the divisor operator is the
joint signed quantity `raw - 2 * smooth`, not separate absolute estimates.
-/

/-- Positive prefix of an integer-valued arithmetic field.  Using `Icc 1 x`
keeps the zero site out of the square-root recovery statement while still giving
an empty prefix at `x = 0`. -/
def positivePrefix (f : ℕ → ℤ) (x : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 x, f n

/-- Raw seeded prime-wheel mass through `x`. -/
def primeWheelRawPositivePrefix (S : Finset ℕ) (x : ℕ) : ℤ :=
  positivePrefix (seededPrimeComb S) x

/-- Smooth-core mass through `x`, with the correction cutoff pinned at `upper`. -/
def primeWheelSmoothPositivePrefix
    (S : Finset ℕ) (upper x : ℕ) : ℤ :=
  positivePrefix (primeWheelSmoothCoreSite S upper) x

/-- Corrected prime-wheel mass through `x`. -/
def primeWheelCorrectedPositivePrefix
    (S : Finset ℕ) (upper x : ℕ) : ℤ :=
  positivePrefix (correctedPrimeWheelSite S upper) x

/-- Ordinary positive Möbius prefix through `x`. -/
def moebiusPositivePrefix (x : ℕ) : ℤ :=
  positivePrefix (fun n => μ n) x

/-- The corrected prefix is exactly raw mass minus twice the smooth core. -/
theorem primeWheelCorrectedPositivePrefix_eq_raw_sub_two_smooth
    (S : Finset ℕ) (upper x : ℕ) :
    primeWheelCorrectedPositivePrefix S upper x =
      primeWheelRawPositivePrefix S x -
        2 * primeWheelSmoothPositivePrefix S upper x := by
  classical
  unfold primeWheelCorrectedPositivePrefix primeWheelRawPositivePrefix
    primeWheelSmoothPositivePrefix positivePrefix correctedPrimeWheelSite
  symm
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]

/-- Square-root prime coverage recovers the ordinary Möbius prefix exactly. -/
theorem primeWheelCorrectedPositivePrefix_eq_moebiusPositivePrefix
    (S : Finset ℕ) (upper x : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hx : x ≤ upper) :
    primeWheelCorrectedPositivePrefix S upper x =
      moebiusPositivePrefix x := by
  classical
  unfold primeWheelCorrectedPositivePrefix moebiusPositivePrefix positivePrefix
  apply Finset.sum_congr rfl
  intro n hn
  have hmem := Finset.mem_Icc.mp hn
  have hnpos : 0 < n := by omega
  exact correctedPrimeWheelSite_eq_moebius
    S hprime hcover hnpos (hmem.2.trans hx)

/-- The signed raw-minus-twice-smooth prefix is the Möbius prefix under
square-root coverage.  This is the exact quantity whose cancellation matters. -/
theorem primeWheelRaw_sub_two_smooth_eq_moebiusPositivePrefix
    (S : Finset ℕ) (upper x : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hx : x ≤ upper) :
    primeWheelRawPositivePrefix S x -
        2 * primeWheelSmoothPositivePrefix S upper x =
      moebiusPositivePrefix x := by
  calc
    primeWheelRawPositivePrefix S x -
        2 * primeWheelSmoothPositivePrefix S upper x =
      primeWheelCorrectedPositivePrefix S upper x :=
        (primeWheelCorrectedPositivePrefix_eq_raw_sub_two_smooth
          S upper x).symm
    _ = moebiusPositivePrefix x :=
      primeWheelCorrectedPositivePrefix_eq_moebiusPositivePrefix
        S upper x hprime hcover hx

/-- Canonical divisor-difference interface for square-root prime-wheel recovery.
At every physical prefix `x ≤ upper`, applying `D_S` to the joint
raw-minus-twice-smooth field is exactly the same as applying `D_S` to the
ordinary Möbius prefix.  Every floor-shifted argument remains inside the same
physical cutoff, so no complete-period hypothesis enters. -/
theorem finiteDifferenceOperator_primeWheelRecovery
    (S : Finset ℕ) (upper x : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hx : x ≤ upper) :
    finiteDifferenceOperator S
        (fun y =>
          primeWheelRawPositivePrefix S y -
            2 * primeWheelSmoothPositivePrefix S upper y) x =
      finiteDifferenceOperator S moebiusPositivePrefix x := by
  classical
  unfold finiteDifferenceOperator
  apply Finset.sum_congr rfl
  intro d hd
  have hdx : x / d ≤ upper :=
    (Nat.div_le_self x d).trans hx
  have hprefix :=
    primeWheelRaw_sub_two_smooth_eq_moebiusPositivePrefix
      S upper (x / d) hprime hcover hdx
  rw [show
    shift d
        (fun y =>
          primeWheelRawPositivePrefix S y -
            2 * primeWheelSmoothPositivePrefix S upper y) x =
      shift d moebiusPositivePrefix x by
        simpa [shift] using hprefix]

/-- The positive-prefix convention agrees with the repository's standard
Möbius prefix because the zero Möbius value contributes nothing. -/
theorem moebiusPositivePrefix_eq_moebiusPrefix (X : ℕ) :
    moebiusPositivePrefix X =
      ∑ n ∈ Finset.range (X + 1), μ n := by
  classical
  have hrange :
      Finset.range (X + 1) = insert 0 (Finset.Icc 1 X) := by
    ext n
    simp
    omega
  unfold moebiusPositivePrefix positivePrefix
  rw [hrange]
  simp

/-- Contraction-facing exact frontier identity.  Once the wheel covers every
prime through the square-root cutoff, the signed raw-minus-twice-smooth mass is
not merely equal to Möbius pointwise: its whole physical prefix is exactly the
existing first-failure Möbius frontier at every prime coordinate `ell ≤ X`.
Thus a quantitative bound on this signed frontier contracts the established
Mertens route directly, without asking for separate bounds on raw and smooth
mass and without invoking complete CRT periods. -/
theorem primeWheelRaw_sub_two_smooth_eq_primeFrontier
    (S : Finset ℕ) (upper X ell : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hX : X ≤ upper)
    (hellPrime : Nat.Prime ell)
    (hellX : ell ≤ X) :
    primeWheelRawPositivePrefix S X -
        2 * primeWheelSmoothPositivePrefix S upper X =
      ∑ t ∈ primeProductFirstFailureBoundary (primesUpTo X) X ell,
        μ (primeFaceProduct t) := by
  calc
    primeWheelRawPositivePrefix S X -
        2 * primeWheelSmoothPositivePrefix S upper X =
      moebiusPositivePrefix X :=
        primeWheelRaw_sub_two_smooth_eq_moebiusPositivePrefix
          S upper X hprime hcover hX
    _ = ∑ n ∈ Finset.range (X + 1), μ n :=
      moebiusPositivePrefix_eq_moebiusPrefix X
    _ = ∑ t ∈ primeProductFirstFailureBoundary (primesUpTo X) X ell,
          μ (primeFaceProduct t) :=
      moebiusPrefix_eq_primeFrontier hellPrime hellX

end RHLean.Arithmetic
