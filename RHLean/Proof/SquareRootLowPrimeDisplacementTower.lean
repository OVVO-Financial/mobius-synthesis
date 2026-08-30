import Mathlib
import RHLean.Proof.SquareRootLowPrimeCanonicalCreationResponseMap

/-!
# Canonical coordinates of an unstable displacement corner

A genuine high-channel displacement diamond has four ordered arithmetic
coordinates

`a --q--> a*q --p--> a*q*p --Q--> a*q*p*Q`

with

`P+(a) < q < p < Q`

and all three displayed coordinates prime.  The terminal partner `Q` lies above
all processed primes.  Hence the missing top corner canonically remembers the
entire instability:

* its largest prime is `Q`;
* the largest prime of its canonical cofactor is `p`;
* the largest prime after a second cofactor deletion is `q`;
* a third cofactor deletion is the base `a`.

This proves the global uniqueness that a fixed-pivot product cancellation does
not provide: two unstable events charged to the same missing arithmetic child
are identical coordinate by coordinate.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Arithmetic data of one ordered displacement tower. -/
structure SquareRootLowPrimeDisplacementTower where
  base : ℕ
  earlierPrime : ℕ
  laterPrime : ℕ
  partnerPrime : ℕ
  base_pos : 0 < base
  earlier_prime : earlierPrime.Prime
  later_prime : laterPrime.Prime
  partner_prime : partnerPrime.Prime
  base_rough : canonicalLargestPrimeFactor base < earlierPrime
  earlier_lt_later : earlierPrime < laterPrime
  later_lt_partner : laterPrime < partnerPrime

/-- The arithmetic child at the missing top corner. -/
def squareRootLowPrimeDisplacementTowerChild
    (t : SquareRootLowPrimeDisplacementTower) : ℕ :=
  ((t.base * t.earlierPrime) * t.laterPrime) * t.partnerPrime

/-- First extension has canonical largest prime `q`. -/
theorem squareRootLowPrimeDisplacementTower_lpf_baseEarlier
    (t : SquareRootLowPrimeDisplacementTower) :
    canonicalLargestPrimeFactor (t.base * t.earlierPrime) =
      t.earlierPrime :=
  canonicalLargestPrimeFactor_mul_prime_eq_of_rough
    t.base_pos t.earlier_prime t.base_rough

/-- First extension has canonical cofactor `a`. -/
theorem squareRootLowPrimeDisplacementTower_cofactor_baseEarlier
    (t : SquareRootLowPrimeDisplacementTower) :
    canonicalCofactor (t.base * t.earlierPrime) = t.base :=
  canonicalCofactor_mul_prime_eq_of_rough
    t.base_pos t.earlier_prime t.base_rough

/-- The two-prime internal corner has largest prime `p`. -/
theorem squareRootLowPrimeDisplacementTower_lpf_internal
    (t : SquareRootLowPrimeDisplacementTower) :
    canonicalLargestPrimeFactor
        ((t.base * t.earlierPrime) * t.laterPrime) =
      t.laterPrime := by
  apply canonicalLargestPrimeFactor_mul_prime_eq_of_rough
  · exact Nat.mul_pos t.base_pos t.earlier_prime.pos
  · exact t.later_prime
  · rw [squareRootLowPrimeDisplacementTower_lpf_baseEarlier]
    exact t.earlier_lt_later

/-- The two-prime internal corner deletes back to `a*q`. -/
theorem squareRootLowPrimeDisplacementTower_cofactor_internal
    (t : SquareRootLowPrimeDisplacementTower) :
    canonicalCofactor ((t.base * t.earlierPrime) * t.laterPrime) =
      t.base * t.earlierPrime := by
  apply canonicalCofactor_mul_prime_eq_of_rough
  · exact Nat.mul_pos t.base_pos t.earlier_prime.pos
  · exact t.later_prime
  · rw [squareRootLowPrimeDisplacementTower_lpf_baseEarlier]
    exact t.earlier_lt_later

/-- The missing response child has terminal partner `Q` as its largest prime. -/
theorem squareRootLowPrimeDisplacementTower_lpf_child
    (t : SquareRootLowPrimeDisplacementTower) :
    canonicalLargestPrimeFactor
        (squareRootLowPrimeDisplacementTowerChild t) =
      t.partnerPrime := by
  unfold squareRootLowPrimeDisplacementTowerChild
  apply canonicalLargestPrimeFactor_mul_prime_eq_of_rough
  · exact Nat.mul_pos
      (Nat.mul_pos t.base_pos t.earlier_prime.pos) t.later_prime.pos
  · exact t.partner_prime
  · rw [squareRootLowPrimeDisplacementTower_lpf_internal]
    exact t.later_lt_partner

/-- The first canonical deletion of the missing child recovers `a*q*p`. -/
theorem squareRootLowPrimeDisplacementTower_cofactor_child
    (t : SquareRootLowPrimeDisplacementTower) :
    canonicalCofactor (squareRootLowPrimeDisplacementTowerChild t) =
      (t.base * t.earlierPrime) * t.laterPrime := by
  unfold squareRootLowPrimeDisplacementTowerChild
  apply canonicalCofactor_mul_prime_eq_of_rough
  · exact Nat.mul_pos
      (Nat.mul_pos t.base_pos t.earlier_prime.pos) t.later_prime.pos
  · exact t.partner_prime
  · rw [squareRootLowPrimeDisplacementTower_lpf_internal]
    exact t.later_lt_partner

/-- The second canonical deletion recovers `a*q`. -/
theorem squareRootLowPrimeDisplacementTower_cofactor_two
    (t : SquareRootLowPrimeDisplacementTower) :
    canonicalCofactor
        (canonicalCofactor (squareRootLowPrimeDisplacementTowerChild t)) =
      t.base * t.earlierPrime := by
  rw [squareRootLowPrimeDisplacementTower_cofactor_child,
    squareRootLowPrimeDisplacementTower_cofactor_internal]

/-- The third canonical deletion recovers the original base. -/
theorem squareRootLowPrimeDisplacementTower_cofactor_three
    (t : SquareRootLowPrimeDisplacementTower) :
    canonicalCofactor
        (canonicalCofactor
          (canonicalCofactor
            (squareRootLowPrimeDisplacementTowerChild t))) =
      t.base := by
  rw [squareRootLowPrimeDisplacementTower_cofactor_child,
    squareRootLowPrimeDisplacementTower_cofactor_internal,
    squareRootLowPrimeDisplacementTower_cofactor_baseEarlier]

/-- The later displacement prime is recovered after one canonical deletion. -/
theorem squareRootLowPrimeDisplacementTower_laterPrime_recover
    (t : SquareRootLowPrimeDisplacementTower) :
    canonicalLargestPrimeFactor
        (canonicalCofactor (squareRootLowPrimeDisplacementTowerChild t)) =
      t.laterPrime := by
  rw [squareRootLowPrimeDisplacementTower_cofactor_child,
    squareRootLowPrimeDisplacementTower_lpf_internal]

/-- The earlier pivot prime is recovered after two canonical deletions. -/
theorem squareRootLowPrimeDisplacementTower_earlierPrime_recover
    (t : SquareRootLowPrimeDisplacementTower) :
    canonicalLargestPrimeFactor
        (canonicalCofactor
          (canonicalCofactor (squareRootLowPrimeDisplacementTowerChild t))) =
      t.earlierPrime := by
  rw [squareRootLowPrimeDisplacementTower_cofactor_child,
    squareRootLowPrimeDisplacementTower_cofactor_internal,
    squareRootLowPrimeDisplacementTower_lpf_baseEarlier]

/-- **Global uniqueness of the missing-corner charge.** -/
theorem squareRootLowPrimeDisplacementTowerChild_injective :
    Function.Injective squareRootLowPrimeDisplacementTowerChild := by
  intro s t hchild
  have hpartner : s.partnerPrime = t.partnerPrime := by
    rw [← squareRootLowPrimeDisplacementTower_lpf_child s,
      ← squareRootLowPrimeDisplacementTower_lpf_child t,
      hchild]
  have hlater : s.laterPrime = t.laterPrime := by
    rw [← squareRootLowPrimeDisplacementTower_laterPrime_recover s,
      ← squareRootLowPrimeDisplacementTower_laterPrime_recover t,
      hchild]
  have hearlier : s.earlierPrime = t.earlierPrime := by
    rw [← squareRootLowPrimeDisplacementTower_earlierPrime_recover s,
      ← squareRootLowPrimeDisplacementTower_earlierPrime_recover t,
      hchild]
  have hbase : s.base = t.base := by
    rw [← squareRootLowPrimeDisplacementTower_cofactor_three s,
      ← squareRootLowPrimeDisplacementTower_cofactor_three t,
      hchild]
  cases s
  cases t
  simp_all

end RHLean.Proof
