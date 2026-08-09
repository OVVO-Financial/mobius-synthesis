import Mathlib
import RHLean.Arithmetic.PrimeFaceMoebius

open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHLean.Arithmetic

/-- The finite ambient coordinate set consisting of every prime at most `X`. -/
def primesUpTo (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter Nat.Prime

@[simp] theorem mem_primesUpTo {X p : ℕ} :
    p ∈ primesUpTo X ↔ Nat.Prime p ∧ p ≤ X := by
  simp [primesUpTo, Nat.lt_succ_iff, and_comm]

/-- Every coordinate in `primesUpTo X` is prime. -/
theorem prime_of_mem_primesUpTo {X p : ℕ}
    (hp : p ∈ primesUpTo X) : Nat.Prime p :=
  (mem_primesUpTo.mp hp).1

/-- Every prime not exceeding `X` occurs in the ambient coordinate set. -/
theorem mem_primesUpTo_of_prime_le {X p : ℕ}
    (hp : Nat.Prime p) (hpX : p ≤ X) : p ∈ primesUpTo X :=
  mem_primesUpTo.mpr ⟨hp, hpX⟩

/-- The prime-product cube on all prime coordinates up to `X` is exactly a
Möbius-weighted first-failure frontier at any selected prime coordinate. -/
theorem primesUpToCube_eq_moebius_frontier
    {X ell : ℕ}
    (hellPrime : Nat.Prime ell)
    (hellX : ell ≤ X) :
    truncatedCubeAlternatingSum (primesUpTo X)
        (primeProductAdmissible (primesUpTo X) X) =
      ∑ t ∈ primeProductFirstFailureBoundary (primesUpTo X) X ell,
        μ (primeFaceProduct t) := by
  apply truncatedPrimeProductCube_eq_moebius_frontier
  · exact mem_primesUpTo_of_prime_le hellPrime hellX
  · intro p hp
    exact prime_of_mem_primesUpTo hp

/-- Every admissible face in the full prime ambient set represents a product
not exceeding the cutoff. -/
theorem primeFaceProduct_le_of_admissible_primesUpTo
    {X : ℕ} {t : Finset ℕ}
    (ht : primeProductAdmissible (primesUpTo X) X t) :
    primeFaceProduct t ≤ X :=
  ht.2

/-- Every coordinate of an admissible face in the full ambient set is a prime
not exceeding `X`. -/
theorem prime_of_mem_admissibleFace_primesUpTo
    {X : ℕ} {t : Finset ℕ}
    (ht : primeProductAdmissible (primesUpTo X) X t)
    {p : ℕ} (hp : p ∈ t) :
    Nat.Prime p ∧ p ≤ X := by
  exact mem_primesUpTo.mp (ht.1 hp)

/-- Hence the Möbius weight of every admissible full-ambient face is exactly
its Boolean parity sign. -/
theorem moebius_admissiblePrimeFace_eq_booleanCubeSign
    {X : ℕ} {t : Finset ℕ}
    (ht : primeProductAdmissible (primesUpTo X) X t) :
    μ (primeFaceProduct t) = booleanCubeSign t := by
  apply moebius_primeFaceProduct_eq_booleanCubeSign
  intro p hp
  exact (prime_of_mem_admissibleFace_primesUpTo ht hp).1

end RHLean.Arithmetic
