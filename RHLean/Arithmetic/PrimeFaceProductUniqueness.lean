import Mathlib
import RHLean.Arithmetic.PrimesUpToFrontier

noncomputable section

namespace RHLean.Arithmetic

/-- Two finite sets of prime coordinates with the same product are equal. -/
theorem primeFaceProduct_eq_iff
    {t u : Finset ℕ}
    (htPrime : ∀ p ∈ t, Nat.Prime p)
    (huPrime : ∀ p ∈ u, Nat.Prime p) :
    primeFaceProduct t = primeFaceProduct u ↔ t = u := by
  constructor
  · intro hprod
    apply Finset.ext
    intro p
    constructor
    · intro hpt
      have hpPrime : Nat.Prime p := htPrime p hpt
      have hpdiv : p ∣ primeFaceProduct t := by
        unfold primeFaceProduct
        exact Finset.dvd_prod_of_mem id hpt
      rw [hprod] at hpdiv
      have hpdiv' : p ∣ u.prod id := by
        simpa [primeFaceProduct] using hpdiv
      rcases (Prime.dvd_finset_prod_iff hpPrime.prime id).mp hpdiv' with
        ⟨q, hqu, hpq⟩
      rcases (huPrime q hqu).eq_one_or_self_of_dvd p hpq with hpOne | hpqEq
      · exact (hpPrime.ne_one hpOne).elim
      · exact hpqEq ▸ hqu
    · intro hpu
      have hpPrime : Nat.Prime p := huPrime p hpu
      have hpdiv : p ∣ primeFaceProduct u := by
        unfold primeFaceProduct
        exact Finset.dvd_prod_of_mem id hpu
      rw [← hprod] at hpdiv
      have hpdiv' : p ∣ t.prod id := by
        simpa [primeFaceProduct] using hpdiv
      rcases (Prime.dvd_finset_prod_iff hpPrime.prime id).mp hpdiv' with
        ⟨q, hqt, hpq⟩
      rcases (htPrime q hqt).eq_one_or_self_of_dvd p hpq with hpOne | hpqEq
      · exact (hpPrime.ne_one hpOne).elim
      · exact hpqEq ▸ hqt
  · intro htu
    subst u
    rfl

/-- Equality of prime-face products is therefore literal equality for faces
admissible in the canonical ambient set of all primes up to `X`. -/
theorem primeFaceProduct_injective_on_admissible_primesUpTo
    {X : ℕ} {t u : Finset ℕ}
    (ht : primeProductAdmissible (primesUpTo X) X t)
    (hu : primeProductAdmissible (primesUpTo X) X u)
    (hprod : primeFaceProduct t = primeFaceProduct u) :
    t = u := by
  apply (primeFaceProduct_eq_iff
    (fun p hp => (prime_of_mem_admissibleFace_primesUpTo ht hp).1)
    (fun p hp => (prime_of_mem_admissibleFace_primesUpTo hu hp).1)).mp
  exact hprod

end RHLean.Arithmetic
