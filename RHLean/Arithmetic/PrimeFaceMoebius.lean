import Mathlib
import RHLean.Arithmetic.PrimeProductCubeFrontier

open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHLean.Arithmetic

/-- The product of a finite set of distinct primes has Möbius value equal to
its Boolean-cube parity sign. -/
theorem moebius_primeFaceProduct_eq_booleanCubeSign
    (t : Finset ℕ)
    (hprime : ∀ p ∈ t, Nat.Prime p) :
    μ (primeFaceProduct t) = booleanCubeSign t := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp [primeFaceProduct, booleanCubeSign]
  | @insert p t hp ih =>
      have hpPrime : Nat.Prime p := hprime p (Finset.mem_insert_self p t)
      have htPrime : ∀ q ∈ t, Nat.Prime q := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      have hcop : Nat.Coprime p (primeFaceProduct t) := by
        rw [hpPrime.coprime_iff_not_dvd]
        intro hpdiv
        have hpdiv' : p ∣ t.prod id := by
          simpa [primeFaceProduct] using hpdiv
        rcases (Prime.dvd_finset_prod_iff hpPrime.prime id).mp hpdiv' with
          ⟨q, hqt, hpq⟩
        rcases (htPrime q hqt).eq_one_or_self_of_dvd p hpq with hpOne | hpqEq
        · exact hpPrime.ne_one hpOne
        · exact hp (hpqEq ▸ hqt)
      have hprod :
          primeFaceProduct (insert p t) = p * primeFaceProduct t := by
        simp [primeFaceProduct, hp]
      rw [hprod]
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
      rw [ArithmeticFunction.moebius_apply_prime hpPrime]
      rw [ih htPrime]
      simp [booleanCubeSign, Finset.card_insert_of_notMem, hp, pow_succ]

/-- Every term in the concrete prime-product frontier can therefore be read
as an actual Möbius value rather than an abstract parity sign. -/
theorem truncatedPrimeProductCube_eq_moebius_frontier
    {S : Finset ℕ} {X ell : ℕ}
    (hell : ell ∈ S)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    truncatedCubeAlternatingSum S (primeProductAdmissible S X) =
      ∑ t ∈ primeProductFirstFailureBoundary S X ell,
        μ (primeFaceProduct t) := by
  rw [truncatedPrimeProductCube_eq_frontier hell hprime]
  apply Finset.sum_congr rfl
  intro t ht
  symm
  apply moebius_primeFaceProduct_eq_booleanCubeSign
  intro p hp
  have hpErase : p ∈ S.erase ell :=
    (mem_primeProductFirstFailureBoundary.mp ht).1 hp
  exact hprime p (Finset.mem_of_mem_erase hpErase)

end RHLean.Arithmetic
