import Mathlib
import RHLean.Arithmetic.MoebiusPrefixFrontierIdentity

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- Summing the exact frontier representation over every prime coordinate up to
`X` gives a simultaneous family identity rather than a single-coordinate one. -/
theorem sum_moebiusPrefix_eq_sum_primeFrontiers
    (X : ℕ) :
    (∑ _ell ∈ primesUpTo X, ∑ n ∈ Finset.range (X + 1), μ n) =
      ∑ ell ∈ primesUpTo X,
        ∑ t ∈ primeProductFirstFailureBoundary (primesUpTo X) X ell,
          μ (primeFaceProduct t) := by
  apply Finset.sum_congr rfl
  intro ell hell
  exact moebiusPrefix_eq_primeFrontier
    (prime_of_mem_primesUpTo hell) (mem_primesUpTo.mp hell).2

/-- Equivalently, the number of prime coordinates up to `X` times the Möbius
prefix is the total signed mass of all prime-coordinate frontiers. -/
theorem card_nsmul_moebiusPrefix_eq_sum_primeFrontiers
    (X : ℕ) :
    (primesUpTo X).card • (∑ n ∈ Finset.range (X + 1), μ n) =
      ∑ ell ∈ primesUpTo X,
        ∑ t ∈ primeProductFirstFailureBoundary (primesUpTo X) X ell,
          μ (primeFaceProduct t) := by
  simpa using sum_moebiusPrefix_eq_sum_primeFrontiers X

end RHLean.Arithmetic
