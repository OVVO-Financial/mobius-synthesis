import Mathlib
import RHLean.Arithmetic.TruncatedCubeMertensPrefix
import RHLean.Arithmetic.PrimesUpToFrontier

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- The ordinary Möbius prefix sum through `X` is exactly the Möbius-weighted
first-failure frontier at any prime coordinate `ell ≤ X`. -/
theorem moebiusPrefix_eq_primeFrontier
    {X ell : ℕ}
    (hellPrime : Nat.Prime ell)
    (hellX : ell ≤ X) :
    (∑ n ∈ Finset.range (X + 1), μ n) =
      ∑ t ∈ primeProductFirstFailureBoundary (primesUpTo X) X ell,
        μ (primeFaceProduct t) := by
  rw [← truncatedPrimeCube_eq_moebiusPrefix]
  exact primesUpToCube_eq_moebius_frontier hellPrime hellX

end RHLean.Arithmetic
