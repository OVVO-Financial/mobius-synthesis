import Mathlib
import RHLean.Arithmetic.AdmissibleFaceSquarefreeImage

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- The indicator-form truncated cube sum is exactly the sum over its admitted
faces. -/
theorem truncatedCubeAlternatingSum_primesUpTo_eq_admissibleFaceSum
    (X : ℕ) :
    truncatedCubeAlternatingSum (primesUpTo X)
        (primeProductAdmissible (primesUpTo X) X) =
      ∑ t ∈ admissiblePrimeFaces X, booleanCubeSign t := by
  classical
  unfold truncatedCubeAlternatingSum admissiblePrimeFaces
  rw [Finset.sum_filter]

/-- Reindexing through the injective prime-product map turns the admitted face
sum into the Möbius sum over squarefree integers up to `X`. -/
theorem admissibleFaceSum_eq_squarefreeMoebiusSum
    (X : ℕ) :
    (∑ t ∈ admissiblePrimeFaces X, booleanCubeSign t) =
      ∑ n ∈ squarefreeUpTo X, μ n := by
  calc
    (∑ t ∈ admissiblePrimeFaces X, booleanCubeSign t) =
        ∑ t ∈ admissiblePrimeFaces X, μ (primeFaceProduct t) := by
      apply Finset.sum_congr rfl
      intro t ht
      symm
      exact moebius_admissiblePrimeFace_eq_booleanCubeSign
        (mem_admissiblePrimeFaces.mp ht)
    _ = ∑ n ∈ (admissiblePrimeFaces X).image primeFaceProduct, μ n := by
      symm
      apply Finset.sum_image
      intro t ht u hu htu
      exact primeFaceProduct_injective_on_admissible_primesUpTo
        (mem_admissiblePrimeFaces.mp ht)
        (mem_admissiblePrimeFaces.mp hu) htu
    _ = ∑ n ∈ squarefreeUpTo X, μ n := by
      rw [image_primeFaceProduct_admissiblePrimeFaces]

/-- Möbius vanishes on the omitted nonsquarefree terms, so filtering the range
by squarefreeness does not change the prefix sum. -/
theorem squarefreeMoebiusSum_eq_fullPrefix
    (X : ℕ) :
    (∑ n ∈ squarefreeUpTo X, μ n) =
      ∑ n ∈ Finset.range (X + 1), μ n := by
  classical
  unfold squarefreeUpTo
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hsq : Squarefree n
  · simp [hsq]
  · simp [hsq, ArithmeticFunction.moebius_eq_zero_of_not_squarefree]

/-- Exact arithmetic closure: the truncated Boolean cube on all primes up to
`X` is the ordinary Möbius prefix sum through `X`. -/
theorem truncatedPrimeCube_eq_moebiusPrefix
    (X : ℕ) :
    truncatedCubeAlternatingSum (primesUpTo X)
        (primeProductAdmissible (primesUpTo X) X) =
      ∑ n ∈ Finset.range (X + 1), μ n := by
  rw [truncatedCubeAlternatingSum_primesUpTo_eq_admissibleFaceSum,
    admissibleFaceSum_eq_squarefreeMoebiusSum,
    squarefreeMoebiusSum_eq_fullPrefix]

end RHLean.Arithmetic
