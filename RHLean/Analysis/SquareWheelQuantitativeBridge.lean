import Mathlib
import RHLean.Arithmetic.PrimeProductLowerBound
import RHLean.Analysis.PrimeWheelRawBoundaryExpansionCollapse
import RHLean.Analysis.SquareWheelZeroModeElimination

/-!
# Quantitative square-wheel bridge

This module freezes the two exact bridges needed by the square-wheel attack.

First, Bertrand's postulate is sharpened at the existing square-root cutoff:
for `y >= 5`, the product of all primes up to `y` exceeds `3y`.  Consequently,
from primorial block `k = 2` onward the natural square-sensitive modulus exceeds
six times the arithmetic endpoint.  Every complete-square zero-mode coefficient
inside the minimal wheel is therefore uniformly smaller than `1/6`.

Second, the square-sampled nonzero Fourier response is identified directly with
the fully collapsed expansion-reindexed wheel numerator.  Thus the only object
left to estimate is the genuine nonzero quadratic response; no further exact
decomposition is introduced here.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- Bertrand plus the three distinct primes `2`, `3`, and a prime just above
`y/2` gives a quantitative lower bound for the full prime product.  The endpoint
`y = 5` is the unique small case where Bertrand may return `3`, and is discharged
from the explicit primes `2`, `3`, and `5`. -/
theorem three_mul_lt_primeProductUpTo
    (y : ℕ) (hy : 5 ≤ y) :
    3 * y < primeProductUpTo y := by
  by_cases hy5 : y = 5
  · subst y
    have h2mem : 2 ∈ primesUpTo 5 :=
      mem_primesUpTo.mpr ⟨Nat.prime_two, by omega⟩
    have h3mem : 3 ∈ primesUpTo 5 :=
      mem_primesUpTo.mpr ⟨Nat.prime_three, by omega⟩
    have h5mem : 5 ∈ primesUpTo 5 :=
      mem_primesUpTo.mpr ⟨Nat.prime_five, by omega⟩
    have h3erase : 3 ∈ (primesUpTo 5).erase 2 := by
      exact Finset.mem_erase.mpr ⟨by omega, h3mem⟩
    have h5erase : 5 ∈ (primesUpTo 5).erase 2 := by
      exact Finset.mem_erase.mpr ⟨by omega, h5mem⟩
    have hrest :
        3 * 5 ≤ ∏ q ∈ (primesUpTo 5).erase 2, q := by
      exact Finset.mul_le_prod
        (fun q hq =>
          (prime_of_mem_primesUpTo (Finset.mem_of_mem_erase hq)).one_le)
        h3erase h5erase (by omega)
    have hprod : 30 ≤ primeProductUpTo 5 := by
      calc
        30 = 2 * (3 * 5) := by norm_num
        _ ≤ 2 * (∏ q ∈ (primesUpTo 5).erase 2, q) :=
          Nat.mul_le_mul_left 2 hrest
        _ = primeProductUpTo 5 := by
          unfold primeProductUpTo
          exact Finset.mul_prod_erase
            (primesUpTo 5) (fun q : ℕ => q) h2mem
    omega
  · have hy6 : 6 ≤ y := by omega
    let n := y / 2
    have hn0 : n ≠ 0 := by
      dsimp [n]
      omega
    rcases Nat.bertrand n hn0 with ⟨p, hpPrime, hnp, hp2n⟩
    have hn3 : 3 ≤ n := by
      dsimp [n]
      omega
    have hpgt3 : 3 < p := lt_of_le_of_lt hn3 hnp
    have hpY : p ≤ y := by
      dsimp [n] at hp2n
      omega
    have h2mem : 2 ∈ primesUpTo y :=
      mem_primesUpTo.mpr ⟨Nat.prime_two, by omega⟩
    have h3mem : 3 ∈ primesUpTo y :=
      mem_primesUpTo.mpr ⟨Nat.prime_three, by omega⟩
    have hpmem : p ∈ primesUpTo y :=
      mem_primesUpTo.mpr ⟨hpPrime, hpY⟩
    have h3erase : 3 ∈ (primesUpTo y).erase 2 := by
      exact Finset.mem_erase.mpr ⟨by omega, h3mem⟩
    have hperase : p ∈ (primesUpTo y).erase 2 := by
      exact Finset.mem_erase.mpr ⟨by omega, hpmem⟩
    have hrest :
        3 * p ≤ ∏ q ∈ (primesUpTo y).erase 2, q := by
      exact Finset.mul_le_prod
        (fun q hq =>
          (prime_of_mem_primesUpTo (Finset.mem_of_mem_erase hq)).one_le)
        h3erase hperase (by omega)
    have hprod : 6 * p ≤ primeProductUpTo y := by
      calc
        6 * p = 2 * (3 * p) := by ring
        _ ≤ 2 * (∏ q ∈ (primesUpTo y).erase 2, q) :=
          Nat.mul_le_mul_left 2 hrest
        _ = primeProductUpTo y := by
          unfold primeProductUpTo
          exact Finset.mul_prod_erase
            (primesUpTo y) (fun q : ℕ => q) h2mem
    have hylt : 3 * y < 6 * p := by
      dsimp [n] at hnp
      omega
    exact hylt.trans_le hprod

/-- From block `k >= 2`, the natural square-sensitive period exceeds six times
the full primorial block endpoint. -/
theorem six_mul_primorialBlockUpper_lt_squareSensitiveModulus
    {k : ℕ} (hk : 2 ≤ k) :
    6 * primorialBlockUpper k < primorialSquareSensitiveModulus k := by
  let y := primorialWheelCutoff k
  let P := primeProductUpTo y
  have hy : 5 ≤ y := by
    dsimp [y]
    exact five_le_primorialWheelCutoff hk
  have hP : 3 * y < P := three_mul_lt_primeProductUpTo y hy
  have hU : primorialBlockUpper k < (y + 1) ^ 2 := by
    dsimp [y, primorialWheelCutoff]
    exact Nat.lt_succ_sqrt' (primorialBlockUpper k)
  have h6U : 6 * primorialBlockUpper k < 9 * y ^ 2 := by
    nlinarith
  have h9P : 9 * y ^ 2 < P ^ 2 := by
    nlinarith
  rw [primorialSquareSensitiveModulus_eq_primeProductUpTo_sq k]
  change 6 * primorialBlockUpper k < P ^ 2
  exact h6U.trans h9P

/-- On `k >= 2` the minimal torus is the natural square-sensitive period, so the
same factor-six separation holds for the actual modulus used by the collapsed
conductor expansion. -/
theorem six_mul_primorialBlockUpper_lt_minimalTorusModulus
    {k : ℕ} (hk : 2 ≤ k) :
    6 * primorialBlockUpper k < primorialMinimalTorusModulus k := by
  rw [primorialMinimalTorusModulus_eq_squareSensitiveModulus hk]
  exact six_mul_primorialBlockUpper_lt_squareSensitiveModulus hk

end RHLean.Arithmetic

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- The real zero-frequency coupling ratio of every complete-square sample in a
minimal primorial wheel is uniformly smaller than `1/6`. -/
theorem primorialMinimalSquareSampleRatio_lt_one_sixth
    {k n : ℕ} (hk : 2 ≤ k)
    (hupper : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    (squareWheelSampleLength (primorialMinimalWheelSystem k) n : ℝ) /
        ((primorialMinimalWheelSystem k).modulus : ℝ) < (1 : ℝ) / 6 := by
  have hNle :
      squareWheelSampleLength (primorialMinimalWheelSystem k) n ≤
        squarePrefixEndpoint n :=
    Nat.sub_le _ _
  have hNleU :
      squareWheelSampleLength (primorialMinimalWheelSystem k) n ≤
        primorialBlockUpper k :=
    hNle.trans hupper
  have hQ :
      6 * primorialBlockUpper k <
        (primorialMinimalWheelSystem k).modulus := by
    change 6 * primorialBlockUpper k < primorialMinimalTorusModulus k
    exact six_mul_primorialBlockUpper_lt_minimalTorusModulus hk
  have h6N :
      6 * squareWheelSampleLength (primorialMinimalWheelSystem k) n <
        (primorialMinimalWheelSystem k).modulus :=
    (Nat.mul_le_mul_left 6 hNleU).trans_lt hQ
  have h6Nreal :
      6 * (squareWheelSampleLength (primorialMinimalWheelSystem k) n : ℝ) <
        ((primorialMinimalWheelSystem k).modulus : ℝ) := by
    exact_mod_cast h6N
  have hQpos : 0 < ((primorialMinimalWheelSystem k).modulus : ℝ) := by
    exact_mod_cast (primorialMinimalWheelSystem k).modulus_pos
  apply (div_lt_iff₀ hQpos).2
  nlinarith

/-- The same coupling ratio is nonnegative, so complete-square samples lie in
the uniform interval `[0,1/6)`. -/
theorem primorialMinimalSquareSampleRatio_nonneg
    (k n : ℕ) :
    0 ≤ (squareWheelSampleLength (primorialMinimalWheelSystem k) n : ℝ) /
      ((primorialMinimalWheelSystem k).modulus : ℝ) := by
  positivity

/-- The complex square-wheel ratio is exactly the arithmetic ratio
`(X_n-L_k)/Q_k` on the minimal torus. -/
theorem primorialMinimalSquareWheelSampleRatio_eq
    (k n : ℕ) :
    squareWheelSampleRatio (primorialMinimalWheelSystem k) n =
      (((primorialMinimalTorusModulus k : ℕ) : ℂ)⁻¹) *
        (((squarePrefixEndpoint n - primorialBlockLower k : ℕ) : ℂ)) := by
  rfl

/-- The already-collapsed wheel numerator: raw ternary expansion boundary,
retained conductor-one raw bulk, and collapsed smooth boundary-bulk. -/
def primorialExpansionReindexedNumerator (k x : ℕ) : ℂ :=
  primorialRawExpansionBoundaryPairing k x +
    primorialRawRetainedBulk k x -
    2 * (((primorialSmoothCollapsedBoundaryBulk k x : ℤ) : ℂ))

/-- The decisive exact bridge.  At every complete-square sample in a block
`k >= 2`, the nonzero quadratic square response is the minimal-torus inverse
multiplying the explicit collapsed wheel numerator with precisely the endpoint
zero mode removed. -/
theorem primorialMinimalSquareWheelNonzeroResponse_eq_expansionReindexed
    (k n : ℕ) (hk : 2 ≤ k)
    (hlower : primorialBlockLower k < squarePrefixEndpoint n)
    (hupper : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n =
      (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        (primorialExpansionReindexedNumerator k (squarePrefixEndpoint n) -
          squareWheelSampleRatio (primorialMinimalWheelSystem k) n *
            primorialExpansionReindexedNumerator k (primorialBlockUpper k)) := by
  have hsample :=
    primeWheelResidual_squareEndpoint_eq_nonzero_add_zero
      (primorialMinimalWheelSystem k) n hlower hupper
  change
    ((((primorialMinimalWheelSystem k).residual
      (squarePrefixEndpoint n) : ℤ) : ℂ)) =
      squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n +
        squareWheelSampleRatio (primorialMinimalWheelSystem k) n *
          ((((primorialMinimalWheelSystem k).residual
            (primorialBlockUpper k) : ℤ) : ℂ))
    at hsample
  have hminSample :
      (primorialMinimalWheelSystem k).residual (squarePrefixEndpoint n) =
        (primorialWheelSystem k).residual (squarePrefixEndpoint n) :=
    primorialMinimalWheel_residual_eq_primorialWheel_residual k hupper
  have hminUpper :
      (primorialMinimalWheelSystem k).residual (primorialBlockUpper k) =
        (primorialWheelSystem k).residual (primorialBlockUpper k) :=
    primorialMinimalWheel_residual_eq_primorialWheel_residual k le_rfl
  have hlowerUpper : primorialBlockLower k < primorialBlockUpper k :=
    primorialEndpoint_strictMono (Nat.lt_succ_self k)
  have hsampleExpansion :
      ((((primorialWheelSystem k).residual
        (squarePrefixEndpoint n) : ℤ) : ℂ)) =
        (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
          primorialExpansionReindexedNumerator k (squarePrefixEndpoint n) := by
    simpa [primorialExpansionReindexedNumerator] using
      (primorialPeriodicRawResidual_eq_expansionReindexed
        k hk hlower hupper)
  have hupperExpansion :
      ((((primorialWheelSystem k).residual
        (primorialBlockUpper k) : ℤ) : ℂ)) =
        (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
          primorialExpansionReindexedNumerator k (primorialBlockUpper k) := by
    simpa [primorialExpansionReindexedNumerator] using
      (primorialPeriodicRawResidual_eq_expansionReindexed
        k hk hlowerUpper le_rfl)
  rw [hminSample, hminUpper, hsampleExpansion, hupperExpansion] at hsample
  calc
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n =
        (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
            primorialExpansionReindexedNumerator k (squarePrefixEndpoint n) -
          squareWheelSampleRatio (primorialMinimalWheelSystem k) n *
            ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
              primorialExpansionReindexedNumerator k (primorialBlockUpper k)) := by
      calc
        squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n =
            (squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n +
              squareWheelSampleRatio (primorialMinimalWheelSystem k) n *
                ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
                  primorialExpansionReindexedNumerator k
                    (primorialBlockUpper k))) -
              squareWheelSampleRatio (primorialMinimalWheelSystem k) n *
                ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
                  primorialExpansionReindexedNumerator k
                    (primorialBlockUpper k)) := by
          ring
        _ =
            (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
                primorialExpansionReindexedNumerator k (squarePrefixEndpoint n) -
              squareWheelSampleRatio (primorialMinimalWheelSystem k) n *
                ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
                  primorialExpansionReindexedNumerator k
                    (primorialBlockUpper k)) := by
          rw [← hsample]
    _ =
        (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
          (primorialExpansionReindexedNumerator k (squarePrefixEndpoint n) -
            squareWheelSampleRatio (primorialMinimalWheelSystem k) n *
              primorialExpansionReindexedNumerator k
                (primorialBlockUpper k)) := by
      ring

/-- Fully explicit form of the preceding bridge, with the zero-mode coefficient
written as `(X_n-L_k)/Q_k` rather than through the square-sampling abbreviation. -/
theorem primorialMinimalSquareWheelNonzeroResponse_eq_explicitExpansionReindexed
    (k n : ℕ) (hk : 2 ≤ k)
    (hlower : primorialBlockLower k < squarePrefixEndpoint n)
    (hupper : squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n =
      (((primorialMinimalTorusModulus k : ℕ) : ℂ)⁻¹) *
        (primorialExpansionReindexedNumerator k (squarePrefixEndpoint n) -
          ((((primorialMinimalTorusModulus k : ℕ) : ℂ)⁻¹) *
            (((squarePrefixEndpoint n - primorialBlockLower k : ℕ) : ℂ))) *
            primorialExpansionReindexedNumerator k (primorialBlockUpper k)) := by
  rw [primorialMinimalSquareWheelNonzeroResponse_eq_expansionReindexed
    k n hk hlower hupper]
  rw [primorialMinimalSquareWheelSampleRatio_eq k n]
  rfl

end RHLean.Analysis
