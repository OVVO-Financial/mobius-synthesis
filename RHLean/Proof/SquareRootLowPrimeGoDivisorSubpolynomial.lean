import Mathlib
import RHLean.Proof.DeathShellSubpolynomial
import RHLean.Proof.SquareRootLowPrimeGoDivisorFibers

/-!
# Subpolynomial control from a localized Go height set

The remaining Go-specific task is geometric: identify the globally recombined
second-difference support and show that its canonical heights occupy a short
finite set.  Once that is available, no further analytic estimate is needed.

This module packages the generic consequence of the repository's elementary
divisor bound.  If a finite source population `S` has positive canonical height,
all of its heights lie in a finite set `H`, and every `k in H` satisfies
`1 <= k <= N`, then for every `epsilon > 0`

`|S| <= C_epsilon * |H| * N^epsilon`.

Combined with `|H| = O(R)` and polynomial `N = R^O(1)`, this is exactly the
`R^(1+o(1))` cardinality mechanism sought for the Go shell.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- **Localized canonical heights have subpolynomial divisor multiplicity.**
The constant depends only on `ε`; the population, height set, and ambient height
bound are otherwise arbitrary. -/
theorem card_canonicalHeight_population_le_subpolynomial
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {S H : Finset ℕ} {N : ℕ},
        (∀ m ∈ S, 0 < deathShellHeightNat m) →
        (∀ m ∈ S, deathShellHeightNat m ∈ H) →
        (∀ k ∈ H, 1 ≤ k) →
        (∀ k ∈ H, k ≤ N) →
        (S.card : ℝ) ≤
          C * (H.card : ℝ) * Real.rpow (N : ℝ) ε := by
  obtain ⟨C, hC, hdiv⟩ := card_divisors_le_subpolynomial hε
  refine ⟨C, hC, ?_⟩
  intro S H N hpos hheight hHpos hHle
  have hcardNat :
      S.card ≤ ∑ k ∈ H, k.divisors.card :=
    card_le_canonicalHeight_divisorSum hpos hheight
  have hcardReal :
      (S.card : ℝ) ≤
        ∑ k ∈ H, (k.divisors.card : ℝ) := by
    exact_mod_cast hcardNat
  have hterm :
      ∀ k ∈ H,
        (k.divisors.card : ℝ) ≤ C * Real.rpow (N : ℝ) ε := by
    intro k hk
    have hkDiv := hdiv k (hHpos k hk)
    have hkNReal : (k : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hHle k hk
    have hrpow :
        Real.rpow (k : ℝ) ε ≤ Real.rpow (N : ℝ) ε :=
      Real.rpow_le_rpow (by positivity) hkNReal hε.le
    exact hkDiv.trans (mul_le_mul_of_nonneg_left hrpow hC)
  calc
    (S.card : ℝ) ≤ ∑ k ∈ H, (k.divisors.card : ℝ) := hcardReal
    _ ≤ ∑ k ∈ H, C * Real.rpow (N : ℝ) ε := by
      exact Finset.sum_le_sum fun k hk => hterm k hk
    _ = C * (H.card : ℝ) * Real.rpow (N : ℝ) ε := by
      simp
      ring

end RHLean.Proof
