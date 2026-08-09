import Mathlib
import RHLean.Proof.SignedCanonicalHeight

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

namespace BalancedCanonicalGap

/-!
# Balanced canonical gaps

This module continues `SignedCanonicalHeight.lean`.  Write an unordered factor pair as

```text
(u, u + d),   u >= 1,   d >= 0.
```

The balanced regime is `0 < d < u`.  In that regime the square-block map is almost
an ordinary translation, the canonical largest-prime orientation is equivalent to
one of the two endpoints being prime, and the two signed-height channels combine
into a single symmetric coefficient.

The final section defines a finite canonical-pair block increment and proves its exact
balanced/extreme decomposition.  No analytic estimate is assumed.
-/

/-- The product `u * (u + d)` lies in the complete square block
`B_n = [n^2, (n+1)^2)`. -/
def InSquareBlock (n u d : ℕ) : Prop :=
  n ^ 2 ≤ u * (u + d) ∧ u * (u + d) < (n + 1) ^ 2

/-- A nonzero gap smaller than the lower endpoint. -/
def BalancedGap (u d : ℕ) : Prop :=
  0 < d ∧ d < u

/-- Twice the absolute canonical height:
`2 Z = |q-c|(q+c) = d(2u+d)`. -/
def doubledHeight (u d : ℕ) : ℕ :=
  d * (2 * u + d)

/-- The factor sum in a square block is at least `2n`. -/
theorem factor_sum_ge_two_n {n u d : ℕ} (hblock : InSquareBlock n u d) :
    2 * n ≤ 2 * u + d := by
  by_contra hcon
  push_neg at hcon
  have hamgm : 4 * (u * (u + d)) ≤ (2 * u + d) ^ 2 := by
    nlinarith
  nlinarith [hblock.1]

/-- Any lower endpoint in `B_n` satisfies `u ≤ n`, without a balance assumption. -/
theorem left_le_block_index {n u d : ℕ}
    (hblock : InSquareBlock n u d) : u ≤ n := by
  by_contra hcon
  have hnu : n < u := by omega
  have hn1u : n + 1 ≤ u := by omega
  have hprod : u ^ 2 ≤ u * (u + d) := by
    nlinarith
  nlinarith [hblock.2]

/-- **Scale localization in the balanced regime.** -/
theorem scale_localization {n u d : ℕ} (hu : 1 ≤ u)
    (hblock : InSquareBlock n u d) (hbal : BalancedGap u d) :
    n ^ 2 < 2 * u ^ 2 ∧ u ≤ n ∧ n ≤ u + d ∧ u + d < 2 * n := by
  rcases hbal with ⟨hdpos, hdlt⟩
  have hupos : 0 < u := by omega
  have huvlt : u + d < 2 * u := by omega
  have hn2lt : n ^ 2 < 2 * u ^ 2 := by
    nlinarith [hblock.1]
  have hun : u ≤ n := left_le_block_index hblock
  have hnuv : n ≤ u + d := by
    by_contra hcon
    have huv_n : u + d < n := by omega
    have hu_uv : u ≤ u + d := by omega
    nlinarith [hblock.1]
  have huv2n : u + d < 2 * n := by
    nlinarith
  exact ⟨hn2lt, hun, hnuv, huv2n⟩

/-- **Height sandwich.**  In the balanced regime the doubled height is comparable
with `d n` with explicit constants `2` and `3`. -/
theorem height_sandwich {n u d : ℕ} (hu : 1 ≤ u)
    (hblock : InSquareBlock n u d) (hbal : BalancedGap u d) :
    2 * d * n ≤ doubledHeight u d ∧ doubledHeight u d < 3 * d * n := by
  rcases hbal with ⟨hdpos, hdlt⟩
  have hsum := factor_sum_ge_two_n hblock
  have hloc := scale_localization hu hblock ⟨hdpos, hdlt⟩
  dsimp [doubledHeight]
  constructor
  · nlinarith
  · nlinarith

/-! ## Canonical endpoint characterization -/

/-- `q` is a prime endpoint which dominates every prime divisor of the cofactor `c`.
This is the largest-prime condition without introducing a separate `P⁺` function. -/
def DominantPrime (q c : ℕ) : Prop :=
  q.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ c → p ≤ q

/-- The unordered pair `(u, u+d)` is the canonical largest-prime split of its
product.  Coprimality excludes the zero-Möbius repeated-prime case. -/
def CanonicalPair (u d : ℕ) : Prop :=
  Nat.Coprime u (u + d) ∧
    (DominantPrime (u + d) u ∨ DominantPrime u (u + d))

/-- In a balanced pair the upper endpoint is strictly between `u` and `2u`. -/
theorem right_between {u d : ℕ} (hbal : BalancedGap u d) :
    u < u + d ∧ u + d < 2 * u := by
  rcases hbal with ⟨hdpos, hdlt⟩
  omega

/-- If the upper endpoint of a balanced pair is composite, every prime divisor of
it is at most the lower endpoint. -/
theorem prime_dvd_right_le_left {u d p : ℕ} (hu : 1 ≤ u)
    (hbal : BalancedGap u d) (hcomp : ¬(u + d).Prime)
    (hp : p.Prime) (hpdvd : p ∣ u + d) : p ≤ u := by
  have huvpos : 0 < u + d := by omega
  have hple : p ≤ u + d := Nat.le_of_dvd huvpos hpdvd
  have hpne : p ≠ u + d := by
    intro heq
    apply hcomp
    simpa [heq] using hp
  obtain ⟨k, hk⟩ := hpdvd
  have hk2 : 2 ≤ k := by
    by_contra hnot
    have hkle : k ≤ 1 := by omega
    interval_cases k <;> simp_all
  have huvlt : u + d < 2 * u := (right_between hbal).2
  nlinarith

/-- A prime upper endpoint is coprime to the smaller endpoint. -/
theorem coprime_of_right_prime {u d : ℕ} (hu : 1 ≤ u)
    (hbal : BalancedGap u d) (hv : (u + d).Prime) :
    Nat.Coprime u (u + d) := by
  have huv : u < u + d := (right_between hbal).1
  have hnotdvd : ¬u + d ∣ u := by
    intro hdvd
    have hle : u + d ≤ u := Nat.le_of_dvd (by omega) hdvd
    omega
  exact ((hv.coprime_iff_not_dvd).2 hnotdvd).symm

/-- A prime lower endpoint is coprime to the upper endpoint in the balanced regime. -/
theorem coprime_of_left_prime {u d : ℕ} (hu : 1 ≤ u)
    (hbal : BalancedGap u d) (huprime : u.Prime) :
    Nat.Coprime u (u + d) := by
  rcases hbal with ⟨hdpos, hdlt⟩
  apply (huprime.coprime_iff_not_dvd).2
  intro hdvd
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by
    by_contra hnot
    have hkle : k ≤ 1 := by omega
    interval_cases k <;> simp_all
  have huvlt : u + d < 2 * u := by omega
  nlinarith

/-- A prime upper endpoint satisfies the dominant-prime condition. -/
theorem dominant_right_of_prime {u d : ℕ} (hu : 1 ≤ u)
    (hv : (u + d).Prime) : DominantPrime (u + d) u := by
  refine ⟨hv, ?_⟩
  intro p hp hpdvd
  have hple : p ≤ u := Nat.le_of_dvd (by omega) hpdvd
  exact hple.trans (Nat.le_add_right u d)

/-- If the lower endpoint is prime and the upper endpoint is composite, then the
lower endpoint satisfies the dominant-prime condition. -/
theorem dominant_left_of_prime {u d : ℕ} (hu : 1 ≤ u)
    (hbal : BalancedGap u d) (huprime : u.Prime)
    (hcomp : ¬(u + d).Prime) : DominantPrime u (u + d) := by
  refine ⟨huprime, ?_⟩
  intro p hp hpdvd
  exact prime_dvd_right_le_left hu hbal hcomp hp hpdvd

/-- **Endpoint-prime characterization.**  For a balanced pair, being the canonical
largest-prime split is equivalent to at least one endpoint being prime. -/
theorem canonicalPair_iff_endpoint_prime {u d : ℕ} (hu : 1 ≤ u)
    (hbal : BalancedGap u d) :
    CanonicalPair u d ↔ u.Prime ∨ (u + d).Prime := by
  constructor
  · intro hcan
    rcases hcan.2 with hright | hleft
    · exact Or.inr hright.1
    · exact Or.inl hleft.1
  · intro hend
    rcases hend with huprime | hvprime
    · by_cases hv : (u + d).Prime
      · exact ⟨coprime_of_right_prime hu hbal hv,
          Or.inl (dominant_right_of_prime hu hv)⟩
      · exact ⟨coprime_of_left_prime hu hbal huprime,
          Or.inr (dominant_left_of_prime hu hbal huprime hv)⟩
    · exact ⟨coprime_of_right_prime hu hbal hvprime,
        Or.inl (dominant_right_of_prime hu hvprime)⟩

/-! ## The symmetric balanced coefficient -/

/-- Integer indicator. -/
def indicator (P : Prop) [Decidable P] : ℤ :=
  if P then 1 else 0

/-- The actual canonical source coefficient for the unordered pair. -/
noncomputable def canonicalCoefficient (u d : ℕ) : ℤ := by
  classical
  exact if CanonicalPair u d then (μ (u * (u + d)) : ℤ) else 0

/-- The symmetric balanced coefficient. -/
def beta (u d : ℕ) : ℤ :=
  (μ u : ℤ) * (μ (u + d) : ℤ) *
    indicator (u.Prime ∨ (u + d).Prime)

/-- On a canonical coprime pair the source Möbius weight factors. -/
theorem moebius_product_of_canonical {u d : ℕ} (hcan : CanonicalPair u d) :
    (μ (u * (u + d)) : ℤ) = (μ u : ℤ) * (μ (u + d) : ℤ) := by
  exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcan.1

/-- In the balanced regime the canonical source coefficient is exactly `beta`. -/
theorem canonicalCoefficient_eq_beta {u d : ℕ} (hu : 1 ≤ u)
    (hbal : BalancedGap u d) : canonicalCoefficient u d = beta u d := by
  classical
  by_cases hend : u.Prime ∨ (u + d).Prime
  · have hcan : CanonicalPair u d :=
      (canonicalPair_iff_endpoint_prime hu hbal).2 hend
    have hmul := moebius_product_of_canonical hcan
    simp [canonicalCoefficient, beta, indicator, hcan, hend, hmul]
  · have hcan : ¬CanonicalPair u d := by
      intro h
      exact hend ((canonicalPair_iff_endpoint_prime hu hbal).1 h)
    simp [canonicalCoefficient, beta, indicator, hcan, hend]

/-- **Symmetric coefficient identity.**  The two signed-height endpoint-prime
channels combine into one coefficient, with the prime-prime overlap subtracted once. -/
theorem beta_symmetric_identity (u d : ℕ) :
    beta u d =
      -(μ u : ℤ) * indicator (u + d).Prime
      - (μ (u + d) : ℤ) * indicator u.Prime
      - indicator u.Prime * indicator (u + d).Prime := by
  by_cases hu : u.Prime <;> by_cases hv : (u + d).Prime <;>
    simp [beta, indicator, hu, hv, ArithmeticFunction.moebius_apply_prime]

/-! ## Fixed-gap injectivity of the square-block coordinate -/

/-- The square-block coordinate attached to the pair `(u, u+d)`. -/
def blockIndex (d u : ℕ) : ℕ :=
  Nat.sqrt (u * (u + d))

/-- Every pair belongs to the block indexed by `blockIndex`. -/
theorem blockIndex_mem (d u : ℕ) : InSquareBlock (blockIndex d u) u d := by
  constructor
  · exact Nat.sqrt_le' (u * (u + d))
  · exact Nat.lt_succ_sqrt' (u * (u + d))

/-- For a fixed gap, at most one lower endpoint can lie in a square block. -/
theorem not_lt_of_same_block {n u₁ u₂ d : ℕ}
    (h1 : InSquareBlock n u₁ d) (h2 : InSquareBlock n u₂ d) : ¬u₁ < u₂ := by
  intro hlt
  have hsum := factor_sum_ge_two_n h1
  obtain ⟨k, rfl⟩ : ∃ k, u₂ = u₁ + 1 + k :=
    ⟨u₂ - u₁ - 1, by omega⟩
  nlinarith [h1.1, h2.2]

/-- Fixed-gap uniqueness inside one square block. -/
theorem unique_in_same_block {n u₁ u₂ d : ℕ}
    (h1 : InSquareBlock n u₁ d) (h2 : InSquareBlock n u₂ d) : u₁ = u₂ := by
  have h12 := not_lt_of_same_block h1 h2
  have h21 := not_lt_of_same_block h2 h1
  omega

/-- **Fixed-gap injectivity.** -/
theorem blockIndex_injective (d : ℕ) : Function.Injective (blockIndex d) := by
  intro u₁ u₂ heq
  have h1 := blockIndex_mem d u₁
  have h2 := blockIndex_mem d u₂
  rw [← heq] at h2
  exact unique_in_same_block h1 h2

/-! ## Exact balanced/extreme reconstruction -/

/-- A finite universe large enough to contain every positive factor pair in `B_n`. -/
def pairUniverse (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1)).product (Finset.range ((n + 1) ^ 2 + 1))

/-- Every positive pair in `B_n` occurs in `pairUniverse n`. -/
theorem mem_pairUniverse_of_block {n u d : ℕ} (hu : 1 ≤ u)
    (hblock : InSquareBlock n u d) : (u, d) ∈ pairUniverse n := by
  have hun : u ≤ n := left_le_block_index hblock
  have hult : u < n + 1 := by omega
  have huv_le_prod : u + d ≤ u * (u + d) := by
    nlinarith
  have hdlt : d < (n + 1) ^ 2 + 1 := by
    nlinarith [hblock.2]
  simp [pairUniverse, hult, hdlt]

/-- The active high-band predicate.  `K` is a threshold for the doubled height. -/
def HighPair (n K : ℕ) (p : ℕ × ℕ) : Prop :=
  1 ≤ p.1 ∧ InSquareBlock n p.1 p.2 ∧ K < doubledHeight p.1 p.2

/-- The full canonical high-band block increment. -/
noncomputable def highBandBlockIncrement (n K : ℕ) : ℤ := by
  classical
  exact ∑ p ∈ pairUniverse n,
    if HighPair n K p then canonicalCoefficient p.1 p.2 else 0

/-- The balanced part `0 < d < u`; positivity of `d` follows automatically from
`HighPair`. -/
noncomputable def balancedHighBandBlockIncrement (n K : ℕ) : ℤ := by
  classical
  exact ∑ p ∈ pairUniverse n,
    if HighPair n K p ∧ p.2 < p.1 then beta p.1 p.2 else 0

/-- The extreme part `u ≤ d`. -/
noncomputable def extremeHighBandBlockIncrement (n K : ℕ) : ℤ := by
  classical
  exact ∑ p ∈ pairUniverse n,
    if HighPair n K p ∧ p.1 ≤ p.2 then canonicalCoefficient p.1 p.2 else 0

/-- **Exact reconstruction of the high-band block increment.** -/
theorem highBandBlockIncrement_eq_balanced_add_extreme (n K : ℕ) :
    highBandBlockIncrement n K =
      balancedHighBandBlockIncrement n K + extremeHighBandBlockIncrement n K := by
  classical
  unfold highBandBlockIncrement balancedHighBandBlockIncrement
    extremeHighBandBlockIncrement
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rcases p with ⟨u, d⟩
  by_cases hhigh : HighPair n K (u, d)
  · by_cases hdu : d < u
    · have hdpos : 0 < d := by
        rcases hhigh with ⟨hu, hblock, hheight⟩
        by_contra hnot
        have hd0 : d = 0 := by omega
        subst d
        simp [doubledHeight] at hheight
      have hu : 1 ≤ u := hhigh.1
      have hbal : BalancedGap u d := ⟨hdpos, hdu⟩
      have hcoeff := canonicalCoefficient_eq_beta hu hbal
      have hnotext : ¬u ≤ d := by omega
      simp [hhigh, hdu, hnotext, hcoeff]
    · have hext : u ≤ d := by omega
      simp [hhigh, hdu, hext]
  · simp [hhigh]

end BalancedCanonicalGap

end RHLean.Proof
