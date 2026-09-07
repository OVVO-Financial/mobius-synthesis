import Mathlib
import RHLean.Arithmetic.PrimeWheelMobiusRecovery

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- `IsPrimeWheelSmooth` unfolds to a squarefree test together with a bounded
quantifier over `Nat.primeFactors`, so it is decidable.  The instance has to be
available before the population filters below, otherwise `Finset.filter` cannot
elaborate. -/
instance instDecidableIsPrimeWheelSmooth (S : Finset ℕ) (n : ℕ) :
    Decidable (IsPrimeWheelSmooth S n) :=
  inferInstanceAs (Decidable (Squarefree n ∧ ∀ p ∈ n.primeFactors, p ∈ S))

namespace PrimeWheelFiniteSystem

/-- Sites in the pinned prefix killed by at least one prime square. -/
def squareFactorSites (W : PrimeWheelFiniteSystem) (x : ℕ) : Finset ℕ :=
  (W.prefixInterval x).filter fun n => ¬ Squarefree n

/-- Squarefree sites whose complete prime support lies in the selected wheel. -/
def smoothCoreSites (W : PrimeWheelFiniteSystem) (x : ℕ) : Finset ℕ :=
  (W.prefixInterval x).filter fun n => IsPrimeWheelSmooth W.primeCoordinates n

/-- Squarefree sites with a prime factor outside the selected wheel.

Under square-root coverage there can be at most one such factor, and the raw
prime-comb field already equals `μ` on this population. -/
def combResolvedSites (W : PrimeWheelFiniteSystem) (x : ℕ) : Finset ℕ :=
  (W.prefixInterval x).filter fun n =>
    Squarefree n ∧ ¬ IsPrimeWheelSmooth W.primeCoordinates n

@[simp] theorem mem_squareFactorSites
    (W : PrimeWheelFiniteSystem) (x n : ℕ) :
    n ∈ W.squareFactorSites x ↔
      n ∈ W.prefixInterval x ∧ ¬ Squarefree n := by
  simp [squareFactorSites]

@[simp] theorem mem_smoothCoreSites
    (W : PrimeWheelFiniteSystem) (x n : ℕ) :
    n ∈ W.smoothCoreSites x ↔
      n ∈ W.prefixInterval x ∧ IsPrimeWheelSmooth W.primeCoordinates n := by
  simp [smoothCoreSites]

@[simp] theorem mem_combResolvedSites
    (W : PrimeWheelFiniteSystem) (x n : ℕ) :
    n ∈ W.combResolvedSites x ↔
      n ∈ W.prefixInterval x ∧ Squarefree n ∧
        ¬ IsPrimeWheelSmooth W.primeCoordinates n := by
  simp [combResolvedSites]

/-- The three populations are an exact finite partition of every pinned prefix. -/
theorem densitySites_partition
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    (W.squareFactorSites x ∪ W.combResolvedSites x) ∪ W.smoothCoreSites x =
      W.prefixInterval x := by
  classical
  ext n
  simp only [Finset.mem_union, mem_squareFactorSites, mem_combResolvedSites,
    mem_smoothCoreSites]
  constructor
  · rintro ((h | h) | h) <;> exact h.1
  · intro hn
    by_cases hsq : Squarefree n
    · by_cases hsmooth : IsPrimeWheelSmooth W.primeCoordinates n
      · exact Or.inr ⟨hn, hsmooth⟩
      · exact Or.inl (Or.inr ⟨hn, hsq, hsmooth⟩)
    · exact Or.inl (Or.inl ⟨hn, hsq⟩)

/-- Square-factor sites are disjoint from comb-resolved sites. -/
theorem squareFactorSites_disjoint_combResolvedSites
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    Disjoint (W.squareFactorSites x) (W.combResolvedSites x) := by
  classical
  rw [Finset.disjoint_left]
  intro n hn0 hn1
  rw [mem_squareFactorSites] at hn0
  rw [mem_combResolvedSites] at hn1
  exact hn0.2 hn1.2.1

/-- Square-factor sites are disjoint from the smooth core. -/
theorem squareFactorSites_disjoint_smoothCoreSites
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    Disjoint (W.squareFactorSites x) (W.smoothCoreSites x) := by
  classical
  rw [Finset.disjoint_left]
  intro n hn0 hn1
  rw [mem_squareFactorSites] at hn0
  rw [mem_smoothCoreSites] at hn1
  exact hn0.2 hn1.2.1

/-- Comb-resolved sites are disjoint from the smooth core. -/
theorem combResolvedSites_disjoint_smoothCoreSites
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    Disjoint (W.combResolvedSites x) (W.smoothCoreSites x) := by
  classical
  rw [Finset.disjoint_left]
  intro n hn0 hn1
  rw [mem_combResolvedSites] at hn0
  rw [mem_smoothCoreSites] at hn1
  exact hn0.2.2 hn1.2

/-- Exact finite density identity:

`prefix population = square-factor zeros + comb-resolved signs + smooth core`.
-/
theorem density_card_decomposition
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    (W.prefixInterval x).card =
      (W.squareFactorSites x).card +
      (W.combResolvedSites x).card +
      (W.smoothCoreSites x).card := by
  classical
  have hAB := W.squareFactorSites_disjoint_combResolvedSites x
  have hAC := W.squareFactorSites_disjoint_smoothCoreSites x
  have hBC := W.combResolvedSites_disjoint_smoothCoreSites x
  have hABC :
      Disjoint (W.squareFactorSites x ∪ W.combResolvedSites x)
        (W.smoothCoreSites x) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hAC, hBC⟩
  rw [← W.densitySites_partition x]
  rw [Finset.card_union_of_disjoint hABC]
  rw [Finset.card_union_of_disjoint hAB]

/-- The raw comb is zero on the square-factor population. -/
theorem rawSite_eq_zero_on_squareFactorSites
    (W : PrimeWheelFiniteSystem)
    (hcover : PrimeWheelSqrtCoverage W.primeCoordinates W.upper)
    {x n : ℕ} (hx : x ≤ W.upper)
    (hn : n ∈ W.squareFactorSites x) :
    W.rawSite n = 0 := by
  have hmem := (W.mem_squareFactorSites x n).mp hn
  have hinterval := Finset.mem_Ioc.mp hmem.1
  unfold rawSite
  exact seededPrimeComb_eq_zero_of_not_squarefree
    W.primeCoordinates hcover (Nat.zero_lt_of_lt hinterval.1)
      (hinterval.2.trans hx) hmem.2

/-- The raw comb already equals Möbius on the non-smooth squarefree population. -/
theorem rawSite_eq_moebius_on_combResolvedSites
    (W : PrimeWheelFiniteSystem)
    (hcover : PrimeWheelSqrtCoverage W.primeCoordinates W.upper)
    {x n : ℕ} (hx : x ≤ W.upper)
    (hn : n ∈ W.combResolvedSites x) :
    W.rawSite n = μ n := by
  have hmem := (W.mem_combResolvedSites x n).mp hn
  have hinterval := Finset.mem_Ioc.mp hmem.1
  unfold rawSite
  exact seededPrimeComb_eq_moebius_of_not_smooth
    W.primeCoordinates W.primeCoordinates_prime hcover hmem.2.1
      (hinterval.2.trans hx) hmem.2.2

/-- The raw comb has the opposite Möbius sign on the smooth core. -/
theorem rawSite_eq_neg_moebius_on_smoothCoreSites
    (W : PrimeWheelFiniteSystem)
    {x n : ℕ}
    (hn : n ∈ W.smoothCoreSites x) :
    W.rawSite n = -μ n := by
  have hmem := (W.mem_smoothCoreSites x n).mp hn
  unfold rawSite
  exact seededPrimeComb_eq_neg_moebius_of_smooth
    W.primeCoordinates W.primeCoordinates_prime hmem.2

/-- Exact pointwise population classification matching the prime-comb
visualization. Every site in the prefix is in exactly one of the three cases:

* a square factor kills it and both raw/Möbius values are zero;
* the raw comb already equals Möbius;
* the site is smooth squarefree and the raw comb equals `-μ`.
-/
theorem primeWheelMobius_density_classification
    (W : PrimeWheelFiniteSystem)
    (hcover : PrimeWheelSqrtCoverage W.primeCoordinates W.upper)
    {x n : ℕ} (hx : x ≤ W.upper)
    (hn : n ∈ W.prefixInterval x) :
    (¬ Squarefree n ∧ W.rawSite n = 0 ∧ μ n = 0) ∨
    (Squarefree n ∧ ¬ IsPrimeWheelSmooth W.primeCoordinates n ∧
      W.rawSite n = μ n) ∨
    (IsPrimeWheelSmooth W.primeCoordinates n ∧ W.rawSite n = -μ n) := by
  by_cases hsq : Squarefree n
  · by_cases hsmooth : IsPrimeWheelSmooth W.primeCoordinates n
    · right
      right
      refine ⟨hsmooth, ?_⟩
      exact W.rawSite_eq_neg_moebius_on_smoothCoreSites
        (x := x) ((W.mem_smoothCoreSites x n).mpr ⟨hn, hsmooth⟩)
    · right
      left
      refine ⟨hsq, hsmooth, ?_⟩
      exact W.rawSite_eq_moebius_on_combResolvedSites hcover hx
        ((W.mem_combResolvedSites x n).mpr ⟨hn, hsq, hsmooth⟩)
  · left
    refine ⟨hsq, ?_, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq⟩
    exact W.rawSite_eq_zero_on_squareFactorSites hcover hx
      ((W.mem_squareFactorSites x n).mpr ⟨hn, hsq⟩)

/-- The Möbius sum over a prefix is supported exactly on the two squarefree
populations; square-factor sites contribute zero. -/
theorem moebius_sum_eq_resolved_add_smooth
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    (∑ n ∈ W.prefixInterval x, μ n) =
      (∑ n ∈ W.combResolvedSites x, μ n) +
      (∑ n ∈ W.smoothCoreSites x, μ n) := by
  classical
  have hABC :
      Disjoint (W.squareFactorSites x ∪ W.combResolvedSites x)
        (W.smoothCoreSites x) := by
    rw [Finset.disjoint_union_left]
    exact ⟨W.squareFactorSites_disjoint_smoothCoreSites x,
      W.combResolvedSites_disjoint_smoothCoreSites x⟩
  have hzero : ∑ n ∈ W.squareFactorSites x, μ n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      ((W.mem_squareFactorSites x n).mp hn).2
  rw [← W.densitySites_partition x, Finset.sum_union hABC,
    Finset.sum_union (W.squareFactorSites_disjoint_combResolvedSites x),
    hzero, zero_add]

/-! ## Exact finite `+ / 0 / -` population algebra

The limiting `30/40/30` law must not be used as if it were an independent local
sampling model.  At every finite prefix the two nonzero populations are tied
exactly to the squarefree mass and the signed Möbius residual.  In particular,
the local deviation of the positive and negative counts from equality *is* the
Möbius sum itself.
-/

/-- Integer indicator of a positive Möbius site. -/
def moebiusPositiveIndicator (n : ℕ) : ℤ :=
  if μ n = 1 then 1 else 0

/-- Integer indicator of a negative Möbius site. -/
def moebiusNegativeIndicator (n : ℕ) : ℤ :=
  if μ n = -1 then 1 else 0

/-- Positive Möbius population in a pinned prefix, represented as an integer count. -/
def moebiusPositiveCount (W : PrimeWheelFiniteSystem) (x : ℕ) : ℤ :=
  ∑ n ∈ W.prefixInterval x, moebiusPositiveIndicator n

/-- Negative Möbius population in a pinned prefix, represented as an integer count. -/
def moebiusNegativeCount (W : PrimeWheelFiniteSystem) (x : ℕ) : ℤ :=
  ∑ n ∈ W.prefixInterval x, moebiusNegativeIndicator n

/-- Exact squarefree population mass, since `μ(n)^2` is `1` exactly on squarefree sites. -/
def moebiusSquarefreeMass (W : PrimeWheelFiniteSystem) (x : ℕ) : ℤ :=
  ∑ n ∈ W.prefixInterval x, (μ n) ^ 2

/-- Pointwise positive-count identity `2*1_{μ=1} = μ^2 + μ`. -/
theorem two_mul_moebiusPositiveIndicator_eq (n : ℕ) :
    2 * moebiusPositiveIndicator n = (μ n) ^ 2 + μ n := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [moebiusPositiveIndicator, h]

/-- Pointwise negative-count identity `2*1_{μ=-1} = μ^2 - μ`. -/
theorem two_mul_moebiusNegativeIndicator_eq (n : ℕ) :
    2 * moebiusNegativeIndicator n = (μ n) ^ 2 - μ n := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [moebiusNegativeIndicator, h]

/-- Exact finite positive-population identity. -/
theorem two_mul_moebiusPositiveCount_eq_squarefree_add_sum
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    2 * W.moebiusPositiveCount x =
      W.moebiusSquarefreeMass x + ∑ n ∈ W.prefixInterval x, μ n := by
  unfold moebiusPositiveCount moebiusSquarefreeMass
  calc
    2 * (∑ n ∈ W.prefixInterval x, moebiusPositiveIndicator n) =
        ∑ n ∈ W.prefixInterval x, 2 * moebiusPositiveIndicator n := by
      rw [Finset.mul_sum]
    _ = ∑ n ∈ W.prefixInterval x, ((μ n) ^ 2 + μ n) := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact two_mul_moebiusPositiveIndicator_eq n
    _ = (∑ n ∈ W.prefixInterval x, (μ n) ^ 2) +
        ∑ n ∈ W.prefixInterval x, μ n := by
      rw [Finset.sum_add_distrib]

/-- Exact finite negative-population identity. -/
theorem two_mul_moebiusNegativeCount_eq_squarefree_sub_sum
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    2 * W.moebiusNegativeCount x =
      W.moebiusSquarefreeMass x - ∑ n ∈ W.prefixInterval x, μ n := by
  unfold moebiusNegativeCount moebiusSquarefreeMass
  calc
    2 * (∑ n ∈ W.prefixInterval x, moebiusNegativeIndicator n) =
        ∑ n ∈ W.prefixInterval x, 2 * moebiusNegativeIndicator n := by
      rw [Finset.mul_sum]
    _ = ∑ n ∈ W.prefixInterval x, ((μ n) ^ 2 - μ n) := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact two_mul_moebiusNegativeIndicator_eq n
    _ = (∑ n ∈ W.prefixInterval x, (μ n) ^ 2) -
        ∑ n ∈ W.prefixInterval x, μ n := by
      rw [Finset.sum_sub_distrib]

/-- **Finite nonzero-count balance.**  The positive-minus-negative population is
exactly the signed Möbius residual on the same prefix. -/
theorem moebiusPositiveCount_sub_negativeCount_eq_sum
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    W.moebiusPositiveCount x - W.moebiusNegativeCount x =
      ∑ n ∈ W.prefixInterval x, μ n := by
  have hp := W.two_mul_moebiusPositiveCount_eq_squarefree_add_sum x
  have hn := W.two_mul_moebiusNegativeCount_eq_squarefree_sub_sum x
  omega

/-- The squarefree population is exactly the sum of the two nonzero sign counts. -/
theorem moebiusPositiveCount_add_negativeCount_eq_squarefree
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    W.moebiusPositiveCount x + W.moebiusNegativeCount x =
      W.moebiusSquarefreeMass x := by
  have hp := W.two_mul_moebiusPositiveCount_eq_squarefree_add_sum x
  have hn := W.two_mul_moebiusNegativeCount_eq_squarefree_sub_sum x
  omega

end PrimeWheelFiniteSystem

end RHLean.Arithmetic
