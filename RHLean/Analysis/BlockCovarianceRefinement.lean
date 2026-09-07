import Mathlib
import RHLean.Analysis.BlockCovarianceDecomposition

open scoped ArithmeticFunction.Moebius BigOperators

/-!
# Refining blocks to the exact diagonal, and the fresh-prime family isomorphism

`BlockCovarianceDecomposition` proves `S^2 = E + 2X` for signed blocks and
instantiates it at the square blocks.  Two things follow, and both are exact.

## 1. The block energy is not a free linear fact

The square-block energy exceeds the exact squarefree diagonal by *precisely*
twice the aggregate within-block covariance:

```text
E - Q = 2 * sum_j C_j,        Q(N) = sum_{n<N} mu(n)^2 = N - Z(N).
```

So proving `E << N^(1+eps)` is proving that aggregate is of RH scale.  It is not
an independent input, and the linear behaviour measured numerically must not be
promoted to a theorem.

The way out is not to bound `E` but to *refine* it.  For any splitting of every
block into signed children,

```text
E_coarse = E_refined + 2 * sum_j (children cross covariance of block j),
```

so each refinement step moves energy into the children and leaves behind an
explicit signed cross term.  Iterated down to singletons the energy becomes the
exact squarefree diagonal `Q(N)`, which is linear with no conjecture at all, and
every unordered Möbius pair has been charged to the unique refinement node at
which its two entries first separate.  That is the Green--Kubo identity rewritten
as an Euler/Othello covariance tree, with every signed cross term preserved on
the way down.

## 2. Fresh post-root primes preserve pair covariance

For a prime `p` and cofactors below `p`, multiplication by `p` flips the Möbius
sign, so it *reverses* the family mass but **preserves** the family pair
covariance:

```text
mu(p c) = - mu(c),        mu(p c) mu(p d) = mu(c) mu(d).
```

Hence the covariance carried strictly inside the `p`-family is literally the
global Möbius covariance at the reduced scale:

```text
C_inside p-family (through W) = C(floor(W/p) + 1)        for p * p > W.
```

That is an exact covariance descent, not an analogy: a post-root prime family is
an isometric copy of a lower-scale prefix as far as pair covariance is
concerned.  Summing over post-root primes and grouping by the reciprocal
quotient turns a supercritical scale into a sum of strictly lower-scale
covariances, which is where the descent formulation of
`MertensCovarianceDescent` earns its power saving.

No estimate, asymptotic input or RH hypothesis appears in this file.
-/

noncomputable section

namespace RHLean.Analysis

/-! ## The site-level objects are the generic ones -/

theorem signedBlockPrefix_realMoebiusStep (K : ℕ) :
    signedBlockPrefix realMoebiusStep K = realMertensLength K := rfl

theorem signedBlockEnergy_realMoebiusStep (K : ℕ) :
    signedBlockEnergy realMoebiusStep K = realMertensDiagonal K := rfl

theorem signedBlockCrossCovariance_realMoebiusStep (K : ℕ) :
    signedBlockCrossCovariance realMoebiusStep K =
      realMertensPositiveLagPairSum K := rfl

/-! ## One refinement step -/

/-- **Refinement identity.**  Splitting every block into signed children moves
the energy into the children and leaves exactly twice their internal cross
covariance behind.  Nothing is estimated and no absolute value is taken. -/
theorem signedBlockEnergy_refine
    (b : ℕ → ℕ → ℝ) (m : ℕ → ℕ) (K : ℕ) :
    signedBlockEnergy (fun j => signedBlockPrefix (b j) (m j)) K =
      (∑ j ∈ Finset.range K, signedBlockEnergy (b j) (m j)) +
        2 * ∑ j ∈ Finset.range K, signedBlockCrossCovariance (b j) (m j) := by
  have hstep : ∀ j ∈ Finset.range K,
      signedBlockPrefix (b j) (m j) ^ 2 =
        signedBlockEnergy (b j) (m j) +
          2 * signedBlockCrossCovariance (b j) (m j) :=
    fun j _hj => signedBlockPrefix_sq_eq_energy_add_two_mul_cross (b j) (m j)
  calc signedBlockEnergy (fun j => signedBlockPrefix (b j) (m j)) K
      = ∑ j ∈ Finset.range K, signedBlockPrefix (b j) (m j) ^ 2 := rfl
    _ = ∑ j ∈ Finset.range K,
          (signedBlockEnergy (b j) (m j) +
            2 * signedBlockCrossCovariance (b j) (m j)) :=
        Finset.sum_congr rfl hstep
    _ = (∑ j ∈ Finset.range K, signedBlockEnergy (b j) (m j)) +
          ∑ j ∈ Finset.range K, 2 * signedBlockCrossCovariance (b j) (m j) :=
        Finset.sum_add_distrib
    _ = (∑ j ∈ Finset.range K, signedBlockEnergy (b j) (m j)) +
          2 * ∑ j ∈ Finset.range K, signedBlockCrossCovariance (b j) (m j) := by
        rw [Finset.mul_sum]

/-- The leaf of any refinement is the exact squarefree diagonal, which needs no
conjecture: it is bounded by the number of sites. -/
theorem signedBlockEnergy_leaf_le (K : ℕ) :
    signedBlockEnergy realMoebiusStep K ≤ (K : ℝ) := by
  rw [signedBlockEnergy_realMoebiusStep]
  exact realMertensDiagonal_le K

/-! ## Square blocks: energy versus the exact diagonal -/

/-- Squarefree diagonal carried by the square block `[j^2, (j+1)^2)`. -/
def realSquareBlockDiagonal (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2), realMoebiusStep n ^ 2

private theorem square_le_succ_square (j : ℕ) : j ^ 2 ≤ (j + 1) ^ 2 :=
  Nat.pow_le_pow_left (by omega) 2

theorem realSquareBlockMass_eq_sub (j : ℕ) :
    realSquareBlockMass j =
      realMertensLength ((j + 1) ^ 2) - realMertensLength (j ^ 2) := by
  have hsplit :=
    Finset.sum_range_add_sum_Ico realMoebiusStep (square_le_succ_square j)
  unfold realSquareBlockMass realMertensLength
  linarith [hsplit]

theorem realSquareBlockDiagonal_eq_sub (j : ℕ) :
    realSquareBlockDiagonal j =
      realMertensDiagonal ((j + 1) ^ 2) - realMertensDiagonal (j ^ 2) := by
  have hsplit :=
    Finset.sum_range_add_sum_Ico (fun n => realMoebiusStep n ^ 2)
      (square_le_succ_square j)
  unfold realSquareBlockDiagonal realMertensDiagonal
  linarith [hsplit]

/-- **Green--Kubo inside one square block.** -/
theorem realSquareBlockMass_sq_eq_diagonal_add_two_mul_inner (j : ℕ) :
    realSquareBlockMass j ^ 2 =
      realSquareBlockDiagonal j + 2 * realSquareBlockInnerCovariance j := by
  have hb :=
    realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum ((j + 1) ^ 2)
  have ha :=
    realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum (j ^ 2)
  have hmass := realSquareBlockMass_eq_sub j
  have hinner : realSquareBlockInnerCovariance j =
      realMertensPositiveLagPairSum ((j + 1) ^ 2) -
        realMertensPositiveLagPairSum (j ^ 2) -
        realMertensLength (j ^ 2) *
          (realMertensLength ((j + 1) ^ 2) - realMertensLength (j ^ 2)) := by
    unfold realSquareBlockInnerCovariance
    rw [hmass]
  rw [hmass, realSquareBlockDiagonal_eq_sub j, hinner]
  linear_combination hb - ha

/-- The square-block diagonals telescope to the exact global diagonal. -/
theorem sum_realSquareBlockDiagonal (R : ℕ) :
    ∑ j ∈ Finset.range R, realSquareBlockDiagonal j =
      realMertensDiagonal (R ^ 2) := by
  induction R with
  | zero => norm_num [realMertensDiagonal]
  | succ R ih =>
      rw [Finset.sum_range_succ, ih, realSquareBlockDiagonal_eq_sub R]
      ring

/-- **The square-block energy is the exact diagonal plus twice the aggregate
within-block covariance.** -/
theorem signedBlockEnergy_realSquareBlockMass_eq (R : ℕ) :
    signedBlockEnergy realSquareBlockMass R =
      realMertensDiagonal (R ^ 2) +
        2 * ∑ j ∈ Finset.range R, realSquareBlockInnerCovariance j := by
  induction R with
  | zero => norm_num [realMertensDiagonal]
  | succ R ih =>
      rw [signedBlockEnergy_succ, Finset.sum_range_succ, ih,
        realSquareBlockMass_sq_eq_diagonal_add_two_mul_inner R,
        realSquareBlockDiagonal_eq_sub R]
      ring

/-- **The block energy is not an independent linear input.**  It exceeds the
exact squarefree diagonal by precisely twice the aggregate within-block
covariance, so an RH-scale bound on one is an RH-scale bound on the other. -/
theorem signedBlockEnergy_realSquareBlockMass_sub_diagonal (R : ℕ) :
    signedBlockEnergy realSquareBlockMass R - realMertensDiagonal (R ^ 2) =
      2 * ∑ j ∈ Finset.range R, realSquareBlockInnerCovariance j := by
  rw [signedBlockEnergy_realSquareBlockMass_eq]
  ring

/-! ## Fresh post-root prime families -/

/-- Multiplying a cofactor below `p` by the prime `p` reverses its Möbius
sign. -/
theorem realMoebiusStep_prime_mul_of_lt {p c : ℕ} (hp : p.Prime) (hc : c < p) :
    realMoebiusStep (p * c) = - realMoebiusStep c := by
  rcases Nat.eq_zero_or_pos c with rfl | hcpos
  · simp [realMoebiusStep]
  · have hnd : ¬ p ∣ c := by
      intro hd
      exact absurd (Nat.le_of_dvd hcpos hd) (not_le.mpr hc)
    exact realMoebiusStep_mul_prime_eq_neg hp hnd

/-- **A fresh prime preserves pair covariance while reversing mass.** -/
theorem realMoebiusStep_prime_mul_pair {p c d : ℕ} (hp : p.Prime)
    (hc : c < p) (hd : d < p) :
    realMoebiusStep (p * c) * realMoebiusStep (p * d) =
      realMoebiusStep c * realMoebiusStep d := by
  rw [realMoebiusStep_prime_mul_of_lt hp hc, realMoebiusStep_prime_mul_of_lt hp hd]
  ring

/-- Signed mass of the first `K` members of the `p`-family. -/
def largePrimeFamilyPrefix (p K : ℕ) : ℝ :=
  ∑ c ∈ Finset.range K, realMoebiusStep (p * c)

/-- Pair covariance carried strictly inside the `p`-family. -/
def largePrimeFamilyPairSum (p K : ℕ) : ℝ :=
  ∑ d ∈ Finset.range K, realMoebiusStep (p * d) * largePrimeFamilyPrefix p d

/-- The family mass is the reduced Mertens value with the sign reversed. -/
theorem largePrimeFamilyPrefix_eq_neg {p K : ℕ} (hp : p.Prime) (hK : K ≤ p) :
    largePrimeFamilyPrefix p K = - realMertensLength K := by
  have hstep : ∀ c ∈ Finset.range K,
      realMoebiusStep (p * c) = - realMoebiusStep c := by
    intro c hc
    exact realMoebiusStep_prime_mul_of_lt hp
      (lt_of_lt_of_le (Finset.mem_range.mp hc) hK)
  unfold largePrimeFamilyPrefix realMertensLength
  rw [Finset.sum_congr rfl hstep]
  simp

/-- **Covariance descent through a fresh prime family.**

The pair covariance inside the `p`-family is *exactly* the global Möbius
covariance at the reduced scale.  The two sign reversals cancel in every
product, so nothing is lost and nothing is estimated. -/
theorem largePrimeFamilyPairSum_eq {p K : ℕ} (hp : p.Prime) (hK : K ≤ p) :
    largePrimeFamilyPairSum p K = realMertensPositiveLagPairSum K := by
  unfold largePrimeFamilyPairSum realMertensPositiveLagPairSum
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hdK := Finset.mem_range.mp hd
  have hdp : d < p := lt_of_lt_of_le hdK hK
  rw [realMoebiusStep_prime_mul_of_lt hp hdp,
    largePrimeFamilyPrefix_eq_neg hp (hdK.le.trans hK)]
  ring

/-- **Post-root form.**  For a prime beyond the square root of the cutoff the
whole family lies below `p`, so its internal covariance is the Möbius covariance
at scale `floor(W/p) + 1`. -/
theorem largePrimeFamilyPairSum_postRoot {p W : ℕ} (hp : p.Prime)
    (hW : W < p * p) :
    largePrimeFamilyPairSum p (W / p + 1) =
      realMertensPositiveLagPairSum (W / p + 1) := by
  refine largePrimeFamilyPairSum_eq hp ?_
  have hlt : W / p < p := (Nat.div_lt_iff_lt_mul hp.pos).mpr hW
  omega

/-! ## Fresh-prime pair-cube boundary recombination -/

/-- The four signed descendants obtained by toggling a fresh prime in either
coordinate of a physical ordered pair. -/
def realMoebiusPairFourCornerMass (p K m n : ℕ) : ℝ :=
  realMoebiusStep m * realMoebiusStep n * positiveLagPairIndicator K m n +
    realMoebiusStep (p * m) * realMoebiusStep n *
      positiveLagPairIndicator K (p * m) n +
    realMoebiusStep m * realMoebiusStep (p * n) *
      positiveLagPairIndicator K m (p * n) +
    realMoebiusStep (p * m) * realMoebiusStep (p * n) *
      positiveLagPairIndicator K (p * m) (p * n)

/-- The packaged four-corner mass is exactly the old Möbius pair weight times
the mixed prime cell. -/
theorem realMoebiusPairFourCornerMass_eq_mixedPrimeCell
    {p K m n : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) (hpn : ¬ p ∣ n) :
    realMoebiusPairFourCornerMass p K m n =
      realMoebiusStep m * realMoebiusStep n *
        positiveLagPairMixedPrimeCell p K m n := by
  unfold realMoebiusPairFourCornerMass
  exact realMoebiusPair_fourCorners_eq_mixedPrimeCell hp hpm hpn

/-- **Local boundary recombination.**  Add the two orientations of one old pair.
The two interior order-crossing shells cancel exactly, leaving only the top
escape shell. -/
theorem realMoebiusPairFourCornerMass_add_swap_eq_topEscape
    {p K m n : ℕ} (hp : p.Prime) (hmn : m < n)
    (hpm : ¬ p ∣ m) (hpn : ¬ p ∣ n) :
    realMoebiusPairFourCornerMass p K m n +
        realMoebiusPairFourCornerMass p K n m =
      realMoebiusStep m * realMoebiusStep n *
        (if n < K ∧ K ≤ p * m then 1 else 0) := by
  rw [realMoebiusPairFourCornerMass_eq_mixedPrimeCell hp hpm hpn,
    realMoebiusPairFourCornerMass_eq_mixedPrimeCell hp hpn hpm]
  have hswap : realMoebiusStep n * realMoebiusStep m =
      realMoebiusStep m * realMoebiusStep n := by ring
  rw [hswap, ← mul_add,
    positiveLagPairMixedPrimeCell_add_swap_eq_topEscape hp hmn hpn]

/-- Sum of the swapped four-corner pair cubes over an arbitrary old pair
carrier.  The carrier can include pairs from other Euler families; the only
requirement below is that `p` is fresh in both old coordinates. -/
def realMoebiusPairFourCornerBoundarySum
    (p K : ℕ) (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ mn ∈ S,
    (realMoebiusPairFourCornerMass p K mn.1 mn.2 +
      realMoebiusPairFourCornerMass p K mn.2 mn.1)

/-- The corresponding signed top-escape boundary on the same old pair carrier. -/
def realMoebiusPairTopEscapeBoundarySum
    (p K : ℕ) (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ mn ∈ S,
    realMoebiusStep mn.1 * realMoebiusStep mn.2 *
      (if mn.2 < K ∧ K ≤ p * mn.1 then 1 else 0)

/-- **Finite-carrier boundary recombination.**  Complete fresh-prime pair cubes
cancel on every interior order shell.  After summing the signed old carrier,
only the explicit top-escape boundary remains.  No absolute value is taken and
no distributional assumption is used. -/
theorem realMoebiusPairFourCornerBoundaryRecombination
    {p K : ℕ} (S : Finset (ℕ × ℕ)) (hp : p.Prime)
    (hS : ∀ mn ∈ S,
      mn.1 < mn.2 ∧ ¬ p ∣ mn.1 ∧ ¬ p ∣ mn.2) :
    realMoebiusPairFourCornerBoundarySum p K S =
      realMoebiusPairTopEscapeBoundarySum p K S := by
  unfold realMoebiusPairFourCornerBoundarySum
    realMoebiusPairTopEscapeBoundarySum
  apply Finset.sum_congr rfl
  intro mn hmn
  rcases hS mn hmn with ⟨hlt, hfresh1, hfresh2⟩
  exact realMoebiusPairFourCornerMass_add_swap_eq_topEscape
    hp hlt hfresh1 hfresh2

/-- The complete lower-prefix pair carrier, recombined through the two
orientations of the fresh-prime four-corner cube. -/
def freshPrimePrefixPairCubeBoundaryMass (p K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K,
    ∑ m ∈ Finset.range n,
      (realMoebiusPairFourCornerMass p K m n +
        realMoebiusPairFourCornerMass p K n m)

/-- **Complete-prefix specialization.**  If the whole old prefix lies below the
fresh prime, the top escape left by four-corner cancellation is exactly the old
positive-lag Möbius covariance.  Thus the boundary is not estimated: it is
identified with the lower-scale covariance. -/
theorem freshPrimePrefixPairCubeBoundaryMass_eq_positiveLag
    {p K : ℕ} (hp : p.Prime) (hK : K ≤ p) :
    freshPrimePrefixPairCubeBoundaryMass p K =
      realMertensPositiveLagPairSum K := by
  rw [realMertensPositiveLagPairSum_eq_doubleSum]
  unfold freshPrimePrefixPairCubeBoundaryMass
  apply Finset.sum_congr rfl
  intro n hn
  have hnK : n < K := Finset.mem_range.mp hn
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m < n := Finset.mem_range.mp hm
  by_cases hm0 : m = 0
  · subst m
    simp [realMoebiusPairFourCornerMass, realMoebiusStep]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hnpos : 0 < n := lt_trans hmpos hmn
    have hnp : n < p := lt_of_lt_of_le hnK hK
    have hmp : m < p := hmn.trans hnp
    have hpm : ¬ p ∣ m := by
      intro hdiv
      exact absurd (Nat.le_of_dvd hmpos hdiv) (not_le.mpr hmp)
    have hpn : ¬ p ∣ n := by
      intro hdiv
      exact absurd (Nat.le_of_dvd hnpos hdiv) (not_le.mpr hnp)
    have hpair :=
      realMoebiusPairFourCornerMass_add_swap_eq_topEscape
        (K := K) hp hmn hpm hpn
    have hm1 : 1 ≤ m := hmpos
    have hp_le_pm : p ≤ p * m := by
      have hmul := Nat.mul_le_mul_left p hm1
      simpa using hmul
    have htop : K ≤ p * m := hK.trans hp_le_pm
    rw [hpair]
    simp [hnK, htop]

/-- **Boundary recombination equals covariance descent.**  For a complete fresh
prime family, the entire swapped four-corner boundary is exactly the covariance
carried inside that prime family.  This is the exact bridge between the
four-corner cancellation layer and the lower-scale family descent layer. -/
theorem freshPrimePrefixPairCubeBoundaryMass_eq_familyPairCovariance
    {p K : ℕ} (hp : p.Prime) (hK : K ≤ p) :
    freshPrimePrefixPairCubeBoundaryMass p K =
      largePrimeFamilyPairSum p K := by
  rw [freshPrimePrefixPairCubeBoundaryMass_eq_positiveLag hp hK,
    largePrimeFamilyPairSum_eq hp hK]

/-- Post-root form of the same recombination: the complete physical `p`-family
through cutoff `W` is exactly the boundary left after the fresh-prime pair cube
has canceled its interior shells. -/
theorem freshPrimePrefixPairCubeBoundaryMass_postRoot_eq_familyPairCovariance
    {p W : ℕ} (hp : p.Prime) (hW : W < p * p) :
    freshPrimePrefixPairCubeBoundaryMass p (W / p + 1) =
      largePrimeFamilyPairSum p (W / p + 1) := by
  apply freshPrimePrefixPairCubeBoundaryMass_eq_familyPairCovariance hp
  have hlt : W / p < p := (Nat.div_lt_iff_lt_mul hp.pos).mpr hW
  omega

/-- Aggregate the complete-prefix four-corner boundary over any finite family of
fresh primes. -/
def freshPrimeFamilySetPairCubeBoundaryMass
    (P : Finset ℕ) (K : ℕ) : ℝ :=
  ∑ p ∈ P, freshPrimePrefixPairCubeBoundaryMass p K

/-- **Family-set recombination.**  If every prime in `P` is fresh above the same
lower prefix `K`, all complete pair cubes reduce exactly to prime cardinality
times the one lower-scale covariance.  This is the form consumed by reciprocal
quotient bands. -/
theorem freshPrimeFamilySetPairCubeBoundaryMass_eq_card_mul_positiveLag
    (P : Finset ℕ) (K : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hK : ∀ p ∈ P, K ≤ p) :
    freshPrimeFamilySetPairCubeBoundaryMass P K =
      (P.card : ℝ) * realMertensPositiveLagPairSum K := by
  unfold freshPrimeFamilySetPairCubeBoundaryMass
  calc
    (∑ p ∈ P, freshPrimePrefixPairCubeBoundaryMass p K) =
        ∑ _p ∈ P, realMertensPositiveLagPairSum K := by
          apply Finset.sum_congr rfl
          intro p hpP
          exact freshPrimePrefixPairCubeBoundaryMass_eq_positiveLag
            (hprime p hpP) (hK p hpP)
    _ = (P.card : ℝ) * realMertensPositiveLagPairSum K := by simp

end RHLean.Analysis
