import Mathlib
import RHLean.Analysis.BlockCovarianceRefinement
import RHLean.Analysis.RamanujanDivisorBoundary
import RHLean.Proof.EndpointCubeAnalyticClosure

open scoped ArithmeticFunction.Moebius BigOperators

/-!
# LCM boundary for the post-root covariance remainder

An earlier layer exposed the exact physical pair carrier of the post-root covariance
remainder and the triangular first-separation owner descent on that carrier.
The parent map is necessarily many-to-one.  This file keeps the full pair
geometry instead: first split the remainder by whether the complete squarefree
pair cube fits below the physical endpoint, using the pair lcm as the intrinsic
cube product coordinate.

The interior class has `lcm(m,n) <= W`; the complementary class is the literal
multiplicative boundary `W < lcm(m,n)`.  The split is exact and signed.

The existing fresh-prime four-corner theorem is also specialized to the prefix
cutoff `W+1`: whenever the lower mixed corner `p*m` is already at most `W`, the
complete swapped pair cube has zero boundary mass.  This is the local identity
that the one-parent multiplicity formula suppresses.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open Finset Nat

attribute [local instance] Classical.propDecidable

/-- Pairs in the post-root remainder whose complete squarefree pair product
coordinate still fits below the physical endpoint. -/
def postRootCovarianceRemainderInteriorLcmCarrier
    (W : ℕ) : Finset (ℕ × ℕ) :=
  (postRootCovarianceRemainderPhysicalPairCarrier W).filter fun mn =>
    Nat.lcm mn.1 mn.2 ≤ W

/-- The literal multiplicative boundary left after the complete-lcm interior is
removed.  These are exactly the remainder pairs with `W < lcm(m,n)`. -/
def postRootCovarianceRemainderBoundaryLcmCarrier
    (W : ℕ) : Finset (ℕ × ℕ) :=
  (postRootCovarianceRemainderPhysicalPairCarrier W).filter fun mn =>
    ¬ Nat.lcm mn.1 mn.2 ≤ W

@[simp] theorem mem_postRootCovarianceRemainderInteriorLcmCarrier
    {W : ℕ} {mn : ℕ × ℕ} :
    mn ∈ postRootCovarianceRemainderInteriorLcmCarrier W ↔
      mn ∈ postRootCovarianceRemainderPhysicalPairCarrier W ∧
        Nat.lcm mn.1 mn.2 ≤ W := by
  simp [postRootCovarianceRemainderInteriorLcmCarrier]

@[simp] theorem mem_postRootCovarianceRemainderBoundaryLcmCarrier
    {W : ℕ} {mn : ℕ × ℕ} :
    mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W ↔
      mn ∈ postRootCovarianceRemainderPhysicalPairCarrier W ∧
        W < Nat.lcm mn.1 mn.2 := by
  simp [postRootCovarianceRemainderBoundaryLcmCarrier]

/-- Exact signed partition of the physical remainder carrier into complete
lcm fibres and the super-endpoint multiplicative boundary. -/
theorem postRootCovarianceRemainder_lcm_partition
    (W : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ postRootCovarianceRemainderInteriorLcmCarrier W, f mn) +
        (∑ mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W, f mn) =
      ∑ mn ∈ postRootCovarianceRemainderPhysicalPairCarrier W, f mn := by
  unfold postRootCovarianceRemainderInteriorLcmCarrier
    postRootCovarianceRemainderBoundaryLcmCarrier
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- The scalar post-root remainder is exactly the sum of its complete-lcm
interior and its multiplicative boundary, with Möbius signs retained. -/
theorem postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm
    (W : ℕ) :
    postRootCovarianceRemainder W =
      (∑ mn ∈ postRootCovarianceRemainderInteriorLcmCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) +
      ∑ mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
  rw [postRootCovarianceRemainder_eq_physicalPairCarrier]
  exact (postRootCovarianceRemainder_lcm_partition W
    (fun mn : ℕ × ℕ =>
      realMoebiusStep mn.1 * realMoebiusStep mn.2)).symm

/-- **A complete owner pair cube cancels before any norm.**  At prefix cutoff
`W+1`, if the lower mixed corner `p*m` is already physical, the top-escape
indicator in the existing four-corner recombination is false.  Hence the two
orientations of the entire fresh-prime pair cube sum to zero exactly. -/
theorem realMoebiusPairFourCornerMass_add_swap_eq_zero_of_lowerCorner
    {p W m n : ℕ} (hp : p.Prime) (hmn : m < n)
    (hpm : ¬ p ∣ m) (hpn : ¬ p ∣ n)
    (hlower : p * m ≤ W) :
    realMoebiusPairFourCornerMass p (W + 1) m n +
        realMoebiusPairFourCornerMass p (W + 1) n m = 0 := by
  rw [realMoebiusPairFourCornerMass_add_swap_eq_topEscape
    hp hmn hpm hpn]
  have hnot : ¬ W + 1 ≤ p * m := by omega
  simp [hnot]

/-! ## Exact complete lcm fibres -/

/-- Ordered Möbius mass of the complete divisor-pair fibre with fixed lcm.
This is the intrinsic signed mass of one complete squarefree pair cube. -/
def moebiusLcmPairMass (L : ℕ) : ℤ :=
  ∑ m ∈ L.divisors,
    ∑ n ∈ L.divisors,
      if L = Nat.lcm m n then μ m * μ n else 0

/-- Reindex the divisor sum of lcm fibres onto one common divisor square.  This
is the finite Fubini step behind the exact lcm-fibre Möbius identity. -/
private theorem sum_divisors_lcmPairMass_larger
    (f : ℕ → ℕ → ℕ → ℤ) (N : ℕ) :
    (∑ d ∈ N.divisors,
      ∑ m ∈ d.divisors,
        ∑ n ∈ d.divisors,
          if d = Nat.lcm m n then f m n d else 0) =
    (∑ d ∈ N.divisors,
      ∑ m ∈ N.divisors,
        ∑ n ∈ N.divisors,
          if d = Nat.lcm m n then f m n d else 0) := by
  congr! 1 with d hd
  rw [mem_divisors] at hd
  suffices ∀ m n,
      (m ∣ d ∧ n ∣ d ∧ d = Nat.lcm m n) = (d = Nat.lcm m n) by
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1,
      sum_filter, ite_sum_zero, ← ite_and, this]
  simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]

/-- Summing complete lcm fibres over `d | N` is the square of the divisor
Möbius sum. -/
private theorem sum_divisors_moebiusLcmPairMass_eq_sq (N : ℕ) :
    (∑ d ∈ N.divisors, moebiusLcmPairMass d) =
      (∑ d ∈ N.divisors, μ d) ^ 2 := by
  unfold moebiusLcmPairMass
  rw [sum_divisors_lcmPairMass_larger
    (fun m n _d => μ m * μ n) N, sum_comm]
  symm
  simp_rw [sq, mul_sum, sum_mul]
  congr! 1 with m hm
  rw [sum_comm]
  congr! 1 with n hn
  rw [sum_ite_eq_of_mem', mul_comm]
  rw [mem_divisors, Nat.lcm_dvd_iff]
  exact ⟨⟨dvd_of_mem_divisors hm, dvd_of_mem_divisors hn⟩,
    (mem_divisors.mp hm).2⟩

/-- **Complete lcm cube identity.**  The ordered Möbius mass of all divisor
pairs with `lcm(m,n)=L` is exactly `μ(L)`.

Equivalently, the three local squarefree states of every prime (`m` only,
`n` only, or both) have signed total `-1`, and the full product reproduces the
Möbius sign.  The proof below packages that product law as finite Möbius
inversion. -/
theorem moebiusLcmPairMass_eq_moebius (L : ℕ) :
    moebiusLcmPairMass L = μ L := by
  by_cases hL0 : L = 0
  · subst L
    simp [moebiusLcmPairMass]
  · have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
    let delta : ℕ → ℤ := fun n => if n = 1 then 1 else 0
    have hmass : ∀ n > 0, n ∈ (Set.univ : Set ℕ) →
        (∑ d ∈ n.divisors, moebiusLcmPairMass d) = delta n := by
      intro n hn _hnU
      rw [sum_divisors_moebiusLcmPairMass_eq_sq,
        RHLean.Analysis.sum_moebius_divisors_eq_one_or_zero]
      simp [delta]
    have hmu : ∀ n > 0, n ∈ (Set.univ : Set ℕ) →
        (∑ d ∈ n.divisors, μ d) = delta n := by
      intro n hn _hnU
      simpa [delta] using
        RHLean.Analysis.sum_moebius_divisors_eq_one_or_zero n
    have hinvMass :=
      (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
        (R := ℤ) (Set.univ : Set ℕ) (by simp)).mp hmass
    have hinvMu :=
      (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
        (R := ℤ) (Set.univ : Set ℕ) (by simp)).mp hmu
    have hm := hinvMass L hLpos (by simp)
    have hu := hinvMu L hLpos (by simp)
    exact hm.symm.trans hu

/-! ## Complete lcm interior as a Möbius prefix -/

/-- Ordered positive physical pairs whose lcm already fits below `W`.  Because
`lcm(m,n) ≤ W` forces both coordinates below `W`, this is the union of the
complete lcm fibres `1 ≤ L ≤ W`. -/
def moebiusLcmInteriorOrderedCarrier (W : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 W).product (Finset.Icc 1 W)).filter fun mn =>
    Nat.lcm mn.1 mn.2 ≤ W

@[simp] theorem mem_moebiusLcmInteriorOrderedCarrier
    {W : ℕ} {mn : ℕ × ℕ} :
    mn ∈ moebiusLcmInteriorOrderedCarrier W ↔
      mn.1 ∈ Finset.Icc 1 W ∧ mn.2 ∈ Finset.Icc 1 W ∧
        Nat.lcm mn.1 mn.2 ≤ W := by
  simp [moebiusLcmInteriorOrderedCarrier, and_assoc]

private theorem moebiusLcmInteriorOrderedCarrier_lcm_mem
    {W : ℕ} {mn : ℕ × ℕ}
    (hmn : mn ∈ moebiusLcmInteriorOrderedCarrier W) :
    Nat.lcm mn.1 mn.2 ∈ Finset.Icc 1 W := by
  rcases mem_moebiusLcmInteriorOrderedCarrier.mp hmn with
    ⟨hm, hn, htop⟩
  have hmpos : 0 < mn.1 := (Finset.mem_Icc.mp hm).1
  have hnpos : 0 < mn.2 := (Finset.mem_Icc.mp hn).1
  exact Finset.mem_Icc.mpr ⟨Nat.lcm_pos hmpos hnpos, htop⟩

/-- Inside a fixed interior lcm fibre, the physical ordered carrier is exactly
the complete divisor-pair fibre used by `moebiusLcmPairMass`. -/
private theorem sum_moebiusLcmInteriorOrderedCarrier_fiber
    {W L : ℕ} (hL : L ∈ Finset.Icc 1 W) :
    (∑ mn ∈ moebiusLcmInteriorOrderedCarrier W with
        Nat.lcm mn.1 mn.2 = L, μ mn.1 * μ mn.2) =
      moebiusLcmPairMass L := by
  have hLpos : 0 < L := (Finset.mem_Icc.mp hL).1
  have hLtop : L ≤ W := (Finset.mem_Icc.mp hL).2
  have hcarrier :
      (moebiusLcmInteriorOrderedCarrier W).filter
          (fun mn => Nat.lcm mn.1 mn.2 = L) =
        (L.divisors.product L.divisors).filter
          (fun mn => L = Nat.lcm mn.1 mn.2) := by
    ext mn
    constructor
    · intro hmn
      rcases Finset.mem_filter.mp hmn with ⟨hbase, heq⟩
      rcases mem_moebiusLcmInteriorOrderedCarrier.mp hbase with
        ⟨_hm, _hn, _htop⟩
      have hmdiv : mn.1 ∣ L := by
        rw [← heq]
        exact Nat.dvd_lcm_left mn.1 mn.2
      have hndiv : mn.2 ∣ L := by
        rw [← heq]
        exact Nat.dvd_lcm_right mn.1 mn.2
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_product.mpr ⟨
          mem_divisors.mpr ⟨hmdiv, hLpos.ne'⟩,
          mem_divisors.mpr ⟨hndiv, hLpos.ne'⟩⟩,
        heq.symm⟩
    · intro hmn
      rcases Finset.mem_filter.mp hmn with ⟨hprod, heq⟩
      rcases Finset.mem_product.mp hprod with ⟨hm, hn⟩
      have hmData := mem_divisors.mp hm
      have hnData := mem_divisors.mp hn
      have hmpos : 0 < mn.1 := Nat.pos_of_dvd_of_pos hmData.1 hLpos
      have hnpos : 0 < mn.2 := Nat.pos_of_dvd_of_pos hnData.1 hLpos
      have hmle : mn.1 ≤ L := Nat.le_of_dvd hLpos hmData.1
      have hnle : mn.2 ≤ L := Nat.le_of_dvd hLpos hnData.1
      refine Finset.mem_filter.mpr ⟨?_, heq.symm⟩
      exact mem_moebiusLcmInteriorOrderedCarrier.mpr ⟨
        Finset.mem_Icc.mpr ⟨hmpos, hmle.trans hLtop⟩,
        Finset.mem_Icc.mpr ⟨hnpos, hnle.trans hLtop⟩,
        by simpa [← heq] using hLtop⟩
  unfold moebiusLcmPairMass
  rw [hcarrier, Finset.sum_filter]
  simpa only using
    (Finset.sum_product
      (s := L.divisors) (t := L.divisors)
      (f := fun mn : ℕ × ℕ =>
        if L = Nat.lcm mn.1 mn.2 then μ mn.1 * μ mn.2 else 0))

/-- **Cumulative complete-cube identity.**  The ordered Möbius mass of every
physical pair whose lcm is at most `W` is exactly the ordinary Möbius prefix on
`1,...,W`.  Thus all child multiplicities inside the complete-lcm region have
already recombined before any estimate is taken. -/
theorem sum_moebiusLcmInteriorOrderedCarrier_eq_moebiusPrefix (W : ℕ) :
    (∑ mn ∈ moebiusLcmInteriorOrderedCarrier W, μ mn.1 * μ mn.2) =
      ∑ L ∈ Finset.Icc 1 W, μ L := by
  calc
    (∑ mn ∈ moebiusLcmInteriorOrderedCarrier W, μ mn.1 * μ mn.2) =
        ∑ L ∈ Finset.Icc 1 W,
          ∑ mn ∈ moebiusLcmInteriorOrderedCarrier W with
            Nat.lcm mn.1 mn.2 = L, μ mn.1 * μ mn.2 := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun mn hmn => moebiusLcmInteriorOrderedCarrier_lcm_mem hmn)
        (fun mn => μ mn.1 * μ mn.2)
    _ = ∑ L ∈ Finset.Icc 1 W, moebiusLcmPairMass L := by
      apply Finset.sum_congr rfl
      intro L hL
      exact sum_moebiusLcmInteriorOrderedCarrier_fiber hL
    _ = ∑ L ∈ Finset.Icc 1 W, μ L := by
      apply Finset.sum_congr rfl
      intro L _hL
      exact moebiusLcmPairMass_eq_moebius L

/-! ## Linear control of the complete-lcm positive orientation -/

/-- Canonically oriented positive pairs in the complete-lcm interior. -/
def moebiusLcmInteriorPositiveCarrier (W : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 W).product (Finset.Icc 1 W)).filter fun mn =>
    mn.1 < mn.2 ∧ Nat.lcm mn.1 mn.2 ≤ W

@[simp] theorem mem_moebiusLcmInteriorPositiveCarrier
    {W : ℕ} {mn : ℕ × ℕ} :
    mn ∈ moebiusLcmInteriorPositiveCarrier W ↔
      mn.1 ∈ Finset.Icc 1 W ∧ mn.2 ∈ Finset.Icc 1 W ∧
        mn.1 < mn.2 ∧ Nat.lcm mn.1 mn.2 ≤ W := by
  simp [moebiusLcmInteriorPositiveCarrier, and_assoc]

/-- The direct positive-lcm carrier is exactly the lcm-filter of the physical
positive-pair carrier used by the post-root covariance descent. -/
theorem moebiusLcmInteriorPositiveCarrier_eq_filter (W : ℕ) :
    moebiusLcmInteriorPositiveCarrier W =
      (mertensPositivePhysicalPairCarrier W).filter fun mn =>
        Nat.lcm mn.1 mn.2 ≤ W := by
  ext mn
  simp [moebiusLcmInteriorPositiveCarrier,
    mertensPositivePhysicalPairCarrier, and_assoc]

/-- The ordered complete-lcm carrier splits exactly into its diagonal and two
symmetric positive orientations. -/
theorem sum_moebiusLcmInteriorOrderedCarrier_eq_diagonal_add_two_mul_positive
    (W : ℕ) :
    (∑ mn ∈ moebiusLcmInteriorOrderedCarrier W, μ mn.1 * μ mn.2) =
      (∑ n ∈ Finset.Icc 1 W, μ n * μ n) +
        2 * ∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
          μ mn.1 * μ mn.2 := by
  have hsplit (m n : ℕ) :
      (if Nat.lcm m n ≤ W then μ m * μ n else 0) =
        (if m = n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) +
        (if m < n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) +
        (if n < m ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) := by
    by_cases hcut : Nat.lcm m n ≤ W
    · rcases lt_trichotomy m n with hlt | heq | hgt
      · have hne : m ≠ n := Nat.ne_of_lt hlt
        have hrev : ¬ n < m := by omega
        simp [hcut, hlt, hne, hrev]
      · subst n
        simp
      · have hne : m ≠ n := by omega
        have hfwd : ¬ m < n := by omega
        simp [hcut, hgt, hne, hfwd]
    · simp [hcut]
  have hdiag :
      (∑ m ∈ Finset.Icc 1 W,
        ∑ n ∈ Finset.Icc 1 W,
          if m = n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) =
        ∑ n ∈ Finset.Icc 1 W, μ n * μ n := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_eq_single m]
    · have hmW : m ≤ W := (Finset.mem_Icc.mp hm).2
      simp [hmW]
    · intro b _hb hbm
      simp [Ne.symm hbm]
    · intro hnot
      exact (hnot hm).elim
  have hswap :
      (∑ m ∈ Finset.Icc 1 W,
        ∑ n ∈ Finset.Icc 1 W,
          if n < m ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) =
        ∑ m ∈ Finset.Icc 1 W,
          ∑ n ∈ Finset.Icc 1 W,
            if m < n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _hm
    apply Finset.sum_congr rfl
    intro n _hn
    simp only [Nat.lcm_comm, mul_comm]
  have hordered :
      (∑ mn ∈ moebiusLcmInteriorOrderedCarrier W,
        μ mn.1 * μ mn.2) =
        ∑ m ∈ Finset.Icc 1 W,
          ∑ n ∈ Finset.Icc 1 W,
            if Nat.lcm m n ≤ W then μ m * μ n else 0 := by
    unfold moebiusLcmInteriorOrderedCarrier
    rw [Finset.sum_filter]
    simpa only using
      (Finset.sum_product
        (s := Finset.Icc 1 W) (t := Finset.Icc 1 W)
        (f := fun mn : ℕ × ℕ =>
          if Nat.lcm mn.1 mn.2 ≤ W then μ mn.1 * μ mn.2 else 0))
  have hpositive :
      (∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
        μ mn.1 * μ mn.2) =
        ∑ m ∈ Finset.Icc 1 W,
          ∑ n ∈ Finset.Icc 1 W,
            if m < n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0 := by
    unfold moebiusLcmInteriorPositiveCarrier
    rw [Finset.sum_filter]
    simpa only using
      (Finset.sum_product
        (s := Finset.Icc 1 W) (t := Finset.Icc 1 W)
        (f := fun mn : ℕ × ℕ =>
          if mn.1 < mn.2 ∧ Nat.lcm mn.1 mn.2 ≤ W then
            μ mn.1 * μ mn.2 else 0))
  rw [hordered, hpositive]
  calc
    (∑ m ∈ Finset.Icc 1 W,
      ∑ n ∈ Finset.Icc 1 W,
        if Nat.lcm m n ≤ W then μ m * μ n else 0) =
      (∑ m ∈ Finset.Icc 1 W,
        ∑ n ∈ Finset.Icc 1 W,
          if m = n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) +
      (∑ m ∈ Finset.Icc 1 W,
        ∑ n ∈ Finset.Icc 1 W,
          if m < n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) +
      (∑ m ∈ Finset.Icc 1 W,
        ∑ n ∈ Finset.Icc 1 W,
          if n < m ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) := by
        simp_rw [hsplit, Finset.sum_add_distrib]
    _ = (∑ n ∈ Finset.Icc 1 W, μ n * μ n) +
        2 * ∑ m ∈ Finset.Icc 1 W,
          ∑ n ∈ Finset.Icc 1 W,
            if m < n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0 := by
      rw [hdiag, hswap]
      ring

private theorem moebius_le_square_int (n : ℕ) :
    μ n ≤ μ n * μ n := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

private theorem neg_moebius_square_le_int (n : ℕ) :
    -(μ n * μ n) ≤ μ n := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

private theorem moebius_square_le_one_int (n : ℕ) :
    μ n * μ n ≤ (1 : ℤ) := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

/-- The complete-lcm positive mass never contributes positively. -/
theorem sum_moebiusLcmInteriorPositiveCarrier_nonpos (W : ℕ) :
    (∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
      μ mn.1 * μ mn.2) ≤ 0 := by
  have hdecomp :=
    sum_moebiusLcmInteriorOrderedCarrier_eq_diagonal_add_two_mul_positive W
  rw [sum_moebiusLcmInteriorOrderedCarrier_eq_moebiusPrefix] at hdecomp
  have hprefix_le_diag :
      (∑ n ∈ Finset.Icc 1 W, μ n) ≤
        ∑ n ∈ Finset.Icc 1 W, μ n * μ n := by
    exact Finset.sum_le_sum fun n _hn => moebius_le_square_int n
  omega

/-- The negative size of the complete-lcm positive mass is at most the endpoint. -/
theorem neg_endpoint_le_sum_moebiusLcmInteriorPositiveCarrier (W : ℕ) :
    -(W : ℤ) ≤
      ∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
        μ mn.1 * μ mn.2 := by
  have hdecomp :=
    sum_moebiusLcmInteriorOrderedCarrier_eq_diagonal_add_two_mul_positive W
  rw [sum_moebiusLcmInteriorOrderedCarrier_eq_moebiusPrefix] at hdecomp
  have hneg_prefix :
      -(∑ n ∈ Finset.Icc 1 W, μ n * μ n) ≤
        ∑ n ∈ Finset.Icc 1 W, μ n := by
    calc
      -(∑ n ∈ Finset.Icc 1 W, μ n * μ n) =
          ∑ n ∈ Finset.Icc 1 W, -(μ n * μ n) := by simp
      _ ≤ ∑ n ∈ Finset.Icc 1 W, μ n := by
        exact Finset.sum_le_sum fun n _hn => neg_moebius_square_le_int n
  have hdiag_endpoint :
      (∑ n ∈ Finset.Icc 1 W, μ n * μ n) ≤ (W : ℤ) := by
    calc
      (∑ n ∈ Finset.Icc 1 W, μ n * μ n) ≤
          ∑ _n ∈ Finset.Icc 1 W, (1 : ℤ) := by
        exact Finset.sum_le_sum fun n _hn => moebius_square_le_one_int n
      _ = (W : ℤ) := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp
  omega

/-- Real-valued form used by the covariance carrier. -/
theorem sum_realMoebiusStep_lcmInteriorPositive_nonpos (W : ℕ) :
    (∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) ≤ 0 := by
  simp only [realMoebiusStep]
  exact_mod_cast sum_moebiusLcmInteriorPositiveCarrier_nonpos W

/-- Real-valued lower bound used when subtracting post-root family interiors. -/
theorem neg_endpoint_le_sum_realMoebiusStep_lcmInteriorPositive (W : ℕ) :
    -(W : ℝ) ≤
      ∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
  simp only [realMoebiusStep]
  exact_mod_cast neg_endpoint_le_sum_moebiusLcmInteriorPositiveCarrier W

end RHLean.Proof