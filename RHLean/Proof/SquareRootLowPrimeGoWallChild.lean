import Mathlib
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.SquareRootLowPrimeFirstOwnerWallRecurrence

/-!
# Canonical child carrier for the first-owner Go wall

The wall-pair carrier produced by the first-owner reduction is not intrinsically
multiplicity-weighted.  Every pair `(c,q)` is a genuine fresh-prime Euler edge
with `P+(c) < q`.  Hence the arithmetic child `m = c*q` remembers both
coordinates:

`P+(m) = q`, `canonicalCofactor(m) = c`.

This module therefore replaces the pair carrier by one literal squarefree child
set before any further matching or norm.  The product map is globally injective
and reverses the Möbius sign pointwise.  Thus every subsequent cancellation is
performed on physical integers, with no owner or partner multiplicity hidden in
the bookkeeping.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Arithmetic child of one wall pair. -/
def squareRootLowPrimeGoWallChild (z : ℕ × ℕ) : ℕ := z.1 * z.2

/-- Literal child set of the cofactor-first wall pair carrier. -/
def squareRootLowPrimeGoWallChildren (R K p : ℕ) : Finset ℕ :=
  (squareRootLowPrimeWallPairCarrierCofactorFirst R K p).image
    squareRootLowPrimeGoWallChild

/-- Complete arithmetic data of one literal wall pair. -/
theorem squareRootLowPrimeWallPair_data
    {R K p : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimeWallPairCarrierCofactorFirst R K p) :
    z.1 ∈ squareRootLowPrimeWallCofactors R K p ∧
      z.2 ∈ squareRootBornPartnerSet R z.1 ∧ z.2 ≤ K := by
  unfold squareRootLowPrimeWallPairCarrierCofactorFirst at hz
  rcases Finset.mem_biUnion.mp hz with ⟨c, hc, hz⟩
  rcases Finset.mem_image.mp hz with ⟨q, hq, hqz⟩
  have hcEq : c = z.1 := congrArg Prod.fst hqz
  have hqEq : q = z.2 := congrArg Prod.snd hqz
  subst c
  subst q
  have hqData := Finset.mem_filter.mp hq
  exact ⟨hc, hqData.1, hqData.2⟩

/-- The wall parent is positive, the partner is prime, and the partner strictly
exceeds the parent's canonical largest prime. -/
theorem squareRootLowPrimeWallPair_euler_data
    {R K p : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimeWallPairCarrierCofactorFirst R K p) :
    0 < z.1 ∧ z.2.Prime ∧
      canonicalLargestPrimeFactor z.1 < z.2 := by
  have hdata := squareRootLowPrimeWallPair_data hz
  rcases Finset.mem_filter.mp hdata.2.1 with
    ⟨hqRange, hqPrime, hrough, hqle, _hprod⟩
  have hcPos : 0 < z.1 := by
    have hqPos := hqPrime.pos
    omega
  exact ⟨hcPos, hqPrime, hrough⟩

/-- Every wall child canonically recovers its parent and its old-prime partner. -/
theorem squareRootLowPrimeWallPair_canonical_coordinates
    {R K p : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimeWallPairCarrierCofactorFirst R K p) :
    canonicalCofactor (squareRootLowPrimeGoWallChild z) = z.1 ∧
      canonicalLargestPrimeFactor (squareRootLowPrimeGoWallChild z) = z.2 := by
  have h := squareRootLowPrimeWallPair_euler_data hz
  unfold squareRootLowPrimeGoWallChild
  constructor
  · exact canonicalCofactor_mul_prime_eq_of_rough h.1 h.2.1 h.2.2
  · exact canonicalLargestPrimeFactor_mul_prime_eq_of_rough h.1 h.2.1 h.2.2

/-- **Global wall-child ownership.**  Distinct arithmetic wall pairs produce
distinct child integers; the child itself recovers both coordinates. -/
theorem squareRootLowPrimeGoWallChild_injOn
    {R K p : ℕ} :
    Set.InjOn squareRootLowPrimeGoWallChild
      (squareRootLowPrimeWallPairCarrierCofactorFirst R K p) := by
  intro z hz w hw hchild
  have hzCoords := squareRootLowPrimeWallPair_canonical_coordinates hz
  have hwCoords := squareRootLowPrimeWallPair_canonical_coordinates hw
  have hc : z.1 = w.1 := by
    rw [← hzCoords.1, ← hwCoords.1]
    exact congrArg canonicalCofactor hchild
  have hq : z.2 = w.2 := by
    rw [← hzCoords.2, ← hwCoords.2]
    exact congrArg canonicalLargestPrimeFactor hchild
  exact Prod.ext hc hq

/-- Passing from wall pairs to physical child integers loses no cardinality. -/
theorem card_squareRootLowPrimeGoWallChildren
    (R K p : ℕ) :
    (squareRootLowPrimeGoWallChildren R K p).card =
      (squareRootLowPrimeWallPairCarrierCofactorFirst R K p).card := by
  unfold squareRootLowPrimeGoWallChildren
  exact Finset.card_image_iff.mpr squareRootLowPrimeGoWallChild_injOn

/-- Adjoining the wall partner reverses the Möbius sign exactly. -/
theorem squareRootLowPrimeGoWallChild_moebius
    {R K p : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimeWallPairCarrierCofactorFirst R K p) :
    μ (squareRootLowPrimeGoWallChild z) = - μ z.1 := by
  have h := squareRootLowPrimeWallPair_euler_data hz
  have hfresh : ¬ z.2 ∣ z.1 :=
    squareRootLowPrimePrime_fresh_of_lpf_lt h.1 h.2.1 h.2.2
  have hcop : Nat.Coprime z.1 z.2 :=
    ((h.2.1.coprime_iff_not_dvd).2 hfresh).symm
  unfold squareRootLowPrimeGoWallChild
  calc
    μ (z.1 * z.2) = μ z.1 * μ z.2 :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
    _ = μ z.1 * (-1) := by
      rw [ArithmeticFunction.moebius_apply_prime h.2.1]
    _ = - μ z.1 := by ring

/-- The wall parent mass is exactly the negative Möbius mass of the physical
child set.  This removes the partner-count multiplicity before any estimate. -/
theorem squareRootLowPrimeWallPair_moebiusSum_eq_neg_childSum
    (R K p : ℕ) :
    (∑ z ∈ squareRootLowPrimeWallPairCarrierCofactorFirst R K p, μ z.1) =
      -(∑ n ∈ squareRootLowPrimeGoWallChildren R K p, μ n) := by
  unfold squareRootLowPrimeGoWallChildren
  rw [Finset.sum_image]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    rw [squareRootLowPrimeGoWallChild_moebius hz]
    simp
  · intro a ha b hb hab
    exact squareRootLowPrimeGoWallChild_injOn ha hb hab

/-- Every physical wall child lies below the square endpoint. -/
theorem squareRootLowPrimeGoWallChildren_subset_endpoint
    {R K p : ℕ} :
    squareRootLowPrimeGoWallChildren R K p ⊆
      Finset.Icc 1 (squareRootEndpoint R) := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
  have hdata := squareRootLowPrimeWallPair_data hz
  rcases Finset.mem_filter.mp hdata.2.1 with
    ⟨_hqRange, hqPrime, _hrough, hqle, hprod⟩
  have hcPos : 0 < z.1 := by omega
  have hpos : 0 < squareRootLowPrimeGoWallChild z := by
    unfold squareRootLowPrimeGoWallChild
    exact Nat.mul_pos hcPos hqPrime.pos
  exact Finset.mem_Icc.mpr ⟨by omega, by
    simpa [squareRootLowPrimeGoWallChild] using hprod⟩

/-- Every physical wall child has old-prime canonical owner at most `K`. -/
theorem squareRootLowPrimeGoWallChild_owner_le
    {R K p : ℕ} {n : ℕ}
    (hn : n ∈ squareRootLowPrimeGoWallChildren R K p) :
    canonicalLargestPrimeFactor n ≤ K := by
  rcases Finset.mem_image.mp hn with ⟨z, hz, hzn⟩
  have hcoords := squareRootLowPrimeWallPair_canonical_coordinates hz
  have hK := (squareRootLowPrimeWallPair_data hz).2.2
  rw [← hzn, hcoords.2]
  exact hK

/-- The canonical parent of every physical wall child lies strictly above the
common lower wall cutoff `floor(X_R/p)`. -/
theorem squareRootLowPrimeGoWallChild_parent_gt_cutoff
    {R K p : ℕ} {n : ℕ}
    (hn : n ∈ squareRootLowPrimeGoWallChildren R K p) :
    squareRootEndpoint R / p < canonicalCofactor n := by
  rcases Finset.mem_image.mp hn with ⟨z, hz, hzn⟩
  have hcoords := squareRootLowPrimeWallPair_canonical_coordinates hz
  have hwall := (Finset.mem_filter.mp
    (squareRootLowPrimeWallPair_data hz).1).2
  have hpPos : 0 < p := by
    by_contra hp0
    have hpZero : p = 0 := Nat.eq_zero_of_not_pos hp0
    rw [hpZero, Nat.zero_mul] at hwall
    omega
  have hdiv : squareRootEndpoint R / p < z.1 :=
    (Nat.div_lt_iff_lt_mul hpPos).2 (by
      simpa [Nat.mul_comm] using hwall)
  rw [← hzn, hcoords.1]
  exact hdiv

/-- **Intrinsic Go-wall characterization.**

When `p` is the first scheduled fresh prime after `K`, membership in the entire
wall child carrier depends only on the child integer: it is squarefree, lies
below the square endpoint, and stripping its canonical largest prime still
leaves a parent above the common lower wall cutoff `floor(X_R/p)`.

The old-owner condition is not an extra hypothesis.  It follows automatically:
if the canonical owner `q` were at least `p`, then `p*cofactor <= q*cofactor = n`
would contradict the wall inequality.  First-fresh minimality then forces
`q <= K`. -/
theorem mem_squareRootLowPrimeGoWallChildren_iff_parentAbove
    {R K U p n : ℕ} (hR : 2 ≤ R) (hUR : U < R)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U) K = some p) :
    n ∈ squareRootLowPrimeGoWallChildren R K p ↔
      2 ≤ n ∧ n ≤ squareRootEndpoint R ∧ Squarefree n ∧
        squareRootEndpoint R / p < canonicalCofactor n := by
  rcases squareRootLowPrimeFirstOwnerAbove_split_of_le_shallowCutoff
      (K := K) (U := U) (L := K) (p := p) (le_refl K) hfirst with
    ⟨post, hlist⟩
  have hpList : p ∈ squareRootLowPrimeFreshPrimeList K U := by
    rw [hlist]
    simp
  have hpSet : p ∈ squareRootLowPrimeFreshPrimeSet K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hpList
  have hpData := Finset.mem_filter.mp hpSet
  have hpPrime : p.Prime := hpData.2
  have hpIoc := Finset.mem_Ioc.mp hpData.1
  have hKp : K < p := hpIoc.1
  have hpU : p ≤ U := hpIoc.2
  have hpR : p < R := hpU.trans_lt hUR
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, hzn⟩
    have heuler := squareRootLowPrimeWallPair_euler_data hz
    have hendpoint := squareRootLowPrimeGoWallChildren_subset_endpoint hn
    have hnIcc := Finset.mem_Icc.mp hendpoint
    have hn2 : 2 ≤ n := by
      rw [← hzn]
      unfold squareRootLowPrimeGoWallChild
      have hcOne : 1 ≤ z.1 := by omega
      nlinarith [heuler.2.1.two_le]
    have hwallData := squareRootLowPrimeWallPair_data hz
    have hcSigned := (Finset.mem_filter.mp hwallData.1).1
    have hmuC : μ z.1 ≠ 0 :=
      (Finset.mem_filter.mp hcSigned).2.2
    have hmuChild : μ (squareRootLowPrimeGoWallChild z) ≠ 0 := by
      rw [squareRootLowPrimeGoWallChild_moebius hz]
      exact neg_ne_zero.mpr hmuC
    have hsq : Squarefree n := by
      apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
      simpa [hzn] using hmuChild
    exact ⟨hn2, hnIcc.2, hsq,
      squareRootLowPrimeGoWallChild_parent_gt_cutoff hn⟩
  · rintro ⟨hn2, hnX, hsq, hparent⟩
    have hn1 : 1 < n := by omega
    let q := canonicalLargestPrimeFactor n
    let c := canonicalCofactor n
    have hsource :=
      CanonicalGapAncestryBridge.canonicalSourceData_of_squarefree hsq hn1
    have hqPrime : q.Prime := by
      simpa [q] using hsource.1
    have hcOne : 1 ≤ c := by
      simpa [c] using hsource.2.1
    have hcSq : Squarefree c := by
      simpa [c] using hsource.2.2.1
    have hprod : c * q = n := by
      simpa [c, q] using canonicalCofactor_mul_largestPrimeFactor hn1
    have hrough : canonicalLargestPrimeFactor c < q := by
      by_cases hcEq : c = 1
      · simpa [canonicalLargestPrimeFactor, hcEq] using hqPrime.one_lt
      · have hcGt : 1 < c := by omega
        exact hsource.2.2.2.2
          (canonicalLargestPrimeFactor c)
          (canonicalLargestPrimeFactor_prime hcGt)
          (canonicalLargestPrimeFactor_dvd hcGt)
    have hwall' : squareRootEndpoint R < c * p :=
      (Nat.div_lt_iff_lt_mul hpPrime.pos).1 (by simpa [c] using hparent)
    have hwall : squareRootEndpoint R < p * c := by
      simpa [Nat.mul_comm] using hwall'
    have hqLtP : q < p := by
      by_contra hnot
      have hpq : p ≤ q := Nat.le_of_not_gt hnot
      have hpcq : p * c ≤ q * c := Nat.mul_le_mul_right c hpq
      have hqc : q * c = n := by simpa [Nat.mul_comm] using hprod
      have hpn : p * c ≤ n := by simpa [hqc] using hpcq
      omega
    have hqK : q ≤ K := by
      by_contra hnot
      have hKq : K < q := Nat.lt_of_not_ge hnot
      have hqU : q ≤ U := by omega
      have hqSet : q ∈ squareRootLowPrimeFreshPrimeSet K U := by
        unfold squareRootLowPrimeFreshPrimeSet
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr ⟨hKq, hqU⟩, hqPrime⟩
      have hqList : q ∈ squareRootLowPrimeFreshPrimeList K U := by
        simpa [squareRootLowPrimeFreshPrimeList] using hqSet
      have hpLeq := squareRootLowPrimeFirstOwnerAbove_le_of_mem
        hfirst hqList hKq
      omega
    have hupp : c ≤ squareRootEndpoint R / q := by
      apply (Nat.le_div_iff_mul_le hqPrime.pos).2
      simpa [hprod] using hnX
    have hcWin :
        c ∈ squareRootLowPrimeOldPrimeWallWindowCofactors R p q := by
      exact (mem_squareRootLowPrimeOldPrimeWallWindowCofactors_iff hqPrime).2
        ⟨hcSq, hrough, by simpa [c] using hparent, hupp⟩
    have hqOld : q ∈ squareRootLowPrimeWallOldPrimeSet K :=
      mem_squareRootLowPrimeWallOldPrimeSet.mpr ⟨hqPrime, hqK⟩
    have hpairOld :
        (c, q) ∈ squareRootLowPrimeWallPairCarrierOldPrimeFirst R K p := by
      unfold squareRootLowPrimeWallPairCarrierOldPrimeFirst
      apply Finset.mem_biUnion.mpr
      refine ⟨q, hqOld, ?_⟩
      exact Finset.mem_image.mpr ⟨c, hcWin, rfl⟩
    have hpair :
        (c, q) ∈ squareRootLowPrimeWallPairCarrierCofactorFirst R K p := by
      rw [squareRootLowPrimeWallPairCarrierCofactorFirst_eq_oldPrimeFirst
        hR hpPrime hKp hpR]
      exact hpairOld
    unfold squareRootLowPrimeGoWallChildren
    apply Finset.mem_image.mpr
    refine ⟨(c, q), hpair, ?_⟩
    simpa [squareRootLowPrimeGoWallChild] using hprod

end RHLean.Proof
