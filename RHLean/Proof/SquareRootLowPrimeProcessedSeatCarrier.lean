import Mathlib
import RHLean.Proof.SquareRootLowPrimeResponseSeatCarrier

/-!
# Complete processed low-prime seat carrier

For a running largest-prime cutoff `P`, expand the entire real state `T(P)` as

* one distinguished head of weight `+1`; and
* one seat `(c,s)` for each unit of the complete combined response of every
  nonzero-Möbius cofactor with `P+(c) <= P`.

The seat weight is `-mu(c)`.  The complete carrier therefore has signed mass
exactly `T(P)`.

This is the common state space on which all fresh-prime coordinates can be
processed sequentially.  It contains the shallow creation states, the deep
response states, and every intermediate response cofactor in one literal finite
population.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Nonzero-Möbius cofactors visible at a running prime cutoff `P`. -/
def squareRootLowPrimeProcessedSignedCofactors
    (R P : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (squareRootEndpoint R)).filter fun c =>
    canonicalLargestPrimeFactor c ≤ P ∧ μ c ≠ 0

/-- All unit response seats visible at cutoff `P`. -/
def squareRootLowPrimeProcessedSeatAtoms
    (R K j P : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeProcessedSignedCofactors R P).biUnion
    (squareRootLowPrimeCombinedSeatFiber R K j)

/-- Complete processed carrier, including the distinguished head. -/
def squareRootLowPrimeProcessedSeatCarrier
    (R K j P : ℕ) : Finset (Option (ℕ × ℕ)) :=
  insert none ((squareRootLowPrimeProcessedSeatAtoms R K j P).image some)

/-- Real weight on the complete processed carrier. -/
def squareRootLowPrimeProcessedSeatWeightReal : Option (ℕ × ℕ) → ℝ
  | none => 1
  | some z => ((-μ z.1 : ℤ) : ℝ)

@[simp] theorem mem_squareRootLowPrimeProcessedSeatAtoms
    {R K j P : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeProcessedSeatAtoms R K j P ↔
      z.1 ∈ squareRootLowPrimeProcessedSignedCofactors R P ∧
        z.2 < squareRootLowPrimeCombinedFreshResponse R K j z.1 := by
  unfold squareRootLowPrimeProcessedSeatAtoms
  constructor
  · intro hz
    rcases Finset.mem_biUnion.mp hz with ⟨c, hc, hzc⟩
    have hdata := mem_squareRootLowPrimeCombinedSeatFiber.mp hzc
    rw [hdata.1]
    exact ⟨hc, hdata.2⟩
  · rintro ⟨hc, hs⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨z.1, hc, ?_⟩
    exact mem_squareRootLowPrimeCombinedSeatFiber.mpr ⟨rfl, hs⟩

/-- Distinct processed cofactor fibres are disjoint. -/
theorem squareRootLowPrimeProcessedSeatFiber_pairwiseDisjoint
    (R K j P : ℕ) :
    Set.PairwiseDisjoint
      (↑(squareRootLowPrimeProcessedSignedCofactors R P))
      (squareRootLowPrimeCombinedSeatFiber R K j) := by
  intro c _hc d _hd hcd
  change Disjoint
    (squareRootLowPrimeCombinedSeatFiber R K j c)
    (squareRootLowPrimeCombinedSeatFiber R K j d)
  rw [Finset.disjoint_left]
  intro z hzc hzd
  exact hcd
    ((mem_squareRootLowPrimeCombinedSeatFiber.mp hzc).1.symm.trans
      (mem_squareRootLowPrimeCombinedSeatFiber.mp hzd).1)

/-- Signed mass of all non-head processed seats. -/
theorem squareRootLowPrimeProcessedSeatAtoms_weight_sum
    (R K j P : ℕ) :
    (∑ z ∈ squareRootLowPrimeProcessedSeatAtoms R K j P,
      ((-μ z.1 : ℤ) : ℝ)) =
      ∑ c ∈ squareRootLowPrimeProcessedSignedCofactors R P,
        ((-μ c : ℤ) : ℝ) *
          (squareRootLowPrimeCombinedFreshResponse R K j c : ℝ) := by
  unfold squareRootLowPrimeProcessedSeatAtoms
  rw [Finset.sum_biUnion
    (squareRootLowPrimeProcessedSeatFiber_pairwiseDisjoint R K j P)]
  apply Finset.sum_congr rfl
  intro c _hc
  exact squareRootLowPrimeCombinedSeatFiber_weight_sum R K j c

/-- The head is not a processed seat. -/
theorem none_not_mem_squareRootLowPrimeProcessedSeatAtoms_image
    (R K j P : ℕ) :
    none ∉ (squareRootLowPrimeProcessedSeatAtoms R K j P).image some := by
  simp

/-- Exact mass of the complete processed carrier before identifying it with the
running state. -/
theorem squareRootLowPrimeProcessedSeatCarrier_weight_sum
    (R K j P : ℕ) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCarrier R K j P,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      1 +
        ∑ c ∈ squareRootLowPrimeProcessedSignedCofactors R P,
          ((-μ c : ℤ) : ℝ) *
            (squareRootLowPrimeCombinedFreshResponse R K j c : ℝ) := by
  unfold squareRootLowPrimeProcessedSeatCarrier
  rw [Finset.sum_insert
    (none_not_mem_squareRootLowPrimeProcessedSeatAtoms_image R K j P)]
  have himage :
      (∑ x ∈ (squareRootLowPrimeProcessedSeatAtoms R K j P).image some,
        squareRootLowPrimeProcessedSeatWeightReal x) =
        ∑ z ∈ squareRootLowPrimeProcessedSeatAtoms R K j P,
          ((-μ z.1 : ℤ) : ℝ) := by
    apply Finset.sum_image
    intro a _ha b _hb hab
    simpa using hab
  rw [himage, squareRootLowPrimeProcessedSeatAtoms_weight_sum]
  simp [squareRootLowPrimeProcessedSeatWeightReal]

private theorem processedHighFilter_eq_honestHighRange
    {R : ℕ} (hR : 2 ≤ R) :
    (Finset.Icc 1 (squareRootEndpoint R)).filter (fun c => c ≤ R - 1) =
      Finset.Icc 1 (R - 1) := by
  have hpredX : R - 1 ≤ squareRootEndpoint R := by
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  ext c
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- The processed combined cofactor-seat mass is the negative of the real
running response. -/
theorem squareRootLowPrimeProcessedCofactorMass_eq_neg_runningResponseReal
    {R K j P : ℕ} (hR : 2 ≤ R) :
    (∑ c ∈ squareRootLowPrimeProcessedSignedCofactors R P,
      ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeCombinedFreshResponse R K j c : ℝ)) =
      -(squareRootBornPostTailRunningLowPrimeResponse R K j P).re := by
  unfold squareRootLowPrimeProcessedSignedCofactors
  rw [Finset.sum_filter]
  unfold squareRootLowPrimeCombinedFreshResponse
  have hsplit :
      (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        if canonicalLargestPrimeFactor c ≤ P ∧ μ c ≠ 0 then
          ((-μ c : ℤ) : ℝ) *
            ((squareRootBornPartnerCount R c : ℕ) +
              if c ≤ R - 1 then
                squareRootBornPostTailHighResponse R K j c
              else 0 : ℕ)
        else 0) =
      -(∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          if canonicalLargestPrimeFactor c ≤ P then
            (μ c : ℝ) * (squareRootBornPartnerCount R c : ℝ)
          else 0) -
        ∑ c ∈ Finset.Icc 1 (R - 1),
          if canonicalLargestPrimeFactor c ≤ P then
            (μ c : ℝ) *
              (squareRootBornPostTailHighResponse R K j c : ℝ)
          else 0 := by
    rw [← processedHighFilter_eq_honestHighRange hR,
      Finset.sum_filter, ← Finset.sum_neg_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _hc
    by_cases hlpf : canonicalLargestPrimeFactor c ≤ P
    · by_cases hmu : μ c = 0
      · simp [hlpf, hmu]
      · by_cases hcR : c ≤ R - 1
        · simp [hlpf, hmu, hcR]
          ring
        · simp [hlpf, hmu, hcR]
    · simp [hlpf]
  rw [hsplit]
  unfold squareRootBornPostTailRunningLowPrimeResponse
  simp only [Complex.add_re, Complex.re_sum]
  have hborn :
      (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        (if canonicalLargestPrimeFactor c ≤ P then
          canonicalMoebiusWeight c *
            (squareRootBornPartnerCount R c : ℂ)
        else 0).re) =
      ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        if canonicalLargestPrimeFactor c ≤ P then
          (μ c : ℝ) * (squareRootBornPartnerCount R c : ℝ)
        else 0 := by
    apply Finset.sum_congr rfl
    intro c _hc
    by_cases hlpf : canonicalLargestPrimeFactor c ≤ P <;>
      simp [hlpf, canonicalMoebiusWeight]
  have hhigh :
      (∑ c ∈ Finset.Icc 1 (R - 1),
        (if canonicalLargestPrimeFactor c ≤ P then
          canonicalMoebiusWeight c *
            (squareRootBornPostTailHighResponse R K j c : ℂ)
        else 0).re) =
      ∑ c ∈ Finset.Icc 1 (R - 1),
        if canonicalLargestPrimeFactor c ≤ P then
          (μ c : ℝ) *
            (squareRootBornPostTailHighResponse R K j c : ℝ)
        else 0 := by
    apply Finset.sum_congr rfl
    intro c _hc
    by_cases hlpf : canonicalLargestPrimeFactor c ≤ P <;>
      simp [hlpf, canonicalMoebiusWeight]
  rw [hborn, hhigh]
  ring

/-- **The complete processed seat carrier has signed mass exactly `T(P)`.** -/
theorem squareRootLowPrimeProcessedSeatCarrier_mass_eq_runningImbalanceReal
    {R K j P : ℕ} (hR : 2 ≤ R) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCarrier R K j P,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeRunningImbalanceReal R K j P := by
  rw [squareRootLowPrimeProcessedSeatCarrier_weight_sum,
    squareRootLowPrimeProcessedCofactorMass_eq_neg_runningResponseReal hR]
  unfold squareRootLowPrimeRunningImbalanceReal
    squareRootLowPrimeRunningImbalance
  simp
  ring

/-- Every processed seat has real weight at most one in absolute value. -/
theorem abs_squareRootLowPrimeProcessedSeatWeightReal_le_one
    (x : Option (ℕ × ℕ)) :
    |squareRootLowPrimeProcessedSeatWeightReal x| ≤ 1 := by
  rcases x with _ | z
  · simp [squareRootLowPrimeProcessedSeatWeightReal]
  · change |(((-μ z.1 : ℤ) : ℝ))| ≤ 1
    have hInt : |(-μ z.1 : ℤ)| ≤ 1 := by
      simpa using (ArithmeticFunction.abs_moebius_le_one (n := z.1))
    exact_mod_cast hInt

end RHLean.Proof
