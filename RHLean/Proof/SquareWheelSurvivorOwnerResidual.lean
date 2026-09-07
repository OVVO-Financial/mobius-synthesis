import Mathlib
import RHLean.Proof.SquareRootBornPostTailLowPrimeRemainder
import RHLean.Proof.SquareWheelSurvivorProcessedResponseBridge

/-!
# Survivor owner-window residual and degree-of-freedom reduction

The physical survivor/processed-response bridge identifies the matched survivor
atoms whose canonical cofactor owner lies in the processed window `(K,U]`.
This file records what is left, before taking any norm.

For the endpoint survivor carrier `S` write

`S = D ⊔ W ⊔ P`,

where

* `D` is the processed-compatible matched sector `K < P+(c) <= U`;
* `W` is the matched owner-window residual `P+(c) <= K` or `U < P+(c)`;
* `P` is the complementary positive orientation `c < q <= R`.

The owner residual itself splits as

`W = W_shallow ⊔ W_above`

when `K <= U`.  Consequently the signed mass of the positive orientation is a
dependent coordinate:

`mass(P) = mass(S) - mass(D) - mass(W)`.

Equivalently, after splitting `W`,

`mass(P) = mass(S) - mass(D) - mass(W_shallow) - mass(W_above)`.

At the canonical cutoff `U = R - floor(sqrt R)`, the above-cutoff survivor
sector is even simpler: the born orientation is impossible, every remaining
cofactor is a near-root prime, every pair has source weight `+1`, and the whole
sector has cardinality at most `R` by the existing `sqrt R × sqrt R` near-root
rectangle.

Thus a later proof need not construct a separate positive-orientation carrier
bridge merely to identify its signed mass.  No cancellation estimate is used
in the degree-of-freedom identities; the only magnitude estimate below is the
already-elementary near-root rectangle bound.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Matched survivor atoms whose cofactor owner is at or below the packet depth. -/
noncomputable def squareWheelSurvivorShallowMatchedPairSet
    (R K : ℕ) : Finset (ℕ × ℕ) :=
  (squareWheelSurvivorEndpointMatchedPairSet R).filter fun cq =>
    canonicalLargestPrimeFactor cq.1 ≤ K

/-- Matched survivor atoms whose cofactor owner lies strictly above cutoff `U`. -/
noncomputable def squareWheelSurvivorAboveCutoffMatchedPairSet
    (R U : ℕ) : Finset (ℕ × ℕ) :=
  (squareWheelSurvivorEndpointMatchedPairSet R).filter fun cq =>
    U < canonicalLargestPrimeFactor cq.1

/-- The matched survivor atoms not represented by the processed deep owner
window `(K,U]`. -/
noncomputable def squareWheelSurvivorOwnerResidualPairSet
    (R K U : ℕ) : Finset (ℕ × ℕ) :=
  (squareWheelSurvivorEndpointMatchedPairSet R).filter fun cq =>
    canonicalLargestPrimeFactor cq.1 ≤ K ∨
      U < canonicalLargestPrimeFactor cq.1

@[simp] theorem mem_squareWheelSurvivorShallowMatchedPairSet
    {R K : ℕ} {cq : ℕ × ℕ} :
    cq ∈ squareWheelSurvivorShallowMatchedPairSet R K ↔
      cq ∈ squareWheelSurvivorEndpointMatchedPairSet R ∧
        canonicalLargestPrimeFactor cq.1 ≤ K := by
  simp [squareWheelSurvivorShallowMatchedPairSet]

@[simp] theorem mem_squareWheelSurvivorAboveCutoffMatchedPairSet
    {R U : ℕ} {cq : ℕ × ℕ} :
    cq ∈ squareWheelSurvivorAboveCutoffMatchedPairSet R U ↔
      cq ∈ squareWheelSurvivorEndpointMatchedPairSet R ∧
        U < canonicalLargestPrimeFactor cq.1 := by
  simp [squareWheelSurvivorAboveCutoffMatchedPairSet]

@[simp] theorem mem_squareWheelSurvivorOwnerResidualPairSet
    {R K U : ℕ} {cq : ℕ × ℕ} :
    cq ∈ squareWheelSurvivorOwnerResidualPairSet R K U ↔
      cq ∈ squareWheelSurvivorEndpointMatchedPairSet R ∧
        (canonicalLargestPrimeFactor cq.1 ≤ K ∨
          U < canonicalLargestPrimeFactor cq.1) := by
  simp [squareWheelSurvivorOwnerResidualPairSet]

/-- **Exact matched-sector degree split.**  Every matched survivor is either in
the processed deep owner window or in its owner residual. -/
theorem squareWheelSurvivorEndpointMatchedPairSet_eq_deep_union_ownerResidual
    (R K U : ℕ) :
    squareWheelSurvivorEndpointMatchedPairSet R =
      squareWheelSurvivorProcessedDeepPairSet R K U ∪
        squareWheelSurvivorOwnerResidualPairSet R K U := by
  ext cq
  simp only [Finset.mem_union,
    mem_squareWheelSurvivorProcessedDeepPairSet,
    mem_squareWheelSurvivorOwnerResidualPairSet]
  constructor
  · intro hm
    by_cases hK : canonicalLargestPrimeFactor cq.1 ≤ K
    · exact Or.inr ⟨hm, Or.inl hK⟩
    · have hK' : K < canonicalLargestPrimeFactor cq.1 := by omega
      by_cases hU : canonicalLargestPrimeFactor cq.1 ≤ U
      · exact Or.inl ⟨hm, hK', hU⟩
      · exact Or.inr ⟨hm, Or.inr (by omega)⟩
  · rintro (⟨hm, _hK, _hU⟩ | ⟨hm, _howner⟩)
    · exact hm
    · exact hm

/-- The processed deep sector and owner residual cannot overlap. -/
theorem squareWheelSurvivorProcessedDeep_disjoint_ownerResidual
    (R K U : ℕ) :
    Disjoint (squareWheelSurvivorProcessedDeepPairSet R K U)
      (squareWheelSurvivorOwnerResidualPairSet R K U) := by
  rw [Finset.disjoint_left]
  intro cq hd hw
  have hd' := (mem_squareWheelSurvivorProcessedDeepPairSet.mp hd).2
  have hw' := (mem_squareWheelSurvivorOwnerResidualPairSet.mp hw).2
  rcases hw' with hshallow | habove
  · omega
  · omega

/-- The owner residual is exactly its shallow and above-cutoff pieces. -/
theorem squareWheelSurvivorOwnerResidualPairSet_eq_shallow_union_above
    (R K U : ℕ) :
    squareWheelSurvivorOwnerResidualPairSet R K U =
      squareWheelSurvivorShallowMatchedPairSet R K ∪
        squareWheelSurvivorAboveCutoffMatchedPairSet R U := by
  ext cq
  simp only [Finset.mem_union,
    mem_squareWheelSurvivorOwnerResidualPairSet,
    mem_squareWheelSurvivorShallowMatchedPairSet,
    mem_squareWheelSurvivorAboveCutoffMatchedPairSet]
  constructor
  · rintro ⟨hm, howner⟩
    rcases howner with hshallow | habove
    · exact Or.inl ⟨hm, hshallow⟩
    · exact Or.inr ⟨hm, habove⟩
  · rintro (⟨hm, hshallow⟩ | ⟨hm, habove⟩)
    · exact ⟨hm, Or.inl hshallow⟩
    · exact ⟨hm, Or.inr habove⟩

/-- At an ordered owner window the shallow and above-cutoff residual pieces are
disjoint. -/
theorem squareWheelSurvivorShallow_disjoint_above
    (R K U : ℕ) (hKU : K ≤ U) :
    Disjoint (squareWheelSurvivorShallowMatchedPairSet R K)
      (squareWheelSurvivorAboveCutoffMatchedPairSet R U) := by
  rw [Finset.disjoint_left]
  intro cq hs ha
  have hs' := (mem_squareWheelSurvivorShallowMatchedPairSet.mp hs).2
  have ha' := (mem_squareWheelSurvivorAboveCutoffMatchedPairSet.mp ha).2
  omega

/-- Signed mass of any finite survivor-pair population. -/
def squareWheelSurvivorPairSetMassReal (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ cq ∈ S, squareWheelSurvivorPairWeightReal cq

/-- Total endpoint survivor-pair mass. -/
def squareWheelSurvivorEndpointPairMassReal (R : ℕ) : ℝ :=
  squareWheelSurvivorPairSetMassReal (squareWheelSurvivorEndpointPairSet R)

/-- Matched endpoint survivor-pair mass. -/
def squareWheelSurvivorMatchedPairMassReal (R : ℕ) : ℝ :=
  squareWheelSurvivorPairSetMassReal
    (squareWheelSurvivorEndpointMatchedPairSet R)

/-- Positive-orientation endpoint survivor-pair mass. -/
def squareWheelSurvivorPositivePairMassReal (R : ℕ) : ℝ :=
  squareWheelSurvivorPairSetMassReal
    (squareWheelSurvivorEndpointPositivePairSet R)

/-- Processed-compatible deep survivor-pair mass. -/
def squareWheelSurvivorProcessedDeepPairMassReal
    (R K U : ℕ) : ℝ :=
  squareWheelSurvivorPairSetMassReal
    (squareWheelSurvivorProcessedDeepPairSet R K U)

/-- Matched owner-window residual mass. -/
def squareWheelSurvivorOwnerResidualPairMassReal
    (R K U : ℕ) : ℝ :=
  squareWheelSurvivorPairSetMassReal
    (squareWheelSurvivorOwnerResidualPairSet R K U)

/-- Shallow matched survivor residual mass. -/
def squareWheelSurvivorShallowMatchedPairMassReal
    (R K : ℕ) : ℝ :=
  squareWheelSurvivorPairSetMassReal
    (squareWheelSurvivorShallowMatchedPairSet R K)

/-- Above-cutoff matched survivor residual mass. -/
def squareWheelSurvivorAboveCutoffMatchedPairMassReal
    (R U : ℕ) : ℝ :=
  squareWheelSurvivorPairSetMassReal
    (squareWheelSurvivorAboveCutoffMatchedPairSet R U)

/-- Endpoint survivor mass is exactly matched plus positive-orientation mass. -/
theorem squareWheelSurvivorEndpointPairMassReal_eq_matched_add_positive
    (R : ℕ) :
    squareWheelSurvivorEndpointPairMassReal R =
      squareWheelSurvivorMatchedPairMassReal R +
        squareWheelSurvivorPositivePairMassReal R := by
  unfold squareWheelSurvivorEndpointPairMassReal
    squareWheelSurvivorMatchedPairMassReal
    squareWheelSurvivorPositivePairMassReal
    squareWheelSurvivorPairSetMassReal
  rw [squareWheelSurvivorEndpointPairSet_eq_matched_union_positive]
  rw [Finset.sum_union
    (squareWheelSurvivorEndpointMatched_disjoint_positive R)]

/-- Matched mass is exactly processed-compatible deep mass plus the owner
residual mass. -/
theorem squareWheelSurvivorMatchedPairMassReal_eq_deep_add_ownerResidual
    (R K U : ℕ) :
    squareWheelSurvivorMatchedPairMassReal R =
      squareWheelSurvivorProcessedDeepPairMassReal R K U +
        squareWheelSurvivorOwnerResidualPairMassReal R K U := by
  unfold squareWheelSurvivorMatchedPairMassReal
    squareWheelSurvivorProcessedDeepPairMassReal
    squareWheelSurvivorOwnerResidualPairMassReal
    squareWheelSurvivorPairSetMassReal
  rw [squareWheelSurvivorEndpointMatchedPairSet_eq_deep_union_ownerResidual]
  rw [Finset.sum_union
    (squareWheelSurvivorProcessedDeep_disjoint_ownerResidual R K U)]

/-- **Degree-of-freedom identity.**  Once the total survivor mass, the processed
compatible deep mass, and the owner residual mass are known, the positive
orientation is forced. -/
theorem squareWheelSurvivorPositivePairMassReal_eq_residual
    (R K U : ℕ) :
    squareWheelSurvivorPositivePairMassReal R =
      squareWheelSurvivorEndpointPairMassReal R -
        squareWheelSurvivorProcessedDeepPairMassReal R K U -
          squareWheelSurvivorOwnerResidualPairMassReal R K U := by
  rw [squareWheelSurvivorEndpointPairMassReal_eq_matched_add_positive,
    squareWheelSurvivorMatchedPairMassReal_eq_deep_add_ownerResidual]
  ring

/-- At an ordered owner window the owner residual mass is exactly shallow plus
above-cutoff mass. -/
theorem squareWheelSurvivorOwnerResidualPairMassReal_eq_shallow_add_above
    (R K U : ℕ) (hKU : K ≤ U) :
    squareWheelSurvivorOwnerResidualPairMassReal R K U =
      squareWheelSurvivorShallowMatchedPairMassReal R K +
        squareWheelSurvivorAboveCutoffMatchedPairMassReal R U := by
  unfold squareWheelSurvivorOwnerResidualPairMassReal
    squareWheelSurvivorShallowMatchedPairMassReal
    squareWheelSurvivorAboveCutoffMatchedPairMassReal
    squareWheelSurvivorPairSetMassReal
  rw [squareWheelSurvivorOwnerResidualPairSet_eq_shallow_union_above]
  rw [Finset.sum_union
    (squareWheelSurvivorShallow_disjoint_above R K U hKU)]

/-- Four-sector form of the degree-of-freedom identity.  The positive sector is
not an additional independent mass once the other three sectors and the total
are fixed. -/
theorem squareWheelSurvivorPositivePairMassReal_eq_fourSectorResidual
    (R K U : ℕ) (hKU : K ≤ U) :
    squareWheelSurvivorPositivePairMassReal R =
      squareWheelSurvivorEndpointPairMassReal R -
        squareWheelSurvivorProcessedDeepPairMassReal R K U -
          squareWheelSurvivorShallowMatchedPairMassReal R K -
            squareWheelSurvivorAboveCutoffMatchedPairMassReal R U := by
  rw [squareWheelSurvivorPositivePairMassReal_eq_residual,
    squareWheelSurvivorOwnerResidualPairMassReal_eq_shallow_add_above R K U hKU]
  ring

/-! ## Canonical-cutoff rigidity of the above-owner residual -/

/-- At the canonical low-prime cutoff, an above-cutoff matched survivor cannot
be born-oriented.  It is necessarily post-root, and its cofactor belongs to the
existing near-root high-complement set. -/
theorem squareWheelSurvivorAboveCutoffMatchedPair_postRoot_highComplement
    {R c q : ℕ} (hR : 16 ≤ R)
    (hcq : (c, q) ∈ squareWheelSurvivorAboveCutoffMatchedPairSet R
      (squareRootBornPostTailLowPrimeCutoff R)) :
    R < q ∧ c ∈ squareRootBornPostTailHighComplementCofactors R := by
  have hmem := mem_squareWheelSurvivorAboveCutoffMatchedPairSet.mp hcq
  have hmatched := hmem.1
  have howner := hmem.2
  have hbase := (mem_squareWheelSurvivorEndpointMatchedPairSet.mp hmatched).1
  have horient := (mem_squareWheelSurvivorEndpointMatchedPairSet.mp hmatched).2
  have hdata := squareWheelSurvivorEndpointPair_sourceData hbase
  have hprod := squareWheelSurvivorEndpointPair_product_le (by omega) hbase
  have hrough := canonicalLargestPrimeFactor_lt_of_sourceData hdata
  rcases hdata with ⟨hqPrime, hc1, _hsq, _hcop, _hdom⟩
  rcases horient with hqcBorn | hRq
  · have hqR : q ≤ R :=
      squareWheelSurvivorEndpointPair_prime_le_root_of_le_cofactor
        (by omega) hbase hqcBorn
    have hqBorn : q ∈ squareRootBornPartnerSet R c := by
      unfold squareRootBornPartnerSet
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hqPrime.two_le, hqR⟩,
          hqPrime, hrough, hqcBorn, hprod⟩
    have hpos : 0 < squareRootBornPartnerCount R c := by
      unfold squareRootBornPartnerCount
      exact Finset.card_pos.mpr ⟨q, hqBorn⟩
    have hzero :=
      squareRootBornPartnerCount_eq_zero_of_lowPrimeCutoff_lt_lpf hR howner
    rw [hzero] at hpos
    omega
  · have hcR : c ≤ R - 1 := by
      by_contra hnot
      have hRc : R ≤ c := by omega
      have hRq1 : R + 1 ≤ q := by omega
      have hmul : R * (R + 1) ≤ c * q := Nat.mul_le_mul hRc hRq1
      have hXlt : squareRootEndpoint R < R * (R + 1) := by
        have hsub : squareRootEndpoint R < R ^ 2 := by
          unfold squareRootEndpoint
          exact Nat.sub_lt (by positivity) (by norm_num)
        have hsqLt : R ^ 2 < R * (R + 1) := by
          nlinarith
        exact hsub.trans hsqLt
      have hle : R * (R + 1) ≤ squareRootEndpoint R :=
        hmul.trans hprod
      exact (not_lt_of_ge hle) hXlt
    refine ⟨hRq, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hc1, hcR⟩, howner⟩

/-- Every canonical-cutoff above-owner survivor pair has source Möbius weight
`+1`: both its near-root cofactor and its post-root distinguished coordinate
are prime. -/
theorem squareWheelSurvivorAboveCutoffMatchedPair_weight_eq_one
    {R c q : ℕ} (hR : 16 ≤ R)
    (hcq : (c, q) ∈ squareWheelSurvivorAboveCutoffMatchedPairSet R
      (squareRootBornPostTailLowPrimeCutoff R)) :
    squareWheelSurvivorPairWeightReal (c, q) = 1 := by
  have hclass :=
    squareWheelSurvivorAboveCutoffMatchedPair_postRoot_highComplement hR hcq
  have hcPrime := (squareRootBornPostTailHighComplement_prime hR hclass.2).1
  have hmatched :=
    (mem_squareWheelSurvivorAboveCutoffMatchedPairSet.mp hcq).1
  have hbase := (mem_squareWheelSurvivorEndpointMatchedPairSet.mp hmatched).1
  have hdata := squareWheelSurvivorEndpointPair_sourceData hbase
  rcases hdata with ⟨hqPrime, _hc1, _hsq, hcop, _hdom⟩
  have hmul :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop.symm
  unfold squareWheelSurvivorPairWeightReal
  rw [hmul, ArithmeticFunction.moebius_apply_prime hcPrime,
    ArithmeticFunction.moebius_apply_prime hqPrime]
  norm_num

/-- A simple rectangle containing every canonical-cutoff above-owner survivor:
near-root cofactors times the first `floor(sqrt R)` integer seats above `R`. -/
def squareWheelSurvivorAboveCutoffBoundingBox (R : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootBornPostTailHighComplementCofactors R).product
    (Finset.Ioc R (R + Nat.sqrt R))

/-- Every canonical-cutoff above-owner survivor lies in the elementary
`sqrt R × sqrt R` near-root rectangle. -/
theorem squareWheelSurvivorAboveCutoffMatchedPairSet_subset_boundingBox
    {R : ℕ} (hR : 16 ≤ R) :
    squareWheelSurvivorAboveCutoffMatchedPairSet R
        (squareRootBornPostTailLowPrimeCutoff R) ⊆
      squareWheelSurvivorAboveCutoffBoundingBox R := by
  intro cq hcq
  rcases cq with ⟨c, q⟩
  have hclass :=
    squareWheelSurvivorAboveCutoffMatchedPair_postRoot_highComplement hR hcq
  have hmatched :=
    (mem_squareWheelSurvivorAboveCutoffMatchedPairSet.mp hcq).1
  have hbase := (mem_squareWheelSurvivorEndpointMatchedPairSet.mp hmatched).1
  have hprod := squareWheelSurvivorEndpointPair_product_le (by omega) hbase
  have hcRigid :=
    squareRootBornPostTailHighComplement_prime hR hclass.2
  have hcpos : 0 < c := hcRigid.1.pos
  have hqDiv : q ≤ squareRootEndpoint R / c := by
    apply (Nat.le_div_iff_mul_le hcpos).2
    simpa [Nat.mul_comm] using hprod
  have hdiv :=
    squareRootBornPostTail_reciprocalCutoff_le_root_add_sqrt hR hcRigid.2.1
  unfold squareWheelSurvivorAboveCutoffBoundingBox
  exact Finset.mem_product.mpr
    ⟨hclass.2, Finset.mem_Ioc.mpr ⟨hclass.1, hqDiv.trans hdiv⟩⟩

/-- The canonical-cutoff above-owner survivor population has at most `R` atoms. -/
theorem squareWheelSurvivorAboveCutoffMatchedPairSet_card_le_root
    {R : ℕ} (hR : 16 ≤ R) :
    (squareWheelSurvivorAboveCutoffMatchedPairSet R
      (squareRootBornPostTailLowPrimeCutoff R)).card ≤ R := by
  have hsub := Finset.card_le_card
    (squareWheelSurvivorAboveCutoffMatchedPairSet_subset_boundingBox hR)
  have hcof := squareRootBornPostTailHighComplementCofactors_card_le_sqrt hR
  have hIoc : (Finset.Ioc R (R + Nat.sqrt R)).card = Nat.sqrt R := by
    rw [Nat.card_Ioc]
    omega
  have hsub' :
      (squareWheelSurvivorAboveCutoffMatchedPairSet R
        (squareRootBornPostTailLowPrimeCutoff R)).card ≤
        (squareRootBornPostTailHighComplementCofactors R).card * Nat.sqrt R := by
    simpa [squareWheelSurvivorAboveCutoffBoundingBox, hIoc] using hsub
  have hrect :
      (squareRootBornPostTailHighComplementCofactors R).card * Nat.sqrt R ≤
        Nat.sqrt R * Nat.sqrt R :=
    Nat.mul_le_mul_right (Nat.sqrt R) hcof
  have hsqrt : Nat.sqrt R * Nat.sqrt R ≤ R := by
    simpa [pow_two] using Nat.sqrt_le' R
  exact hsub'.trans (hrect.trans hsqrt)

/-- The above-cutoff matched survivor mass is exactly its cardinality. -/
theorem squareWheelSurvivorAboveCutoffMatchedPairMassReal_eq_card
    {R : ℕ} (hR : 16 ≤ R) :
    squareWheelSurvivorAboveCutoffMatchedPairMassReal R
        (squareRootBornPostTailLowPrimeCutoff R) =
      ((squareWheelSurvivorAboveCutoffMatchedPairSet R
        (squareRootBornPostTailLowPrimeCutoff R)).card : ℝ) := by
  unfold squareWheelSurvivorAboveCutoffMatchedPairMassReal
    squareWheelSurvivorPairSetMassReal
  calc
    (∑ cq ∈ squareWheelSurvivorAboveCutoffMatchedPairSet R
        (squareRootBornPostTailLowPrimeCutoff R),
        squareWheelSurvivorPairWeightReal cq) =
      ∑ _cq ∈ squareWheelSurvivorAboveCutoffMatchedPairSet R
        (squareRootBornPostTailLowPrimeCutoff R), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro cq hcq
          rcases cq with ⟨c, q⟩
          exact squareWheelSurvivorAboveCutoffMatchedPair_weight_eq_one hR hcq
    _ = ((squareWheelSurvivorAboveCutoffMatchedPairSet R
        (squareRootBornPostTailLowPrimeCutoff R)).card : ℝ) := by simp

/-- **Above-owner residual discharged.**  At the canonical cutoff its signed
mass already satisfies the elementary root-scale bound with constant one. -/
theorem abs_squareWheelSurvivorAboveCutoffMatchedPairMassReal_le_root
    {R : ℕ} (hR : 16 ≤ R) :
    |squareWheelSurvivorAboveCutoffMatchedPairMassReal R
        (squareRootBornPostTailLowPrimeCutoff R)| ≤ (R : ℝ) := by
  rw [squareWheelSurvivorAboveCutoffMatchedPairMassReal_eq_card hR]
  have hcard := squareWheelSurvivorAboveCutoffMatchedPairSet_card_le_root hR
  have hcast :
      ((squareWheelSurvivorAboveCutoffMatchedPairSet R
        (squareRootBornPostTailLowPrimeCutoff R)).card : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hcard
  have hnonneg :
      0 ≤ ((squareWheelSurvivorAboveCutoffMatchedPairSet R
        (squareRootBornPostTailLowPrimeCutoff R)).card : ℝ) := by positivity
  rw [abs_of_nonneg hnonneg]
  exact hcast

end RHLean.Proof
