import Mathlib
import RHLean.Analysis.SquareRootPostCrossingRenewal
import RHLean.Proof.SquareRootLowPrimeShallowProcessedCreationEquiv
import RHLean.Proof.SquareWheelSurvivorOwnerResidual

/-!
# Shallow survivor bridge and bounded crossing core

The owner-residual decomposition leaves one independent shallow sector

`P+(c) <= K`.

It has two geometrically different parts.

* If `K < c`, the existing deep response-seat/partner equivalence still applies:
  "deep" in that theorem refers to the numerical cofactor inequality `K < c`,
  not to the owner `P+(c)`.  These survivors therefore map canonically into the
  shallow processed-seat carrier and then, by the already-compiled shallow
  processed/creation equivalence, into the literal creation carrier.

* If `c <= K`, an atomwise map to the current high-response seats would be the
  wrong object: those seats retain only the unfilled part of reciprocal layer
  `K` and the deeper prefix, while a survivor remembers its original post-root
  prime.  On this bounded core the correct bridge is therefore a signed mass
  identity.  The full post-root cofactor mass differs from the shallow high
  creation mass by exactly the partial crossing packet `V(R,K,j)`.

Thus the only failure of literal seatwise transport in the shallow owner sector
is precisely the already-existing crossing residual.  No norm or estimate is
used in this file.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-! ## Split the shallow owner residual at the numerical cofactor cutoff -/

/-- Shallow-owner survivors whose numerical cofactor lies beyond `K`. -/
noncomputable def squareWheelSurvivorShallowLargePairSet
    (R K : ℕ) : Finset (ℕ × ℕ) :=
  (squareWheelSurvivorShallowMatchedPairSet R K).filter fun cq =>
    K < cq.1

/-- The bounded shallow crossing core `c <= K`. -/
noncomputable def squareWheelSurvivorShallowCorePairSet
    (R K : ℕ) : Finset (ℕ × ℕ) :=
  (squareWheelSurvivorShallowMatchedPairSet R K).filter fun cq =>
    cq.1 ≤ K

@[simp] theorem mem_squareWheelSurvivorShallowLargePairSet
    {R K : ℕ} {cq : ℕ × ℕ} :
    cq ∈ squareWheelSurvivorShallowLargePairSet R K ↔
      cq ∈ squareWheelSurvivorShallowMatchedPairSet R K ∧ K < cq.1 := by
  simp [squareWheelSurvivorShallowLargePairSet]

@[simp] theorem mem_squareWheelSurvivorShallowCorePairSet
    {R K : ℕ} {cq : ℕ × ℕ} :
    cq ∈ squareWheelSurvivorShallowCorePairSet R K ↔
      cq ∈ squareWheelSurvivorShallowMatchedPairSet R K ∧ cq.1 ≤ K := by
  simp [squareWheelSurvivorShallowCorePairSet]

/-- Exact shallow-sector split into literal-seat and bounded-core pieces. -/
theorem squareWheelSurvivorShallowMatchedPairSet_eq_large_union_core
    (R K : ℕ) :
    squareWheelSurvivorShallowMatchedPairSet R K =
      squareWheelSurvivorShallowLargePairSet R K ∪
        squareWheelSurvivorShallowCorePairSet R K := by
  ext cq
  simp only [Finset.mem_union, mem_squareWheelSurvivorShallowLargePairSet,
    mem_squareWheelSurvivorShallowCorePairSet]
  constructor
  · intro h
    by_cases hc : cq.1 ≤ K
    · exact Or.inr ⟨h, hc⟩
    · exact Or.inl ⟨h, by omega⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact h
    · exact h

/-- The two shallow pieces are disjoint. -/
theorem squareWheelSurvivorShallowLarge_disjoint_core
    (R K : ℕ) :
    Disjoint (squareWheelSurvivorShallowLargePairSet R K)
      (squareWheelSurvivorShallowCorePairSet R K) := by
  rw [Finset.disjoint_left]
  intro cq hl hc
  have hl' := (mem_squareWheelSurvivorShallowLargePairSet.mp hl).2
  have hc' := (mem_squareWheelSurvivorShallowCorePairSet.mp hc).2
  omega

/-! ## Literal seat map on the `K < c` shallow-owner sector -/

/-- Arithmetic data of one shallow-large survivor cofactor. -/
theorem squareWheelSurvivorShallowLargePair_cofactor_data
    {R K c q : ℕ}
    (hcq : (c, q) ∈ squareWheelSurvivorShallowLargePairSet R K) :
    0 < c ∧ K < c ∧ canonicalLargestPrimeFactor c ≤ K ∧ μ c ≠ 0 := by
  have hshallow := (mem_squareWheelSurvivorShallowLargePairSet.mp hcq).1
  have hKc := (mem_squareWheelSurvivorShallowLargePairSet.mp hcq).2
  have hmatched := (mem_squareWheelSurvivorShallowMatchedPairSet.mp hshallow).1
  have howner := (mem_squareWheelSurvivorShallowMatchedPairSet.mp hshallow).2
  have hbase := (mem_squareWheelSurvivorEndpointMatchedPairSet.mp hmatched).1
  have hdata := squareWheelSurvivorEndpointPair_sourceData hbase
  rcases hdata with ⟨_hq, hc1, hsq, _hcop, _hdom⟩
  have hmu : μ c ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
  exact ⟨by omega, hKc, howner, hmu⟩

/-- A shallow-large survivor cofactor belongs to the processed signed carrier
at every cutoff `U >= K`. -/
theorem squareWheelSurvivorShallowLargePair_cofactor_mem_processed
    {R K U c q : ℕ} (hR : 1 ≤ R) (hKU : K ≤ U)
    (hcq : (c, q) ∈ squareWheelSurvivorShallowLargePairSet R K) :
    c ∈ squareRootLowPrimeProcessedSignedCofactors R U := by
  have hshallow := (mem_squareWheelSurvivorShallowLargePairSet.mp hcq).1
  have hmatched := (mem_squareWheelSurvivorShallowMatchedPairSet.mp hshallow).1
  have hbase := (mem_squareWheelSurvivorEndpointMatchedPairSet.mp hmatched).1
  have hdata := squareWheelSurvivorEndpointPair_sourceData hbase
  have hprod := squareWheelSurvivorEndpointPair_product_le hR hbase
  have hcof := squareWheelSurvivorShallowLargePair_cofactor_data hcq
  rcases hdata with ⟨hqPrime, hc1, _hsq, _hcop, _hdom⟩
  have hcLeProd : c ≤ c * q := by
    calc
      c = c * 1 := by simp
      _ ≤ c * q := Nat.mul_le_mul_left c hqPrime.one_le
  unfold squareRootLowPrimeProcessedSignedCofactors
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hc1, hcLeProd.trans hprod⟩,
      hcof.2.2.1.trans hKU, hcof.2.2.2⟩

/-- Canonical response-seat index of the literal prime partner on a
shallow-owner cofactor with `K < c`. -/
noncomputable def squareWheelSurvivorShallowLargeSeatIndex
    (R K j : ℕ) (hR : 1 ≤ R)
    (cq : ↥(squareWheelSurvivorShallowLargePairSet R K)) :
    ↥(squareRootLowPrimeResponseSeatIndexSet R K j cq.1.1) := by
  have hcData := squareWheelSurvivorShallowLargePair_cofactor_data cq.2
  have hshallow := (mem_squareWheelSurvivorShallowLargePairSet.mp cq.2).1
  have hmatched := (mem_squareWheelSurvivorShallowMatchedPairSet.mp hshallow).1
  have hqDeep :=
    squareWheelSurvivorEndpointMatchedPair_mem_deepPartnerSet hR hmatched
  let qDeep : ↥(squareRootLowPrimeDeepPartnerSet R cq.1.1) :=
    ⟨cq.1.2, hqDeep⟩
  exact (squareRootLowPrimeResponseSeatPartnerEquiv
    R K j cq.1.1 hR hcData.1 hcData.2.1).symm qDeep

/-- **Literal shallow-large survivor -> shallow processed-seat map.** -/
noncomputable def squareWheelSurvivorShallowLargeToProcessedSeat
    (R K j U : ℕ) (hR : 1 ≤ R) (hKU : K ≤ U)
    (cq : ↥(squareWheelSurvivorShallowLargePairSet R K)) :
    ↥(squareRootLowPrimeProcessedShallowSeatAtoms R K j U) := by
  let s := squareWheelSurvivorShallowLargeSeatIndex R K j hR cq
  have hcof := squareWheelSurvivorShallowLargePair_cofactor_data cq.2
  refine ⟨(cq.1.1, (s : ℕ)), ?_⟩
  apply mem_squareRootLowPrimeProcessedShallowSeatAtoms.mpr
  refine ⟨mem_squareRootLowPrimeProcessedSeatAtoms.mpr
    ⟨squareWheelSurvivorShallowLargePair_cofactor_mem_processed
      hR hKU cq.2, ?_⟩, hcof.2.2.1⟩
  exact mem_squareRootLowPrimeResponseSeatIndexSet.mp s.2

/-- Composing with the existing shallow processed/creation equivalence gives a
literal creation state without any new finite-cardinality choice. -/
noncomputable def squareWheelSurvivorShallowLargeToCreation
    (R K j U : ℕ) (hR : 1 ≤ R) (hKU : K ≤ U)
    (cq : ↥(squareWheelSurvivorShallowLargePairSet R K)) :
    ↥((squareRootLowPrimeCreationCarrierExact R K j).erase none) :=
  squareRootLowPrimeProcessedShallowSeatCreationEquiv R K j U hR hKU
    (squareWheelSurvivorShallowLargeToProcessedSeat
      R K j U hR hKU cq)

/-- Reading the response seat back recovers the original survivor prime. -/
theorem squareWheelSurvivorShallowLarge_partner_eq
    (R K j : ℕ) (hR : 1 ≤ R)
    (cq : ↥(squareWheelSurvivorShallowLargePairSet R K)) :
    (squareRootLowPrimeResponseSeatPartnerEquiv
      R K j cq.1.1 hR
        (squareWheelSurvivorShallowLargePair_cofactor_data cq.2).1
        (squareWheelSurvivorShallowLargePair_cofactor_data cq.2).2.1
      (squareWheelSurvivorShallowLargeSeatIndex R K j hR cq) : ℕ) =
        cq.1.2 := by
  unfold squareWheelSurvivorShallowLargeSeatIndex
  simp

private theorem squareWheel_moebius_mul_eq_neg_of_sourceData
    {c q : ℕ} (hdata : CanonicalGapAncestryBridge.CanonicalSourceData q c) :
    μ (c * q) = -μ c := by
  rcases hdata with ⟨hq, _hc1, _hsq, hcop, _hdom⟩
  have hmul :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop.symm
  rw [hmul, ArithmeticFunction.moebius_apply_prime hq]
  ring

/-- The shallow-large map preserves the native signed weight pointwise. -/
theorem squareWheelSurvivorShallowLargeToCreation_weight_eq
    (R K j U : ℕ) (hR : 1 ≤ R) (hKU : K ≤ U)
    (cq : ↥(squareWheelSurvivorShallowLargePairSet R K)) :
    squareRootLowPrimeCreationWeightReal
        (squareWheelSurvivorShallowLargeToCreation
          R K j U hR hKU cq : SquareRootLowPrimeCreationState) =
      squareWheelSurvivorPairWeightReal cq.1 := by
  let z := squareWheelSurvivorShallowLargeToProcessedSeat
    R K j U hR hKU cq
  have hcreation :=
    squareRootLowPrimeProcessedShallowSeatCreationEquiv_weight_eq
      hR hKU z
  have hshallow := (mem_squareWheelSurvivorShallowLargePairSet.mp cq.2).1
  have hmatched := (mem_squareWheelSurvivorShallowMatchedPairSet.mp hshallow).1
  have hbase := (mem_squareWheelSurvivorEndpointMatchedPairSet.mp hmatched).1
  have hdata := squareWheelSurvivorEndpointPair_sourceData hbase
  have hsign := squareWheel_moebius_mul_eq_neg_of_sourceData hdata
  rw [show squareWheelSurvivorShallowLargeToCreation R K j U hR hKU cq =
      squareRootLowPrimeProcessedShallowSeatCreationEquiv
        R K j U hR hKU z by rfl]
  rw [hcreation]
  change (((-μ cq.1.1 : ℤ) : ℝ)) =
    (((μ (cq.1.1 * cq.1.2) : ℤ) : ℝ))
  rw [hsign]

/-! ## Exact mass bridge on the bounded crossing core -/

/-- Full post-root signed cofactor mass through the bounded core `c <= K`. -/
def squareWheelShallowCorePostRootMassComplex (R K : ℕ) : ℂ :=
  -∑ c ∈ Finset.Icc 1 K,
    canonicalMoebiusWeight c * squareRootPostRootPrimePrefix R c

/-- The same bounded cofactors evaluated in the current shallow high-response
creation channel. -/
def squareWheelShallowCoreHighCreationMassComplex
    (R K j : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 K,
    -canonicalMoebiusWeight c *
      ((squareRootBornPostTailHighResponse R K j c : ℕ) : ℂ)

/-- On every bounded core cofactor `c <= K`, the current high response is the
common remaining post-root prefix `P_R(K) - j`. -/
theorem squareRootBornPostTailHighResponse_cast_eq_postRootPrefix_sub_j
    {R K j c : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) (hcK : c ≤ K) :
    ((squareRootBornPostTailHighResponse R K j c : ℕ) : ℂ) =
      squareRootPostRootPrimePrefix R K - (j : ℂ) := by
  have hlayer :
      ((squareRootReciprocalPrimeLayerCard R K : ℕ) : ℂ) =
        squareRootPostRootPrimePrefix R K -
          squareRootPostRootPrimePrefix R (K + 1) := by
    rw [← squareRootReciprocalPrimeCount_eq_layerCard]
    exact squareRoot_reciprocalPrimeCount_eq_postRootPrefix_diff hR hK hKR
  rw [squareRootBornPostTailHighResponse_cast hj, if_pos hcK, hlayer]
  ring

/-- The bounded high-creation mass is one common remaining prefix multiplied by
`-M(K)`. -/
theorem squareWheelShallowCoreHighCreationMassComplex_eq
    {R K j : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareWheelShallowCoreHighCreationMassComplex R K j =
      -mertensSummatory K *
        (squareRootPostRootPrimePrefix R K - (j : ℂ)) := by
  have hmu :
      (∑ c ∈ Finset.Icc 1 K, canonicalMoebiusWeight c) =
        mertensSummatory K := by
    rw [← cofactorMobiusPrefixMass_eq_mertensSummatory K]
    rfl
  unfold squareWheelShallowCoreHighCreationMassComplex
  calc
    (∑ c ∈ Finset.Icc 1 K,
        -canonicalMoebiusWeight c *
          ((squareRootBornPostTailHighResponse R K j c : ℕ) : ℂ)) =
      ∑ c ∈ Finset.Icc 1 K,
        -canonicalMoebiusWeight c *
          (squareRootPostRootPrimePrefix R K - (j : ℂ)) := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [squareRootBornPostTailHighResponse_cast_eq_postRootPrefix_sub_j
              hR hK hKR hj (Finset.mem_Icc.mp hc).2]
    _ = -(∑ c ∈ Finset.Icc 1 K, canonicalMoebiusWeight c) *
        (squareRootPostRootPrimePrefix R K - (j : ℂ)) := by
          simp_rw [neg_mul]
          rw [Finset.sum_neg_distrib, Finset.sum_mul]
    _ = -mertensSummatory K *
        (squareRootPostRootPrimePrefix R K - (j : ℂ)) := by rw [hmu]

/-- **Bounded-core bridge.**  The full post-root survivor-side cofactor mass is
exactly the current shallow high-creation mass plus the partial crossing packet.
The crossing residual is therefore the sole signed degree of freedom lost when
old post-root primes are compressed into the current shallow high seats. -/
theorem squareWheelShallowCorePostRootMassComplex_eq_partial_add_highCreation
    {R K j : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareWheelShallowCorePostRootMassComplex R K =
      ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) +
        squareWheelShallowCoreHighCreationMassComplex R K j := by
  have hpartial := squareRootCrossingLayerPartialPacketInt_cast_complex R K j
  have hstepInt := squareRootTruncatedUpperMiddlePacketInt_succ R (K - 1)
  rw [Nat.sub_add_cancel hK] at hstepInt
  have hstepC := congrArg (fun z : ℤ => (z : ℂ)) hstepInt
  push_cast at hstepC
  rw [squareRootTruncatedUpperMiddlePacketInt_cast_complex,
    squareRootTruncatedUpperMiddlePacketInt_cast_complex,
    squareRootMertensInt_cast_complex] at hstepC
  have hlayer :
      ((squareRootReciprocalPrimeLayerCard R K : ℕ) : ℂ) =
        squareRootPostRootPrimePrefix R K -
          squareRootPostRootPrimePrefix R (K + 1) := by
    rw [← squareRootReciprocalPrimeCount_eq_layerCard]
    exact squareRoot_reciprocalPrimeCount_eq_postRootPrefix_diff hR hK hKR
  have habel := squareRootTruncatedUpperMiddlePacket_eq_abel R K hR hKR
  have hhigh := squareWheelShallowCoreHighCreationMassComplex_eq
    hR hK hKR hj
  have hprev :
      squareRootTruncatedUpperMiddlePacket R (K - 1) =
        squareWheelShallowCorePostRootMassComplex R K +
          mertensSummatory K * squareRootPostRootPrimePrefix R K := by
    unfold squareWheelShallowCorePostRootMassComplex
    rw [habel] at hstepC
    rw [hlayer] at hstepC
    simp only [canonicalMoebiusWeight]
    linear_combination -hstepC
  rw [hhigh]
  rw [hprev] at hpartial
  rw [hpartial]
  ring

end RHLean.Proof