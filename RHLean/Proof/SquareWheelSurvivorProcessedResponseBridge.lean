import Mathlib
import RHLean.Analysis.SquareWheelSurvivorRun
import RHLean.Proof.SquareRootAncestryRoot
import RHLean.Proof.SquareRootLowPrimeProcessedSeatCarrier
import RHLean.Proof.SquareRootLowPrimeResponseSeatAtomEquiv
import RHLean.Proof.SquareRootLowPrimeSmoothTransportRecoupling
import RHLean.Proof.SurvivorZeroMode

/-!
# Square-wheel survivor / processed-response bridge

The square-wheel survivor coordinate and the low-prime processed-seat coordinate
are not definitionally the same carrier.

At the square endpoint `X_R = R^2 - 1`, a survivor atom is a canonical pair
`(c,q)` with native source weight `mu(c*q)`.  The processed low-prime carrier
instead stores a response unit as `(c,s)`, where `s` is an absolute seat index
and the native seat weight is `-mu(c)`.

This module records the exact arithmetic seam between those coordinates.

First, the endpoint survivor population is partitioned before any norm into

* the **matched orientation**: `q <= c` (born-smooth) or `R < q` (post-root);
* the complementary **positive orientation**: `c < q <= R`.

Every matched survivor partner belongs to the already-existing literal
`squareRootLowPrimeDeepPartnerSet R c`.  On the subpopulation whose cofactor
owner lies in the processed fresh-prime window `(K,U]`, the repository's
canonical response-seat/partner equivalence therefore gives a literal map

`(c,q) -> (c,s)`

into `squareRootLowPrimeProcessedSeatAtoms R K j U`.  The map preserves the
cofactor, recovers the original prime partner, and preserves the native signed
weight pointwise.

No cardinality choice, norm, estimate, PNT input, or RH-scale hypothesis is used.
The positive-orientation survivor population remains deliberately outside the
processed response carrier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Survivor `(c,q)` pairs at the square endpoint `R^2 - 1`. -/
noncomputable def squareWheelSurvivorEndpointPairSet (R : ℕ) : Finset (ℕ × ℕ) :=
  survivorZeroModePairSet 16 (R - 1)

/-- The part of the endpoint survivor population already oriented toward the
matched born/post-root response channel. -/
noncomputable def squareWheelSurvivorEndpointMatchedPairSet
    (R : ℕ) : Finset (ℕ × ℕ) :=
  (squareWheelSurvivorEndpointPairSet R).filter fun cq =>
    cq.2 ≤ cq.1 ∨ R < cq.2

/-- The complementary positive-smooth orientation inside the endpoint survivor
population. -/
noncomputable def squareWheelSurvivorEndpointPositivePairSet
    (R : ℕ) : Finset (ℕ × ℕ) :=
  (squareWheelSurvivorEndpointPairSet R).filter fun cq =>
    cq.1 < cq.2 ∧ cq.2 ≤ R

@[simp] theorem mem_squareWheelSurvivorEndpointMatchedPairSet
    {R : ℕ} {cq : ℕ × ℕ} :
    cq ∈ squareWheelSurvivorEndpointMatchedPairSet R ↔
      cq ∈ squareWheelSurvivorEndpointPairSet R ∧
        (cq.2 ≤ cq.1 ∨ R < cq.2) := by
  simp [squareWheelSurvivorEndpointMatchedPairSet]

@[simp] theorem mem_squareWheelSurvivorEndpointPositivePairSet
    {R : ℕ} {cq : ℕ × ℕ} :
    cq ∈ squareWheelSurvivorEndpointPositivePairSet R ↔
      cq ∈ squareWheelSurvivorEndpointPairSet R ∧
        cq.1 < cq.2 ∧ cq.2 ≤ R := by
  simp [squareWheelSurvivorEndpointPositivePairSet]

/-- **Exact orientation partition.**  The survivor endpoint carrier is the
union of the processed-compatible matched orientation and the complementary
positive orientation. -/
theorem squareWheelSurvivorEndpointPairSet_eq_matched_union_positive
    (R : ℕ) :
    squareWheelSurvivorEndpointPairSet R =
      squareWheelSurvivorEndpointMatchedPairSet R ∪
        squareWheelSurvivorEndpointPositivePairSet R := by
  ext cq
  simp only [Finset.mem_union,
    mem_squareWheelSurvivorEndpointMatchedPairSet,
    mem_squareWheelSurvivorEndpointPositivePairSet]
  constructor
  · intro h
    by_cases hqc : cq.2 ≤ cq.1
    · exact Or.inl ⟨h, Or.inl hqc⟩
    · have hcq : cq.1 < cq.2 := by omega
      by_cases hRq : R < cq.2
      · exact Or.inl ⟨h, Or.inr hRq⟩
      · exact Or.inr ⟨h, hcq, by omega⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact h
    · exact h

/-- The two orientation pieces are genuinely disjoint. -/
theorem squareWheelSurvivorEndpointMatched_disjoint_positive
    (R : ℕ) :
    Disjoint (squareWheelSurvivorEndpointMatchedPairSet R)
      (squareWheelSurvivorEndpointPositivePairSet R) := by
  rw [Finset.disjoint_left]
  intro cq hm hp
  have hm' := (mem_squareWheelSurvivorEndpointMatchedPairSet.mp hm).2
  have hp' := (mem_squareWheelSurvivorEndpointPositivePairSet.mp hp).2
  rcases hm' with hqc | hRq
  · omega
  · omega

/-- Arithmetic data carried by any endpoint survivor pair. -/
theorem squareWheelSurvivorEndpointPair_sourceData
    {R : ℕ} {cq : ℕ × ℕ}
    (hcq : cq ∈ squareWheelSurvivorEndpointPairSet R) :
    CanonicalSourceData cq.2 cq.1 := by
  unfold squareWheelSurvivorEndpointPairSet at hcq
  unfold survivorZeroModePairSet at hcq
  exact (Finset.mem_filter.mp hcq).2.1

/-- The product cutoff of an endpoint survivor is exactly `R^2 - 1`. -/
theorem squareWheelSurvivorEndpointPair_product_le
    {R : ℕ} (hR : 1 ≤ R) {cq : ℕ × ℕ}
    (hcq : cq ∈ squareWheelSurvivorEndpointPairSet R) :
    cq.1 * cq.2 ≤ squareRootEndpoint R := by
  unfold squareWheelSurvivorEndpointPairSet at hcq
  unfold survivorZeroModePairSet at hcq
  have hpair := (Finset.mem_filter.mp hcq).2
  simpa [squarePrefixEndpoint_pred_eq_squareRootEndpoint R hR] using hpair.2.1

/-- Canonical source data forces the displayed prime to lie above every prime
factor of its cofactor, hence above the cofactor's canonical largest prime. -/
theorem canonicalLargestPrimeFactor_lt_of_sourceData
    {c q : ℕ} (hdata : CanonicalSourceData q c) :
    canonicalLargestPrimeFactor c < q := by
  rcases hdata with ⟨hq, hc1, _hsq, _hcop, hdom⟩
  by_cases hc : c = 1
  · subst c
    simpa [canonicalLargestPrimeFactor] using hq.one_lt
  · have hcgt : 1 < c := by omega
    exact hdom (canonicalLargestPrimeFactor c)
      (canonicalLargestPrimeFactor_prime hcgt)
      (canonicalLargestPrimeFactor_dvd hcgt)

/-- A born-oriented endpoint survivor automatically has `q <= R`. -/
theorem squareWheelSurvivorEndpointPair_prime_le_root_of_le_cofactor
    {R c q : ℕ} (hR : 1 ≤ R)
    (hcq : (c, q) ∈ squareWheelSurvivorEndpointPairSet R)
    (hqc : q ≤ c) :
    q ≤ R := by
  by_contra hnot
  have hRq : R < q := by omega
  have hprod := squareWheelSurvivorEndpointPair_product_le hR hcq
  have hXlt : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hsq : 0 < R ^ 2 := by positivity
    omega
  have hqq : q * q ≤ c * q := Nat.mul_le_mul_right q hqc
  have hRqsq : R ^ 2 < q * q := by nlinarith
  exact (not_lt_of_ge hprod)
    (lt_of_lt_of_le (hXlt.trans hRqsq) hqq)

/-- **Matched survivors are literal processed-response partners.**

If the endpoint survivor is in either the born orientation `q <= c` or the
post-root orientation `R < q`, then `q` belongs to the repository's existing
`DeepPartnerSet(R,c)`. -/
theorem squareWheelSurvivorEndpointMatchedPair_mem_deepPartnerSet
    {R c q : ℕ} (hR : 1 ≤ R)
    (hcq : (c, q) ∈ squareWheelSurvivorEndpointMatchedPairSet R) :
    q ∈ squareRootLowPrimeDeepPartnerSet R c := by
  have hbase := (mem_squareWheelSurvivorEndpointMatchedPairSet.mp hcq).1
  have horient := (mem_squareWheelSurvivorEndpointMatchedPairSet.mp hcq).2
  have hdata := squareWheelSurvivorEndpointPair_sourceData hbase
  have hprod := squareWheelSurvivorEndpointPair_product_le hR hbase
  have hrough := canonicalLargestPrimeFactor_lt_of_sourceData hdata
  rcases hdata with ⟨hqPrime, hc1, _hsq, _hcop, _hdom⟩
  unfold squareRootLowPrimeDeepPartnerSet
  rcases horient with hqc | hRq
  · apply Finset.mem_union_left
    unfold squareRootBornPartnerSet
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hqPrime.two_le, ?_⟩, hqPrime, hrough, hqc, hprod⟩
    exact squareWheelSurvivorEndpointPair_prime_le_root_of_le_cofactor hR hbase hqc
  · apply Finset.mem_union_right
    unfold squareRootPostRootPrimePartnerSet
    apply Finset.mem_filter.mpr
    have hqProd : q ≤ c * q := by
      calc
        q = 1 * q := by simp
        _ ≤ c * q := Nat.mul_le_mul_right q hc1
    exact ⟨Finset.mem_Ioc.mpr ⟨hRq, hqProd.trans hprod⟩, hqPrime, hprod⟩

/-- Matched endpoint survivors whose cofactor owner lies in the exact processed
fresh-prime window `(K,U]`.  This is the subcarrier on which the deep
response-seat equivalence can be used without changing coordinates or capacity. -/
noncomputable def squareWheelSurvivorProcessedDeepPairSet
    (R K U : ℕ) : Finset (ℕ × ℕ) :=
  (squareWheelSurvivorEndpointMatchedPairSet R).filter fun cq =>
    K < canonicalLargestPrimeFactor cq.1 ∧
      canonicalLargestPrimeFactor cq.1 ≤ U

@[simp] theorem mem_squareWheelSurvivorProcessedDeepPairSet
    {R K U : ℕ} {cq : ℕ × ℕ} :
    cq ∈ squareWheelSurvivorProcessedDeepPairSet R K U ↔
      cq ∈ squareWheelSurvivorEndpointMatchedPairSet R ∧
        K < canonicalLargestPrimeFactor cq.1 ∧
          canonicalLargestPrimeFactor cq.1 ≤ U := by
  simp [squareWheelSurvivorProcessedDeepPairSet]

/-- The cofactor of a deep processed-compatible survivor is positive and lies
strictly above the packet depth. -/
theorem squareWheelSurvivorProcessedDeepPair_cofactor_data
    {R K U c q : ℕ} (hK : 1 ≤ K)
    (hcq : (c, q) ∈ squareWheelSurvivorProcessedDeepPairSet R K U) :
    0 < c ∧ K < c := by
  have hbase :=
    (mem_squareWheelSurvivorProcessedDeepPairSet.mp hcq).1
  have hdata :=
    squareWheelSurvivorEndpointPair_sourceData
      (mem_squareWheelSurvivorEndpointMatchedPairSet.mp hbase).1
  have howner :=
    (mem_squareWheelSurvivorProcessedDeepPairSet.mp hcq).2.1
  rcases hdata with ⟨_hq, hc1, _hsq, _hcop, _hdom⟩
  have hcne : c ≠ 1 := by
    intro h
    subst c
    simp [canonicalLargestPrimeFactor] at howner
    omega
  have hcgt : 1 < c := by omega
  have hlpfLe : canonicalLargestPrimeFactor c ≤ c :=
    Nat.le_of_dvd (by omega) (canonicalLargestPrimeFactor_dvd hcgt)
  exact ⟨by omega, howner.trans_le hlpfLe⟩

/-- A processed-compatible survivor cofactor is literally in the processed
signed-cofactor carrier at cutoff `U`. -/
theorem squareWheelSurvivorProcessedDeepPair_cofactor_mem_processed
    {R K U c q : ℕ} (hR : 1 ≤ R) (_hK : 1 ≤ K)
    (hcq : (c, q) ∈ squareWheelSurvivorProcessedDeepPairSet R K U) :
    c ∈ squareRootLowPrimeProcessedSignedCofactors R U := by
  have hmatched :=
    (mem_squareWheelSurvivorProcessedDeepPairSet.mp hcq).1
  have hbase :=
    (mem_squareWheelSurvivorEndpointMatchedPairSet.mp hmatched).1
  have hdata := squareWheelSurvivorEndpointPair_sourceData hbase
  have hprod := squareWheelSurvivorEndpointPair_product_le hR hbase
  have hownerLe :=
    (mem_squareWheelSurvivorProcessedDeepPairSet.mp hcq).2.2
  rcases hdata with ⟨hqPrime, hc1, hsq, _hcop, _hdom⟩
  have hcLeProd : c ≤ c * q := by
    calc
      c = c * 1 := by simp
      _ ≤ c * q := Nat.mul_le_mul_left c hqPrime.one_le
  have hcX : c ≤ squareRootEndpoint R := hcLeProd.trans hprod
  have hmu : μ c ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
  unfold squareRootLowPrimeProcessedSignedCofactors
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hc1, hcX⟩, hownerLe, hmu⟩

/-- The literal response-seat index corresponding to a processed-compatible
survivor prime partner.  This is the inverse of the already-compiled canonical
seat/partner equivalence, not a new enumeration. -/
noncomputable def squareWheelSurvivorProcessedSeatIndex
    (R K j U : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K)
    (cq : ↥(squareWheelSurvivorProcessedDeepPairSet R K U)) :
    ↥(squareRootLowPrimeResponseSeatIndexSet R K j cq.1.1) := by
  have hcData := squareWheelSurvivorProcessedDeepPair_cofactor_data hK cq.2
  have hqDeep :=
    squareWheelSurvivorEndpointMatchedPair_mem_deepPartnerSet hR
      (mem_squareWheelSurvivorProcessedDeepPairSet.mp cq.2).1
  let qDeep : ↥(squareRootLowPrimeDeepPartnerSet R cq.1.1) :=
    ⟨cq.1.2, hqDeep⟩
  exact (squareRootLowPrimeResponseSeatPartnerEquiv
    R K j cq.1.1 hR hcData.1 hcData.2).symm qDeep

/-- **Physical survivor -> processed-seat map.**  The cofactor is unchanged;
only the literal prime partner `q` is replaced by its canonical absolute seat
index `s`. -/
noncomputable def squareWheelSurvivorToProcessedSeat
    (R K j U : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K)
    (cq : ↥(squareWheelSurvivorProcessedDeepPairSet R K U)) :
    ↥(squareRootLowPrimeProcessedSeatAtoms R K j U) := by
  let s := squareWheelSurvivorProcessedSeatIndex R K j U hR hK cq
  refine ⟨(cq.1.1, (s : ℕ)), ?_⟩
  apply mem_squareRootLowPrimeProcessedSeatAtoms.mpr
  refine ⟨squareWheelSurvivorProcessedDeepPair_cofactor_mem_processed
      hR hK cq.2, ?_⟩
  exact mem_squareRootLowPrimeResponseSeatIndexSet.mp s.2

@[simp] theorem squareWheelSurvivorToProcessedSeat_fst
    (R K j U : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K)
    (cq : ↥(squareWheelSurvivorProcessedDeepPairSet R K U)) :
    (squareWheelSurvivorToProcessedSeat R K j U hR hK cq : ℕ × ℕ).1 =
      cq.1.1 := by
  rfl

/-- Reading the mapped seat back through the existing seat/partner equivalence
recovers the original survivor prime `q` exactly. -/
theorem squareWheelSurvivorToProcessedSeat_partner_eq
    (R K j U : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K)
    (cq : ↥(squareWheelSurvivorProcessedDeepPairSet R K U)) :
    (squareRootLowPrimeResponseSeatPartnerEquiv
      R K j cq.1.1 hR
        (squareWheelSurvivorProcessedDeepPair_cofactor_data hK cq.2).1
        (squareWheelSurvivorProcessedDeepPair_cofactor_data hK cq.2).2
      (squareWheelSurvivorProcessedSeatIndex R K j U hR hK cq) : ℕ) =
        cq.1.2 := by
  unfold squareWheelSurvivorProcessedSeatIndex
  simp

/-- Möbius source weight of one survivor pair, in the real scalar used by the
processed-seat API. -/
def squareWheelSurvivorPairWeightReal (cq : ℕ × ℕ) : ℝ :=
  ((μ (cq.1 * cq.2) : ℤ) : ℝ)

private theorem moebius_mul_eq_neg_of_sourceData
    {c q : ℕ} (hdata : CanonicalSourceData q c) :
    μ (c * q) = -μ c := by
  rcases hdata with ⟨hq, _hc1, _hsq, hcop, _hdom⟩
  have hmul :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop.symm
  rw [hmul, ArithmeticFunction.moebius_apply_prime hq]
  ring

/-- The physical survivor-to-seat map preserves the native signed weight
pointwise. -/
theorem squareWheelSurvivorToProcessedSeat_weight_eq
    (R K j U : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K)
    (cq : ↥(squareWheelSurvivorProcessedDeepPairSet R K U)) :
    squareRootLowPrimeProcessedSeatWeightReal
        (some (squareWheelSurvivorToProcessedSeat R K j U hR hK cq : ℕ × ℕ)) =
      squareWheelSurvivorPairWeightReal cq.1 := by
  have hmatched :=
    (mem_squareWheelSurvivorProcessedDeepPairSet.mp cq.2).1
  have hbase :=
    (mem_squareWheelSurvivorEndpointMatchedPairSet.mp hmatched).1
  have hdata := squareWheelSurvivorEndpointPair_sourceData hbase
  change (((-μ cq.1.1 : ℤ) : ℝ)) =
    (((μ (cq.1.1 * cq.1.2) : ℤ) : ℝ))
  rw [moebius_mul_eq_neg_of_sourceData hdata]

/-! ## Exact total-mass bridge -/

/-- **Exact survivor / processed-total degree-of-freedom bridge.**

The native survivor zero mode is the complete processed running imbalance plus
the other four endpoint coordinates.  This is the mass-level projection that
does not require the survivor-to-seat map above to be surjective. -/
theorem survivorZeroMode_eq_processedRunningImbalance_add_endpointResiduals
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    survivorZeroMode 16 (R - 1) =
      squareRootLowPrimeRunningImbalance R K j
        (squareRootBornPostTailLowPrimeCutoff R) +
      squareRootPositiveSmoothMass R +
      squareRootLowPrimeTerminalShallowBoundary R K j -
      canonicalLowPrefix 16 (R - 1) -
      lifetimeDeathMass 16 (R - 1) := by
  rw [squareRootLowPrimeRunningImbalance_at_cutoff_eq_squarePrefixMertens_sub_positiveSmooth_sub_boundary
      R K j hR hK hKR hj,
    squarePrefixMertens_eq_low_add_survivor_add_death]
  ring

/-- Literal processed-seat-carrier form of the same exact identity on real
parts.  The first term on the right is the signed mass of the actual
`SquareRootLowPrimeProcessedState` carrier. -/
theorem survivorZeroMode_re_eq_processedSeatCarrierMass_add_endpointResiduals
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    (survivorZeroMode 16 (R - 1)).re =
      (∑ x ∈ squareRootLowPrimeProcessedSeatCarrier R K j
          (squareRootBornPostTailLowPrimeCutoff R),
        squareRootLowPrimeProcessedSeatWeightReal x) +
      (squareRootPositiveSmoothMass R).re +
      (squareRootLowPrimeTerminalShallowBoundary R K j).re -
      (canonicalLowPrefix 16 (R - 1)).re -
      (lifetimeDeathMass 16 (R - 1)).re := by
  rw [squareRootLowPrimeProcessedSeatCarrier_mass_eq_runningImbalanceReal
      (R := R) (K := K) (j := j)
      (P := squareRootBornPostTailLowPrimeCutoff R) (by omega)]
  have h :=
    survivorZeroMode_eq_processedRunningImbalance_add_endpointResiduals
      R K j hR hK hKR hj
  have hre := congrArg Complex.re h
  simpa [squareRootLowPrimeRunningImbalanceReal] using hre

end RHLean.Proof
