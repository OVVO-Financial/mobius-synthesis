import Mathlib
import RHLean.Analysis.SquareRootPrimeCountGap
import RHLean.Proof.OrderedEulerCutProjection
import RHLean.Proof.VanishingTransitionRelevance

/-!
# Upper-half obstruction to a fixed first-jump-prime seat bound

The product-packing reduction in `VanishingTransitionRelevance` is exact, but
its proposed fixed-prime input is too strong.  This module isolates and then
aggregates the upper-half geometry responsible for the obstruction.

For a post-root prime `p` with `R / 2 < p`, the numerical packing factor is
`R / p = 1`.  Nevertheless, the same first-jump prime can remain live under
many later oriented owners `k`.  Every prime

`p < k <= (R^2 - 1) / p`

produces the actual oriented state `(1,k)` carrying the singleton low face
`{p}`.  Once the owner window is below `2p`, the entire canonical `p`-slice is
literally the singleton Boolean face `{p}` and therefore has signed mass `-1`.
Nontrivial cofactors vanish, so the complete fixed-`p` aggregate is exactly the
negative cardinality of that later-prime owner interval.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open SignedOwnershipInterval

attribute [local instance] Classical.propDecidable

/-- Later prime owners available to one upper-half first-jump prime. -/
def upperHalfFirstJumpOwnerSet (R p : ℕ) : Finset ℕ :=
  frozenPrimeUniverseHighPrimeSet p (squareRootEndpoint R / p)

@[simp] theorem mem_upperHalfFirstJumpOwnerSet
    {R p k : ℕ} :
    k ∈ upperHalfFirstJumpOwnerSet R p ↔
      k.Prime ∧ p < k ∧ k ≤ squareRootEndpoint R / p := by
  simp [upperHalfFirstJumpOwnerSet, mem_frozenPrimeUniverseHighPrimeSet]

/-- **The upper-half owner column is physically real.**

If `p` is a surviving first-jump prime above `R/2`, every later prime
`k <= (R^2-1)/p` gives an actual oriented state `(1,k)`.  The witness is the
singleton low face `{p}`.  This is an exact lifetime statement; there is no
prime-gap, PNT, iid, or norm estimate here. -/
theorem upperHalfFirstJumpOwner_state_mem
    {R p k : ℕ}
    (hR : 3 ≤ R)
    (hpSet : p ∈ signedFirstJumpPostRootPrimeSet R)
    (hhalf : R / 2 < p)
    (hkSet : k ∈ upperHalfFirstJumpOwnerSet R p) :
    (1, k) ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R := by
  have hpData : p.Prime ∧ Nat.sqrt R < p ∧ p ≤ R := by
    simpa [signedFirstJumpPostRootPrimeSet] using
      (mem_frozenPrimeUniverseHighPrimeSet.mp hpSet)
  have hkData : k.Prime ∧ p < k ∧ k ≤ squareRootEndpoint R / p :=
    mem_upperHalfFirstJumpOwnerSet.mp hkSet
  let y : OrderedEulerCutTaggedState := (({p} : Finset ℕ), (1, k))
  have hshape : OrderedEulerCutShape y := by
    dsimp [y, OrderedEulerCutShape]
    refine ⟨hkData.1, by norm_num, by simp, ?_, ?_, ?_⟩
    · intro hdiv
      have hkOne : k = 1 := Nat.dvd_one.mp hdiv
      exact hkData.1.ne_one hkOne
    · intro q hq
      have hqp : q = p := by simpa using hq
      subst q
      exact ⟨hpData.1, hkData.2.1⟩
    · simp [RoughAbove]
  have hkp : k * p ≤ squareRootEndpoint R :=
    (Nat.le_div_iff_mul_le hpData.1.pos).1 hkData.2.2
  have hchild : orderedEulerCutChildInteger y ≤ squareRootEndpoint R := by
    simpa [y, orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
      orderedEulerCutPivot, orderedEulerCutLowProduct, primeFaceProduct] using hkp
  have hsqrt : Nat.sqrt (orderedEulerCutChildInteger y) < R :=
    (orderedEulerCutChild_le_endpoint_iff (R := R) hshape).1 hchild
  have hbirth : orderedEulerCutBirthRoot y ≤ R := by
    unfold orderedEulerCutBirthRoot
    apply Nat.max_le.mpr
    constructor
    · simpa [y, orderedEulerCutLowProduct, primeFaceProduct] using hpData.2.2
    · apply Nat.max_le.mpr
      constructor
      · dsimp [y, orderedEulerCutHighCofactor]
        omega
      · exact Nat.succ_le_iff.mpr hsqrt
  have hR2p : R < p * 2 :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).1 hhalf
  have hp2k : p * 2 ≤ p * k :=
    Nat.mul_le_mul_left p hkData.1.two_le
  have hdeathNat : R < k * p := by
    calc
      R < p * 2 := hR2p
      _ ≤ p * k := hp2k
      _ = k * p := Nat.mul_comm p k
  have hdeath : R < orderedEulerCutDeathRoot y := by
    simpa [y, orderedEulerCutDeathRoot, orderedEulerCutPivot,
      orderedEulerCutLowProduct, primeFaceProduct] using hdeathNat
  have hocc : OrderedEulerCutOccursAt R y :=
    (orderedEulerCutOccursAt_iff_lifetime hshape).2 ⟨hbirth, hdeath⟩
  have hcharge :
      ({p} : Finset ℕ) ∈
        lowWheelCanonicalDowncrossOrientedChargingFaces R (1, k) := by
    exact mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mpr hocc
  exact mem_orientedStateCarrier_of_chargingFaces_nonempty ⟨{p}, hcharge⟩

/-- **Upper-half first-jump slices are singleton faces.** -/
theorem upperHalfFirstJumpFrozenWindowSlice_eq_singleton
    {R q A B p : ℕ}
    (hpPrime : p.Prime)
    (hpRoot : Nat.sqrt R < p)
    (hpq : p < q)
    (hAp : A < p)
    (hpB : p ≤ B)
    (hBR : B ≤ R)
    (hR2p : R < p * 2) :
    predecessorFirstJumpFrozenWindowSlice
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B p =
      {{p}} := by
  have hpS : p ∈ primesUpTo (q - 1) := by
    exact mem_primesUpTo.mpr ⟨hpPrime, by omega⟩
  have hwindow :
      ({p} : Finset ℕ) ∈
        frozenPrimeUniverseWindowFaces (primesUpTo (q - 1)) A B := by
    apply mem_frozenPrimeUniverseWindowFaces.mpr
    refine ⟨?_, ?_, ?_⟩
    · apply Finset.mem_powerset.mpr
      intro r hr
      have hrp : r = p := by simpa using hr
      simpa [hrp] using hpS
    · simpa [primeFaceProduct] using hAp
    · simpa [primeFaceProduct] using hpB
  have hfirst : IsPredecessorFirstJumpAt 3 (Nat.sqrt R) ({p} : Finset ℕ) p := by
    refine ⟨by simp, hpRoot, ?_, ?_⟩
    · have hpredProd :
          predecessorPrimeFaceProduct ({p} : Finset ℕ) p = 1 := by
        unfold predecessorPrimeFaceProduct predecessorPrimeFace primeFaceProduct
        simp
      have hpCube : Nat.sqrt R < p ^ 3 :=
        hpRoot.trans_le (Nat.le_self_pow (by norm_num : 3 ≠ 0) p)
      rw [hpredProd, Nat.mul_one]
      exact hpCube
    · intro r hr hrp _hrRoot
      have hrEq : r = p := by simpa using hr
      omega
  have hjump :
      ({p} : Finset ℕ) ∈
        predecessorFirstJumpFrozenWindowFaces
          3 (Nat.sqrt R) (primesUpTo (q - 1)) A B := by
    apply mem_predecessorFirstJumpFrozenWindowFaces.mpr
    refine ⟨hwindow, ?_⟩
    intro hdense
    have hdenseP := hdense p (by simp) hpRoot
    exact (Nat.not_lt_of_ge hdenseP) hfirst.2.2.1
  have hpSlice :
      ({p} : Finset ℕ) ∈
        predecessorFirstJumpFrozenWindowSlice
          3 (Nat.sqrt R) (primesUpTo (q - 1)) A B p :=
    mem_predecessorFirstJumpFrozenWindowSlice.mpr ⟨hjump, hfirst⟩
  ext t
  constructor
  · intro ht
    have hslice := mem_predecessorFirstJumpFrozenWindowSlice.mp ht
    have hwindowT :=
      (mem_predecessorFirstJumpFrozenWindowFaces.mp hslice.1).1
    have htPow := (mem_frozenPrimeUniverseWindowFaces.mp hwindowT).1
    have htSub := Finset.mem_powerset.mp htPow
    have hshape := sqrtFirstJumpSlice_face_eq_insert_predecessor hBR ht
    have hpredEmpty : predecessorPrimeFace t p = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      have hrData := mem_predecessorPrimeFace.mp hr
      have hrPrime : r.Prime := prime_of_mem_primesUpTo (htSub hrData.1)
      have hsub : insert p {r} ⊆ t := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz | hz
        · subst z
          exact hslice.2.1
        · subst z
          exact hrData.1
      have hprodLower : p * r ≤ primeFaceProduct t := by
        unfold primeFaceProduct
        have hle := Finset.prod_le_prod_of_subset_of_one_le' hsub (by
          intro z hzt _hzsmall
          exact (prime_of_mem_primesUpTo (htSub hzt)).one_le)
        have hne : p ≠ r := by omega
        simpa [hne, Nat.mul_comm] using hle
      have hprodLeR : primeFaceProduct t ≤ R :=
        (mem_frozenPrimeUniverseWindowFaces.mp hwindowT).2.2.trans hBR
      have htwo : p * 2 ≤ p * r :=
        Nat.mul_le_mul_left p hrPrime.two_le
      have : p * 2 ≤ R := htwo.trans (hprodLower.trans hprodLeR)
      omega
    have htEq : t = {p} := by
      rw [hshape, hpredEmpty]
      simp
    exact Finset.mem_singleton.mpr htEq
  · intro ht
    have htEq : t = {p} := Finset.mem_singleton.mp ht
    subst t
    exact hpSlice

/-- Consequently the signed mass of every upper-half frozen `p`-slice is
exactly `-1`; there is no cancellation left inside that fixed owner state. -/
theorem upperHalfFirstJumpFrozenWindowSliceMass_eq_neg_one
    {R q A B p : ℕ}
    (hpPrime : p.Prime)
    (hpRoot : Nat.sqrt R < p)
    (hpq : p < q)
    (hAp : A < p)
    (hpB : p ≤ B)
    (hBR : B ≤ R)
    (hR2p : R < p * 2) :
    predecessorFirstJumpFrozenWindowSliceMass
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B p = -1 := by
  unfold predecessorFirstJumpFrozenWindowSliceMass
  rw [upperHalfFirstJumpFrozenWindowSlice_eq_singleton
    hpPrime hpRoot hpq hAp hpB hBR hR2p]
  simp [booleanCubeSign]

/-- **Nontrivial cofactors cannot carry an upper-half first jump.** -/
theorem upperHalfFirstJumpPrimeStateSlice_eq_zero_of_cofactor_ne_one
    {R p c k : ℕ}
    (hR : 9 ≤ R)
    (hhalf : R / 2 < p)
    (hx : (c, k) ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R)
    (hc : c ≠ 1) :
    signedFirstJumpPrimeStateSlice R p (c, k) = 0 := by
  classical
  unfold signedFirstJumpPrimeStateSlice
  split_ifs with hstate hpMem
  · have hxData := mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mp hx
    have hne := hxData.2
    have hkPivot : k = lowWheelCanonicalDowncrossPivot (c, k) :=
      lowWheelCanonicalDowncrossOrientedChargingFaces_quotient_eq_pivot hne
    have hkRoot : Nat.sqrt R < k := by
      simpa only [← hkPivot] using hstate.2
    have hshape := highOwner_orientedState_shape hx hkRoot
    rcases hshape.2 with hcOne | hcData
    · exact (hc hcOne).elim
    have hpData := mem_primesUpTo.mp hpMem
    have hpLtK : p < k := by omega
    have hp4 : 4 ≤ p := by omega
    have hR2p : R < p * 2 :=
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).1 hhalf
    have hRsq : R ^ 2 < (p * 2) ^ 2 :=
      Nat.pow_lt_pow_left hR2p (by norm_num : 2 ≠ 0)
    have h4p2 : (p * 2) ^ 2 ≤ p ^ 3 := by
      calc
        (p * 2) ^ 2 = 4 * (p * p) := by ring
        _ ≤ p * (p * p) := Nat.mul_le_mul_right (p * p) hp4
        _ = p ^ 3 := by ring
    have hpk : p ≤ k := Nat.le_of_lt hpLtK
    have hpc : p ≤ c := hpk.trans (Nat.le_of_lt hcData.2)
    have hpcProd : p ^ 3 ≤ p * (c * k) := by
      calc
        p ^ 3 = p * (p * p) := by ring
        _ ≤ p * (c * k) :=
          Nat.mul_le_mul_left p (Nat.mul_le_mul hpc hpk)
    have hXltRsq : squareRootEndpoint R < R ^ 2 := by
      unfold squareRootEndpoint
      have hpos : 0 < R ^ 2 := by positivity
      omega
    have hXlt : squareRootEndpoint R < p * (c * k) :=
      hXltRsq.trans (hRsq.trans_le (h4p2.trans hpcProd))
    have hckPos : 0 < c * k := Nat.mul_pos hcData.1.pos hshape.1.pos
    have hdiv : squareRootEndpoint R / (c * k) < p :=
      (Nat.div_lt_iff_lt_mul hckPos).2 hXlt
    have hupper : lowWheelCanonicalDowncrossOwnershipUpper R c k < p := by
      unfold lowWheelCanonicalDowncrossOwnershipUpper
      exact (min_le_right _ _).trans_lt hdiv
    rw [predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_upper_lt hupper]
    simp
  · rfl
  · rfl

/-- **Every actual owner in the upper-half column contributes exactly `-1`.** -/
theorem upperHalfFirstJumpOwner_stateSlice_eq_neg_one
    {R p k : ℕ}
    (hR : 3 ≤ R)
    (hpSet : p ∈ signedFirstJumpPostRootPrimeSet R)
    (hhalf : R / 2 < p)
    (hkSet : k ∈ upperHalfFirstJumpOwnerSet R p) :
    signedFirstJumpPrimeStateSlice R p (1, k) = -1 := by
  classical
  have hpData : p.Prime ∧ Nat.sqrt R < p ∧ p ≤ R := by
    simpa [signedFirstJumpPostRootPrimeSet] using
      (mem_frozenPrimeUniverseHighPrimeSet.mp hpSet)
  have hkData : k.Prime ∧ p < k ∧ k ≤ squareRootEndpoint R / p :=
    mem_upperHalfFirstJumpOwnerSet.mp hkSet
  have hx := upperHalfFirstJumpOwner_state_mem hR hpSet hhalf hkSet
  have hxData := mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mp hx
  have hne := hxData.2
  have hkPivot : k = lowWheelCanonicalDowncrossPivot (1, k) :=
    lowWheelCanonicalDowncrossOrientedChargingFaces_quotient_eq_pivot hne
  have hkRoot : Nat.sqrt R < k := hpData.2.1.trans hkData.2.1
  have hactive :
      (lowWheelCanonicalDowncrossOrientedChargingFaces R (1, k)).Nonempty ∧
        Nat.sqrt R < lowWheelCanonicalDowncrossPivot (1, k) := by
    refine ⟨hne, ?_⟩
    simpa only [← hkPivot] using hkRoot
  have hpMem : p ∈ primesUpTo (lowWheelCanonicalDowncrossPivot (1, k) - 1) := by
    apply mem_primesUpTo.mpr
    refine ⟨hpData.1, ?_⟩
    rw [← hkPivot]
    omega
  have hR2p : R < p * 2 :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).1 hhalf
  have hp2k : p * 2 ≤ p * k :=
    Nat.mul_le_mul_left p hkData.1.two_le
  have hRpk : R < p * k := hR2p.trans_le hp2k
  have hA : R / k < p :=
    (Nat.div_lt_iff_lt_mul hkData.1.pos).2 hRpk
  have hraw : lowWheelCanonicalCofactorQuotientPivot (1, k) = k := by
    simpa [lowWheelCanonicalDowncrossPivot] using hkPivot.symm
  have hBform :
      lowWheelCanonicalDowncrossOwnershipUpper R 1 k =
        min R (squareRootEndpoint R / k) := by
    unfold lowWheelCanonicalDowncrossOwnershipUpper
    rw [hraw, Nat.div_self hkData.1.pos]
    simp
  have hkp : k * p ≤ squareRootEndpoint R :=
    (Nat.le_div_iff_mul_le hpData.1.pos).1 hkData.2.2
  have hpXdiv : p ≤ squareRootEndpoint R / k := by
    apply (Nat.le_div_iff_mul_le hkData.1.pos).2
    simpa [Nat.mul_comm] using hkp
  have hpB : p ≤ lowWheelCanonicalDowncrossOwnershipUpper R 1 k := by
    rw [hBform]
    exact le_min hpData.2.2 hpXdiv
  have hBR : lowWheelCanonicalDowncrossOwnershipUpper R 1 k ≤ R := by
    rw [hBform]
    exact min_le_left _ _
  have hpPivot : p < lowWheelCanonicalDowncrossPivot (1, k) := by
    simpa only [← hkPivot] using hkData.2.1
  have hmass :
      predecessorFirstJumpFrozenWindowSliceMass
          3 (Nat.sqrt R)
          (primesUpTo (lowWheelCanonicalDowncrossPivot (1, k) - 1))
          (R / k)
          (lowWheelCanonicalDowncrossOwnershipUpper R 1 k)
          p = -1 :=
    upperHalfFirstJumpFrozenWindowSliceMass_eq_neg_one
      hpData.1 hpData.2.1 hpPivot hA hpB hBR hR2p
  simp [signedFirstJumpPrimeStateSlice, hactive, hpMem, hmass,
    canonicalMoebiusWeight]

/-! ## Exact aggregate collapse -/

/-- A unit-cofactor high-owner state outside the canonical later-prime owner
interval cannot contain the fixed first-jump prime `p`. -/
theorem upperHalfFirstJumpPrimeStateSlice_eq_zero_unit_of_not_owner
    {R p k : ℕ}
    (hx : (1, k) ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R)
    (hkNot : k ∉ upperHalfFirstJumpOwnerSet R p) :
    signedFirstJumpPrimeStateSlice R p (1, k) = 0 := by
  classical
  unfold signedFirstJumpPrimeStateSlice
  split_ifs with hstate hpMem
  · have hxData := mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mp hx
    have hne := hxData.2
    have hkPivot : k = lowWheelCanonicalDowncrossPivot (1, k) :=
      lowWheelCanonicalDowncrossOrientedChargingFaces_quotient_eq_pivot hne
    have hkRoot : Nat.sqrt R < k := by
      simpa only [← hkPivot] using hstate.2
    have hshape := highOwner_orientedState_shape hx hkRoot
    have hpData := mem_primesUpTo.mp hpMem
    have hpLtK : p < k := by
      have hpLe : p ≤ k - 1 := by
        simpa only [← hkPivot] using hpData.2
      omega
    have hkNotLe : ¬ k ≤ squareRootEndpoint R / p := by
      intro hkLe
      apply hkNot
      exact mem_upperHalfFirstJumpOwnerSet.mpr ⟨hshape.1, hpLtK, hkLe⟩
    have hXpLtK : squareRootEndpoint R / p < k :=
      Nat.lt_of_not_ge hkNotLe
    have hXlt : squareRootEndpoint R < k * p :=
      (Nat.div_lt_iff_lt_mul hpData.1.pos).1 hXpLtK
    have hdiv : squareRootEndpoint R / k < p := by
      apply (Nat.div_lt_iff_lt_mul hshape.1.pos).2
      simpa [Nat.mul_comm] using hXlt
    have hdiv' : squareRootEndpoint R / (1 * k) < p := by
      simpa using hdiv
    have hupper : lowWheelCanonicalDowncrossOwnershipUpper R 1 k < p := by
      unfold lowWheelCanonicalDowncrossOwnershipUpper
      exact (min_le_right _ _).trans_lt hdiv'
    rw [predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_upper_lt hupper]
    simp
  · rfl
  · rfl

/-- Exact statewise classification in the upper half. -/
theorem upperHalfFirstJumpPrimeStateSlice_classification
    {R p c k : ℕ}
    (hR : 9 ≤ R)
    (hpSet : p ∈ signedFirstJumpPostRootPrimeSet R)
    (hhalf : R / 2 < p)
    (hx : (c, k) ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R) :
    signedFirstJumpPrimeStateSlice R p (c, k) =
      if c = 1 ∧ k ∈ upperHalfFirstJumpOwnerSet R p then -1 else 0 := by
  by_cases hc : c = 1
  · subst c
    by_cases hk : k ∈ upperHalfFirstJumpOwnerSet R p
    · rw [upperHalfFirstJumpOwner_stateSlice_eq_neg_one
        (by omega) hpSet hhalf hk]
      simp [hk]
    · rw [upperHalfFirstJumpPrimeStateSlice_eq_zero_unit_of_not_owner hx hk]
      simp [hk]
  · rw [upperHalfFirstJumpPrimeStateSlice_eq_zero_of_cofactor_ne_one
      hR hhalf hx hc]
    simp [hc]

/-- Physical states belonging to the surviving upper-half owner column. -/
def upperHalfFirstJumpOwnerStateSet (R p : ℕ) :
    Finset LowWheelCofactorQuotientState :=
  (upperHalfFirstJumpOwnerSet R p).image fun k => (1, k)

/-- Every owner-column state is an actual member of the oriented state carrier. -/
theorem upperHalfFirstJumpOwnerStateSet_subset_carrier
    {R p : ℕ}
    (hR : 3 ≤ R)
    (hpSet : p ∈ signedFirstJumpPostRootPrimeSet R)
    (hhalf : R / 2 < p) :
    upperHalfFirstJumpOwnerStateSet R p ⊆
      lowWheelCanonicalDowncrossOrientedStateCarrier R := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  exact upperHalfFirstJumpOwner_state_mem hR hpSet hhalf hk

/-- The owner-state embedding `k |-> (1,k)` is injective. -/
theorem upperHalfFirstJumpOwnerStateSet_card (R p : ℕ) :
    (upperHalfFirstJumpOwnerStateSet R p).card =
      (upperHalfFirstJumpOwnerSet R p).card := by
  unfold upperHalfFirstJumpOwnerStateSet
  rw [Finset.card_image_of_injective _
    (fun a b hab => congrArg Prod.snd hab)]

/-- **Exact upper-half fixed-prime aggregate.**

For `R >= 9` and `R/2 < p <= R`, every non-owner state vanishes and every
owner contributes the same signed atom `-1`.  Thus the complete signed slice is
not controlled by `R/p`; it is literally the negative owner-prime count. -/
theorem signedFirstJumpPrimeSliceAggregate_eq_neg_upperHalfOwnerCard
    {R p : ℕ}
    (hR : 9 ≤ R)
    (hpSet : p ∈ signedFirstJumpPostRootPrimeSet R)
    (hhalf : R / 2 < p) :
    signedFirstJumpPrimeSliceAggregate R p =
      -((upperHalfFirstJumpOwnerSet R p).card : ℂ) := by
  classical
  have hsub :
      upperHalfFirstJumpOwnerStateSet R p ⊆
        lowWheelCanonicalDowncrossOrientedStateCarrier R :=
    upperHalfFirstJumpOwnerStateSet_subset_carrier (by omega) hpSet hhalf
  have hrestrict :
      (∑ x ∈ upperHalfFirstJumpOwnerStateSet R p,
          signedFirstJumpPrimeStateSlice R p x) =
        ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
          signedFirstJumpPrimeStateSlice R p x := by
    refine Finset.sum_subset hsub ?_
    intro x hxCarrier hxNotOwner
    rcases x with ⟨c, k⟩
    by_cases hc : c = 1
    · subst c
      by_cases hk : k ∈ upperHalfFirstJumpOwnerSet R p
      · exfalso
        apply hxNotOwner
        exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
      · exact upperHalfFirstJumpPrimeStateSlice_eq_zero_unit_of_not_owner
          hxCarrier hk
    · exact upperHalfFirstJumpPrimeStateSlice_eq_zero_of_cofactor_ne_one
        hR hhalf hxCarrier hc
  unfold signedFirstJumpPrimeSliceAggregate
  calc
    (∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        signedFirstJumpPrimeStateSlice R p x) =
      ∑ x ∈ upperHalfFirstJumpOwnerStateSet R p,
        signedFirstJumpPrimeStateSlice R p x := hrestrict.symm
    _ = ∑ _x ∈ upperHalfFirstJumpOwnerStateSet R p, (-1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      exact upperHalfFirstJumpOwner_stateSlice_eq_neg_one
        (by omega) hpSet hhalf hk
    _ = -((upperHalfFirstJumpOwnerStateSet R p).card : ℂ) := by simp
    _ = -((upperHalfFirstJumpOwnerSet R p).card : ℂ) := by
      rw [upperHalfFirstJumpOwnerStateSet_card]

/-- Norm form of the exact identity. -/
theorem norm_signedFirstJumpPrimeSliceAggregate_eq_upperHalfOwnerCard
    {R p : ℕ}
    (hR : 9 ≤ R)
    (hpSet : p ∈ signedFirstJumpPostRootPrimeSet R)
    (hhalf : R / 2 < p) :
    ‖signedFirstJumpPrimeSliceAggregate R p‖ =
      ((upperHalfFirstJumpOwnerSet R p).card : ℝ) := by
  rw [signedFirstJumpPrimeSliceAggregate_eq_neg_upperHalfOwnerCard
    hR hpSet hhalf]
  simp

/-- The owner cardinality is exactly the ordinary prime count in
`(p, (R^2-1)/p]`, written additively to avoid natural-number subtraction. -/
theorem upperHalfFirstJumpOwnerSet_card_add_primeCounting_eq
    {R p : ℕ}
    (hle : p ≤ squareRootEndpoint R / p) :
    (upperHalfFirstJumpOwnerSet R p).card + Nat.primeCounting p =
      Nat.primeCounting (squareRootEndpoint R / p) := by
  have hset :
      upperHalfFirstJumpOwnerSet R p =
        (Finset.Ioc p (squareRootEndpoint R / p)).filter Nat.Prime := by
    ext k
    simp only [mem_upperHalfFirstJumpOwnerSet, Finset.mem_filter, Finset.mem_Ioc]
    tauto
  rw [hset]
  exact primeCard_Ioc_add_primeCounting_eq hle

end RHLean.Proof