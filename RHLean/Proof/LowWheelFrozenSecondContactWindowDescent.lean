import Mathlib
import RHLean.Proof.LowWheelFrozenSecondContactDescent
import RHLean.Proof.ComplexVerticalLineSquarefreeDiagonal

/-!
# Saturated frozen second-contact windows and signed owner descent

The image of the actual frozen source is the high-product part of the native
predecessor window: `max R (X_R/q^2) < P(V) <= X_R/q`.  The converse uses the
compiled squarefree-shell realization, not a new source carrier.

Subtracting the finite Euler telescopes at positive endpoints cancels the
empty-face anchor exactly.  The resulting double sum is then reassembled by
the child owner before any norm is taken.  These are signed identities; the
fourth-power localization of a different Go defect is not assumed here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The actual source retains the high-product portion of the window. -/
def lowWheelFrozenSecondContactHighOwnerWindow (R q : ℕ) : Finset (Finset ℕ) :=
  frozenPrimeUniverseWindowFaces (primesUpTo (q - 1))
    (max R (squareRootEndpoint R / (q * q))) (squareRootEndpoint R / q)

/-- Signed mass on that independently specified high-product window. -/
def lowWheelFrozenSecondContactHighOwnerWindowMass (R q : ℕ) : ℤ :=
  frozenPrimeUniverseWindowMass (primesUpTo (q - 1))
    (max R (squareRootEndpoint R / (q * q))) (squareRootEndpoint R / q)

/-- Erasing the largest cofactor prime leaves the original root-crossing
prefix as a factor, so the parent product is still strictly above `R`. -/
theorem lowWheelFrozenSecondContactParentFace_root_lt
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    R < primeFaceProduct (lowWheelFrozenSecondContactParentFace y) := by
  have hs := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have hq := lowWheelFrozenCofactorTopPrime_data hy
  have hqLe : lowWheelFrozenCofactorTopPrime y ≤ y.2.1 :=
    Nat.le_of_dvd (by omega) hq.2.1
  have htag := (Finset.mem_filter.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1).1
  have hphys := mem_lowWheelCanonicalPhysicalStateSet.mp
    (mem_lowWheelCanonicalDowncrossPart.mp
      (mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htag).2).1
  have hroot : R < lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := by
    have h := hphys.2.2.2.2.2.1
    simpa [hs.1, Nat.mul_comm] using h
  have hprod : lowWheelFrozenCofactorTopPrime y *
      primeFaceProduct (lowWheelFrozenSecondContactParentFace y) =
      y.2.1 * (lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1) := by
    rw [lowWheelFrozenSecondContact_owner_mul_parentFaceProduct hy,
      lowWheelCanonicalRepeatedFrozenProductOneFace_product hy]
    ring
  have hmul := Nat.mul_le_mul_right
    (lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1) hqLe
  have hle : lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 ≤
      primeFaceProduct (lowWheelFrozenSecondContactParentFace y) := by
    nlinarith [hq.1.pos]
  exact hroot.trans_le hle

/-- The actual source lands in the high-product window. -/
theorem lowWheelFrozenSecondContactParentFace_mem_highOwnerWindow
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    lowWheelFrozenSecondContactParentFace y ∈
      lowWheelFrozenSecondContactHighOwnerWindow R (lowWheelFrozenCofactorTopPrime y) := by
  have hw := mem_frozenPrimeUniverseWindowFaces.mp
    (lowWheelFrozenSecondContactParentFace_mem_ownerWindow hy)
  apply mem_frozenPrimeUniverseWindowFaces.mpr
  exact ⟨hw.1, max_lt
    (lowWheelFrozenSecondContactParentFace_root_lt (Finset.mem_filter.mp hy).1)
    hw.2.1, hw.2.2⟩

/-- A nontrivial-cofactor ordered cut automatically has a repeated parent:
deleting its whole high cofactor leaves a second physical cut with the same
root-side parent.  Thus the repeated-parent filter costs no saturation. -/
theorem orderedEulerCut_mem_frozenCofactor_of_one_lt
    {R : ℕ} {y : OrderedEulerCutTaggedState}
    (hy : y ∈ orderedEulerCutCarrier R) (hc : 1 < y.2.1) :
    y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R := by
  rcases y with ⟨t, c, p⟩
  change 1 < c at hc
  have hs := orderedEulerCutShape_of_mem_carrier hy
  have ho := mem_orderedEulerCutCarrier.mp hy
  have hl := (mem_orderedEulerCutCarrier_iff_shape_lifetime.mp hy).2
  have hpiv : lowWheelCanonicalCofactorQuotientPivot (c, p) = p :=
    orderedEulerCutShape_canonicalPivot hs
  have htag : (t, (c, p)) ∈ lowWheelCanonicalTaggedDowncrossCarrier R :=
    mem_lowWheelCanonicalTaggedDowncrossCarrier.mpr
      ⟨ho.1, (LowWheelCanonicalDowncrossOwnership.mem_lowWheelCanonicalDowncrossOrientedPart.mp
        ho.2).1⟩
  have hfrozen : LowWheelDowncrossFrozenShape (t, (c, p)) := by
    constructor
    · exact hpiv.symm
    · intro r hr
      change r < lowWheelCanonicalCofactorQuotientPivot (c, p)
      rw [hpiv]
      exact (hs.2.2.2.2.1 r hr).2
  have hzShape : OrderedEulerCutShape (t, (1, p)) := by
    refine ⟨hs.1, by norm_num, squarefree_one, ?_, hs.2.2.2.2.1, ?_⟩
    · exact fun h => hs.1.ne_one (Nat.dvd_one.mp h)
    · simp [RoughAbove]
  have hchildLe : orderedEulerCutChildInteger (t, (1, p)) ≤
      orderedEulerCutChildInteger (t, (c, p)) := by
    change 1 * (p * primeFaceProduct t) ≤ c * (p * primeFaceProduct t)
    exact Nat.mul_le_mul_right _ (by omega)
  have hzBirth : orderedEulerCutBirthRoot (t, (1, p)) ≤ R := by
    have hbirth := hl.1
    change max (primeFaceProduct t)
      (max (c + 1) (Nat.sqrt (orderedEulerCutChildInteger (t, (c, p))) + 1)) ≤ R
      at hbirth
    change max (primeFaceProduct t)
      (max (1 + 1) (Nat.sqrt (orderedEulerCutChildInteger (t, (1, p))) + 1)) ≤ R
    have hsqrt := Nat.sqrt_le_sqrt hchildLe
    rcases max_le_iff.mp hbirth with ⟨htR, hrest⟩
    rcases max_le_iff.mp hrest with ⟨hcR, hnR⟩
    exact max_le htR (max_le (by omega) (by omega))
  have hz : (t, (1, p)) ∈ orderedEulerCutCarrier R :=
    mem_orderedEulerCutCarrier_iff_shape_lifetime.mpr ⟨hzShape, hzBirth, hl.2⟩
  have hzo := mem_orderedEulerCutCarrier.mp hz
  have hzTag : (t, (1, p)) ∈ lowWheelCanonicalTaggedDowncrossCarrier R :=
    mem_lowWheelCanonicalTaggedDowncrossCarrier.mpr
      ⟨hzo.1, (LowWheelCanonicalDowncrossOwnership.mem_lowWheelCanonicalDowncrossOrientedPart.mp
        hzo.2).1⟩
  have hzPiv : lowWheelCanonicalCofactorQuotientPivot (1, p) = p :=
    orderedEulerCutShape_canonicalPivot hzShape
  have hparent : lowWheelCanonicalDowncrossParent (t, (1, p)) =
      lowWheelCanonicalDowncrossParent (t, (c, p)) := by
    simp only [lowWheelCanonicalDowncrossParent, hzPiv, hpiv]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨htag, ?_⟩, hfrozen⟩, hc⟩
  intro hunique
  have heq := hunique (t, (1, p)) hzTag hparent
  have hco := congrArg (fun z : LowWheelTaggedDowncrossState => z.2.1) heq
  change 1 = c at hco
  omega

/-- The frozen cofactor owner is also the largest prime of the physical child. -/
theorem lowWheelFrozenCofactorTopPrime_eq_childLargest
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelFrozenCofactorTopPrime y =
      canonicalLargestPrimeFactor (orderedEulerCutChildInteger y) := by
  have hmax := canonicalLargestPrimeFactor_insert_freshPrime
    (lowWheelFrozenCofactorTopPrime_data hy).1
    (lowWheelFrozenSecondContactParentFace_mem_predecessor hy)
  have hins : insert (lowWheelFrozenCofactorTopPrime y)
      (lowWheelFrozenSecondContactParentFace y) =
      lowWheelCanonicalRepeatedFrozenProductOneFace y :=
    Finset.insert_erase (lowWheelFrozenSecondContact_owner_mem_productOneFace hy)
  have hchild : orderedEulerCutChildInteger y =
      primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) := by
    rw [lowWheelFrozenSecondContact_child_eq_owner_mul_parentProduct hy,
      lowWheelFrozenSecondContact_owner_mul_parentFaceProduct hy]
  rw [hins, ← hchild] at hmax
  exact hmax.symm

/-- **Saturation.** Every high-product face in the independent native window
comes from an actual frozen second-contact source. -/
theorem lowWheelFrozenSecondContactParentMap_surjOn_highOwnerWindow
    {R q : ℕ} {V : Finset ℕ} (hq : q.Prime) (hqR : q < R)
    (hV : V ∈ lowWheelFrozenSecondContactHighOwnerWindow R q) :
    ∃ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      lowWheelFrozenSecondContactParentMap y = (q, V) := by
  rcases mem_frozenPrimeUniverseWindowFaces.mp hV with ⟨hpred, hlow, hupp⟩
  have hroot : R < primeFaceProduct V := (le_max_left _ _).trans_lt hlow
  have hann : squareRootEndpoint R / (q * q) < primeFaceProduct V :=
    (le_max_right _ _).trans_lt hlow
  have hqNot : q ∉ V := Finset.notMem_of_mem_powerset_of_notMem hpred
    (freshPrime_not_mem_primesUpTo_pred hq)
  have hVPrime : ∀ r ∈ V, r.Prime :=
    fun r hr => prime_of_mem_primesUpTo ((Finset.mem_powerset.mp hpred) hr)
  have hUPrime : ∀ r ∈ insert q V, r.Prime := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hq
    · exact hVPrime r hr
  have hprod : primeFaceProduct (insert q V) = q * primeFaceProduct V := by
    simp [primeFaceProduct, hqNot]
  have hmu : μ (primeFaceProduct (insert q V)) ≠ 0 := by
    rw [moebius_primeFaceProduct_eq_booleanCubeSign _ hUPrime]
    simp [booleanCubeSign]
  have hsq := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
  have hR : 2 ≤ R := by have := hq.two_le; omega
  have htop : primeFaceProduct (insert q V) ≤ squareRootEndpoint R := by
    rw [hprod]
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq.pos).1 hupp
  have hRn : R < primeFaceProduct (insert q V) := by
    rw [hprod]
    exact hroot.trans_le (Nat.le_mul_of_pos_left _ hq.pos)
  have hnR : primeFaceProduct (insert q V) < R ^ 2 := by
    unfold squareRootEndpoint at htop
    have : 0 < R ^ 2 := pow_pos (by omega) 2
    omega
  have hactive := orderedEulerCutActiveChild_of_squarefree_shell hR hsq hRn hnR
  rcases Finset.mem_image.mp hactive with ⟨y, hy, hchild⟩
  have hs := orderedEulerCutShape_of_mem_carrier hy
  have hmax : canonicalLargestPrimeFactor (orderedEulerCutChildInteger y) = q := by
    rw [hchild]
    exact canonicalLargestPrimeFactor_insert_freshPrime hq hpred
  have hc : 1 < y.2.1 := by
    by_contra hnot
    have hcOne : y.2.1 = 1 := by have := hs.2.1; omega
    have htPred : y.1 ∈ (primesUpTo (y.2.2 - 1)).powerset := by
      apply Finset.mem_powerset.mpr
      intro r hr
      have hd := hs.2.2.2.2.1 r hr
      exact mem_primesUpTo.mpr ⟨hd.1, by omega⟩
    have hpNot : y.2.2 ∉ y.1 := Finset.notMem_of_mem_powerset_of_notMem htPred
      (freshPrime_not_mem_primesUpTo_pred hs.1)
    have hcp : orderedEulerCutChildInteger y =
        primeFaceProduct (insert y.2.2 y.1) := by
      simp [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
        orderedEulerCutPivot, orderedEulerCutLowProduct, hcOne,
        primeFaceProduct, hpNot]
    have hpq : y.2.2 = q := by
      rw [hcp, canonicalLargestPrimeFactor_insert_freshPrime hs.1 htPred] at hmax
      exact hmax
    have hmul : q * primeFaceProduct y.1 = q * primeFaceProduct V := by
      simpa [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
        orderedEulerCutPivot, orderedEulerCutLowProduct, hcOne, hpq, hprod] using hchild
    have heq : primeFaceProduct y.1 = primeFaceProduct V := by nlinarith [hq.pos]
    have htR := orderedEulerCutOccursAt_lowProduct_le hs (mem_orderedEulerCutCarrier.mp hy)
    change primeFaceProduct y.1 ≤ R at htR
    omega
  have hfrozen := orderedEulerCut_mem_frozenCofactor_of_one_lt hy hc
  have howner : lowWheelFrozenCofactorTopPrime y = q :=
    (lowWheelFrozenCofactorTopPrime_eq_childLargest hfrozen).trans hmax
  have hfullprod : primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) =
      primeFaceProduct (insert q V) := by
    rw [← lowWheelFrozenSecondContact_owner_mul_parentFaceProduct hfrozen,
      ← lowWheelFrozenSecondContact_child_eq_owner_mul_parentProduct hfrozen, hchild]
  have hfull : lowWheelCanonicalRepeatedFrozenProductOneFace y = insert q V := by
    apply (primeFaceProduct_eq_iff (fun r hr => prime_of_mem_primesUpTo
      ((Finset.mem_powerset.mp
        (lowWheelCanonicalRepeatedFrozenProductOneFace_mem_powerset hfrozen)) hr))
      hUPrime).mp
    exact hfullprod
  have hsecond : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R := by
    apply Finset.mem_filter.mpr
    refine ⟨hfrozen, ?_⟩
    rw [howner, hfull, hprod]
    have h := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hq.pos hq.pos)).1 hann
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  refine ⟨y, hsecond, ?_⟩
  apply Prod.ext
  · exact howner
  · change (lowWheelCanonicalRepeatedFrozenProductOneFace y).erase
      (lowWheelFrozenCofactorTopPrime y) = V
    rw [howner, hfull, Finset.erase_insert hqNot]

/-- Exact fixed-owner image, with neither omissions nor multiplicities. -/
theorem mem_lowWheelFrozenSecondContactParentMap_image_iff_highOwnerWindow
    {R q : ℕ} {V : Finset ℕ} (hq : q.Prime) (hqR : q < R) :
    (q, V) ∈ (lowWheelCanonicalRepeatedFrozenSecondContactPart R).image
        lowWheelFrozenSecondContactParentMap ↔
      V ∈ lowWheelFrozenSecondContactHighOwnerWindow R q := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨y, hy, heq⟩
    have hw := lowWheelFrozenSecondContactParentFace_mem_highOwnerWindow hy
    have hqeq := congrArg Prod.fst heq
    have hVeq := congrArg Prod.snd heq
    change lowWheelFrozenCofactorTopPrime y = q at hqeq
    change lowWheelFrozenSecondContactParentFace y = V at hVeq
    simpa only [hqeq, hVeq] using hw
  · intro hV
    rcases lowWheelFrozenSecondContactParentMap_surjOn_highOwnerWindow hq hqR hV with
      ⟨y, hy, heq⟩
    exact Finset.mem_image.mpr ⟨y, hy, heq⟩

/-- Saturation and injectivity transport the complete fixed-owner source
ledger to exactly one native signed window. -/
theorem lowWheelFrozenSecondContactSource_owner_sum_eq_highOwnerWindowMass
    {R q : ℕ} (hq : q.Prime) (hqR : q < R) :
    (∑ y ∈ (lowWheelCanonicalRepeatedFrozenSecondContactPart R).filter
        (fun y => lowWheelFrozenCofactorTopPrime y = q),
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      (lowWheelFrozenSecondContactHighOwnerWindowMass R q : ℂ) := by
  have hcast : (lowWheelFrozenSecondContactHighOwnerWindowMass R q : ℂ) =
      ∑ V ∈ lowWheelFrozenSecondContactHighOwnerWindow R q, (booleanCubeSign V : ℂ) := by
    simp only [lowWheelFrozenSecondContactHighOwnerWindowMass,
      frozenPrimeUniverseWindowMass, lowWheelFrozenSecondContactHighOwnerWindow,
      Int.cast_sum]
  rw [hcast]
  refine Finset.sum_bij (fun y _hy => lowWheelFrozenSecondContactParentFace y) ?_ ?_ ?_ ?_
  · intro y hy
    have hd := Finset.mem_filter.mp hy
    simpa only [hd.2] using lowWheelFrozenSecondContactParentFace_mem_highOwnerWindow hd.1
  · intro y hy z hz heq
    have hyd := Finset.mem_filter.mp hy
    have hzd := Finset.mem_filter.mp hz
    apply lowWheelFrozenSecondContactParentMap_injOn R hyd.1 hzd.1
    exact Prod.ext (hyd.2.trans hzd.2.symm) heq
  · intro V hV
    rcases lowWheelFrozenSecondContactParentMap_surjOn_highOwnerWindow hq hqR hV with
      ⟨y, hy, heq⟩
    have ho := congrArg Prod.fst heq
    have hv := congrArg Prod.snd heq
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, ho⟩, hv⟩
  · intro y hy
    exact (lowWheelFrozenSecondContactParentMap_weight_eq_source
      (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1).symm

/-- **Positive-endpoint Euler difference.** The only anchor in the finite
upper-column telescope is the empty face.  It cancels at any two positive
endpoints, even when an endpoint is below the current owner. -/
theorem frozenPrimeUniverseWindowMass_eq_neg_smallerOwnerWindows
    (K : ℕ) {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    frozenPrimeUniverseWindowMass (primesUpTo K) A B =
      -∑ r ∈ primesUpTo K,
        frozenPrimeUniverseWindowMass (primesUpTo (r - 1)) (A / r) (B / r) := by
  rw [frozenPrimeUniverseWindowMass_eq_sub hAB]
  have hwin : (∑ r ∈ primesUpTo K,
      frozenPrimeUniverseWindowMass (primesUpTo (r - 1)) (A / r) (B / r)) =
      (∑ r ∈ primesUpTo K, frozenPrimeUniverseMass (primesUpTo (r - 1)) (B / r)) -
      ∑ r ∈ primesUpTo K, frozenPrimeUniverseMass (primesUpTo (r - 1)) (A / r) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _hr
    exact frozenPrimeUniverseWindowMass_eq_sub (Nat.div_le_div_right hAB)
  rw [hwin, frozenPrimeUniverse_upperColumn_telescope B K (hA.trans hAB),
    frozenPrimeUniverse_upperColumn_telescope A K hA]
  ring

/-- Exact global source ledger after saturation of every owner fibre. -/
theorem lowWheelFrozenSecondContactSource_sum_eq_highOwnerWindowMass_sum
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      ((∑ q ∈ primesUpTo (R - 1),
        lowWheelFrozenSecondContactHighOwnerWindowMass R q : ℤ) : ℂ) := by
  have hmaps : ∀ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      lowWheelFrozenCofactorTopPrime y ∈ primesUpTo (R - 1) := by
    intro y hy
    have hd := mem_lowWheelFrozenSecondContactParentCarrier.mp
      (lowWheelFrozenSecondContactParentMap_mem hy)
    exact mem_primesUpTo.mpr ⟨hd.2.2.1, (Finset.mem_Icc.mp hd.1).2⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun y => canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ))
  rw [← hfib, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hd := mem_primesUpTo.mp hq
  have := hd.1.two_le
  exact lowWheelFrozenSecondContactSource_owner_sum_eq_highOwnerWindowMass hd.1 (by omega)

/-- The high-window endpoints are correctly ordered at every native owner. -/
theorem lowWheelFrozenSecondContactHighOwnerWindow_endpoints
    {R q : ℕ} (hq : q.Prime) (hqR : q < R) :
    1 ≤ max R (squareRootEndpoint R / (q * q)) ∧
      max R (squareRootEndpoint R / (q * q)) ≤ squareRootEndpoint R / q := by
  have hR : 2 ≤ R := by have := hq.two_le; omega
  have hroot : R ≤ squareRootEndpoint R / q := by
    apply (Nat.le_div_iff_mul_le hq.pos).2
    have hx : squareRootEndpoint R + 1 = R ^ 2 := by
      unfold squareRootEndpoint
      have : 0 < R ^ 2 := pow_pos (by omega) 2
      omega
    have hqSucc : q + 1 ≤ R := by omega
    nlinarith
  exact ⟨(by omega : 1 ≤ R).trans (le_max_left _ _), max_le hroot
    (Nat.div_le_div_left (by nlinarith [hq.two_le]) hq.pos)⟩

/-- **Native high-tail window descent.** Both endpoint bases disappear before
the source is reassembled; every new owner is strictly smaller than `q`. -/
theorem lowWheelFrozenSecondContactHighOwnerWindowMass_eq_neg_childWindows
    {R q : ℕ} (hq : q.Prime) (hqR : q < R) :
    lowWheelFrozenSecondContactHighOwnerWindowMass R q =
      -∑ r ∈ primesUpTo (q - 1),
        frozenPrimeUniverseWindowMass (primesUpTo (r - 1))
          (max R (squareRootEndpoint R / (q * q)) / r)
          (squareRootEndpoint R / q / r) := by
  have he := lowWheelFrozenSecondContactHighOwnerWindow_endpoints hq hqR
  exact frozenPrimeUniverseWindowMass_eq_neg_smallerOwnerWindows (q - 1) he.1 he.2

/-- A literal fixed-child-owner column, with the old owner retained only as a
finite schedule index. -/
def lowWheelFrozenSecondContactChildOwnerColumn (R r : ℕ) : ℤ :=
  ∑ q ∈ (primesUpTo (R - 1)).filter (fun q => r < q),
    frozenPrimeUniverseWindowMass (primesUpTo (r - 1))
      (max R (squareRootEndpoint R / (q * q)) / r)
      (squareRootEndpoint R / q / r)

/-- **Global signed reassembly by the child owner.** No owner count and no
absolute value is introduced when interchanging the finite triangular sums. -/
theorem lowWheelFrozenSecondContactHighOwnerWindowMass_sum_eq_neg_childOwnerColumns
    (R : ℕ) :
    (∑ q ∈ primesUpTo (R - 1), lowWheelFrozenSecondContactHighOwnerWindowMass R q) =
      -∑ r ∈ primesUpTo (R - 1), lowWheelFrozenSecondContactChildOwnerColumn R r := by
  have hpred : ∀ q ∈ primesUpTo (R - 1),
      primesUpTo (q - 1) = (primesUpTo (R - 1)).filter (fun r => r < q) := by
    intro q hq
    have hqData := mem_primesUpTo.mp hq
    ext r
    simp only [mem_primesUpTo, Finset.mem_filter]
    constructor
    · rintro ⟨hrPrime, hrq⟩
      have := hqData.1.two_le
      exact ⟨⟨hrPrime, by omega⟩, by omega⟩
    · rintro ⟨⟨hrPrime, _hrR⟩, hrq⟩
      exact ⟨hrPrime, by omega⟩
  calc
    (∑ q ∈ primesUpTo (R - 1), lowWheelFrozenSecondContactHighOwnerWindowMass R q) =
        ∑ q ∈ primesUpTo (R - 1), -∑ r ∈ primesUpTo (q - 1),
          frozenPrimeUniverseWindowMass (primesUpTo (r - 1))
            (max R (squareRootEndpoint R / (q * q)) / r)
            (squareRootEndpoint R / q / r) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hd := mem_primesUpTo.mp hq
      have := hd.1.two_le
      exact lowWheelFrozenSecondContactHighOwnerWindowMass_eq_neg_childWindows hd.1 (by omega)
    _ = -∑ q ∈ primesUpTo (R - 1),
        ∑ r ∈ (primesUpTo (R - 1)).filter (fun r => r < q),
          frozenPrimeUniverseWindowMass (primesUpTo (r - 1))
            (max R (squareRootEndpoint R / (q * q)) / r)
            (squareRootEndpoint R / q / r) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      rw [hpred q hq]
    _ = -∑ r ∈ primesUpTo (R - 1), lowWheelFrozenSecondContactChildOwnerColumn R r := by
      simp only [Finset.sum_filter, lowWheelFrozenSecondContactChildOwnerColumn]
      rw [Finset.sum_comm]

/-- Both exact identities composed on the original frozen source ledger. -/
theorem lowWheelFrozenSecondContactSource_sum_eq_neg_childOwnerColumns
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      -((∑ r ∈ primesUpTo (R - 1),
        lowWheelFrozenSecondContactChildOwnerColumn R r : ℤ) : ℂ) := by
  rw [lowWheelFrozenSecondContactSource_sum_eq_highOwnerWindowMass_sum,
    lowWheelFrozenSecondContactHighOwnerWindowMass_sum_eq_neg_childOwnerColumns,
    Int.cast_neg]

/-- The exact old-owner fibre above a reassembled parent product `r*d`. -/
def lowWheelFrozenSecondContactOldOwnerFiber (R r d : ℕ) : Finset ℕ :=
  (primesUpTo (R - 1)).filter fun q =>
    r < q ∧ R < r * d ∧ q * (r * d) ≤ squareRootEndpoint R ∧
      squareRootEndpoint R < q * q * (r * d)

/-- After division by the new owner, window membership is exactly a root
crossing plus the old owner's two contact inequalities. -/
theorem mem_lowWheelFrozenSecondContactChildWindow_iff
    {R q r : ℕ} {V : Finset ℕ} (hq : q.Prime) (hr : r.Prime) :
    V ∈ frozenPrimeUniverseWindowFaces (primesUpTo (r - 1))
        (max R (squareRootEndpoint R / (q * q)) / r)
        (squareRootEndpoint R / q / r) ↔
      V ∈ (primesUpTo (r - 1)).powerset ∧
        R < r * primeFaceProduct V ∧
        q * (r * primeFaceProduct V) ≤ squareRootEndpoint R ∧
        squareRootEndpoint R < q * q * (r * primeFaceProduct V) := by
  rw [mem_frozenPrimeUniverseWindowFaces]
  have hlow : max R (squareRootEndpoint R / (q * q)) / r < primeFaceProduct V ↔
      R < r * primeFaceProduct V ∧
        squareRootEndpoint R < q * q * (r * primeFaceProduct V) := by
    rw [Nat.div_lt_iff_lt_mul hr.pos, max_lt_iff,
      Nat.div_lt_iff_lt_mul (Nat.mul_pos hq.pos hq.pos)]
    simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hupp : primeFaceProduct V ≤ squareRootEndpoint R / q / r ↔
      q * (r * primeFaceProduct V) ≤ squareRootEndpoint R := by
    rw [Nat.le_div_iff_mul_le hr.pos, Nat.le_div_iff_mul_le hq.pos]
    simp only [Nat.mul_comm]
  rw [hlow, hupp]
  tauto

/-- **Exact fixed-child-owner overlap formula.** Windows for different old
owners have the same sign at a common face.  Their exact overlap is the old
owner fibre multiplicity; cancellation can still occur between different
signed faces.  This is an equality, not an unsigned estimate. -/
theorem lowWheelFrozenSecondContactChildOwnerColumn_eq_signed_fibers
    {R r : ℕ} (hr : r.Prime) :
    lowWheelFrozenSecondContactChildOwnerColumn R r =
      ∑ V ∈ (primesUpTo (r - 1)).powerset,
        ((lowWheelFrozenSecondContactOldOwnerFiber R r (primeFaceProduct V)).card : ℤ) *
          booleanCubeSign V := by
  unfold lowWheelFrozenSecondContactChildOwnerColumn
  have hwindow : ∀ q ∈ primesUpTo (R - 1),
      frozenPrimeUniverseWindowMass (primesUpTo (r - 1))
        (max R (squareRootEndpoint R / (q * q)) / r)
        (squareRootEndpoint R / q / r) =
        ∑ V ∈ (primesUpTo (r - 1)).powerset,
          if R < r * primeFaceProduct V ∧
              q * (r * primeFaceProduct V) ≤ squareRootEndpoint R ∧
              squareRootEndpoint R < q * q * (r * primeFaceProduct V)
          then booleanCubeSign V else 0 := by
    intro q hq
    have hp := (mem_primesUpTo.mp hq).1
    unfold frozenPrimeUniverseWindowMass frozenPrimeUniverseWindowFaces
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro V hV
    have hw := mem_lowWheelFrozenSecondContactChildWindow_iff (R := R) (V := V) hp hr
    simp only [mem_frozenPrimeUniverseWindowFaces, hV, true_and] at hw
    simp only [hw]
  rw [Finset.sum_filter]
  calc
    (∑ q ∈ primesUpTo (R - 1), if r < q then
        frozenPrimeUniverseWindowMass (primesUpTo (r - 1))
          (max R (squareRootEndpoint R / (q * q)) / r)
          (squareRootEndpoint R / q / r) else 0) =
        ∑ q ∈ primesUpTo (R - 1), ∑ V ∈ (primesUpTo (r - 1)).powerset,
          if r < q ∧ R < r * primeFaceProduct V ∧
              q * (r * primeFaceProduct V) ≤ squareRootEndpoint R ∧
              squareRootEndpoint R < q * q * (r * primeFaceProduct V)
          then booleanCubeSign V else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hwindow q hq]
      by_cases hqr : r < q <;> simp [hqr]
    _ = ∑ V ∈ (primesUpTo (r - 1)).powerset,
        ((lowWheelFrozenSecondContactOldOwnerFiber R r (primeFaceProduct V)).card : ℤ) *
          booleanCubeSign V := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro V _hV
      rw [← Finset.sum_filter]
      simp only [lowWheelFrozenSecondContactOldOwnerFiber, Finset.sum_const,
        nsmul_eq_mul]

/-! ## Carrier checks required before using an energy gate -/

/-- The two old-owner windows can overlap on the same signed face.  Thus the
fixed-child-owner reassembly is not a disjoint interval partition. -/
theorem lowWheelFrozenSecondContactChildWindows_overlap :
    {3} ∈ frozenPrimeUniverseWindowFaces (primesUpTo (5 - 1))
      (max 13 (squareRootEndpoint 13 / (7 * 7)) / 5)
      (squareRootEndpoint 13 / 7 / 5) ∧
    {3} ∈ frozenPrimeUniverseWindowFaces (primesUpTo (5 - 1))
      (max 13 (squareRootEndpoint 13 / (11 * 11)) / 5)
      (squareRootEndpoint 13 / 11 / 5) := by
  norm_num [mem_frozenPrimeUniverseWindowFaces, Finset.mem_powerset,
    Finset.subset_iff, mem_primesUpTo, primeFaceProduct, squareRootEndpoint]

private theorem source_exists_of_highOwnerWindow_of_fourth_le
    {R q : ℕ} {V : Finset ℕ} (hq : q.Prime) (hqR : q < R)
    (hwin : V ∈ lowWheelFrozenSecondContactHighOwnerWindow R q)
    (hfourth : q ^ 4 ≤ squareRootEndpoint R) :
    ∃ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      lowWheelFrozenCofactorTopPrime y = q ∧
        (lowWheelFrozenCofactorTopPrime y) ^ 4 ≤ squareRootEndpoint R := by
  rcases lowWheelFrozenSecondContactParentMap_surjOn_highOwnerWindow hq hqR hwin with
    ⟨y, hy, hm⟩
  have ho : lowWheelFrozenCofactorTopPrime y = q := congrArg Prod.fst hm
  exact ⟨y, hy, ho, by simpa only [ho] using hfourth⟩

private theorem highOwnerWindow_122_contains_primorial7 :
    ({2, 3, 5, 7} : Finset ℕ) ∈ lowWheelFrozenSecondContactHighOwnerWindow 122 11 := by
  norm_num [lowWheelFrozenSecondContactHighOwnerWindow,
    mem_frozenPrimeUniverseWindowFaces, Finset.mem_powerset,
    Finset.subset_iff, mem_primesUpTo, primeFaceProduct, squareRootEndpoint]

/-- The raw source is not already supported in the fourth-power Go band.
At `R=122`, the face `{2,3,5,7}` belongs to the owner-11 high window although
`11^4 <= X_R`.  A later energy gate needs an additional exact defect bridge. -/
theorem lowWheelFrozenSecondContactSource_exists_outside_fourthPowerGate :
    ∃ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart 122,
      lowWheelFrozenCofactorTopPrime y = 11 ∧
        (lowWheelFrozenCofactorTopPrime y) ^ 4 ≤ squareRootEndpoint 122 :=
  source_exists_of_highOwnerWindow_of_fourth_le
    (by norm_num) (by norm_num) highOwnerWindow_122_contains_primorial7
    (by norm_num [squareRootEndpoint])

end RHLean.Proof
