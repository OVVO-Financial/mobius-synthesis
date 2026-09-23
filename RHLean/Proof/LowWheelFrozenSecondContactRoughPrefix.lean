import Mathlib
import RHLean.Proof.LowWheelFrozenSecondContactScaleFlux
import RHLean.Proof.LowWheelCanonicalDefectReduction

/-!
# Exact rough-prefix fibre of the existing physical transport

At a represented source scale `A`, the complete frozen cofactor fibre is the
nonunit squarefree `P+(A)`-rough prefix at `B = X_R / A`. Its second-contact
subfibre is cut out by `B < P+(c)*c`; the complementary square residual obeys
`P+(c)*c <= B` and hence lies below `B/2`.

The full prefix has an opposite-weight mate in the existing physical transport
carrier. We identify that actual subledger and retain an arbitrary test function
of the physical integer, so the cancellation preserves every integer fibre and
all multiplicities. The unit cofactor is excluded on both sides.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Full frozen cofactor fibre, before imposing the second-contact wall. -/
def lowWheelFrozenCofactorSourceScaleFiber (R A : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalRepeatedFrozenCofactorPart R).filter fun y =>
    lowWheelFrozenSecondContactSourceScale y = A

/-- Independent nonunit rough prefix. Squarefreeness removes only zero weights. -/
def lowWheelFrozenSourceRoughPrefix (p B : ℕ) : Finset ℕ :=
  (Finset.Icc 2 B).filter fun c => Squarefree c ∧ RoughAbove p c

/-- Complement of the second-contact shell in the full rough prefix. -/
def lowWheelFrozenSourceSquareResidual (p B : ℕ) : Finset ℕ :=
  (lowWheelFrozenSourceRoughPrefix p B).filter fun c =>
    canonicalLargestPrimeFactor c * c ≤ B

/-- Literal product-one subcarrier of the already-defined physical transport. -/
def lowWheelFrozenSourceScaleTransportCarrier (R A : ℕ) :
    Finset LowWheelTaggedCofactorQuotientState :=
  (lowWheelFrozenCofactorSourceScaleFiber R A).image
    lowWheelCanonicalRepeatedFrozenProductOneMate

/-- Physical integer represented by one tagged cofactor/quotient transport
state. This is the invariant product `c * P(t) * k`. -/
def lowWheelTaggedPhysicalInteger
    (z : LowWheelTaggedCofactorQuotientState) : ℕ :=
  z.2.1 * primeFaceProduct z.1 * z.2.2

private theorem frozenSource_scale_eq_insert
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelFrozenSecondContactSourceScale y =
      primeFaceProduct (insert (lowWheelTaggedDowncrossPivot y) y.1) := by
  have hpNot : lowWheelTaggedDowncrossPivot y ∉ y.1 := by
    intro hp
    exact (Nat.lt_irrefl _)
      (lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hp)
  simp [lowWheelFrozenSecondContactSourceScale, primeFaceProduct, hpNot]

private theorem frozenSource_scale_largestPrime
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    canonicalLargestPrimeFactor (lowWheelFrozenSecondContactSourceScale y) =
      lowWheelTaggedDowncrossPivot y := by
  have hs := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have ho := orderedEulerCutShape_of_mem_carrier
    (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hy)
  have ht : y.1 ∈ (primesUpTo (lowWheelTaggedDowncrossPivot y - 1)).powerset := by
    apply Finset.mem_powerset.mpr
    intro r hr
    have hp := (ho.2.2.2.2.1 r hr).1
    have hlt := lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hr
    exact mem_primesUpTo.mpr ⟨hp, by omega⟩
  rw [frozenSource_scale_eq_insert hy]
  exact canonicalLargestPrimeFactor_insert_freshPrime hs.2.1 ht

private theorem frozenSource_productOne_eq_scale_mul_cofactor
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) =
      lowWheelFrozenSecondContactSourceScale y * y.2.1 := by
  rw [lowWheelCanonicalRepeatedFrozenProductOneFace_product hy]
  unfold lowWheelFrozenSecondContactSourceScale
  ring

private theorem frozenSource_child_eq_scale_mul_cofactor
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    orderedEulerCutChildInteger y =
      lowWheelFrozenSecondContactSourceScale y * y.2.1 := by
  rw [lowWheelFrozenSecondContact_child_eq_owner_mul_parentProduct hy,
    lowWheelFrozenSecondContact_owner_mul_parentFaceProduct hy]
  exact frozenSource_productOne_eq_scale_mul_cofactor hy

private theorem frozenSource_weight_eq
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedDowncrossWeight y =
      -(canonicalMoebiusWeight (lowWheelFrozenSecondContactSourceScale y) *
        canonicalMoebiusWeight y.2.1) := by
  have hs := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have ho := orderedEulerCutShape_of_mem_carrier
    (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hy)
  have hpNot : lowWheelTaggedDowncrossPivot y ∉ y.1 := by
    intro hp
    exact (Nat.lt_irrefl _)
      (lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hp)
  have hprime : ∀ r ∈ insert (lowWheelTaggedDowncrossPivot y) y.1, r.Prime := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hs.2.1
    · exact (ho.2.2.2.2.1 r hr).1
  have hmu : μ (lowWheelFrozenSecondContactSourceScale y) =
      -booleanCubeSign y.1 := by
    rw [frozenSource_scale_eq_insert hy,
      moebius_primeFaceProduct_eq_booleanCubeSign _ hprime]
    simp [booleanCubeSign, Finset.card_insert_of_notMem hpNot, pow_succ]
  simp only [lowWheelTaggedDowncrossWeight, canonicalMoebiusWeight, hmu,
    Int.cast_neg]
  ring

/-- Every fixed-`A` product-one mate is an actual state of the historical
physical transport carrier. -/
theorem lowWheelFrozenSourceScaleTransportCarrier_subset_transport
    (R A : ℕ) :
    lowWheelFrozenSourceScaleTransportCarrier R A ⊆
      lowWheelCanonicalTaggedPhysicalCarrier R := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hyFiber, rfl⟩
  have hy := (Finset.mem_filter.mp hyFiber).1
  exact lowWheelCanonicalRepeatedFrozenProductOneMateImage_subset_transport R
    (Finset.mem_image.mpr ⟨y, hy, rfl⟩)

/-- More precisely, those matching transport states lie in the old fixed part:
the cofactor/quotient coordinate is literally `(1,1)`. -/
theorem lowWheelFrozenSourceScaleTransportCarrier_mem_fixedPart
    {R A : ℕ} {z : LowWheelTaggedCofactorQuotientState}
    (hz : z ∈ lowWheelFrozenSourceScaleTransportCarrier R A) :
    z.2 ∈ lowWheelCanonicalFixedPart
      (lowWheelCanonicalPhysicalStateSet R z.1) := by
  rcases Finset.mem_image.mp hz with ⟨y, hyFiber, rfl⟩
  have hy := (Finset.mem_filter.mp hyFiber).1
  change (1, 1) ∈ lowWheelCanonicalFixedPart
    (lowWheelCanonicalPhysicalStateSet R
      (lowWheelCanonicalRepeatedFrozenProductOneFace y))
  apply Finset.mem_filter.mpr
  constructor
  · exact lowWheelCanonicalRepeatedFrozenProductOneMate_mem_physical hy
  · exact lowWheelCanonicalToggle_eq_self_of_product_eq_one (by norm_num)

/-- The product-one mate preserves the represented arithmetic integer exactly. -/
theorem lowWheelFrozenProductOneMate_physicalInteger_eq_child
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedPhysicalInteger
        (lowWheelCanonicalRepeatedFrozenProductOneMate y) =
      orderedEulerCutChildInteger y := by
  unfold lowWheelTaggedPhysicalInteger lowWheelCanonicalRepeatedFrozenProductOneMate
  dsimp
  simp only [Nat.one_mul, Nat.mul_one]
  rw [frozenSource_productOne_eq_scale_mul_cofactor hy,
    frozenSource_child_eq_scale_mul_cofactor hy]

/-- Reindex a fixed-scale transport subcarrier by the frozen source which
created its product-one mate. The global whole-cofactor mate is injective, so
no multiplicity is lost. -/
theorem lowWheelFrozenSourceScaleTransportCarrier_sum_image
    (R A : ℕ) (F : LowWheelTaggedCofactorQuotientState → ℂ) :
    (∑ z ∈ lowWheelFrozenSourceScaleTransportCarrier R A, F z) =
      ∑ y ∈ lowWheelFrozenCofactorSourceScaleFiber R A,
        F (lowWheelCanonicalRepeatedFrozenProductOneMate y) := by
  unfold lowWheelFrozenSourceScaleTransportCarrier
  rw [Finset.sum_image]
  intro y hy z hz heq
  exact lowWheelCanonicalRepeatedFrozenProductOneMate_injOn R
    (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hz).1 heq

/-- **Physical-fibre cancellation.** At fixed source scale `A`, the entire
frozen rough-prefix source and its actual historical transport mates cancel
before any norm is taken. An arbitrary test function of the represented
integer may be retained, so the identity preserves every arithmetic fibre and
all multiplicities. -/
theorem lowWheelFrozenSourceScale_source_add_transport_test_eq_zero
    (R A : ℕ) (φ : ℕ → ℂ) :
    (∑ y ∈ lowWheelFrozenCofactorSourceScaleFiber R A,
        lowWheelTaggedDowncrossWeight y * φ (orderedEulerCutChildInteger y)) +
      (∑ z ∈ lowWheelFrozenSourceScaleTransportCarrier R A,
        lowWheelTaggedCanonicalWeight z * φ (lowWheelTaggedPhysicalInteger z)) =
      0 := by
  rw [lowWheelFrozenSourceScaleTransportCarrier_sum_image R A
    (fun z => lowWheelTaggedCanonicalWeight z *
      φ (lowWheelTaggedPhysicalInteger z))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro y hy
  have hyFrozen := (Finset.mem_filter.mp hy).1
  rw [lowWheelCanonicalRepeatedFrozenProductOneMate_taggedWeight_neg hyFrozen,
    lowWheelFrozenProductOneMate_physicalInteger_eq_child hyFrozen]
  ring

/-- A represented source scale is above the old root. -/
theorem lowWheelFrozenSourceScale_root_lt
    {R A : ℕ} (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R) :
    R < A := by
  rcases Finset.mem_image.mp hA with ⟨y, hy, hyA⟩
  have h := lowWheelCanonicalRepeatedFrozenCofactor_facePivot_crosses_root
    (Finset.mem_filter.mp hy).1
  change R < lowWheelFrozenSecondContactSourceScale y at h
  simpa [hyA] using h

/-- Its reciprocal cutoff is strictly below the old root. -/
theorem lowWheelFrozenSourceScale_cutoff_lt_root
    {R A : ℕ} (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R) :
    squareRootEndpoint R / A < R := by
  rcases Finset.mem_image.mp hA with ⟨y, hy, hyA⟩
  have h := (lowWheelFrozenSecondContact_source_lowerScaleExit hy).2.2
  change squareRootEndpoint R / lowWheelFrozenSecondContactSourceScale y < R at h
  simpa [hyA] using h

/-- The actual full source fibre exhausts the independently defined rough
prefix. The reverse direction reconstructs an ordered physical cut. -/
theorem lowWheelFrozenCofactorSourceScaleFiber_image_eq_roughPrefix
    {R A : ℕ} (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R) :
    (lowWheelFrozenCofactorSourceScaleFiber R A).image (fun y => y.2.1) =
      lowWheelFrozenSourceRoughPrefix (canonicalLargestPrimeFactor A)
        (squareRootEndpoint R / A) := by
  have hApos : 0 < A := (Nat.zero_le R).trans_lt (lowWheelFrozenSourceScale_root_lt hA)
  have hBR := lowWheelFrozenSourceScale_cutoff_lt_root hA
  ext c
  constructor
  · rintro hc
    rcases Finset.mem_image.mp hc with ⟨y, hyF, rfl⟩
    rcases Finset.mem_filter.mp hyF with ⟨hy, hyA⟩
    have hs := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
    have hp : canonicalLargestPrimeFactor A = lowWheelTaggedDowncrossPivot y := by
      rw [← hyA]
      exact frozenSource_scale_largestPrime hy
    have hrough : RoughAbove (canonicalLargestPrimeFactor A) y.2.1 := by
      intro q hq
      rw [hp]
      exact lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_primeFactor hy hq
    have hprod := lowWheelFrozenProductOneFace_le_endpoint hy
    rw [frozenSource_productOne_eq_scale_mul_cofactor hy, hyA] at hprod
    have hcB : y.2.1 ≤ squareRootEndpoint R / A := by
      apply (Nat.le_div_iff_mul_le hApos).2
      simpa [Nat.mul_comm] using hprod
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hcB⟩,
      hs.2.2.2.1, hrough⟩
  · intro hc
    rcases Finset.mem_filter.mp hc with ⟨hcI, hcsq, hcrough⟩
    rcases Finset.mem_Icc.mp hcI with ⟨hc2, hcB⟩
    rcases Finset.mem_image.mp hA with ⟨y, hySecond, hyA⟩
    have hy := (Finset.mem_filter.mp hySecond).1
    have hs := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
    have ho := orderedEulerCutShape_of_mem_carrier
      (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hy)
    let p := lowWheelTaggedDowncrossPivot y
    let z : LowWheelTaggedDowncrossState := (y.1, (c, p))
    have hp : canonicalLargestPrimeFactor A = p := by
      rw [← hyA]
      exact frozenSource_scale_largestPrime hy
    have hrough : RoughAbove p c := by simpa [hp] using hcrough
    have hcOne : 1 ≤ c :=
      (show 1 ≤ 2 by norm_num).trans hc2
    have hzShape : OrderedEulerCutShape z := by
      refine ⟨hs.2.1, hcOne, hcsq,
        RoughAbove.not_dvd hs.2.1 hcOne hrough, ?_, hrough⟩
      intro q hq
      exact ⟨(ho.2.2.2.2.1 q hq).1,
        lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hq⟩
    have hpivot : lowWheelTaggedDowncrossPivot z = p :=
      orderedEulerCutShape_canonicalPivot hzShape
    have hzA : lowWheelFrozenSecondContactSourceScale z = A := by
      change lowWheelTaggedDowncrossPivot z * primeFaceProduct y.1 = A
      rw [hpivot]
      exact hyA
    have hzChild : orderedEulerCutChildInteger z ≤ squareRootEndpoint R := by
      change c * (p * primeFaceProduct y.1) ≤ squareRootEndpoint R
      have hbase : p * primeFaceProduct y.1 = A := hyA
      rw [hbase]
      exact (Nat.le_div_iff_mul_le hApos).1 hcB
    have hzSqrt := (orderedEulerCutChild_le_endpoint_iff hzShape).1 hzChild
    have hzBirth : orderedEulerCutBirthRoot z ≤ R := by
      change max (primeFaceProduct y.1)
        (max (c + 1) (Nat.sqrt (orderedEulerCutChildInteger z) + 1)) ≤ R
      exact max_le
        (lowWheelCanonicalRepeatedFrozenCofactor_faceProduct_le_root hy)
        (max_le (by omega) (by omega))
    have hzDeath : R < orderedEulerCutDeathRoot z := by
      change R < p * primeFaceProduct y.1
      exact lowWheelCanonicalRepeatedFrozenCofactor_facePivot_crosses_root hy
    have hzOrdered : z ∈ orderedEulerCutCarrier R :=
      mem_orderedEulerCutCarrier_iff_shape_lifetime.mpr
        ⟨hzShape, hzBirth, hzDeath⟩
    have hzFrozen := orderedEulerCut_mem_frozenCofactor_of_one_lt hzOrdered
      (by change 1 < c; omega)
    exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzFrozen, hzA⟩, rfl⟩

/-- Saturation at fixed `A`, including the exact strict second-contact wall. -/
theorem lowWheelFrozenSecondContactSourceScaleCofactors_eq_roughPrefix_filter
    {R A : ℕ} (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R) :
    lowWheelFrozenSecondContactSourceScaleCofactors R A =
      (lowWheelFrozenSourceRoughPrefix (canonicalLargestPrimeFactor A)
        (squareRootEndpoint R / A)).filter fun c =>
          squareRootEndpoint R / A < canonicalLargestPrimeFactor c * c := by
  have hApos : 0 < A := (Nat.zero_le R).trans_lt (lowWheelFrozenSourceScale_root_lt hA)
  ext c
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨y, hyF, rfl⟩
    rcases mem_lowWheelFrozenSecondContactSourceScaleFiber.mp hyF with ⟨hy, hyA⟩
    have hfull : y.2.1 ∈ (lowWheelFrozenCofactorSourceScaleFiber R A).image
        (fun z => z.2.1) :=
      Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hy).1, hyA⟩, rfl⟩
    rw [lowWheelFrozenCofactorSourceScaleFiber_image_eq_roughPrefix hA] at hfull
    have hwall := (lowWheelFrozenSecondContact_source_lowerScaleExit hy).2.1
    change squareRootEndpoint R / lowWheelFrozenSecondContactSourceScale y <
      canonicalLargestPrimeFactor y.2.1 * y.2.1 at hwall
    rw [hyA] at hwall
    exact Finset.mem_filter.mpr ⟨hfull, hwall⟩
  · intro hc
    rcases Finset.mem_filter.mp hc with ⟨hfull, hwall⟩
    rw [← lowWheelFrozenCofactorSourceScaleFiber_image_eq_roughPrefix hA] at hfull
    rcases Finset.mem_image.mp hfull with ⟨y, hyF, rfl⟩
    rcases Finset.mem_filter.mp hyF with ⟨hy, hyA⟩
    have hwallX := (Nat.div_lt_iff_lt_mul hApos).1 hwall
    have hySecond : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R := by
      apply Finset.mem_filter.mpr
      refine ⟨hy, ?_⟩
      change squareRootEndpoint R < canonicalLargestPrimeFactor y.2.1 *
        primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y)
      rw [frozenSource_productOne_eq_scale_mul_cofactor hy, hyA]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hwallX
    exact Finset.mem_image.mpr ⟨y,
      mem_lowWheelFrozenSecondContactSourceScaleFiber.mpr ⟨hySecond, hyA⟩, rfl⟩

/-- The full prefix is exactly the second-contact fibre plus the square
residual, with all signs or other cofactor weights preserved. -/
theorem lowWheelFrozenSourceRoughPrefix_sum_eq_secondContact_add_residual
    {R A : ℕ} (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R)
    (g : ℕ → ℂ) :
    (∑ c ∈ lowWheelFrozenSourceRoughPrefix (canonicalLargestPrimeFactor A)
        (squareRootEndpoint R / A), g c) =
      (∑ c ∈ lowWheelFrozenSecondContactSourceScaleCofactors R A, g c) +
        ∑ c ∈ lowWheelFrozenSourceSquareResidual (canonicalLargestPrimeFactor A)
          (squareRootEndpoint R / A), g c := by
  rw [lowWheelFrozenSecondContactSourceScaleCofactors_eq_roughPrefix_filter hA]
  symm
  simpa only [lowWheelFrozenSourceSquareResidual, Nat.not_lt] using
    (Finset.sum_filter_add_sum_filter_not
      (lowWheelFrozenSourceRoughPrefix (canonicalLargestPrimeFactor A)
        (squareRootEndpoint R / A))
      (fun c => squareRootEndpoint R / A < canonicalLargestPrimeFactor c * c) g)

/-- The complementary square residual has genuine half-scale support. -/
theorem lowWheelFrozenSourceSquareResidual_subset_halfScale (p B : ℕ) :
    lowWheelFrozenSourceSquareResidual p B ⊆ Finset.Icc 1 (B / 2) := by
  intro c hc
  rcases Finset.mem_filter.mp hc with ⟨hcFull, hcontact⟩
  have hcI := (Finset.mem_filter.mp hcFull).1
  have hc2 := (Finset.mem_Icc.mp hcI).1
  have hq2 := (canonicalLargestPrimeFactor_prime (by omega : 1 < c)).two_le
  have htwo : 2 * c ≤ B := (Nat.mul_le_mul_right c hq2).trans hcontact
  exact Finset.mem_Icc.mpr ⟨by omega,
    (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).2
      (by simpa [Nat.mul_comm] using htwo)⟩

/-! ## Signed rough-prefix cancellation inside the endpoint identity -/

/-- At fixed source scale, the cofactor itself still determines the source.
This extends the no-multiplicity statement from the second-contact subfibre to
the complete frozen rough-prefix fibre. -/
theorem lowWheelFrozenCofactorSourceScaleFiber_cofactor_injOn
    (R A : ℕ) :
    Set.InjOn (fun y : LowWheelTaggedDowncrossState => y.2.1)
      (lowWheelFrozenCofactorSourceScaleFiber R A :
        Set LowWheelTaggedDowncrossState) := by
  intro y hy z hz hcofactor
  have hyd := Finset.mem_filter.mp hy
  have hzd := Finset.mem_filter.mp hz
  have hchild : orderedEulerCutChildInteger y = orderedEulerCutChildInteger z := by
    calc
      orderedEulerCutChildInteger y =
          lowWheelFrozenSecondContactSourceScale y * y.2.1 :=
        frozenSource_child_eq_scale_mul_cofactor hyd.1
      _ = A * y.2.1 := by rw [hyd.2]
      _ = A * z.2.1 := congrArg (fun c : ℕ => A * c) hcofactor
      _ = lowWheelFrozenSecondContactSourceScale z * z.2.1 := by rw [hzd.2]
      _ = orderedEulerCutChildInteger z :=
        (frozenSource_child_eq_scale_mul_cofactor hzd.1).symm
  exact orderedEulerCutChildInteger_injective_on_carrier
    (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hyd.1)
    (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hzd.1)
    hchild

/-- The complete fixed-`A` frozen source is exactly `-mu(A)` times the signed
Möbius mass of its rough prefix. -/
theorem lowWheelFrozenCofactorSourceScaleFiber_sum_eq_roughPrefix
    {R A : ℕ} (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R) :
    (∑ y ∈ lowWheelFrozenCofactorSourceScaleFiber R A,
        lowWheelTaggedDowncrossWeight y) =
      -(canonicalMoebiusWeight A *
        ∑ c ∈ lowWheelFrozenSourceRoughPrefix (canonicalLargestPrimeFactor A)
          (squareRootEndpoint R / A), canonicalMoebiusWeight c) := by
  have hcofactorSum :
      (∑ y ∈ lowWheelFrozenCofactorSourceScaleFiber R A,
          canonicalMoebiusWeight y.2.1) =
        ∑ c ∈ lowWheelFrozenSourceRoughPrefix (canonicalLargestPrimeFactor A)
          (squareRootEndpoint R / A), canonicalMoebiusWeight c := by
    rw [← lowWheelFrozenCofactorSourceScaleFiber_image_eq_roughPrefix hA]
    rw [Finset.sum_image]
    intro y hy z hz heq
    exact lowWheelFrozenCofactorSourceScaleFiber_cofactor_injOn R A hy hz heq
  calc
    (∑ y ∈ lowWheelFrozenCofactorSourceScaleFiber R A,
        lowWheelTaggedDowncrossWeight y) =
      ∑ y ∈ lowWheelFrozenCofactorSourceScaleFiber R A,
        -(canonicalMoebiusWeight A * canonicalMoebiusWeight y.2.1) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyd := Finset.mem_filter.mp hy
      calc
        lowWheelTaggedDowncrossWeight y =
            -(canonicalMoebiusWeight
                (lowWheelFrozenSecondContactSourceScale y) *
              canonicalMoebiusWeight y.2.1) :=
          frozenSource_weight_eq hyd.1
        _ = -(canonicalMoebiusWeight A * canonicalMoebiusWeight y.2.1) := by
          rw [hyd.2]
    _ = -(canonicalMoebiusWeight A *
        ∑ y ∈ lowWheelFrozenCofactorSourceScaleFiber R A,
          canonicalMoebiusWeight y.2.1) := by
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
    _ = -(canonicalMoebiusWeight A *
        ∑ c ∈ lowWheelFrozenSourceRoughPrefix (canonicalLargestPrimeFactor A)
          (squareRootEndpoint R / A), canonicalMoebiusWeight c) := by
      rw [hcofactorSum]

/-- Signed mass of the actual product-one transport partners at one source
scale. Every term is already proved to lie in the historical fixed part. -/
def lowWheelFrozenSourceScaleTransportMass (R A : ℕ) : ℂ :=
  ∑ z ∈ lowWheelFrozenSourceScaleTransportCarrier R A,
    lowWheelTaggedCanonicalWeight z

/-- The fixed transport mass at scale `A` is `mu(A)` times the complete rough
prefix. This is the opposite charge to the full frozen source fibre. -/
theorem lowWheelFrozenSourceScaleTransportMass_eq_roughPrefix
    {R A : ℕ} (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R) :
    lowWheelFrozenSourceScaleTransportMass R A =
      canonicalMoebiusWeight A *
        ∑ c ∈ lowWheelFrozenSourceRoughPrefix (canonicalLargestPrimeFactor A)
          (squareRootEndpoint R / A), canonicalMoebiusWeight c := by
  unfold lowWheelFrozenSourceScaleTransportMass
  rw [lowWheelFrozenSourceScaleTransportCarrier_sum_image R A
    lowWheelTaggedCanonicalWeight]
  calc
    (∑ y ∈ lowWheelFrozenCofactorSourceScaleFiber R A,
        lowWheelTaggedCanonicalWeight
          (lowWheelCanonicalRepeatedFrozenProductOneMate y)) =
      ∑ y ∈ lowWheelFrozenCofactorSourceScaleFiber R A,
        -lowWheelTaggedDowncrossWeight y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact lowWheelCanonicalRepeatedFrozenProductOneMate_taggedWeight_neg
        (Finset.mem_filter.mp hy).1
    _ = -(∑ y ∈ lowWheelFrozenCofactorSourceScaleFiber R A,
        lowWheelTaggedDowncrossWeight y) := by
      rw [Finset.sum_neg_distrib]
    _ = canonicalMoebiusWeight A *
        ∑ c ∈ lowWheelFrozenSourceRoughPrefix (canonicalLargestPrimeFactor A)
          (squareRootEndpoint R / A), canonicalMoebiusWeight c := by
      rw [lowWheelFrozenCofactorSourceScaleFiber_sum_eq_roughPrefix hA]
      ring

/-- Signed square-residual charge left at one source scale after the historical
fixed transport cancels the entire rough prefix against the second-contact
source. -/
def lowWheelFrozenSecondContactSquareResidualMassAtScale (R A : ℕ) : ℂ :=
  canonicalMoebiusWeight A *
    ∑ c ∈ lowWheelFrozenSourceSquareResidual (canonicalLargestPrimeFactor A)
      (squareRootEndpoint R / A), canonicalMoebiusWeight c

/-- **Fixed-scale cancellation identity.** The genuine second-contact source
plus its existing fixed transport partners is exactly the signed square
residual. No norm has been taken; the outer `mu(A)` sign is retained. -/
theorem lowWheelFrozenSecondContactSourceScale_add_transport_eq_squareResidual
    {R A : ℕ} (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R) :
    (∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
        lowWheelTaggedDowncrossWeight y) +
      lowWheelFrozenSourceScaleTransportMass R A =
        lowWheelFrozenSecondContactSquareResidualMassAtScale R A := by
  have hsource :
      (∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
          lowWheelTaggedDowncrossWeight y) =
        -(canonicalMoebiusWeight A *
          lowWheelFrozenSecondContactSourceScaleCofactorMass R A) := by
    simpa [lowWheelTaggedDowncrossWeight] using
      (lowWheelFrozenSecondContactSourceScaleFiber_sum_eq R A)
  have htransport := lowWheelFrozenSourceScaleTransportMass_eq_roughPrefix hA
  have hpartition :
      (∑ c ∈ lowWheelFrozenSourceRoughPrefix (canonicalLargestPrimeFactor A)
          (squareRootEndpoint R / A), canonicalMoebiusWeight c) =
        lowWheelFrozenSecondContactSourceScaleCofactorMass R A +
          ∑ c ∈ lowWheelFrozenSourceSquareResidual (canonicalLargestPrimeFactor A)
            (squareRootEndpoint R / A), canonicalMoebiusWeight c := by
    simpa [lowWheelFrozenSecondContactSourceScaleCofactorMass] using
      (lowWheelFrozenSourceRoughPrefix_sum_eq_secondContact_add_residual
        hA canonicalMoebiusWeight)
  rw [hsource, htransport, hpartition]
  unfold lowWheelFrozenSecondContactSquareResidualMassAtScale
  ring

/-- Matching historical fixed transport mass, with the outer source-scale sum
left signed. -/
def lowWheelFrozenSecondContactMatchingFixedTransportMass (R : ℕ) : ℂ :=
  ∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
    lowWheelFrozenSourceScaleTransportMass R A

/-- Global signed square-residual mass. Each inner residual is supported below
half of its strict lower cutoff, but no separate absolute values are taken. -/
def lowWheelFrozenSecondContactSquareResidualMass (R : ℕ) : ℂ :=
  ∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
    lowWheelFrozenSecondContactSquareResidualMassAtScale R A

/-- **Common signed carrier identity.** Globally, second-contact source charge
plus its already-existing fixed transport charge collapses exactly to the
half-scale square residual, while the source-scale sum stays signed. -/
theorem lowWheelFrozenSecondContactSource_add_matchingFixedTransport_eq_squareResidual
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
        lowWheelTaggedDowncrossWeight y) +
      lowWheelFrozenSecondContactMatchingFixedTransportMass R =
        lowWheelFrozenSecondContactSquareResidualMass R := by
  have hsource :
      (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
          lowWheelTaggedDowncrossWeight y) =
        ∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
          ∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
            lowWheelTaggedDowncrossWeight y := by
    simpa [lowWheelTaggedDowncrossWeight] using
      (lowWheelFrozenSecondContactSource_sum_eq_sourceScaleFibers R)
  rw [hsource]
  unfold lowWheelFrozenSecondContactMatchingFixedTransportMass
    lowWheelFrozenSecondContactSquareResidualMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  exact lowWheelFrozenSecondContactSourceScale_add_transport_eq_squareResidual hA

/-- Algebraic remainder of the historical endpoint transport after isolating
the matching fixed transport mass and the frozen second-contact source charge. -/
def lowWheelFrozenSecondContactEndpointRest (R : ℕ) : ℂ :=
  (lowWheelCanonicalFixedLedger R -
      lowWheelFrozenSecondContactMatchingFixedTransportMass R) +
    (lowWheelCanonicalDefectLedger R -
      ∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
        lowWheelTaggedDowncrossWeight y)

/-- **Endpoint insertion of the new cancellation.** The original exact
`smooth - transport` endpoint can be rewritten as the algebraic rest plus the
new globally signed square residual. Thus the cancellation is now connected to
the same endpoint identity used by `S = A - T`, rather than living on a
separate coordinate system. -/
theorem squarePrefixMertens_eq_smooth_sub_secondContactEndpointRest_add_residual
    (R : ℕ) (hR : 3 ≤ R) :
    squarePrefixMertens (R - 1) =
      squareRootSmoothMass (R - 1) -
        (lowWheelFrozenSecondContactEndpointRest R +
          lowWheelFrozenSecondContactSquareResidualMass R) := by
  rw [squarePrefixMertens_eq_squareRootSmooth_sub_transport,
    squareRootTransportMass_pred_eq_cofactorFirst R (by omega),
    squareRootTransportCofactorFirst_eq_canonicalPhysicalLedger R (by omega),
    lowWheelCanonicalPhysicalLedger_eq_fixed_add_defect R]
  unfold lowWheelFrozenSecondContactEndpointRest
  rw [← lowWheelFrozenSecondContactSource_add_matchingFixedTransport_eq_squareResidual R]
  ring

end RHLean.Proof