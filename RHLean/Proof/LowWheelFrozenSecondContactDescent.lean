import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedFrozenFactorGeometry
import RHLean.Proof.LowWheelFrozenCofactorTopBottomToggle
import RHLean.Proof.LowWheelFaceTailToggle
import RHLean.Proof.ComplexVerticalFiberSpacing
import RHLean.Proof.OneBlockInvariant
import RHLean.Proof.SquareRootLowPrimeFirstOwnerWallRecurrence

/-!
# Frozen second-contact descent

A frozen repeated state with nontrivial cofactor has already been moved, without
changing its represented integer, to the product-one Boolean face

`U = {p} ∪ t ∪ primeFactors(c)`.

This file does not stop at that same-scale realization.  Let `q = P+(c)` be the
largest prime of the frozen cofactor and erase `q` from `U`.  The resulting
predecessor face `V = U \\ {q}` satisfies

`q * P(V) = P(U)`.

On the genuine second-contact residue the endpoint inequalities are therefore

`q * P(V) <= X_R < q^2 * P(V)`,

so `P(V)` lies in the strict lower-scale annulus

`X_R / q^2 < P(V) <= X_R / q`.

All primes in `V` are strictly below `q`, hence this is a signed carrier in the
frozen predecessor universe `primesUpTo (q-1)`.  Erasing `q` reverses the
Boolean sign once, exactly undoing the sign reversal of the product-one mate;
the predecessor face therefore carries the original frozen source sign.

Finally, the map `y |-> (q,V)` is injective on the second-contact population.
The proof is non-circular: equality of `(q,V)` gives equality of the represented
physical child, and the already-proved ordered-Euler-cut uniqueness theorem
recovers the unique active source occurrence at root `R`.

No norm, density estimate, PNT input, Mertens hypothesis, or RH-scale bound is
used.  The target endpoint is strictly smaller than `X_R` by division by the
prime `q >= 2`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open LowWheelCanonicalDowncrossOwnership

attribute [local instance] Classical.propDecidable

abbrev LowWheelFrozenSecondContactParentState := ℕ × Finset ℕ

/-- Frozen nontrivial-cofactor states for which the doubly-adjoined largest
cofactor prime crosses the square endpoint.  This is the global source version
of the `p^2*n` defect isolated by the mixed double-cube cell. -/
def lowWheelCanonicalRepeatedFrozenSecondContactPart (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalRepeatedFrozenCofactorPart R).filter fun y =>
    squareRootEndpoint R <
      lowWheelFrozenCofactorTopPrime y *
        primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y)

/-- Erase the largest frozen cofactor prime from the complete product-one face. -/
def lowWheelFrozenSecondContactParentFace
    (y : LowWheelTaggedDowncrossState) : Finset ℕ :=
  (lowWheelCanonicalRepeatedFrozenProductOneFace y).erase
    (lowWheelFrozenCofactorTopPrime y)

/-- Owner together with the strict predecessor face. -/
def lowWheelFrozenSecondContactParentMap
    (y : LowWheelTaggedDowncrossState) : LowWheelFrozenSecondContactParentState :=
  (lowWheelFrozenCofactorTopPrime y,
    lowWheelFrozenSecondContactParentFace y)

/-- Independent finite target carrier.  It is not defined as an image of the
source: one chooses a prime owner `q<R`, a Boolean face using only primes below
`q`, and the literal square-dilated annulus `q*P(V) <= X_R < q^2*P(V)`. -/
def lowWheelFrozenSecondContactParentCarrier (R : ℕ) :
    Finset LowWheelFrozenSecondContactParentState :=
  (((Finset.Icc 2 (R - 1)).product (primesUpTo R).powerset).filter fun z =>
    z.1.Prime ∧
      z.2 ∈ (primesUpTo (z.1 - 1)).powerset ∧
      z.1 * primeFaceProduct z.2 ≤ squareRootEndpoint R ∧
      squareRootEndpoint R < z.1 * z.1 * primeFaceProduct z.2)

/-- Native signed weight on the smaller predecessor face. -/
def lowWheelFrozenSecondContactParentWeight
    (z : LowWheelFrozenSecondContactParentState) : ℂ :=
  (booleanCubeSign z.2 : ℂ)

@[simp] theorem mem_lowWheelFrozenSecondContactParentCarrier
    {R : ℕ} {z : LowWheelFrozenSecondContactParentState} :
    z ∈ lowWheelFrozenSecondContactParentCarrier R ↔
      z.1 ∈ Finset.Icc 2 (R - 1) ∧
      z.2 ∈ (primesUpTo R).powerset ∧
      z.1.Prime ∧
      z.2 ∈ (primesUpTo (z.1 - 1)).powerset ∧
      z.1 * primeFaceProduct z.2 ≤ squareRootEndpoint R ∧
      squareRootEndpoint R < z.1 * z.1 * primeFaceProduct z.2 := by
  simp [lowWheelFrozenSecondContactParentCarrier, and_assoc]

/-- The largest cofactor prime is literally present in the complete product-one
face. -/
theorem lowWheelFrozenSecondContact_owner_mem_productOneFace
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelFrozenCofactorTopPrime y ∈
      lowWheelCanonicalRepeatedFrozenProductOneFace y := by
  rcases lowWheelFrozenCofactorTopPrime_data hy with
    ⟨hqPrime, hqDvd, _hpq⟩
  rcases lowWheelCanonicalRepeatedFrozenCofactor_source_data hy with
    ⟨_hk, _hpPrime, _hpNotC, _hsq, hcgt, _hcR⟩
  have hc0 : y.2.1 ≠ 0 := by omega
  have hqFactors : lowWheelFrozenCofactorTopPrime y ∈ y.2.1.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hqPrime, hqDvd, hc0⟩
  unfold lowWheelCanonicalRepeatedFrozenProductOneFace
  apply Finset.mem_insert.mpr
  right
  apply Finset.mem_union.mpr
  right
  simpa [squarefreePrimeFace] using hqFactors

/-- Erasing the owner is an exact factorization of the old physical integer. -/
theorem lowWheelFrozenSecondContact_owner_mul_parentFaceProduct
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelFrozenCofactorTopPrime y *
        primeFaceProduct (lowWheelFrozenSecondContactParentFace y) =
      primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) := by
  unfold lowWheelFrozenSecondContactParentFace
  exact primeFaceProduct_erase_mul
    (lowWheelFrozenSecondContact_owner_mem_productOneFace hy)

/-- Every prime retained in the predecessor face is strictly below its owner. -/
theorem lowWheelFrozenSecondContactParentFace_prime_lt_owner
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R)
    {r : ℕ} (hr : r ∈ lowWheelFrozenSecondContactParentFace y) :
    r.Prime ∧ r < lowWheelFrozenCofactorTopPrime y := by
  have hrErase := Finset.mem_erase.mp hr
  have hrFull := hrErase.2
  unfold lowWheelCanonicalRepeatedFrozenProductOneFace at hrFull
  rcases Finset.mem_insert.mp hrFull with hpivot | hrest
  · subst r
    have hsource := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
    have htop := lowWheelFrozenCofactorTopPrime_data hy
    exact ⟨hsource.2.1, htop.2.2⟩
  · rcases Finset.mem_union.mp hrest with hface | hcofactor
    · have hfrozen := (Finset.mem_filter.mp hy).1
      have hrepeated := (Finset.mem_filter.mp hfrozen).1
      have htagged := (Finset.mem_filter.mp hrepeated).1
      have ht := (mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged).1
      have hrGlobal := (Finset.mem_powerset.mp ht) hface
      have hrPrime := prime_of_mem_primesUpTo hrGlobal
      have hrp :=
        lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hface
      have hpq := (lowWheelFrozenCofactorTopPrime_data hy).2.2
      exact ⟨hrPrime, hrp.trans hpq⟩
    · have hrFactors : r ∈ y.2.1.primeFactors := by
        simpa [squarefreePrimeFace] using hcofactor
      have hrPrime := (Nat.mem_primeFactors.mp hrFactors).1
      have hcgt :=
        (lowWheelCanonicalRepeatedFrozenCofactor_source_data hy).2.2.2.2.1
      have hrLe : r ≤ canonicalLargestPrimeFactor y.2.1 :=
        primeFactor_le_canonicalLargestPrimeFactor hcgt hrFactors
      have hrLeOwner : r ≤ lowWheelFrozenCofactorTopPrime y := by
        simpa [lowWheelFrozenCofactorTopPrime] using hrLe
      exact ⟨hrPrime, by omega⟩

/-- The predecessor face belongs to the frozen prime universe immediately
before the owner. -/
theorem lowWheelFrozenSecondContactParentFace_mem_predecessor
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelFrozenSecondContactParentFace y ∈
      (primesUpTo (lowWheelFrozenCofactorTopPrime y - 1)).powerset := by
  apply Finset.mem_powerset.mpr
  intro r hr
  have hdata := lowWheelFrozenSecondContactParentFace_prime_lt_owner hy hr
  exact mem_primesUpTo.mpr ⟨hdata.1, by omega⟩

/-- The complete product-one face is still under the physical square endpoint. -/
theorem lowWheelFrozenProductOneFace_le_endpoint
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) ≤
      squareRootEndpoint R := by
  have hm := lowWheelCanonicalRepeatedFrozenProductOneMate_mem_physical hy
  have hdata := mem_lowWheelCanonicalPhysicalStateSet.mp hm
  have hpair := hdata.2.2.2
  simpa using hpair.2.2.2

/-- A frozen source is already an oriented Euler cut.  This bridge lets the
existing uniqueness theorem certify injectivity of the smaller-scale map rather
than re-proving root-window uniqueness. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    y ∈ orderedEulerCutCarrier R := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged with ⟨ht, hx⟩
  rw [mem_orderedEulerCutCarrier]
  refine ⟨ht, mem_lowWheelCanonicalDowncrossOrientedPart.mpr ⟨hx, ?_⟩⟩
  intro r hr
  have hsource := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have hquot :
      y.2.2 / lowWheelCanonicalDowncrossPivot y.2 = 1 := by
    rw [hsource.1]
    exact Nat.div_self hsource.2.1.pos
  have hparent :
      LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossParent y.1 y.2 =
        primeFaceProduct y.1 := by
    unfold LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossParent
    rw [hquot, Nat.mul_one]
  rw [hparent] at hr
  have hrData := Nat.mem_primeFactors.mp hr
  have hrDvd : r ∣ y.1.prod id := by
    simpa [primeFaceProduct] using hrData.2.1
  rcases (Prime.dvd_finset_prod_iff hrData.1.prime id).mp hrDvd with
    ⟨s, hs, hrs⟩
  have hsGlobal := (Finset.mem_powerset.mp ht) hs
  have hsPrime := prime_of_mem_primesUpTo hsGlobal
  have hre : r = s :=
    (Nat.prime_dvd_prime_iff_eq hrData.1 hsPrime).mp hrs
  subst r
  simpa [lowWheelTaggedDowncrossPivot] using
    (lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hs)

/-- The physical child of the frozen source is exactly `owner * predecessor`. -/
theorem lowWheelFrozenSecondContact_child_eq_owner_mul_parentProduct
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    orderedEulerCutChildInteger y =
      lowWheelFrozenCofactorTopPrime y *
        primeFaceProduct (lowWheelFrozenSecondContactParentFace y) := by
  have hsource := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have hfull := lowWheelCanonicalRepeatedFrozenProductOneFace_product hy
  have herase := lowWheelFrozenSecondContact_owner_mul_parentFaceProduct hy
  calc
    orderedEulerCutChildInteger y =
        y.2.1 * (lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1) := by
      simp only [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
        orderedEulerCutPivot, orderedEulerCutLowProduct]
      rw [hsource.1]
    _ = y.2.1 * lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := by ring
    _ = primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) :=
      hfull.symm
    _ = lowWheelFrozenCofactorTopPrime y *
        primeFaceProduct (lowWheelFrozenSecondContactParentFace y) := herase.symm

/-- **Strict predecessor annulus.**  Every genuine frozen second-contact source
lands in the independent target carrier. -/
theorem lowWheelFrozenSecondContactParentMap_mem
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    lowWheelFrozenSecondContactParentMap y ∈
      lowWheelFrozenSecondContactParentCarrier R := by
  rcases Finset.mem_filter.mp hy with ⟨hyFrozen, hsecond⟩
  rcases lowWheelFrozenCofactorTopPrime_data hyFrozen with
    ⟨hqPrime, hqDvd, _hpq⟩
  have hsource := lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen
  have hqLeC : lowWheelFrozenCofactorTopPrime y ≤ y.2.1 :=
    Nat.le_of_dvd (by omega) hqDvd
  have hqR : lowWheelFrozenCofactorTopPrime y < R :=
    hqLeC.trans_lt hsource.2.2.2.2.2
  have hqRange : lowWheelFrozenCofactorTopPrime y ∈ Finset.Icc 2 (R - 1) :=
    Finset.mem_Icc.mpr ⟨hqPrime.two_le, by omega⟩
  have hpred := lowWheelFrozenSecondContactParentFace_mem_predecessor hyFrozen
  have hpredR : lowWheelFrozenSecondContactParentFace y ∈
      (primesUpTo R).powerset := by
    apply Finset.mem_powerset.mpr
    intro r hr
    have hrData := lowWheelFrozenSecondContactParentFace_prime_lt_owner hyFrozen hr
    exact mem_primesUpTo.mpr ⟨hrData.1, (hrData.2.trans hqR).le⟩
  have herase := lowWheelFrozenSecondContact_owner_mul_parentFaceProduct hyFrozen
  have hlow : lowWheelFrozenCofactorTopPrime y *
        primeFaceProduct (lowWheelFrozenSecondContactParentFace y) ≤
      squareRootEndpoint R := by
    rw [herase]
    exact lowWheelFrozenProductOneFace_le_endpoint hyFrozen
  have hhigh : squareRootEndpoint R <
      lowWheelFrozenCofactorTopPrime y * lowWheelFrozenCofactorTopPrime y *
        primeFaceProduct (lowWheelFrozenSecondContactParentFace y) := by
    calc
      squareRootEndpoint R <
          lowWheelFrozenCofactorTopPrime y *
            primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) :=
        hsecond
      _ = lowWheelFrozenCofactorTopPrime y *
          (lowWheelFrozenCofactorTopPrime y *
            primeFaceProduct (lowWheelFrozenSecondContactParentFace y)) := by
        rw [herase]
      _ = lowWheelFrozenCofactorTopPrime y * lowWheelFrozenCofactorTopPrime y *
          primeFaceProduct (lowWheelFrozenSecondContactParentFace y) := by ring
  rw [mem_lowWheelFrozenSecondContactParentCarrier]
  exact ⟨hqRange, hpredR, hqPrime, hpred, hlow, hhigh⟩

/-- The smaller predecessor face carries exactly the original frozen source
sign.  The product-one transfer flips once and erasing the owner flips back. -/
theorem lowWheelFrozenSecondContactParentMap_weight_eq_source
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelFrozenSecondContactParentWeight
        (lowWheelFrozenSecondContactParentMap y) =
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) := by
  have hqmem := lowWheelFrozenSecondContact_owner_mem_productOneFace hy
  have heraseZ := booleanCubeSign_erase_eq_neg hqmem
  have heraseC :
      (booleanCubeSign
          (lowWheelFrozenSecondContactParentFace y) : ℂ) =
        -(booleanCubeSign
          (lowWheelCanonicalRepeatedFrozenProductOneFace y) : ℂ) := by
    exact_mod_cast heraseZ
  have hmate :
      (booleanCubeSign
          (lowWheelCanonicalRepeatedFrozenProductOneFace y) : ℂ) =
        -(canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) := by
    simpa [canonicalMoebiusWeight] using
      (lowWheelCanonicalRepeatedFrozenProductOneMate_weight_neg hy)
  unfold lowWheelFrozenSecondContactParentWeight
    lowWheelFrozenSecondContactParentMap
  dsimp
  calc
    (booleanCubeSign (lowWheelFrozenSecondContactParentFace y) : ℂ) =
        -(booleanCubeSign
          (lowWheelCanonicalRepeatedFrozenProductOneFace y) : ℂ) := heraseC
    _ = canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) := by
      rw [hmate]
      simp

/-- **Non-circular injection into the lower-scale signed carrier.**  The pair
`(q,V)` reconstructs the physical child `q*P(V)`.  Active ordered Euler cuts are
already injective by physical child, so two frozen second-contact sources with
the same lower-scale target are equal. -/
theorem lowWheelFrozenSecondContactParentMap_injOn (R : ℕ) :
    Set.InjOn lowWheelFrozenSecondContactParentMap
      (lowWheelCanonicalRepeatedFrozenSecondContactPart R :
        Set LowWheelTaggedDowncrossState) := by
  intro y hy z hz hmap
  have hyFrozen := (Finset.mem_filter.mp hy).1
  have hzFrozen := (Finset.mem_filter.mp hz).1
  have htarget :
      lowWheelFrozenCofactorTopPrime y *
          primeFaceProduct (lowWheelFrozenSecondContactParentFace y) =
        lowWheelFrozenCofactorTopPrime z *
          primeFaceProduct (lowWheelFrozenSecondContactParentFace z) := by
    simpa [lowWheelFrozenSecondContactParentMap] using
      congrArg
        (fun a : LowWheelFrozenSecondContactParentState =>
          a.1 * primeFaceProduct a.2) hmap
  have hchild : orderedEulerCutChildInteger y = orderedEulerCutChildInteger z := by
    rw [lowWheelFrozenSecondContact_child_eq_owner_mul_parentProduct hyFrozen,
      lowWheelFrozenSecondContact_child_eq_owner_mul_parentProduct hzFrozen]
    exact htarget
  exact orderedEulerCutChildInteger_injective_on_carrier
    (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hyFrozen)
    (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hzFrozen)
    hchild

/-- The multiplication-shell target is literally the nested reciprocal annulus
`X/q^2 < P(V) <= X/q`. -/
theorem lowWheelFrozenSecondContactParentMap_division_annulus
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    squareRootEndpoint R /
        (lowWheelFrozenCofactorTopPrime y * lowWheelFrozenCofactorTopPrime y) <
      primeFaceProduct (lowWheelFrozenSecondContactParentFace y) ∧
    primeFaceProduct (lowWheelFrozenSecondContactParentFace y) ≤
      squareRootEndpoint R / lowWheelFrozenCofactorTopPrime y := by
  rcases Finset.mem_filter.mp hy with ⟨hyFrozen, _hsecond⟩
  have hqPrime := (lowWheelFrozenCofactorTopPrime_data hyFrozen).1
  have hmem := lowWheelFrozenSecondContactParentMap_mem hy
  rw [mem_lowWheelFrozenSecondContactParentCarrier] at hmem
  have hlow :
      lowWheelFrozenCofactorTopPrime y *
          primeFaceProduct (lowWheelFrozenSecondContactParentFace y) ≤
        squareRootEndpoint R := by
    simpa [lowWheelFrozenSecondContactParentMap] using hmem.2.2.2.2.1
  have hhigh :
      squareRootEndpoint R <
        lowWheelFrozenCofactorTopPrime y * lowWheelFrozenCofactorTopPrime y *
          primeFaceProduct (lowWheelFrozenSecondContactParentFace y) := by
    simpa [lowWheelFrozenSecondContactParentMap] using hmem.2.2.2.2.2
  constructor
  · apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hqPrime.pos hqPrime.pos)).2
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hhigh
  · apply (Nat.le_div_iff_mul_le hqPrime.pos).2
    simpa [Nat.mul_comm] using hlow

/-- **Strict endpoint descent.**  Both reciprocal cutoffs used by the target are
strictly below the source endpoint, and the square-dilated cutoff is strictly
below the one-prime cutoff. -/
theorem lowWheelFrozenSecondContactParentMap_strict_endpoint_descent
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    squareRootEndpoint R /
        (lowWheelFrozenCofactorTopPrime y * lowWheelFrozenCofactorTopPrime y) <
      squareRootEndpoint R / lowWheelFrozenCofactorTopPrime y ∧
    squareRootEndpoint R / lowWheelFrozenCofactorTopPrime y <
      squareRootEndpoint R := by
  rcases Finset.mem_filter.mp hy with ⟨hyFrozen, _hsecond⟩
  have hXpos : 0 < squareRootEndpoint R := by
    have hqPrime := (lowWheelFrozenCofactorTopPrime_data hyFrozen).1
    have hmem := lowWheelFrozenSecondContactParentMap_mem hy
    rw [mem_lowWheelFrozenSecondContactParentCarrier] at hmem
    have hlow : lowWheelFrozenCofactorTopPrime y *
        primeFaceProduct (lowWheelFrozenSecondContactParentFace y) ≤
        squareRootEndpoint R := by
      simpa [lowWheelFrozenSecondContactParentMap] using hmem.2.2.2.2.1
    have hfacePos :=
      primeFaceProduct_pos_of_mem_powerset
        (lowWheelFrozenSecondContactParentFace_mem_predecessor hyFrozen)
    exact lt_of_lt_of_le (Nat.mul_pos hqPrime.pos hfacePos) hlow
  have hqPrime := (lowWheelFrozenCofactorTopPrime_data hyFrozen).1
  have hdivlt : squareRootEndpoint R / lowWheelFrozenCofactorTopPrime y <
      squareRootEndpoint R :=
    Nat.div_lt_self hXpos hqPrime.one_lt
  have hann := lowWheelFrozenSecondContactParentMap_division_annulus hy
  have hpred := lowWheelFrozenSecondContactParentFace_mem_predecessor hyFrozen
  have hfacePos : 0 < primeFaceProduct (lowWheelFrozenSecondContactParentFace y) :=
    primeFaceProduct_pos_of_mem_powerset hpred
  have hdivPos : 0 < squareRootEndpoint R / lowWheelFrozenCofactorTopPrime y :=
    lt_of_lt_of_le hfacePos hann.2
  have hsqdrop :
      (squareRootEndpoint R / lowWheelFrozenCofactorTopPrime y) /
          lowWheelFrozenCofactorTopPrime y <
        squareRootEndpoint R / lowWheelFrozenCofactorTopPrime y :=
    Nat.div_lt_self hdivPos hqPrime.one_lt
  have hdivdiv :
      (squareRootEndpoint R / lowWheelFrozenCofactorTopPrime y) /
          lowWheelFrozenCofactorTopPrime y =
        squareRootEndpoint R /
          (lowWheelFrozenCofactorTopPrime y * lowWheelFrozenCofactorTopPrime y) := by
    exact Nat.div_div_eq_div_mul _ _ _
  rw [hdivdiv] at hsqdrop
  exact ⟨hsqdrop, hdivlt⟩

/-! ## Native Go frozen-window handoff -/

/-- The native frozen predecessor window at one second-contact owner. -/
def lowWheelFrozenSecondContactOwnerWindow
    (R q : ℕ) : Finset (Finset ℕ) :=
  frozenPrimeUniverseWindowFaces
    (primesUpTo (q - 1))
    (squareRootEndpoint R / (q * q))
    (squareRootEndpoint R / q)

/-- **Carrier identification.**  At a genuine prime owner below the root, the
independently-defined target is exactly the native frozen Go window. -/
theorem mem_lowWheelFrozenSecondContactParentCarrier_iff_ownerWindow
    {R q : ℕ} {V : Finset ℕ}
    (hq : q.Prime) (hqR : q < R) :
    (q, V) ∈ lowWheelFrozenSecondContactParentCarrier R ↔
      V ∈ lowWheelFrozenSecondContactOwnerWindow R q := by
  constructor
  · intro hz
    rcases mem_lowWheelFrozenSecondContactParentCarrier.mp hz with
      ⟨_hqRange, _hVR, _hqPrime, hpred, hupperMul, hlowerMul⟩
    apply mem_frozenPrimeUniverseWindowFaces.mpr
    refine ⟨hpred, ?_, ?_⟩
    · apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hq.pos hq.pos)).2
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hlowerMul
    · apply (Nat.le_div_iff_mul_le hq.pos).2
      simpa [Nat.mul_comm] using hupperMul
  · intro hV
    rcases mem_frozenPrimeUniverseWindowFaces.mp hV with
      ⟨hpred, hlower, hupper⟩
    have hqRange : q ∈ Finset.Icc 2 (R - 1) :=
      Finset.mem_Icc.mpr ⟨hq.two_le, by omega⟩
    have hVR : V ∈ (primesUpTo R).powerset := by
      apply Finset.mem_powerset.mpr
      intro r hr
      have hrPred := (Finset.mem_powerset.mp hpred) hr
      rcases mem_primesUpTo.mp hrPred with ⟨hrPrime, hrq⟩
      exact mem_primesUpTo.mpr ⟨hrPrime, by omega⟩
    have hupperMul : q * primeFaceProduct V ≤ squareRootEndpoint R := by
      have h := (Nat.le_div_iff_mul_le hq.pos).1 hupper
      simpa [Nat.mul_comm] using h
    have hlowerMul : squareRootEndpoint R < q * q * primeFaceProduct V := by
      have h := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hq.pos hq.pos)).1 hlower
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
    apply mem_lowWheelFrozenSecondContactParentCarrier.mpr
    exact ⟨hqRange, hVR, hq, hpred, hupperMul, hlowerMul⟩

/-- Every actual frozen second-contact source lands directly in the native Go
owner window, not merely in a newly named carrier. -/
theorem lowWheelFrozenSecondContactParentFace_mem_ownerWindow
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    lowWheelFrozenSecondContactParentFace y ∈
      lowWheelFrozenSecondContactOwnerWindow R
        (lowWheelFrozenCofactorTopPrime y) := by
  have hparent := lowWheelFrozenSecondContactParentMap_mem hy
  have hdata := mem_lowWheelFrozenSecondContactParentCarrier.mp hparent
  have hqPrime : (lowWheelFrozenCofactorTopPrime y).Prime := hdata.2.2.1
  have hqR : lowWheelFrozenCofactorTopPrime y < R := by
    have hqRange := Finset.mem_Icc.mp hdata.1
    have hqLe : lowWheelFrozenCofactorTopPrime y ≤ R - 1 := by
      simpa [lowWheelFrozenSecondContactParentMap] using hqRange.2
    omega
  apply (mem_lowWheelFrozenSecondContactParentCarrier_iff_ownerWindow
    hqPrime hqR).mp
  simpa [lowWheelFrozenSecondContactParentMap] using hparent

/-- Exact signed mass of the complete native owner window. -/
def lowWheelFrozenSecondContactOwnerWindowMass (R q : ℕ) : ℤ :=
  frozenPrimeUniverseWindowMass
    (primesUpTo (q - 1))
    (squareRootEndpoint R / (q * q))
    (squareRootEndpoint R / q)

/-- **Strict lower-scale signed handoff.**  One complete owner window is exactly
the difference of two frozen predecessor states, at the two cutoffs exposed by
the descent. -/
theorem lowWheelFrozenSecondContactOwnerWindowMass_eq_frozenDifference
    {R q : ℕ} (hq : q.Prime) :
    lowWheelFrozenSecondContactOwnerWindowMass R q =
      frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / q) -
        frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / (q * q)) := by
  unfold lowWheelFrozenSecondContactOwnerWindowMass
  apply frozenPrimeUniverseWindowMass_eq_sub
  exact Nat.div_le_div_left (by nlinarith [hq.two_le]) hq.pos

/-- The inherited one-prime cutoff is strictly below the source endpoint. -/
theorem lowWheelFrozenSecondContactOwnerWindow_upper_strict
    {R q : ℕ} (hX : 0 < squareRootEndpoint R) (hq : q.Prime) :
    squareRootEndpoint R / q < squareRootEndpoint R :=
  Nat.div_lt_self hX hq.one_lt

/-- The square-dilated cutoff is strictly below the inherited one-prime cutoff
whenever that inherited cutoff is nonzero. -/
theorem lowWheelFrozenSecondContactOwnerWindow_lower_strict
    {R q : ℕ} (hq : q.Prime)
    (hpos : 0 < squareRootEndpoint R / q) :
    squareRootEndpoint R / (q * q) < squareRootEndpoint R / q := by
  have hdrop :
      (squareRootEndpoint R / q) / q < squareRootEndpoint R / q :=
    Nat.div_lt_self hpos hq.one_lt
  simpa [Nat.div_div_eq_div_mul] using hdrop

end RHLean.Proof
