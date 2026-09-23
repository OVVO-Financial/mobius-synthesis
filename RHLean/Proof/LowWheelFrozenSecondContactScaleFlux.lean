import Mathlib
import RHLean.Analysis.ElevenWeightOneFirstMoment
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.LowWheelFrozenSecondContactGlobalTelescope
import RHLean.Proof.SquareRootLowPrimeTSectorQ2Renormalization

/-!
# Arithmetic scale and sign of frozen second-contact flux

These declarations depend on the completed transport development and therefore
live downstream of it. The foundational UniformResidualBound module cannot
import them without creating a cycle through MobiusRenewalTelescope.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- The predecessor face is literally the source scale times the canonical
cofactor left after stripping the second-contact owner. -/
theorem lowWheelFrozenSecondContact_parentFaceProduct_eq_sourceScale_mul_canonicalCofactor
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    primeFaceProduct (lowWheelFrozenSecondContactParentFace y) =
      lowWheelFrozenSecondContactSourceScale y * canonicalCofactor y.2.1 := by
  have hyFrozen := (Finset.mem_filter.mp hy).1
  have hcgt :=
    (lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen).2.2.2.2.1
  have hfactor :
      canonicalCofactor y.2.1 * lowWheelFrozenCofactorTopPrime y = y.2.1 := by
    simpa [lowWheelFrozenCofactorTopPrime] using
      (canonicalCofactor_mul_largestPrimeFactor hcgt)
  have heq :
      lowWheelFrozenCofactorTopPrime y *
          primeFaceProduct (lowWheelFrozenSecondContactParentFace y) =
        lowWheelFrozenCofactorTopPrime y *
          (lowWheelFrozenSecondContactSourceScale y * canonicalCofactor y.2.1) := by
    calc
      lowWheelFrozenCofactorTopPrime y *
          primeFaceProduct (lowWheelFrozenSecondContactParentFace y) =
        primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) :=
          lowWheelFrozenSecondContact_owner_mul_parentFaceProduct hyFrozen
      _ = y.2.1 * lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 :=
          lowWheelCanonicalRepeatedFrozenProductOneFace_product hyFrozen
      _ = lowWheelFrozenCofactorTopPrime y *
          (lowWheelFrozenSecondContactSourceScale y * canonicalCofactor y.2.1) := by
        conv_lhs => rw [← hfactor]
        unfold lowWheelFrozenSecondContactSourceScale
        ac_rfl
  have hqpos : 0 < lowWheelFrozenCofactorTopPrime y :=
    (lowWheelFrozenCofactorTopPrime_data hyFrozen).1.pos
  exact Nat.mul_left_cancel hqpos heq

/-- After stripping the second-contact owner, the source sign is exactly the
product of the source-scale Möbius sign and the stripped-cofactor Möbius sign. -/
theorem lowWheelFrozenSecondContact_sourceWeight_eq_scale_mul_canonicalCofactor
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) =
      canonicalMoebiusWeight (lowWheelFrozenSecondContactSourceScale y) *
        canonicalMoebiusWeight (canonicalCofactor y.2.1) := by
  have hyFrozen := (Finset.mem_filter.mp hy).1
  rcases lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen with
    ⟨_hk, _hpPrime, _hpNotC, hsq, _hcgt, _hcR⟩
  rcases lowWheelFrozenCofactorTopPrime_data hyFrozen with
    ⟨hqPrime, hqDvd, _hpq⟩
  have hstrip :
      canonicalMoebiusWeight (canonicalCofactor y.2.1) =
        -canonicalMoebiusWeight y.2.1 := by
    simpa [canonicalCofactor, lowWheelFrozenCofactorTopPrime] using
      (canonicalMoebiusWeight_div_prime hqPrime hsq hqDvd)
  calc
    canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) =
        -(canonicalMoebiusWeight (lowWheelFrozenSecondContactSourceScale y) *
          canonicalMoebiusWeight y.2.1) :=
      lowWheelFrozenSecondContactSource_weight_eq_neg_scale_mul_cofactor hy
    _ = canonicalMoebiusWeight (lowWheelFrozenSecondContactSourceScale y) *
        canonicalMoebiusWeight (canonicalCofactor y.2.1) := by
      rw [hstrip]
      ring

/-- The source scale remembers its first root-crossing coordinate intrinsically:
its canonical largest prime is exactly the frozen pivot. -/
theorem lowWheelFrozenSecondContact_sourceScale_largestPrime
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    canonicalLargestPrimeFactor (lowWheelFrozenSecondContactSourceScale y) =
      lowWheelTaggedDowncrossPivot y := by
  have hyFrozen := (Finset.mem_filter.mp hy).1
  have hsource := lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen
  have hfrozen := (Finset.mem_filter.mp hyFrozen).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have ht := (mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged).1
  have htPred :
      y.1 ∈ (primesUpTo (lowWheelTaggedDowncrossPivot y - 1)).powerset := by
    apply Finset.mem_powerset.mpr
    intro r hr
    have hrPrime := prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hr)
    have hrLt := lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hyFrozen hr
    exact mem_primesUpTo.mpr ⟨hrPrime, by omega⟩
  have hmax := canonicalLargestPrimeFactor_insert_freshPrime hsource.2.1 htPred
  rw [lowWheelFrozenSecondContactSourceScale_eq_insertPivotFaceProduct hy]
  exact hmax

/-- **Physical/Go second-contact intertwining certificate.**  All three pieces
that had previously lived in separate coordinate systems are the same source:

* the physical predecessor face is `A*d`;
* its signed weight is exactly `mu(A)*mu(d)`;
* after dividing the parent endpoint by `A`, the stripped cofactor is the
  genuine Go boundary `q*d <= B < q^2*d` on a strict lower scale `B<R`.

No norm, inequality estimate, or probabilistic identification enters this
statement.  It is the exact arithmetic carrier/sign/scale dictionary needed to
transport the physical least-square boundary into the Go recursion. -/
theorem lowWheelFrozenSecondContact_physicalGo_intertwining
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    let A := lowWheelFrozenSecondContactSourceScale y
    let B := squareRootEndpoint R / A
    let c := y.2.1
    let q := lowWheelFrozenCofactorTopPrime y
    let d := canonicalCofactor c
    primeFaceProduct (lowWheelFrozenSecondContactParentFace y) = A * d ∧
      canonicalMoebiusWeight c * (booleanCubeSign y.1 : ℂ) =
        canonicalMoebiusWeight A * canonicalMoebiusWeight d ∧
      q.Prime ∧ Squarefree d ∧ canonicalLargestPrimeFactor d < q ∧
        q * d = c ∧ q * d ≤ B ∧ B < q * q * d ∧ B < R := by
  dsimp only
  refine ⟨
    lowWheelFrozenSecondContact_parentFaceProduct_eq_sourceScale_mul_canonicalCofactor hy,
    lowWheelFrozenSecondContact_sourceWeight_eq_scale_mul_canonicalCofactor hy,
    ?_⟩
  have h := lowWheelFrozenSecondContact_source_lowerScaleSecondContact hy
  simpa [lowWheelFrozenSecondContactSourceScale] using h

/-- **Fixed-owner carrier equivalence.**  On the genuine saturated
second-contact population, erasing the owner is not merely an injection into a
Go-like window.  For every prime owner `q<R` it is a bijection onto the complete
native high-owner predecessor window.  Together with
`lowWheelFrozenSecondContactParentMap_weight_eq_source`, this is the exact
carrier-level equivalence behind the signed owner-mass identity. -/
theorem lowWheelFrozenSecondContactParentFace_bijOn_highOwnerWindow
    {R q : ℕ} (hq : q.Prime) (hqR : q < R) :
    Set.BijOn
      (fun y : LowWheelTaggedDowncrossState =>
        lowWheelFrozenSecondContactParentFace y)
      (↑((lowWheelCanonicalRepeatedFrozenSecondContactPart R).filter
          (fun y => lowWheelFrozenCofactorTopPrime y = q)) :
        Set LowWheelTaggedDowncrossState)
      (↑(lowWheelFrozenSecondContactHighOwnerWindow R q) : Set (Finset ℕ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    change y ∈ (lowWheelCanonicalRepeatedFrozenSecondContactPart R).filter
      (fun y => lowWheelFrozenCofactorTopPrime y = q) at hy
    have hySource := (Finset.mem_filter.mp hy).1
    have hyOwner := (Finset.mem_filter.mp hy).2
    change lowWheelFrozenSecondContactParentFace y ∈
      lowWheelFrozenSecondContactHighOwnerWindow R q
    simpa [hyOwner] using
      lowWheelFrozenSecondContactParentFace_mem_highOwnerWindow hySource
  · intro y hy z hz hface
    change y ∈ (lowWheelCanonicalRepeatedFrozenSecondContactPart R).filter
      (fun y => lowWheelFrozenCofactorTopPrime y = q) at hy
    change z ∈ (lowWheelCanonicalRepeatedFrozenSecondContactPart R).filter
      (fun y => lowWheelFrozenCofactorTopPrime y = q) at hz
    have hySource := (Finset.mem_filter.mp hy).1
    have hzSource := (Finset.mem_filter.mp hz).1
    have hyOwner := (Finset.mem_filter.mp hy).2
    have hzOwner := (Finset.mem_filter.mp hz).2
    have hmap :
        lowWheelFrozenSecondContactParentMap y =
          lowWheelFrozenSecondContactParentMap z := by
      apply Prod.ext
      · exact hyOwner.trans hzOwner.symm
      · exact hface
    exact (lowWheelFrozenSecondContactParentMap_injOn R)
      hySource hzSource hmap
  · intro V hV
    change V ∈ lowWheelFrozenSecondContactHighOwnerWindow R q at hV
    obtain ⟨y, hySource, hmap⟩ :=
      lowWheelFrozenSecondContactParentMap_surjOn_highOwnerWindow hq hqR hV
    have howner := congrArg Prod.fst hmap
    have hface := congrArg Prod.snd hmap
    change lowWheelFrozenCofactorTopPrime y = q at howner
    change lowWheelFrozenSecondContactParentFace y = V at hface
    refine ⟨y, ?_, hface⟩
    change y ∈ (lowWheelCanonicalRepeatedFrozenSecondContactPart R).filter
      (fun y => lowWheelFrozenCofactorTopPrime y = q)
    exact Finset.mem_filter.mpr ⟨hySource, howner⟩

/-! ## Complete q-square contact fibres and the 11 layer

A fixed physical active affine form is `4*k+a`.  For an odd prime owner `q`,
`4` is invertible modulo `q^2`, so the contact equation `q^2 | 4*k+a` has one
and only one local residue.  On a complete product orbit this removes the q-square
coordinate by an exact CRT bijection.  Everything on the complementary prime
coordinates is left arbitrary, so the theorem preserves earlier-square masks,
selected-prime signs and rank-one Schur first-moment weights without an
independence assumption.
-/

/-- Affine permutation of a finite residue ring when its linear coefficient is
a unit. -/
def qSquareContactAffineEquiv
    (m a : ℕ) [NeZero m] (hcop : Nat.Coprime a m) (b : ZMod m) :
    ZMod m ≃ ZMod m where
  toFun z := (a : ZMod m) * z + b
  invFun y := (a : ZMod m)⁻¹ * (y - b)
  left_inv := by
    intro z
    have hu : IsUnit (a : ZMod m) :=
      (ZMod.isUnit_iff_coprime a m).2 hcop
    dsimp
    calc
      (a : ZMod m)⁻¹ * ((a : ZMod m) * z + b - b) =
          ((a : ZMod m)⁻¹ * (a : ZMod m)) * z := by ring
      _ = z := by rw [ZMod.inv_mul_of_unit _ hu, one_mul]
  right_inv := by
    intro y
    have hu : IsUnit (a : ZMod m) :=
      (ZMod.isUnit_iff_coprime a m).2 hcop
    dsimp
    calc
      (a : ZMod m) * ((a : ZMod m)⁻¹ * (y - b)) + b =
          ((a : ZMod m) * (a : ZMod m)⁻¹) * (y - b) + b := by ring
      _ = y := by
        rw [ZMod.mul_inv_of_unit _ hu]
        ring

/-- Indicator of the local q-square collision on one physical affine offset. -/
def qSquareContactIndicator (q a : ℕ) (z : ZMod (q ^ 2)) : ℚ :=
  if (4 : ZMod (q ^ 2)) * z + (a : ZMod (q ^ 2)) = 0 then 1 else 0

/-- Each fixed physical offset has exactly one q-square contact in a complete
`q^2` period.  `NeZero (q^2)` is exposed in the signature because `ZMod`'s
finite instance is required while elaborating the result type. -/
theorem sum_qSquareContactIndicator_eq_one
    {q a : ℕ} [NeZero (q ^ 2)] (hq : q.Prime) (hq2 : q ≠ 2) :
    (∑ z : ZMod (q ^ 2), qSquareContactIndicator q a z) = 1 := by
  have hcop : Nat.Coprime (q ^ 2) 4 := by
    simpa using
      (Nat.coprime_pow_primes (p := q) (q := 2) 2 2
        hq Nat.prime_two hq2)
  let e : ZMod (q ^ 2) ≃ ZMod (q ^ 2) :=
    qSquareContactAffineEquiv (q ^ 2) 4 hcop.symm (a : ZMod (q ^ 2))
  calc
    (∑ z : ZMod (q ^ 2), qSquareContactIndicator q a z) =
        ∑ y : ZMod (q ^ 2), if y = 0 then (1 : ℚ) else 0 := by
      exact Fintype.sum_equiv e
        (fun z : ZMod (q ^ 2) => qSquareContactIndicator q a z)
        (fun y : ZMod (q ^ 2) => if y = 0 then (1 : ℚ) else 0)
        (by
          intro z
          simp [e, qSquareContactIndicator, qSquareContactAffineEquiv])
    _ = 1 := by simp

/-- The modular contact predicate is literally the divisibility predicate used
by the physical least-square channel. -/
theorem qSquareContactIndicator_natCast
    {q a k : ℕ} [NeZero (q ^ 2)] :
    qSquareContactIndicator q a (k : ZMod (q ^ 2)) =
      (if q ^ 2 ∣ 4 * k + a then 1 else 0) := by
  unfold qSquareContactIndicator
  have hcast :
      (4 : ZMod (q ^ 2)) * (k : ZMod (q ^ 2)) +
          (a : ZMod (q ^ 2)) =
        ((4 * k + a : ℕ) : ZMod (q ^ 2)) := by
    push_cast
    rfl
  rw [hcast]
  simp only [ZMod.natCast_eq_zero_iff]

/-- **Complete q-square contact / daughter equivalence.**  On a complete
coprime super-orbit, restricting to one physical q-square contact leaves exactly
one copy of an arbitrary complementary first-moment field.  This is equality,
not the `18*K/q^2` magnitude estimate from the old q-owner argument. -/
theorem qSquareContact_coprimeTensor_firstMoment
    (q M a : ℕ) [NeZero (q ^ 2)] [NeZero M]
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hcop : Nat.Coprime (q ^ 2) M)
    (g : ZMod M → ℚ) :
    (∑ z : ZMod ((q ^ 2) * M),
      qSquareContactIndicator q a
          ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) =
      ∑ b : ZMod M, g b := by
  have htensor := coprimeZMod_sum_tensor (q ^ 2) M hcop
    (qSquareContactIndicator q a) g
  rw [sum_qSquareContactIndicator_eq_one hq hq2] at htensor
  simpa using htensor

/-- Rank-one energy is exactly preserved by the q-square contact/daughter
bijection before the independent 11 layer is applied. -/
theorem qSquareContact_coprimeTensor_firstMoment_sq
    (q M a : ℕ) [NeZero (q ^ 2)] [NeZero M]
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hcop : Nat.Coprime (q ^ 2) M)
    (g : ZMod M → ℚ) :
    (∑ z : ZMod ((q ^ 2) * M),
      qSquareContactIndicator q a
          ((ZMod.chineseRemainder hcop) z).1 *
        g ((ZMod.chineseRemainder hcop) z).2) ^ 2 =
      (∑ b : ZMod M, g b) ^ 2 := by
  rw [qSquareContact_coprimeTensor_firstMoment q M a hq hq2 hcop g]

/-- **11/q² complete-fibre intertwining.**  Applying the selected-11 weight-one
operator before q-square deletion or after the exact q-square daughter transport
gives the same first moment.  The surviving scalar is exactly `19/23`; all
other prime coordinates remain inside the arbitrary field `g`. -/
theorem qSquareContact_eleven_coprimeTensor_firstMoment
    (q M a : ℕ) [NeZero (q ^ 2)] [NeZero M]
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hqcop : Nat.Coprime (q ^ 2) (121 * M))
    (h11cop : Nat.Coprime 121 M)
    (i : Fin 6) (g : ZMod M → ℚ) :
    (∑ z : ZMod ((q ^ 2) * (121 * M)),
      qSquareContactIndicator q a
          ((ZMod.chineseRemainder hqcop) z).1 *
        (elevenZeroFreeCoordinateMultiplierZMod i
            ((ZMod.chineseRemainder h11cop)
              ((ZMod.chineseRemainder hqcop) z).2).1 *
          g ((ZMod.chineseRemainder h11cop)
              ((ZMod.chineseRemainder hqcop) z).2).2)) =
      onePrimeWalshFactor 11 1 *
        (∑ z : ZMod ((q ^ 2) * (121 * M)),
          qSquareContactIndicator q a
              ((ZMod.chineseRemainder hqcop) z).1 *
            (elevenZeroFreeIndicatorZMod
                ((ZMod.chineseRemainder h11cop)
                  ((ZMod.chineseRemainder hqcop) z).2).1 *
              g ((ZMod.chineseRemainder h11cop)
                  ((ZMod.chineseRemainder hqcop) z).2).2)) := by
  let Gsigned : ZMod (121 * M) → ℚ := fun w =>
    elevenZeroFreeCoordinateMultiplierZMod i
        ((ZMod.chineseRemainder h11cop) w).1 *
      g ((ZMod.chineseRemainder h11cop) w).2
  let Gzero : ZMod (121 * M) → ℚ := fun w =>
    elevenZeroFreeIndicatorZMod
        ((ZMod.chineseRemainder h11cop) w).1 *
      g ((ZMod.chineseRemainder h11cop) w).2
  have hqSigned := qSquareContact_coprimeTensor_firstMoment
    q (121 * M) a hq hq2 hqcop Gsigned
  have hqZero := qSquareContact_coprimeTensor_firstMoment
    q (121 * M) a hq hq2 hqcop Gzero
  have h11 := eleven_coprimeTensor_firstMoment M h11cop i g
  have h11' :
      (∑ w : ZMod (121 * M), Gsigned w) =
        onePrimeWalshFactor 11 1 *
          (∑ w : ZMod (121 * M), Gzero w) := by
    simpa [Gsigned, Gzero] using h11
  calc
    (∑ z : ZMod ((q ^ 2) * (121 * M)),
        qSquareContactIndicator q a
            ((ZMod.chineseRemainder hqcop) z).1 *
          (elevenZeroFreeCoordinateMultiplierZMod i
              ((ZMod.chineseRemainder h11cop)
                ((ZMod.chineseRemainder hqcop) z).2).1 *
            g ((ZMod.chineseRemainder h11cop)
                ((ZMod.chineseRemainder hqcop) z).2).2)) =
      ∑ w : ZMod (121 * M), Gsigned w := by
        simpa [Gsigned] using hqSigned
    _ = onePrimeWalshFactor 11 1 *
        (∑ w : ZMod (121 * M), Gzero w) := h11'
    _ = onePrimeWalshFactor 11 1 *
        (∑ z : ZMod ((q ^ 2) * (121 * M)),
          qSquareContactIndicator q a
              ((ZMod.chineseRemainder hqcop) z).1 *
            (elevenZeroFreeIndicatorZMod
                ((ZMod.chineseRemainder h11cop)
                  ((ZMod.chineseRemainder hqcop) z).2).1 *
              g ((ZMod.chineseRemainder h11cop)
                  ((ZMod.chineseRemainder hqcop) z).2).2)) := by
        rw [hqZero]

/-- Squaring the commuting diagram gives exactly the `(19/23)^2` energy factor
used by the q-square renormalization engine. -/
theorem qSquareContact_eleven_coprimeTensor_firstMoment_sq
    (q M a : ℕ) [NeZero (q ^ 2)] [NeZero M]
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hqcop : Nat.Coprime (q ^ 2) (121 * M))
    (h11cop : Nat.Coprime 121 M)
    (i : Fin 6) (g : ZMod M → ℚ) :
    (∑ z : ZMod ((q ^ 2) * (121 * M)),
      qSquareContactIndicator q a
          ((ZMod.chineseRemainder hqcop) z).1 *
        (elevenZeroFreeCoordinateMultiplierZMod i
            ((ZMod.chineseRemainder h11cop)
              ((ZMod.chineseRemainder hqcop) z).2).1 *
          g ((ZMod.chineseRemainder h11cop)
              ((ZMod.chineseRemainder hqcop) z).2).2)) ^ 2 =
      (onePrimeWalshFactor 11 1) ^ 2 *
        (∑ z : ZMod ((q ^ 2) * (121 * M)),
          qSquareContactIndicator q a
              ((ZMod.chineseRemainder hqcop) z).1 *
            (elevenZeroFreeIndicatorZMod
                ((ZMod.chineseRemainder h11cop)
                  ((ZMod.chineseRemainder hqcop) z).2).1 *
              g ((ZMod.chineseRemainder h11cop)
                  ((ZMod.chineseRemainder hqcop) z).2).2)) ^ 2 := by
  rw [qSquareContact_eleven_coprimeTensor_firstMoment
    q M a hq hq2 hqcop h11cop i g]
  ring

/-- Square-dilated daughter cutoff attached to one second-contact owner. -/
def lowWheelFrozenSecondContactFluxChildCutoff (B q : ℕ) : ℕ :=
  B / (q * q)

/-- A square-dilated daughter cutoff is always weakly below its parent scale. -/
theorem lowWheelFrozenSecondContactFluxChildCutoff_le
    {B q : ℕ} :
    lowWheelFrozenSecondContactFluxChildCutoff B q ≤ B := by
  unfold lowWheelFrozenSecondContactFluxChildCutoff
  exact Nat.div_le_self _ _

/-! ## Exact reciprocal-coordinate / Go-daughter intertwining

The unified reciprocal form uses `roughCofactorMobiusPrefixMass q B`.  The Go
wall was developed independently as a frozen predecessor-cube residual.  At the
square-dilated cutoff these are not merely analogous: they are exactly the same
Möbius population.  This is the missing coordinate splice between the
reciprocal transform and the `q^2` daughter carrier.
-/

/-- **Exact q² daughter identification.**  The complex cast of the literal Go
square residual is the rough lower-scale Möbius prefix at the identical
`X/q²` cutoff used by the unified reciprocal transform.  Nonsquarefree
cofactors may be omitted on the Go side because their Möbius weight is zero. -/
theorem squareRootLowPrimeGoWallSquareResidual_cast_eq_roughCofactorMobiusPrefixMass
    {q X : ℕ} (hq : q.Prime) :
    (((squareRootLowPrimeGoWallSquareResidual q X : ℤ) : ℂ)) =
      roughCofactorMobiusPrefixMass q (X / (q * q)) := by
  rw [squareRootLowPrimeGoWallSquareResidual_eq_smoothCofactorSum hq]
  push_cast
  unfold squareRootLowPrimeGoSmoothCofactors
    roughCofactorMobiusPrefixMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hrough : canonicalLargestPrimeFactor c < q
  · rw [if_pos hrough]
    by_cases hsq : Squarefree c
    · simp [hsq, hrough, canonicalMoebiusWeight]
    · have hmu : μ c = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      simp [hsq, hrough, canonicalMoebiusWeight, hmu]
  · simp [hrough]

/-- **One-strip reciprocal/Go intertwining.**  After casting the exact Go strip
to the common complex carrier, its only non-boundary term is literally the
rough Möbius daughter at `X/q²`.  Hence consecutive strips telescope their two
moving boundary states while all surviving arithmetic content is already on
the lower-scale coordinate used by the reciprocal transform. -/
theorem squareRootLowPrimeGoWallStripMass_cast_eq_boundaryDiff_add_roughDaughter
    {ell q X : ℕ} (hq : q.Prime)
    (hpred : primesUpTo (q - 1) = primesUpTo ell) :
    (((squareRootLowPrimeGoWallStripMass ell q X : ℤ) : ℂ)) =
      (((squareRootLowPrimeGoWallBoundaryState q X : ℤ) : ℂ)) -
        (((squareRootLowPrimeGoWallBoundaryState ell X : ℤ) : ℂ)) +
          roughCofactorMobiusPrefixMass q (X / (q * q)) := by
  rw [squareRootLowPrimeGoWallStripMass_eq_boundaryDiff_add_squareResidual
    hq hpred]
  push_cast
  rw [squareRootLowPrimeGoWallSquareResidual_cast_eq_roughCofactorMobiusPrefixMass hq]

/-- **Root-floored q² column = Go daughters plus explicit root boundary.**
The `max R (X_R/q²)` left by the saturated global telescope is split without
any estimate.  When `X_R/q² >= R` the term is literally the Go square residual;
otherwise it is exactly the predecessor mass frozen at the root `R`. -/
theorem lowWheelFrozenSecondContactRootFlooredColumn_eq_goOrRoot
    (R : ℕ) :
    (∑ q ∈ primesUpTo (R - 1),
      frozenPrimeUniverseMass (primesUpTo (q - 1))
        (max R (squareRootEndpoint R / (q * q)))) =
      ∑ q ∈ primesUpTo (R - 1),
        if R ≤ squareRootEndpoint R / (q * q) then
          squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R)
        else
          frozenPrimeUniverseMass (primesUpTo (q - 1)) R := by
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hdeep : R ≤ squareRootEndpoint R / (q * q)
  · rw [if_pos hdeep, max_eq_right hdeep,
      squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff]
  · have hle : squareRootEndpoint R / (q * q) ≤ R :=
      Nat.le_of_lt (Nat.lt_of_not_ge hdeep)
    rw [if_neg hdeep, max_eq_left hle]

/-- **Global signed physical/Go equivalence with boundary bookkeeping.**  The
entire saturated physical second-contact source ledger is exactly one root
anchor minus a finite sum whose deep terms are the literal Go `q²` daughters
and whose complementary terms are the explicit root-floor boundary.  This is
the global form required by an earlier layer: no q-owner absolute value and no omitted
incomplete-period charge. -/
theorem lowWheelFrozenSecondContactSource_sum_eq_rootBoundary_sub_goOrRoot
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      (((1 - frozenPrimeUniverseMass (primesUpTo (R - 1))
            (squareRootEndpoint R)) -
          ∑ q ∈ primesUpTo (R - 1),
            if R ≤ squareRootEndpoint R / (q * q) then
              squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R)
            else
              frozenPrimeUniverseMass (primesUpTo (q - 1)) R : ℤ) : ℂ) := by
  rw [lowWheelFrozenSecondContactSource_sum_eq_highOwnerWindowMass_sum,
    lowWheelFrozenSecondContactHighOwnerWindowMass_sum_eq_rootFlooredLowerColumn R hR,
    lowWheelFrozenSecondContactRootFlooredColumn_eq_goOrRoot R]

/-! ## The collision fibre becomes bounded after q^-2 scaling

`lowWheelFrozenSecondContactChildOwnerColumn_eq_signed_fibers` shows that the
raw coefficient of a reassembled face is the cardinality of
`lowWheelFrozenSecondContactOldOwnerFiber`.  All old owners in that fibre have
the same sign, so the cardinality itself cannot be cancelled locally.

The q-square descent changes the correct coefficient.  Retaining the intrinsic
owner weight `q^-2` turns the same fibre into a sub-sum of the already compiled
prime-owner reciprocal-square budget.  Consequently every collision fibre has
weighted mass at most one, regardless of its raw cardinality.
-/

/-- Reciprocal-square mass of the exact old-owner collision fibre from an earlier layer. -/
def lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass
    (R r d : ℕ) : ℚ :=
  ∑ q ∈ lowWheelFrozenSecondContactOldOwnerFiber R r d,
    (1 : ℚ) / (q : ℚ) ^ 2

/-- Every old-owner collision fibre is literally a subfamily of the ambient
prime-owner schedule. -/
theorem lowWheelFrozenSecondContactOldOwnerFiber_subset_primesUpTo
    (R r d : ℕ) :
    lowWheelFrozenSecondContactOldOwnerFiber R r d ⊆ primesUpTo (R - 1) := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1

/-- The reciprocal-square mass of one collision fibre is no larger than the
complete prime-owner reciprocal-square budget. -/
theorem lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass_le_budget
    (R r d : ℕ) :
    lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass R r d ≤
      primeOwnerReciprocalSquareBudget (R - 1) := by
  unfold lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (lowWheelFrozenSecondContactOldOwnerFiber_subset_primesUpTo R r d)
  intro q _hq hnot
  positivity

/-- **Weighted collision-fibre contraction.**  Arbitrarily large raw old-owner
multiplicity costs at most unit mass after the natural `q^-2` scale is retained.
This is finite and elementary; no prime density estimate is used. -/
theorem lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass_le_one
    (R r d : ℕ) :
    lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass R r d ≤ 1 := by
  exact (lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass_le_budget R r d).trans
    (primeOwnerReciprocalSquareBudget_le_one (R - 1))

/-- The same fact in the literal daughter-cutoff units used by the q-square
renormalization: restricting to any one collision fibre cannot exceed one
parent-scale budget. -/
theorem sum_oldOwnerFiber_squareDilatedCutoffs_le_parent
    (R r d X : ℕ) :
    (∑ q ∈ lowWheelFrozenSecondContactOldOwnerFiber R r d,
      ((X / (q * q) : ℕ) : ℚ)) ≤ (X : ℚ) := by
  calc
    (∑ q ∈ lowWheelFrozenSecondContactOldOwnerFiber R r d,
        ((X / (q * q) : ℕ) : ℚ)) ≤
      ∑ q ∈ primesUpTo (R - 1), ((X / (q * q) : ℕ) : ℚ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (lowWheelFrozenSecondContactOldOwnerFiber_subset_primesUpTo R r d)
        intro q _hq hnot
        positivity
    _ ≤ (X : ℚ) := sum_primeOwner_squareDilatedCutoffs_le_parent (R - 1) X

/-- **Collision-safe subcriticality.**  Even if arbitrarily many old owners
coalesce onto one reassembled face, retaining their `q^-2` daughter scales
before applying the exact prime-11 weight-one energy factor leaves a strict
contraction for every positive parent scale. -/
theorem elevenWeighted_sum_oldOwnerFiber_squareDilatedCutoffs_lt_parent
    (R r d X : ℕ) (hX : 0 < X) :
    elevenWeightOneEnergyFactor *
        (∑ q ∈ lowWheelFrozenSecondContactOldOwnerFiber R r d,
          ((X / (q * q) : ℕ) : ℚ)) <
      (X : ℚ) := by
  have hsum := sum_oldOwnerFiber_squareDilatedCutoffs_le_parent R r d X
  have hXq : (0 : ℚ) < (X : ℚ) := by exact_mod_cast hX
  calc
    elevenWeightOneEnergyFactor *
          (∑ q ∈ lowWheelFrozenSecondContactOldOwnerFiber R r d,
            ((X / (q * q) : ℕ) : ℚ)) ≤
        elevenWeightOneEnergyFactor * (X : ℚ) :=
      mul_le_mul_of_nonneg_left hsum elevenWeightOneEnergyFactor_nonneg
    _ < 1 * (X : ℚ) :=
      mul_lt_mul_of_pos_right
        (elevenWeightOneEnergyFactor_lt_three_quarters.trans (by norm_num)) hXq
    _ = (X : ℚ) := by ring

/-! ## Canonical ancestry congestion on the saturated window

The original collision-defect-chain interface bounded the number of charged
steps pointwise.  That is too strong.  The canonical parent is unique, but many
higher sources can coalesce onto the same lower parent edge.  The scale carried
by a second-contact owner is nevertheless intrinsically `q^-2`, exactly the
weight used by `sum_primeOwner_squareDilatedCutoffs_le_parent` and by the
physical complete-period first-moment bound.

The declarations below therefore expose raw edge multiplicity for diagnostics
but make the weighted aggregate the arithmetic proof target.  No Mertens or RH
conclusion is asserted here.
-/

/-- Iterate the deterministic canonical ancestry parent.  `none` is absorbing. -/
noncomputable def canonicalAncestryParentIterate {B : ℕ} :
    ℕ → SourceIndex B → Option (SourceIndex B)
  | 0, s => some s
  | d + 1, s => (canonicalAncestryParentIterate d s).bind sourceParent

@[simp] theorem canonicalAncestryParentIterate_zero {B : ℕ}
    (s : SourceIndex B) :
    canonicalAncestryParentIterate 0 s = some s := rfl

/-- The saturated owner window written directly on the canonical `(q,c)`
carrier.  It is the arithmetic form

`max R (X_R/q^2) < c <= X_R/q`, with `q<R` and `P+(c)<q` supplied by
`SourceAdmissible`. -/
noncomputable def lowWheelFrozenSecondContactCanonicalSeeds (R : ℕ) :
    Finset (SourceIndex (squareRootEndpoint R)) :=
  Finset.univ.filter fun s =>
    SourceAdmissible s ∧
      sourcePrime s < R ∧
      max R
          (squareRootEndpoint R /
            (sourcePrime s * sourcePrime s)) < sourceCore s ∧
      sourceCore s ≤ squareRootEndpoint R / sourcePrime s

/-- Literal membership criterion for the canonical saturated seed carrier. -/
theorem mem_lowWheelFrozenSecondContactCanonicalSeeds_iff
    {R : ℕ} {s : SourceIndex (squareRootEndpoint R)} :
    s ∈ lowWheelFrozenSecondContactCanonicalSeeds R ↔
      SourceAdmissible s ∧
        sourcePrime s < R ∧
        max R
            (squareRootEndpoint R /
              (sourcePrime s * sourcePrime s)) < sourceCore s ∧
        sourceCore s ≤ squareRootEndpoint R / sourcePrime s := by
  simp [lowWheelFrozenSecondContactCanonicalSeeds]

/-- Number of saturated seeds whose canonical trajectory visits one smooth child.
Because `sourceParent` is a function, the child uniquely determines the edge.
The depth range `B+1` is the certified nilpotence height of the bounded source
flow. -/
noncomputable def canonicalAncestryChargeMultiplicity {B : ℕ}
    (seeds : Finset (SourceIndex B)) (child : SourceIndex B) : ℕ :=
  ∑ d ∈ Finset.range (B + 1),
    (seeds.filter fun seed =>
      canonicalAncestryParentIterate d seed = some child).card

/-- Natural square-scale weight of a canonical edge with owner `q`. -/
def canonicalAncestryOwnerSquareWeight {B : ℕ}
    (child : SourceIndex B) : ℚ :=
  (1 : ℚ) / (sourcePrime child : ℚ) ^ 2

/-- Global ancestry congestion after applying the intrinsic `q^-2` owner scale.
Roots contribute zero because they do not carry a parent edge. -/
noncomputable def canonicalAncestryWeightedCongestion {B : ℕ}
    (seeds : Finset (SourceIndex B)) : ℚ :=
  ∑ child : SourceIndex B,
    if sourceParent child = none then 0
    else
      (canonicalAncestryChargeMultiplicity seeds child : ℚ) *
        canonicalAncestryOwnerSquareWeight child

/-- The weighted congestion specialized to the actual saturated second-contact
seed window. -/
noncomputable def lowWheelFrozenSecondContactCanonicalWeightedCongestion
    (R : ℕ) : ℚ :=
  canonicalAncestryWeightedCongestion
    (lowWheelFrozenSecondContactCanonicalSeeds R)

/-- Strong form suggested by the finite diagnostic.  This is deliberately a
named statement, not a theorem: proving it is the new arithmetic packing seam. -/
def LowWheelFrozenSecondContactCanonicalWeightedLinearBoundStatement : Prop :=
  ∃ C : ℚ, 0 ≤ C ∧ ∀ R : ℕ,
    lowWheelFrozenSecondContactCanonicalWeightedCongestion R ≤ C * (R : ℚ)

/-- RH-scale form allowing the polylogarithmic loss that the proof program can
afford.  Unlike the discarded maximum-multiplicity target, this controls the
aggregate only after the intrinsic `q^-2` scale weight has been applied. -/
def LowWheelFrozenSecondContactCanonicalWeightedPolylogBoundStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ R : ℕ,
    ((lowWheelFrozenSecondContactCanonicalWeightedCongestion R : ℚ) : ℝ) ≤
      C * (R : ℝ) *
        (Real.log (((R + 2 : ℕ) : ℝ)) + 1) ^ k

end RHLean.Proof
