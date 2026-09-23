import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedParentClassification
import RHLean.Arithmetic.SquarefreePrimeFaceSurjectivity
import RHLean.Arithmetic.PrimeProductFrontierExhaustion
import RHLean.Arithmetic.PrimeFaceMoebius

/-!
# Prime geometry of frozen repeated-parent states with nontrivial cofactor

For a frozen repeated-parent source `y=(t,(c,k))`, classification gives
`k=p`, where `p=minFac(c*k)`, while the downcross condition gives `p ∤ c`.
If `c>1`, every prime factor `q|c` is therefore strictly above `p`.  Since the
physical cofactor satisfies `c<R`, all of those factors are still low-wheel
coordinates.  In particular `p<R` as well.

This is the key fact allowing the whole signed cofactor, rather than one factor,
to be moved into the Boolean face and terminated at a product-one fixed state.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Basic arithmetic data carried by a frozen repeated state with `c>1`. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_source_data
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    y.2.2 = lowWheelTaggedDowncrossPivot y ∧
      (lowWheelTaggedDowncrossPivot y).Prime ∧
      ¬ lowWheelTaggedDowncrossPivot y ∣ y.2.1 ∧
      Squarefree y.2.1 ∧
      1 < y.2.1 ∧ y.2.1 < R := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hcgt := (Finset.mem_filter.mp hy).2
  have hshape := (Finset.mem_filter.mp hfrozen).2
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hdown := mem_lowWheelCanonicalDowncrossPart.mp htag.2
  have hphys := mem_lowWheelCanonicalPhysicalStateSet.mp hdown.1
  have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
    have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell htag.2
    simpa [lowWheelTaggedDowncrossPivot] using hshell.1
  exact ⟨hshape.1, hp, hdown.2.1, hphys.2.2.1, hcgt,
    (Finset.mem_Ico.mp hphys.1).2⟩

/-- Every prime factor of the frozen cofactor lies strictly above the canonical
pivot. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_primeFactor
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R)
    {q : ℕ} (hq : q ∈ y.2.1.primeFactors) :
    lowWheelTaggedDowncrossPivot y < q := by
  have hdata := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have hqData := Nat.mem_primeFactors.mp hq
  have hqPrime : q.Prime := hqData.1
  have hqDvdC : q ∣ y.2.1 := hqData.2.1
  have hk := hdata.1
  have hqDvdProd : q ∣ y.2.1 * y.2.2 := dvd_mul_of_dvd_left hqDvdC _
  have hpLe : lowWheelTaggedDowncrossPivot y ≤ q := by
    have h := Nat.minFac_le_of_dvd hqPrime.two_le hqDvdProd
    simpa [lowWheelTaggedDowncrossPivot] using h
  exact hpLe.lt_of_ne fun heq =>
    hdata.2.2.1 (by simpa [heq] using hqDvdC)

/-- Every prime factor of the frozen cofactor is an actual low-wheel coordinate
strictly below the root cutoff. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_primeFactor_lt_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R)
    {q : ℕ} (hq : q ∈ y.2.1.primeFactors) :
    q < R := by
  have hdata := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have hqDvdC := (Nat.mem_primeFactors.mp hq).2.1
  have hqLeC : q ≤ y.2.1 := Nat.le_of_dvd (by omega) hqDvdC
  exact hqLeC.trans_lt hdata.2.2.2.2.2

/-- Consequently the complete prime support of the frozen cofactor belongs to
the low Boolean wheel. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_primeFactors_subset_primesUpTo
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    y.2.1.primeFactors ⊆ primesUpTo R := by
  intro q hq
  exact mem_primesUpTo.mpr
    ⟨(Nat.mem_primeFactors.mp hq).1,
      (lowWheelCanonicalRepeatedFrozenCofactor_primeFactor_lt_root hy hq).le⟩

/-- A frozen nontrivial-cofactor pivot itself is strictly below the root.  Thus
there are no `c>1` frozen states in the external `R<p` obstruction. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedDowncrossPivot y < R := by
  have hdata := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  let q := Nat.minFac y.2.1
  have hqPrime : q.Prime := by
    simpa [q] using Nat.minFac_prime (by omega : y.2.1 ≠ 1)
  have hqDvd : q ∣ y.2.1 := by
    simpa [q] using Nat.minFac_dvd y.2.1
  have hqMem : q ∈ y.2.1.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hqPrime, hqDvd, by omega⟩
  exact (lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_primeFactor hy hqMem).trans
    (lowWheelCanonicalRepeatedFrozenCofactor_primeFactor_lt_root hy hqMem)

/-- The frozen pivot is therefore itself an available low-wheel coordinate. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_pivot_mem_primesUpTo
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedDowncrossPivot y ∈ primesUpTo R := by
  have hdata := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  exact mem_primesUpTo.mpr
    ⟨hdata.2.1,
      (lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_root hy).le⟩

/-! ## Whole-cofactor transfer to a product-one Boolean face -/

/-- Every old Boolean-face prime lies strictly below the frozen pivot. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R)
    {q : ℕ} (hq : q ∈ y.1) :
    q < lowWheelTaggedDowncrossPivot y := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hshape := (Finset.mem_filter.mp hfrozen).2
  exact hshape.2 q hq

/-- The old transport face and the complete prime face of the cofactor are
disjoint: the former lies below the pivot and the latter strictly above it. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_face_disjoint_cofactorFace
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    Disjoint y.1 (squarefreePrimeFace y.2.1) := by
  rw [Finset.disjoint_left]
  intro q hqt hqc
  have hlt := lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hqt
  have hgt := lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_primeFactor hy
    (by simpa [squarefreePrimeFace] using hqc)
  omega

/-- The pivot belongs to neither side of the union used by the product-one
mate. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_pivot_not_mem_face_union
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedDowncrossPivot y ∉
      y.1 ∪ squarefreePrimeFace y.2.1 := by
  intro hp
  rcases Finset.mem_union.mp hp with hpFace | hpC
  · have hlt :=
      lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hpFace
    omega
  · rcases lowWheelCanonicalRepeatedFrozenCofactor_source_data hy with
      ⟨_hk, _hpPrime, hpNotC, _hsq, _hcgt, _hcR⟩
    have hpData := Nat.mem_primeFactors.mp
      (by simpa [squarefreePrimeFace] using hpC)
    exact hpNotC hpData.2.1

/-- Final Boolean face after absorbing the pivot and the complete signed
cofactor. -/
def lowWheelCanonicalRepeatedFrozenProductOneFace
    (y : LowWheelTaggedDowncrossState) : Finset ℕ :=
  insert (lowWheelTaggedDowncrossPivot y)
    (y.1 ∪ squarefreePrimeFace y.2.1)

/-- The whole-cofactor mate terminates at the product-one state `(1,1)`. -/
def lowWheelCanonicalRepeatedFrozenProductOneMate
    (y : LowWheelTaggedDowncrossState) :
    Finset ℕ × LowWheelCofactorQuotientState :=
  (lowWheelCanonicalRepeatedFrozenProductOneFace y, (1, 1))

/-- The final face consists entirely of available low-wheel coordinates. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneFace_mem_powerset
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelCanonicalRepeatedFrozenProductOneFace y ∈
      (primesUpTo R).powerset := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  apply Finset.mem_powerset.mpr
  intro q hq
  rcases Finset.mem_insert.mp hq with hp | hq
  · subst q
    exact lowWheelCanonicalRepeatedFrozenCofactor_pivot_mem_primesUpTo hy
  · rcases Finset.mem_union.mp hq with hqt | hqc
    · exact (Finset.mem_powerset.mp htag.1) hqt
    · exact lowWheelCanonicalRepeatedFrozenCofactor_primeFactors_subset_primesUpTo
        hy (by simpa [squarefreePrimeFace] using hqc)

/-- The absorbed face represents exactly the old complete physical product. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneFace_product
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) =
      y.2.1 * lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := by
  rcases lowWheelCanonicalRepeatedFrozenCofactor_source_data hy with
    ⟨_hk, _hpPrime, _hpNotC, hsq, _hcgt, _hcR⟩
  have hdisj :=
    lowWheelCanonicalRepeatedFrozenCofactor_face_disjoint_cofactorFace hy
  have hpNot :=
    lowWheelCanonicalRepeatedFrozenCofactor_pivot_not_mem_face_union hy
  have hunion :
      primeFaceProduct (y.1 ∪ squarefreePrimeFace y.2.1) =
        primeFaceProduct y.1 * y.2.1 := by
    rw [primeFaceProduct_union_of_disjoint hdisj,
      primeFaceProduct_squarefreePrimeFace hsq]
  unfold lowWheelCanonicalRepeatedFrozenProductOneFace
  rw [show primeFaceProduct
      (insert (lowWheelTaggedDowncrossPivot y)
        (y.1 ∪ squarefreePrimeFace y.2.1)) =
      lowWheelTaggedDowncrossPivot y *
        primeFaceProduct (y.1 ∪ squarefreePrimeFace y.2.1) by
        simp [primeFaceProduct, hpNot]]
  rw [hunion]
  ring

/-- The product-one mate is a literal state of the existing physical carrier
at its new Boolean face. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneMate_mem_physical
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    (1, 1) ∈ lowWheelCanonicalPhysicalStateSet R
      (lowWheelCanonicalRepeatedFrozenProductOneFace y) := by
  rcases lowWheelCanonicalRepeatedFrozenCofactor_source_data hy with
    ⟨hk, _hpPrime, _hpNotC, _hsq, hcgt, hcR⟩
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hphysSource := (mem_lowWheelCanonicalDowncrossPart.mp htag.2).1
  have hcarrier :=
    (mem_lowWheelCanonicalPhysicalStateSet.mp hphysSource).2.2.2
  have hRgt : 1 < R := by omega
  have hrootOld : R < primeFaceProduct y.1 * y.2.2 := hcarrier.2.2.1
  have htopOld :
      (y.2.1 * primeFaceProduct y.1) * y.2.2 ≤ squareRootEndpoint R :=
    hcarrier.2.2.2
  have hrootOld' :
      R < primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y := by
    simpa [hk] using hrootOld
  have htopOld' :
      (y.2.1 * primeFaceProduct y.1) * lowWheelTaggedDowncrossPivot y ≤
        squareRootEndpoint R := by
    simpa [hk] using htopOld
  have hprod := lowWheelCanonicalRepeatedFrozenProductOneFace_product hy
  have hrootFinal :
      R < primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) := by
    rw [hprod]
    have hle :
        primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y ≤
          y.2.1 * lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := by
      nlinarith
    exact hrootOld'.trans_le hle
  have htopFinal :
      primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) ≤
        squareRootEndpoint R := by
    rw [hprod]
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using htopOld'
  have hXOne : 1 ≤ squareRootEndpoint R := by
    have hR2 : 2 ≤ R := by omega
    have hsq : 4 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  have hpair :
      LowWheelTransportPairCarrier R
        (lowWheelCanonicalRepeatedFrozenProductOneFace y) (1, 1) := by
    refine ⟨by norm_num, hRgt, ?_, ?_⟩
    · simpa using hrootFinal
    · simpa using htopFinal
  exact mem_lowWheelCanonicalPhysicalStateSet.mpr
    ⟨Finset.mem_Ico.mpr ⟨by norm_num, hRgt⟩,
      Finset.mem_Icc.mpr ⟨by norm_num, hXOne⟩,
      squarefree_one, hpair⟩

/-- The one-shot whole-cofactor transfer reverses the signed physical weight
exactly. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneMate_weight_neg
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    canonicalMoebiusWeight 1 *
        (booleanCubeSign (lowWheelCanonicalRepeatedFrozenProductOneFace y) : ℂ) =
      -(canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) := by
  rcases lowWheelCanonicalRepeatedFrozenCofactor_source_data hy with
    ⟨_hk, _hpPrime, _hpNotC, hsq, _hcgt, _hcR⟩
  let u := squarefreePrimeFace y.2.1
  have hdisj : Disjoint y.1 u := by
    simpa [u] using
      lowWheelCanonicalRepeatedFrozenCofactor_face_disjoint_cofactorFace hy
  have hpNot : lowWheelTaggedDowncrossPivot y ∉ y.1 ∪ u := by
    simpa [u] using
      lowWheelCanonicalRepeatedFrozenCofactor_pivot_not_mem_face_union hy
  have hmuU : μ y.2.1 = booleanCubeSign u := by
    have hprime : ∀ q ∈ u, q.Prime := by
      intro q hq
      exact (Nat.mem_primeFactors.mp (by simpa [u, squarefreePrimeFace] using hq)).1
    have hmu := moebius_primeFaceProduct_eq_booleanCubeSign u hprime
    rw [primeFaceProduct_squarefreePrimeFace hsq] at hmu
    exact hmu
  have hsign :
      booleanCubeSign (lowWheelCanonicalRepeatedFrozenProductOneFace y) =
        -(booleanCubeSign u * booleanCubeSign y.1) := by
    unfold lowWheelCanonicalRepeatedFrozenProductOneFace booleanCubeSign
    rw [Finset.card_insert_of_notMem hpNot,
      Finset.card_union_of_disjoint hdisj, pow_succ, pow_add]
    ring
  rw [hsign]
  unfold canonicalMoebiusWeight
  rw [hmuU]
  push_cast
  simp

end RHLean.Proof
