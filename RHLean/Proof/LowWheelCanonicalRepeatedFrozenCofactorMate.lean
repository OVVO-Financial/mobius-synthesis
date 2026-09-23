import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedFrozenFactorGeometry
import RHLean.Proof.SquareRootLowPrimeGoCrossingMateLedger
import RHLean.Proof.LowWheelSurvivorFloorExpansion
import RHLean.Proof.LowWheelCanonicalDowncrossSignedParentSplit
import RHLean.Arithmetic.PrimeFaceProductUniqueness

/-!
# Existing physical mates for frozen repeated-parent states with c > 1

For a frozen repeated-parent state `y = (t,(c,k))`, classification gives
`k = p`, where `p = minFac(c*k)`, and every Boolean-face prime is below `p`.
The historical mate removes one concrete cofactor prime into the quotient.
The frozen-factor geometry now also supplies a one-shot whole-cofactor mate

`(t,(c,p)) -> (insert p (t ∪ squarefreePrimeFace c),(1,1))`.

The second half of this file proves that this product-one map loses no
multiplicity.  The final face remembers the pivot as its unique first root
crossing: all old face primes are below the pivot, all cofactor primes are above
it, `P(t) <= R`, and `R < p*P(t)`.  Equal product-one faces therefore recover
the pivot, the old face, the cofactor prime face, and the complete source.

Consequently the complete frozen `c>1` ledger cancels exactly against a literal
product-one subledger of the already-existing physical transport carrier.
No norm, root-factorization hypothesis, or asymptotic estimate appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Canonical physical removal prime for a frozen nontrivial cofactor. -/
def lowWheelCanonicalRepeatedFrozenCofactorPrime
    (y : LowWheelTaggedDowncrossState) : ℕ :=
  Nat.minFac y.2.1

/-- The existing physical transport mate, retaining the Boolean face tag. -/
def lowWheelCanonicalRepeatedFrozenCofactorMate
    (y : LowWheelTaggedDowncrossState) : LowWheelTaggedCofactorQuotientState :=
  (y.1, lowWheelCofactorQuotientToggleAt
    (lowWheelCanonicalRepeatedFrozenCofactorPrime y) y.2)

/-- The chosen removal coordinate is prime and divides the source cofactor. -/
theorem lowWheelCanonicalRepeatedFrozenCofactorPrime_spec
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    (lowWheelCanonicalRepeatedFrozenCofactorPrime y).Prime ∧
      lowWheelCanonicalRepeatedFrozenCofactorPrime y ∣ y.2.1 := by
  have hcgt := (Finset.mem_filter.mp hy).2
  have hcne : y.2.1 ≠ 1 := by omega
  constructor
  · simpa only [lowWheelCanonicalRepeatedFrozenCofactorPrime] using
      Nat.minFac_prime hcne
  · simpa only [lowWheelCanonicalRepeatedFrozenCofactorPrime] using
      Nat.minFac_dvd y.2.1

/-- Frozen shape turns the abstract mate into the requested concrete formula
`(t,(c/q,q*p))`. -/
theorem lowWheelCanonicalRepeatedFrozenCofactorMate_eq
    {R c k : ℕ} {t : Finset ℕ}
    (hy : (t, (c, k)) ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    let p := lowWheelTaggedDowncrossPivot (t, (c, k))
    let q := Nat.minFac c
    lowWheelCanonicalRepeatedFrozenCofactorMate (t, (c, k)) =
      (t, (c / q, q * p)) := by
  let p := lowWheelTaggedDowncrossPivot (t, (c, k))
  let q := Nat.minFac c
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hshape := (Finset.mem_filter.mp hfrozen).2
  have hk : k = p := by simpa only [p] using hshape.1
  have hqd : q ∣ c := by
    simpa only [q, lowWheelCanonicalRepeatedFrozenCofactorPrime] using
      (lowWheelCanonicalRepeatedFrozenCofactorPrime_spec hy).2
  change (t, lowWheelCofactorQuotientToggleAt q (c, k)) =
    (t, (c / q, q * p))
  unfold lowWheelCofactorQuotientToggleAt
  simp only [hqd, if_true]
  rw [hk]

/-- The frozen `c>1` mate is a literal occurrence of the already-existing
physical transport ledger on the same Boolean face. -/
theorem lowWheelCanonicalRepeatedFrozenCofactorMate_mem_transport
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelCanonicalRepeatedFrozenCofactorMate y ∈
      lowWheelCanonicalTaggedPhysicalCarrier R := by
  rcases y with ⟨t, ⟨c, k⟩⟩
  let q := lowWheelCanonicalRepeatedFrozenCofactorPrime (t, (c, k))
  have hprime := lowWheelCanonicalRepeatedFrozenCofactorPrime_spec hy
  have hqPrime : q.Prime := by exact hprime.1
  have hqc : q ∣ c := by exact hprime.2
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hxData := mem_lowWheelCanonicalDowncrossPart.mp htag.2
  have hphysData := mem_lowWheelCanonicalPhysicalStateSet.mp hxData.1
  have hcarrier := hphysData.2.2.2
  have hmateCarrier : LowWheelTransportPairCarrier R t
      (lowWheelCofactorQuotientToggleAt q (c, k)) :=
    lowWheelCofactorQuotientToggleAt_preserves_of_dvd_cofactor
      hqPrime hcarrier hqc
  have hmateRanges := lowWheelTransportPairCarrier_mem_ranges hmateCarrier
  have hcdiv : c / q ∣ c := ⟨q, (Nat.div_mul_cancel hqc).symm⟩
  have hmateSq : Squarefree (c / q) :=
    hphysData.2.2.1.squarefree_of_dvd hcdiv
  have hmateSq' :
      Squarefree (lowWheelCofactorQuotientToggleAt q (c, k)).1 := by
    unfold lowWheelCofactorQuotientToggleAt
    simp only [hqc, if_true]
    exact hmateSq
  have hmatePhysical : lowWheelCofactorQuotientToggleAt q (c, k) ∈
      lowWheelCanonicalPhysicalStateSet R t := by
    exact mem_lowWheelCanonicalPhysicalStateSet.mpr
      ⟨hmateRanges.1, hmateRanges.2, hmateSq', hmateCarrier⟩
  apply mem_lowWheelCanonicalTaggedPhysicalCarrier.mpr
  refine ⟨htag.1, ?_⟩
  change lowWheelCofactorQuotientToggleAt q (c, k) ∈
    lowWheelCanonicalPhysicalStateSet R t
  exact hmatePhysical

/-- The existing mate has exactly the opposite signed physical weight. -/
theorem lowWheelCanonicalRepeatedFrozenCofactorMate_weight_neg
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedCanonicalWeight
        (lowWheelCanonicalRepeatedFrozenCofactorMate y) =
      -lowWheelTaggedCanonicalWeight (y.1, y.2) := by
  rcases y with ⟨t, ⟨c, k⟩⟩
  let q := lowWheelCanonicalRepeatedFrozenCofactorPrime (t, (c, k))
  have hprime := lowWheelCanonicalRepeatedFrozenCofactorPrime_spec hy
  have hqPrime : q.Prime := by exact hprime.1
  have hqc : q ∣ c := by exact hprime.2
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hphys := (mem_lowWheelCanonicalDowncrossPart.mp htag.2).1
  have hsq := (mem_lowWheelCanonicalPhysicalStateSet.mp hphys).2.2.1
  simpa only [lowWheelCanonicalRepeatedFrozenCofactorMate,
    lowWheelTaggedCanonicalWeight, q] using
    (lowWheelCofactorQuotientToggleAt_weight_neg
      (t := t) hqPrime hsq (Or.inl hqc))

/-- Squarefreeness makes the removal mate pointwise distinct from its source. -/
theorem lowWheelCanonicalRepeatedFrozenCofactorMate_ne
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelCanonicalRepeatedFrozenCofactorMate y ≠ (y.1, y.2) := by
  rcases y with ⟨t, ⟨c, k⟩⟩
  let q := lowWheelCanonicalRepeatedFrozenCofactorPrime (t, (c, k))
  have hprime := lowWheelCanonicalRepeatedFrozenCofactorPrime_spec hy
  have hqPrime : q.Prime := by exact hprime.1
  have hqc : q ∣ c := by exact hprime.2
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hphys := (mem_lowWheelCanonicalDowncrossPart.mp htag.2).1
  have hsq := (mem_lowWheelCanonicalPhysicalStateSet.mp hphys).2.2.1
  have hnot : ¬ q ∣ c / q :=
    prime_not_dvd_div_of_squarefree hqPrime hsq hqc
  intro heq
  have hstate := congrArg Prod.snd heq
  have hcofactor := congrArg Prod.fst hstate
  change (lowWheelCofactorQuotientToggleAt q (c, k)).1 = c at hcofactor
  unfold lowWheelCofactorQuotientToggleAt at hcofactor
  simp only [hqc, if_true] at hcofactor
  have hqdSource : q ∣ c := hqc
  rw [← hcofactor] at hqdSource
  exact hnot hqdSource

/-! ## Global whole-cofactor product-one reassembly -/

/-- The frozen old face is below the root. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_faceProduct_le_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    primeFaceProduct y.1 ≤ R := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell htag.2
  rcases hshell with ⟨_hpPrime, _hpNotC, _hpDvdK, hdown, _hup⟩
  have hdata := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have hpPos : 0 < lowWheelTaggedDowncrossPivot y := hdata.2.1.pos
  change primeFaceProduct y.1 *
      (y.2.2 / lowWheelTaggedDowncrossPivot y) ≤ R at hdown
  rw [hdata.1, Nat.div_self hpPos, Nat.mul_one] at hdown
  exact hdown

/-- Adjoining the frozen pivot to the old face crosses the root. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_facePivot_crosses_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    R < lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell htag.2
  rcases hshell with ⟨hpRaw, _hpNotC, _hpDvdK, _hdown, hup⟩
  have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
    simpa [lowWheelTaggedDowncrossPivot] using hpRaw
  have hdata := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  change R < primeFaceProduct y.1 *
      (lowWheelTaggedDowncrossPivot y *
        (y.2.2 / lowWheelTaggedDowncrossPivot y)) at hup
  rw [hdata.1, Nat.div_self hp.pos, Nat.mul_one] at hup
  simpa [Nat.mul_comm] using hup

/-- The original Boolean face is the below-pivot part of the final face. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneFace_filter_lt_pivot
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    (lowWheelCanonicalRepeatedFrozenProductOneFace y).filter
        (fun q => q < lowWheelTaggedDowncrossPivot y) = y.1 := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqFace, hqLt⟩
    unfold lowWheelCanonicalRepeatedFrozenProductOneFace at hqFace
    rcases Finset.mem_insert.mp hqFace with hqp | hqu
    · subst q
      omega
    · rcases Finset.mem_union.mp hqu with hqt | hqc
      · exact hqt
      · have hgt := lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_primeFactor hy
          (by simpa [squarefreePrimeFace] using hqc)
        omega
  · intro hqt
    apply Finset.mem_filter.mpr
    refine ⟨?_, lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hqt⟩
    unfold lowWheelCanonicalRepeatedFrozenProductOneFace
    exact Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_union.mpr <| Or.inl hqt

/-- The cofactor prime face is the above-pivot part of the final face. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneFace_filter_pivot_lt
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    (lowWheelCanonicalRepeatedFrozenProductOneFace y).filter
        (fun q => lowWheelTaggedDowncrossPivot y < q) =
      squarefreePrimeFace y.2.1 := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqFace, hpq⟩
    unfold lowWheelCanonicalRepeatedFrozenProductOneFace at hqFace
    rcases Finset.mem_insert.mp hqFace with hqp | hqu
    · subst q
      omega
    · rcases Finset.mem_union.mp hqu with hqt | hqc
      · have hlt := lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hqt
        omega
      · exact hqc
  · intro hqc
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · unfold lowWheelCanonicalRepeatedFrozenProductOneFace
      exact Finset.mem_insert.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr hqc
    · exact lowWheelCanonicalRepeatedFrozenCofactor_pivot_lt_primeFactor hy
        (by simpa [squarefreePrimeFace] using hqc)

private theorem lowWheelCanonicalRepeatedFrozenCofactor_face_mem_powerset
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    y.1 ∈ (primesUpTo R).powerset := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  exact (mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged).1

/-- **No multiplicity loss.**  The product-one face recovers the complete
frozen source. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneMate_injOn
    (R : ℕ) :
    Set.InjOn lowWheelCanonicalRepeatedFrozenProductOneMate
      (lowWheelCanonicalRepeatedFrozenCofactorPart R) := by
  intro y hy z hz hmate
  have hfaceEq :
      lowWheelCanonicalRepeatedFrozenProductOneFace y =
        lowWheelCanonicalRepeatedFrozenProductOneFace z :=
    congrArg Prod.fst hmate
  have hpEq :
      lowWheelTaggedDowncrossPivot y = lowWheelTaggedDowncrossPivot z := by
    rcases lt_trichotomy (lowWheelTaggedDowncrossPivot y)
        (lowWheelTaggedDowncrossPivot z) with hpz | hpz | hzp
    · exfalso
      have hsub : insert (lowWheelTaggedDowncrossPivot y) y.1 ⊆ z.1 := by
        intro r hr
        have hrLtY : r ≤ lowWheelTaggedDowncrossPivot y := by
          rcases Finset.mem_insert.mp hr with hrp | hry
          · subst r
            exact le_rfl
          · exact (lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hry).le
        have hrFinalY :
            r ∈ lowWheelCanonicalRepeatedFrozenProductOneFace y := by
          unfold lowWheelCanonicalRepeatedFrozenProductOneFace
          rcases Finset.mem_insert.mp hr with hrp | hry
          · exact Finset.mem_insert.mpr (Or.inl hrp)
          · exact Finset.mem_insert.mpr <| Or.inr <|
              Finset.mem_union.mpr <| Or.inl hry
        have hrFinalZ :
            r ∈ lowWheelCanonicalRepeatedFrozenProductOneFace z := by
          rw [← hfaceEq]
          exact hrFinalY
        have hrFilter :
            r ∈ (lowWheelCanonicalRepeatedFrozenProductOneFace z).filter
              (fun q => q < lowWheelTaggedDowncrossPivot z) :=
          Finset.mem_filter.mpr ⟨hrFinalZ, lt_of_le_of_lt hrLtY hpz⟩
        rw [lowWheelCanonicalRepeatedFrozenProductOneFace_filter_lt_pivot hz]
          at hrFilter
        exact hrFilter
      have hpNotY : lowWheelTaggedDowncrossPivot y ∉ y.1 := by
        intro hpMem
        have hlt := lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hy hpMem
        omega
      have hprodInsert :
          primeFaceProduct (insert (lowWheelTaggedDowncrossPivot y) y.1) =
            lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := by
        simp [primeFaceProduct, hpNotY]
      have hdiv :
          primeFaceProduct (insert (lowWheelTaggedDowncrossPivot y) y.1) ∣
            primeFaceProduct z.1 := by
        unfold primeFaceProduct
        exact Finset.prod_dvd_prod_of_subset _ _ id hsub
      have hzPos : 0 < primeFaceProduct z.1 :=
        primeFaceProduct_pos_of_mem_powerset
          (lowWheelCanonicalRepeatedFrozenCofactor_face_mem_powerset hz)
      have hle := Nat.le_of_dvd hzPos hdiv
      have hcross := lowWheelCanonicalRepeatedFrozenCofactor_facePivot_crosses_root hy
      have hzLow := lowWheelCanonicalRepeatedFrozenCofactor_faceProduct_le_root hz
      rw [hprodInsert] at hle
      omega
    · exact hpz
    · exfalso
      have hsub : insert (lowWheelTaggedDowncrossPivot z) z.1 ⊆ y.1 := by
        intro r hr
        have hrLtZ : r ≤ lowWheelTaggedDowncrossPivot z := by
          rcases Finset.mem_insert.mp hr with hrp | hrz
          · subst r
            exact le_rfl
          · exact (lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hz hrz).le
        have hrFinalZ :
            r ∈ lowWheelCanonicalRepeatedFrozenProductOneFace z := by
          unfold lowWheelCanonicalRepeatedFrozenProductOneFace
          rcases Finset.mem_insert.mp hr with hrp | hrz
          · exact Finset.mem_insert.mpr (Or.inl hrp)
          · exact Finset.mem_insert.mpr <| Or.inr <|
              Finset.mem_union.mpr <| Or.inl hrz
        have hrFinalY :
            r ∈ lowWheelCanonicalRepeatedFrozenProductOneFace y := by
          rw [hfaceEq]
          exact hrFinalZ
        have hrFilter :
            r ∈ (lowWheelCanonicalRepeatedFrozenProductOneFace y).filter
              (fun q => q < lowWheelTaggedDowncrossPivot y) :=
          Finset.mem_filter.mpr ⟨hrFinalY, lt_of_le_of_lt hrLtZ hzp⟩
        rw [lowWheelCanonicalRepeatedFrozenProductOneFace_filter_lt_pivot hy]
          at hrFilter
        exact hrFilter
      have hpNotZ : lowWheelTaggedDowncrossPivot z ∉ z.1 := by
        intro hpMem
        have hlt := lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hz hpMem
        omega
      have hprodInsert :
          primeFaceProduct (insert (lowWheelTaggedDowncrossPivot z) z.1) =
            lowWheelTaggedDowncrossPivot z * primeFaceProduct z.1 := by
        simp [primeFaceProduct, hpNotZ]
      have hdiv :
          primeFaceProduct (insert (lowWheelTaggedDowncrossPivot z) z.1) ∣
            primeFaceProduct y.1 := by
        unfold primeFaceProduct
        exact Finset.prod_dvd_prod_of_subset _ _ id hsub
      have hyPos : 0 < primeFaceProduct y.1 :=
        primeFaceProduct_pos_of_mem_powerset
          (lowWheelCanonicalRepeatedFrozenCofactor_face_mem_powerset hy)
      have hle := Nat.le_of_dvd hyPos hdiv
      have hcross := lowWheelCanonicalRepeatedFrozenCofactor_facePivot_crosses_root hz
      have hyLow := lowWheelCanonicalRepeatedFrozenCofactor_faceProduct_le_root hy
      rw [hprodInsert] at hle
      omega
  have hface : y.1 = z.1 := by
    calc
      y.1 = (lowWheelCanonicalRepeatedFrozenProductOneFace y).filter
          (fun q => q < lowWheelTaggedDowncrossPivot y) :=
        (lowWheelCanonicalRepeatedFrozenProductOneFace_filter_lt_pivot hy).symm
      _ = (lowWheelCanonicalRepeatedFrozenProductOneFace z).filter
          (fun q => q < lowWheelTaggedDowncrossPivot z) := by
        rw [hfaceEq, hpEq]
      _ = z.1 := lowWheelCanonicalRepeatedFrozenProductOneFace_filter_lt_pivot hz
  have hcofactorFace :
      squarefreePrimeFace y.2.1 = squarefreePrimeFace z.2.1 := by
    calc
      squarefreePrimeFace y.2.1 =
          (lowWheelCanonicalRepeatedFrozenProductOneFace y).filter
            (fun q => lowWheelTaggedDowncrossPivot y < q) :=
        (lowWheelCanonicalRepeatedFrozenProductOneFace_filter_pivot_lt hy).symm
      _ = (lowWheelCanonicalRepeatedFrozenProductOneFace z).filter
          (fun q => lowWheelTaggedDowncrossPivot z < q) := by
        rw [hfaceEq, hpEq]
      _ = squarefreePrimeFace z.2.1 :=
        lowWheelCanonicalRepeatedFrozenProductOneFace_filter_pivot_lt hz
  have hyData := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have hzData := lowWheelCanonicalRepeatedFrozenCofactor_source_data hz
  have hc : y.2.1 = z.2.1 := by
    calc
      y.2.1 = primeFaceProduct (squarefreePrimeFace y.2.1) :=
        (primeFaceProduct_squarefreePrimeFace hyData.2.2.2.1).symm
      _ = primeFaceProduct (squarefreePrimeFace z.2.1) := by rw [hcofactorFace]
      _ = z.2.1 := primeFaceProduct_squarefreePrimeFace hzData.2.2.2.1
  have hk : y.2.2 = z.2.2 := by
    calc
      y.2.2 = lowWheelTaggedDowncrossPivot y := hyData.1
      _ = lowWheelTaggedDowncrossPivot z := hpEq
      _ = z.2.2 := hzData.1.symm
  exact Prod.ext hface (Prod.ext hc hk)

/-- Literal image of the frozen product-one mates. -/
def lowWheelCanonicalRepeatedFrozenProductOneMateImage (R : ℕ) :
    Finset LowWheelTaggedCofactorQuotientState :=
  (lowWheelCanonicalRepeatedFrozenCofactorPart R).image
    lowWheelCanonicalRepeatedFrozenProductOneMate

/-- Every mate image occurrence is already in the global tagged physical
transport carrier. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneMateImage_subset_transport
    (R : ℕ) :
    lowWheelCanonicalRepeatedFrozenProductOneMateImage R ⊆
      lowWheelCanonicalTaggedPhysicalCarrier R := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  apply mem_lowWheelCanonicalTaggedPhysicalCarrier.mpr
  exact ⟨lowWheelCanonicalRepeatedFrozenProductOneFace_mem_powerset hy,
    lowWheelCanonicalRepeatedFrozenProductOneMate_mem_physical hy⟩

/-- Signed product-one mate ledger. -/
def lowWheelCanonicalRepeatedFrozenProductOneMateLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R,
    lowWheelTaggedCanonicalWeight
      (lowWheelCanonicalRepeatedFrozenProductOneMate y)

/-- Source and one-shot product-one mate have opposite tagged weights. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneMate_taggedWeight_neg
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedCanonicalWeight
        (lowWheelCanonicalRepeatedFrozenProductOneMate y) =
      -lowWheelTaggedDowncrossWeight y := by
  simpa [lowWheelTaggedCanonicalWeight,
    lowWheelTaggedDowncrossWeight,
    lowWheelCanonicalRepeatedFrozenProductOneMate] using
      lowWheelCanonicalRepeatedFrozenProductOneMate_weight_neg hy

/-- Injectivity turns the source-indexed mate ledger into the literal image
subledger. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneMateLedger_eq_imageSum
    (R : ℕ) :
    lowWheelCanonicalRepeatedFrozenProductOneMateLedger R =
      ∑ z ∈ lowWheelCanonicalRepeatedFrozenProductOneMateImage R,
        lowWheelTaggedCanonicalWeight z := by
  unfold lowWheelCanonicalRepeatedFrozenProductOneMateLedger
    lowWheelCanonicalRepeatedFrozenProductOneMateImage
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact lowWheelCanonicalRepeatedFrozenProductOneMate_injOn R ha hb hab

/-- **Exact global whole-cofactor cancellation.**  The complete frozen `c>1`
source ledger cancels against its already-physical product-one mate image before
any norm is taken. -/
theorem sum_lowWheelCanonicalRepeatedFrozenCofactor_add_productOneMate_eq_zero
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R,
        lowWheelTaggedDowncrossWeight y) +
      lowWheelCanonicalRepeatedFrozenProductOneMateLedger R = 0 := by
  unfold lowWheelCanonicalRepeatedFrozenProductOneMateLedger
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro y hy
  rw [lowWheelCanonicalRepeatedFrozenProductOneMate_taggedWeight_neg hy]
  ring

end RHLean.Proof
