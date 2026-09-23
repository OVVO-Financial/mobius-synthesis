import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoReducedSourcePacket
import RHLean.Proof.LowWheelFrozenSecondContactRoughPrefix
import RHLean.Proof.LowWheelFrozenSecondContactWindowReassembly

/-!
# Combined residual / saturated second-contact pushforward

This module is deliberately structural.  It takes no norm and proves no energy
estimate.  The first job is to place the full-face Go source from an earlier layer on the
*existing saturated* second-contact arithmetic carrier, not on the superseded
loose `X/q^2` window and not on a fictitious square-divisible deletion cell.

For an incidence `((r,q),d)`, write

`n = q * (r*d)`.

An earlier layer proves that the physical full-face source is pre-contact for `q`: `q`
appears once and one further `q` crosses the square endpoint.  The independent
arithmetic description of the saturated carrier says that `n` is a genuine
second-contact child exactly when the additional root-floor wall

`R*q < n`

holds.  Here that wall is simply `R < r*d`.  Thus the full-face defect splits
canonically into a saturated child population and the explicit root-floor
failure `r*d <= R`.

The saturated child has the correct signed orientation: the full-face source
weight is `mu(q*d)`, while the arithmetic child has weight `mu(q*r*d) =
-mu(q*d)`.  This is exactly the minus sign in
`lowWheelFrozenSecondContactSource_sum_eq_neg_crossColumnChildMass`.

No statement below treats the root-floor complement as generic leakage; it is
kept as its literal incidence carrier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Full-face defect incidences whose represented pre-contact integer is above
the saturated `R*q` root floor. -/
def squareRootLowPrimeGoFullFaceDefectSaturatedIncidences (R : ℕ) :
    Finset SquareRootLowPrimeGoFullFaceDefectIncidence :=
  (squareRootLowPrimeGoFullFaceDefectCarrier R).filter fun z =>
    R < z.1.1 * z.2

/-- The exact complementary root-floor failures. -/
def squareRootLowPrimeGoFullFaceDefectRootFloorIncidences (R : ℕ) :
    Finset SquareRootLowPrimeGoFullFaceDefectIncidence :=
  (squareRootLowPrimeGoFullFaceDefectCarrier R).filter fun z =>
    z.1.1 * z.2 <= R

/-- Arithmetic pre-contact child represented by one full-face source. -/
def squareRootLowPrimeGoFullFaceDefectArithmeticChild
    (z : SquareRootLowPrimeGoFullFaceDefectIncidence) : ℕ :=
  z.1.2 * (z.1.1 * z.2)

@[simp] theorem mem_squareRootLowPrimeGoFullFaceDefectSaturatedIncidences
    {R r q d : ℕ} :
    ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R ↔
      ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R ∧
        R < r * d := by
  simp [squareRootLowPrimeGoFullFaceDefectSaturatedIncidences]

@[simp] theorem mem_squareRootLowPrimeGoFullFaceDefectRootFloorIncidences
    {R r q d : ℕ} :
    ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R ↔
      ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R ∧
        r * d <= R := by
  simp [squareRootLowPrimeGoFullFaceDefectRootFloorIncidences]

/-- The two incidence populations are an exact partition of the defect. -/
theorem squareRootLowPrimeGoFullFaceDefectCarrier_eq_saturated_union_rootFloor
    (R : ℕ) :
    squareRootLowPrimeGoFullFaceDefectCarrier R =
      squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R ∪
        squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R := by
  ext z
  rcases z with ⟨⟨r, q⟩, d⟩
  by_cases h : R < r * d
  · simp [h]
  · have hle : r * d <= R := Nat.le_of_not_gt h
    simp [h, hle]

/-- The saturated and root-floor pieces are disjoint. -/
theorem squareRootLowPrimeGoFullFaceDefectSaturated_disjoint_rootFloor
    (R : ℕ) :
    Disjoint (squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R)
      (squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R) := by
  rw [Finset.disjoint_left]
  intro z hsat hroot
  rcases z with ⟨⟨r, q⟩, d⟩
  have hlt :=
    (mem_squareRootLowPrimeGoFullFaceDefectSaturatedIncidences.mp hsat).2
  have hle :=
    (mem_squareRootLowPrimeGoFullFaceDefectRootFloorIncidences.mp hroot).2
  omega

/-- On a live defect incidence the source high product is exactly the
independent arithmetic child.  Squarefreeness of `r*d` is essential here; it is
not a definitional equality for an arbitrary triple. -/
theorem squareRootLowPrimeGoFullFaceDefectSource_highProduct_eq_child
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    lowWheelTaggedHighProduct
        (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) =
      squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d) := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, hd⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth hq hr hrq hfull
  have hsqRD : Squarefree (r * d) := hchild.1.2.2.1
  change primeFaceProduct (squarefreePrimeFace (r * d)) * q = q * (r * d)
  rw [primeFaceProduct_squarefreePrimeFace hsqRD]
  ring

/-- The distinguished outer owner is the canonical largest prime of the
arithmetic child. -/
theorem squareRootLowPrimeGoFullFaceDefectArithmeticChild_largestPrime
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    canonicalLargestPrimeFactor
        (squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d)) = q := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, hd⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth hq hr hrq hfull
  rcases hchild.1 with ⟨_hq, hrd1, _hsq, _hcop, hdom⟩
  have hrdgt : 1 < r * d := lt_trans hq.one_lt hchild.2
  have hrough : canonicalLargestPrimeFactor (r * d) < q :=
    hdom _ (canonicalLargestPrimeFactor_prime hrdgt)
      (canonicalLargestPrimeFactor_dvd hrdgt)
  have htop := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
    (by omega : 0 < r * d) hq hrough
  simpa [squareRootLowPrimeGoFullFaceDefectArithmeticChild, Nat.mul_comm] using htop

/-- **Positive splice.**  Above the root floor, the represented full-face Go
source integer is literally a member of the independent saturated second-contact
arithmetic child carrier.  The state itself is pre-contact; the carrier records
that one further copy of its canonical largest prime crosses the endpoint. -/
theorem squareRootLowPrimeGoFullFaceDefectArithmeticChild_mem_saturatedCarrier
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R) :
    squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d) ∈
      lowWheelFrozenSecondContactArithmeticChildCarrier R := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectSaturatedIncidences.mp hz with
    ⟨hzFull, hroot⟩
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hzFull with
    ⟨_hrR, hqR, _hdR, hr, hq, hrq, hcube, hd⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth hq hr hrq hfull
  rcases hchild.1 with ⟨_hq, hrd1, hsqRD, hcop, _hdom⟩
  have hsq : Squarefree (q * (r * d)) :=
    (Nat.squarefree_mul hcop).2 ⟨hq.squarefree, hsqRD⟩
  have hfirst :=
    squareRootLowPrimeGoFullBirthBoundary_firstContact_le
      hq hrq hcube hfull
  have hsecond :=
    squareRootLowPrimeGoSecondBoundaryDefect_secondContact_gt hq hr hd
  have hlpf :=
    squareRootLowPrimeGoFullFaceDefectArithmeticChild_largestPrime hzFull
  unfold lowWheelFrozenSecondContactArithmeticChildCarrier
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hsq, ?_, ?_, ?_⟩
  · have hqle : q ≤ q * (r * d) :=
      Nat.le_mul_of_pos_right q (by omega)
    exact hq.two_le.trans hqle
  · simpa [squareRootLowPrimeGoFullFaceDefectArithmeticChild] using hfirst
  · simpa [hlpf] using hqR
  · rw [hlpf]
    simpa [squareRootLowPrimeGoFullFaceDefectArithmeticChild,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsecond
  · rw [hlpf]
    have hmul := Nat.mul_lt_mul_of_pos_right hroot hq.pos
    simpa [squareRootLowPrimeGoFullFaceDefectArithmeticChild,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul

/-- Below the root floor the same arithmetic integer is *not* in the saturated
carrier: the failed condition is exactly `R*q < n`. -/
theorem squareRootLowPrimeGoFullFaceDefectArithmeticChild_not_mem_saturatedCarrier
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R) :
    squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d) ∉
      lowWheelFrozenSecondContactArithmeticChildCarrier R := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectRootFloorIncidences.mp hz with
    ⟨hzFull, hroot⟩
  have hlpf :=
    squareRootLowPrimeGoFullFaceDefectArithmeticChild_largestPrime hzFull
  intro hmem
  have hwall := (Finset.mem_filter.mp hmem).2.2.2.2
  rw [hlpf] at hwall
  have hq :=
    (mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hzFull).2.2.2.2.1
  have hmul :
      squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d) <= R * q := by
    have := Nat.mul_le_mul_right q hroot
    simpa [squareRootLowPrimeGoFullFaceDefectArithmeticChild,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
  omega

/-- The source sign is exactly the saturated-source orientation: it is the
negative ordinary Mobius weight of the arithmetic child. -/
theorem squareRootLowPrimeGoFullFaceDefectSource_weight_eq_neg_child
    {R r q d : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    lowWheelFullTaggedPhysicalWeight
        (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) =
      -canonicalMoebiusWeight
        (squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d)) := by
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, hd⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hsource :=
    squareRootLowPrimeGoSecondBoundaryFullFaceSource_weight_eq
      hq hr hrq hfull
  have hmu :=
    squareRootLowPrimeGoFullBirthBoundary_source_moebius_cancel
      hq hr hrq hfull
  have hmu' : (μ (q * d) : ℤ) = -(μ (q * (r * d)) : ℤ) := by
    linarith
  calc
    lowWheelFullTaggedPhysicalWeight
        (squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d)) =
      canonicalMoebiusWeight (q * d) := by
        simpa [squareRootLowPrimeGoFullFaceDefectSourceTag] using hsource
    _ = -canonicalMoebiusWeight (q * (r * d)) := by
      unfold canonicalMoebiusWeight
      exact_mod_cast hmu'
    _ = -canonicalMoebiusWeight
        (squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d)) := by
      rfl

/-- The full-face source is not literally one of the frozen nontrivial-cofactor
second-contact source states: its low cofactor is `1`.  This records the
coordinate change that the arithmetic-child map above performs. -/
theorem squareRootLowPrimeGoFullFaceDefectSource_not_literal_frozenSource
    {R r q d : ℕ}
    (_hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d) ∉
      lowWheelCanonicalRepeatedFrozenSecondContactPart R := by
  intro hmem
  have hfrozen := (Finset.mem_filter.mp hmem).1
  have hdata := lowWheelCanonicalRepeatedFrozenCofactor_source_data hfrozen
  have hcgt := hdata.2.2.2.2.1
  change 1 < (1 : ℕ) at hcgt
  omega

/-- Nor is the full-face source literally a RoughPrefix historical fixed
transport mate: every such mate has cofactor/quotient state `(1,1)`, while the
Go pre-contact source retains the prime quotient `q`. -/
theorem squareRootLowPrimeGoFullFaceDefectSource_not_literal_matchingFixedTransport
    {R r q d A : ℕ}
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    squareRootLowPrimeGoFullFaceDefectSourceTag ((r, q), d) ∉
      lowWheelFrozenSourceScaleTransportCarrier R A := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨y, _hy, heq⟩
  have hstate := congrArg (fun z : LowWheelTaggedCofactorQuotientState => z.2) heq
  have hqPrime :=
    (mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz).2.2.2.2.1
  have hqTwo := hqPrime.two_le
  simp [squareRootLowPrimeGoFullFaceDefectSourceTag,
    squareRootLowPrimeGoSecondBoundaryFullFaceSource,
    lowWheelCanonicalRepeatedFrozenProductOneMate] at hstate
  omega

/-! ## Multiplicity-free deep image and exact signed reassembly -/

/-- The saturated arithmetic child remembers the entire defect incidence.
First recover `q` as the largest prime of the child; then recover `r*d` by
cancelling `q`; finally `r` is the largest prime of `r*d`, and `d` follows by
cancellation. -/
theorem squareRootLowPrimeGoFullFaceDefectArithmeticChild_injOn_saturated
    (R : ℕ) :
    Set.InjOn squareRootLowPrimeGoFullFaceDefectArithmeticChild
      (squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R) := by
  intro a ha b hb hab
  rcases a with ⟨⟨r, q⟩, d⟩
  rcases b with ⟨⟨s, t⟩, e⟩
  have haFull :=
    (mem_squareRootLowPrimeGoFullFaceDefectSaturatedIncidences.mp ha).1
  have hbFull :=
    (mem_squareRootLowPrimeGoFullFaceDefectSaturatedIncidences.mp hb).1
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp haFull with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, hd⟩
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hbFull with
    ⟨_hsR, _htR, _heR, hs, ht, hst, _hcube', he⟩
  have hqt : q = t := by
    calc
      q = canonicalLargestPrimeFactor
          (squareRootLowPrimeGoFullFaceDefectArithmeticChild ((r, q), d)) :=
        (squareRootLowPrimeGoFullFaceDefectArithmeticChild_largestPrime haFull).symm
      _ = canonicalLargestPrimeFactor
          (squareRootLowPrimeGoFullFaceDefectArithmeticChild ((s, t), e)) :=
        congrArg canonicalLargestPrimeFactor hab
      _ = t :=
        squareRootLowPrimeGoFullFaceDefectArithmeticChild_largestPrime hbFull
  subst t
  have hrd : r * d = s * e := by
    have hqpos : 0 < q := hq.pos
    apply Nat.eq_of_mul_eq_mul_left hqpos
    simpa [squareRootLowPrimeGoFullFaceDefectArithmeticChild] using hab
  have hfullD :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hfullE :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp he).1
  have hdData := mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfullD
  have heData := mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfullE
  have hdPos : 0 < d := by omega
  have hePos : 0 < e := by omega
  have hrTop : canonicalLargestPrimeFactor (r * d) = r := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hdPos hr hdData.2.2.2.1
    simpa [Nat.mul_comm] using h
  have hsTop : canonicalLargestPrimeFactor (s * e) = s := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hePos hs heData.2.2.2.1
    simpa [Nat.mul_comm] using h
  have hrs : r = s := by
    calc
      r = canonicalLargestPrimeFactor (r * d) := hrTop.symm
      _ = canonicalLargestPrimeFactor (s * e) := congrArg _ hrd
      _ = s := hsTop
  subst s
  have hde : d = e := Nat.eq_of_mul_eq_mul_left hr.pos hrd
  subst e
  rfl

/-- Literal multiplicity-free arithmetic image of the deep full-face defect. -/
def squareRootLowPrimeGoFullFaceDefectSaturatedChildCarrier (R : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R).image
    squareRootLowPrimeGoFullFaceDefectArithmeticChild

/-- The entire deep image is a subcarrier of the already-existing saturated
second-contact arithmetic population. -/
theorem squareRootLowPrimeGoFullFaceDefectSaturatedChildCarrier_subset
    (R : ℕ) :
    squareRootLowPrimeGoFullFaceDefectSaturatedChildCarrier R ⊆
      lowWheelFrozenSecondContactArithmeticChildCarrier R := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
  rcases z with ⟨⟨r, q⟩, d⟩
  exact squareRootLowPrimeGoFullFaceDefectArithmeticChild_mem_saturatedCarrier hz

/-- Deep source ledger, still in the literal physical source coordinates. -/
def squareRootLowPrimeGoFullFaceDefectSaturatedSourceLedger (R : ℕ) : ℂ :=
  ∑ z ∈ squareRootLowPrimeGoFullFaceDefectSaturatedIncidences R,
    lowWheelFullTaggedPhysicalWeight
      (squareRootLowPrimeGoFullFaceDefectSourceTag z)

/-- Explicit root-floor source ledger.  This is a named boundary carrier, not a
catch-all remainder. -/
def squareRootLowPrimeGoFullFaceDefectRootFloorSourceLedger (R : ℕ) : ℂ :=
  ∑ z ∈ squareRootLowPrimeGoFullFaceDefectRootFloorIncidences R,
    lowWheelFullTaggedPhysicalWeight
      (squareRootLowPrimeGoFullFaceDefectSourceTag z)

/-- Exact defect partition at ledger level. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceLedger_eq_saturated_add_rootFloor
    (R : ℕ) :
    squareRootLowPrimeGoFullFaceDefectSourceLedger R =
      squareRootLowPrimeGoFullFaceDefectSaturatedSourceLedger R +
        squareRootLowPrimeGoFullFaceDefectRootFloorSourceLedger R := by
  unfold squareRootLowPrimeGoFullFaceDefectSourceLedger
    squareRootLowPrimeGoFullFaceDefectSaturatedSourceLedger
    squareRootLowPrimeGoFullFaceDefectRootFloorSourceLedger
  rw [squareRootLowPrimeGoFullFaceDefectCarrier_eq_saturated_union_rootFloor R,
    Finset.sum_union
      (squareRootLowPrimeGoFullFaceDefectSaturated_disjoint_rootFloor R)]

/-- **Exact deep signed pushforward.**  No incidence multiplicity survives: the
deep full-face defect source is exactly the negative Mobius mass of one literal
subcarrier of the saturated second-contact arithmetic population. -/
theorem squareRootLowPrimeGoFullFaceDefectSaturatedSourceLedger_eq_neg_childMass
    (R : ℕ) :
    squareRootLowPrimeGoFullFaceDefectSaturatedSourceLedger R =
      -∑ n ∈ squareRootLowPrimeGoFullFaceDefectSaturatedChildCarrier R,
        canonicalMoebiusWeight n := by
  unfold squareRootLowPrimeGoFullFaceDefectSaturatedSourceLedger
    squareRootLowPrimeGoFullFaceDefectSaturatedChildCarrier
  rw [Finset.sum_image
    (squareRootLowPrimeGoFullFaceDefectArithmeticChild_injOn_saturated R)]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rcases z with ⟨⟨r, q⟩, d⟩
  exact squareRootLowPrimeGoFullFaceDefectSource_weight_eq_neg_child
    ((mem_squareRootLowPrimeGoFullFaceDefectSaturatedIncidences.mp hz).1)

/-- An earlier layer combined with the multiplicity-free deep pushforward.  The old
hard physical residual is deliberately retained rather than renamed as a
boundary.  Therefore this is an exact diagnostic normal form: any completion of
an earlier layer must identify that old-residual summand with the complementary saturated
11/`q^2` assembly, or else the architecture has reached the old wall. -/
theorem oldResidual_add_fullFaceDefect_eq_oldResidual_sub_deepChild_add_rootFloor
    {R : ℕ} (_hR : 6 ≤ R) :
    lowWheelFrozenTopFarPhysicalResidualLedger R +
        ((squareRootLowPrimeGoFullFaceDefectSourceMass R : ℤ) : ℂ) =
      lowWheelFrozenTopFarPhysicalResidualLedger R -
          (∑ n ∈ squareRootLowPrimeGoFullFaceDefectSaturatedChildCarrier R,
            canonicalMoebiusWeight n) +
        squareRootLowPrimeGoFullFaceDefectRootFloorSourceLedger R := by
  rw [← squareRootLowPrimeGoFullFaceDefectSourceLedger_eq_mass,
    squareRootLowPrimeGoFullFaceDefectSourceLedger_eq_saturated_add_rootFloor,
    squareRootLowPrimeGoFullFaceDefectSaturatedSourceLedger_eq_neg_childMass]
  ring

end RHLean.Proof