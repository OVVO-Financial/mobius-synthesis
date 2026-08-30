import Mathlib
import RHLean.Proof.LowWheelCanonicalDefectReduction
import RHLean.Proof.SquareRootLowPrimeGoGlobalPartner

/-!
# Strict Go crossing mates as an existing transport subledger

`SquareRootLowPrimeGoGlobalPartner` proves a pointwise fact: a strict Go crossing
incidence has a distinct opposite-sign canonical mate in the same low-wheel
physical carrier.  Pointwise pairability alone does not cancel a one-sided
crossing census.  The mate must occur, with the same multiplicity and without a
double count, in a summand already present in the global endpoint identity.

This file records exactly that missing bookkeeping step.

A strict crossing incidence is kept as the literal triple `((r,q),d)`.  Its
source and mate are embedded into the global transport ledger as *tagged*
`(face,state)` coordinates

`({r}, (d,q))`

and

`({r}, toggle(d,q))`.

The tag is essential: two arithmetic states living on different low-wheel faces
are two different occurrences of the nested global ledger.  The source map and
the mate map are injective on the strict crossing carrier.  Their images are
disjoint: every Go source is in the canonical removal orientation (its pivot
divides the cofactor), whereas the resulting mate has that same pivot absent
from its cofactor.

Both images are literal subsets of the tagged support of
`lowWheelCanonicalPhysicalLedger R`.  The repository already proves

`squareRootTransportCofactorFirst R = lowWheelCanonicalPhysicalLedger R`,

so the mate image is not a newly invented family: it is a finite subledger of
the transport term that already occurs in the square-prefix Mertens identity.
The strict source ledger plus that existing mate subledger is exactly zero.

No norm, asymptotic estimate, prime-count estimate, or further Euler descent is
used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A global crossing incidence keeps both prime owners and the literal defect
parent. -/
abbrev SquareRootLowPrimeGoCrossingIncidence := (ℕ × ℕ) × ℕ

/-- The strict part of the square-endpoint crossing population.  The
coordinates are `((r,q),d)` with `r < q`; the last strict inequality separates
this carrier from the exact root face `r*q = R`. -/
def squareRootLowPrimeGoStrictCrossingCarrier
    (R : ℕ) : Finset SquareRootLowPrimeGoCrossingIncidence :=
  (((Finset.range R).product (Finset.range R)).product (Finset.range R)).filter
    fun z =>
      z.1.1.Prime ∧ z.1.2.Prime ∧ z.1.1 < z.1.2 ∧
        z.1.2 ^ 3 ≤ squareRootEndpoint R ∧
        squareRootEndpoint R < (z.1.2 * z.1.1) ^ 2 ∧
        R < z.1.1 * z.1.2 ∧
        z.2 ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
          z.1.2 (squareRootEndpoint R) z.1.1

@[simp] theorem mem_squareRootLowPrimeGoStrictCrossingCarrier
    {R r q d : ℕ} :
    ((r, q), d) ∈ squareRootLowPrimeGoStrictCrossingCarrier R ↔
      r < R ∧ q < R ∧ d < R ∧
        r.Prime ∧ q.Prime ∧ r < q ∧
        q ^ 3 ≤ squareRootEndpoint R ∧
        squareRootEndpoint R < (q * r) ^ 2 ∧
        R < r * q ∧
        d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
          q (squareRootEndpoint R) r := by
  simp [squareRootLowPrimeGoStrictCrossingCarrier, and_assoc]

/-- A tagged transport occurrence remembers the outer Boolean face as well as
the cofactor/quotient state. -/
abbrev LowWheelTaggedCofactorQuotientState :=
  Finset ℕ × LowWheelCofactorQuotientState

/-- The exact support of the nested physical transport ledger, flattened only
by tagging every state with its original face. -/
def lowWheelCanonicalTaggedPhysicalCarrier
    (R : ℕ) : Finset LowWheelTaggedCofactorQuotientState := by
  classical
  exact (primesUpTo R).powerset.biUnion fun t =>
    (lowWheelCanonicalPhysicalStateSet R t).image fun x => (t, x)

@[simp] theorem mem_lowWheelCanonicalTaggedPhysicalCarrier
    {R : ℕ} {y : LowWheelTaggedCofactorQuotientState} :
    y ∈ lowWheelCanonicalTaggedPhysicalCarrier R ↔
      y.1 ∈ (primesUpTo R).powerset ∧
        y.2 ∈ lowWheelCanonicalPhysicalStateSet R y.1 := by
  classical
  constructor
  · intro hy
    rcases Finset.mem_biUnion.mp hy with ⟨t, ht, hy⟩
    rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
    subst y
    exact ⟨ht, hx⟩
  · intro hy
    rcases hy with ⟨ht, hx⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨y.1, ht, ?_⟩
    exact Finset.mem_image.mpr ⟨y.2, hx, Prod.ext rfl rfl⟩

/-- The source occurrence of one strict crossing incidence. -/
def squareRootLowPrimeGoStrictCrossingSourceTag
    (z : SquareRootLowPrimeGoCrossingIncidence) :
    LowWheelTaggedCofactorQuotientState :=
  (({z.1.1} : Finset ℕ), (z.2, z.1.2))

/-- The canonical mate occurrence of the same incidence. -/
def squareRootLowPrimeGoStrictCrossingMateTag
    (z : SquareRootLowPrimeGoCrossingIncidence) :
    LowWheelTaggedCofactorQuotientState :=
  (({z.1.1} : Finset ℕ),
    lowWheelCanonicalCofactorQuotientToggle (z.2, z.1.2))

/-- Signed weight of one tagged physical transport occurrence. -/
def lowWheelTaggedCanonicalWeight
    (y : LowWheelTaggedCofactorQuotientState) : ℂ :=
  canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)

/-- Source occurrences are literal occurrences of the already-existing global
physical transport ledger. -/
theorem squareRootLowPrimeGoStrictCrossingSourceTag_mem_transport
    {R : ℕ} (hR : 2 ≤ R)
    {z : SquareRootLowPrimeGoCrossingIncidence}
    (hz : z ∈ squareRootLowPrimeGoStrictCrossingCarrier R) :
    squareRootLowPrimeGoStrictCrossingSourceTag z ∈
      lowWheelCanonicalTaggedPhysicalCarrier R := by
  rcases z with ⟨⟨r, q⟩, d⟩
  rcases mem_squareRootLowPrimeGoStrictCrossingCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, hcube, _hcross, hroot, hd⟩
  apply mem_lowWheelCanonicalTaggedPhysicalCarrier.mpr
  constructor
  · exact squareRootLowPrimeGoStrictCrossing_face_mem_global
      hR hq hr hrq hcube
  · exact squareRootLowPrimeGoStrictCrossing_mem_transport
      hR hq hr hrq hcube hroot hd

/-- Mate occurrences are also literal occurrences of that same pre-existing
transport ledger. -/
theorem squareRootLowPrimeGoStrictCrossingMateTag_mem_transport
    {R : ℕ} (hR : 2 ≤ R)
    {z : SquareRootLowPrimeGoCrossingIncidence}
    (hz : z ∈ squareRootLowPrimeGoStrictCrossingCarrier R) :
    squareRootLowPrimeGoStrictCrossingMateTag z ∈
      lowWheelCanonicalTaggedPhysicalCarrier R := by
  rcases z with ⟨⟨r, q⟩, d⟩
  rcases mem_squareRootLowPrimeGoStrictCrossingCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, hcube, _hcross, hroot, hd⟩
  have hpair := squareRootLowPrimeGoStrictCrossing_mem_transport_pairable
    hR hq hr hrq hcube hroot hd
  have hmate := (Finset.mem_filter.mp hpair).2.1
  apply mem_lowWheelCanonicalTaggedPhysicalCarrier.mpr
  exact ⟨squareRootLowPrimeGoStrictCrossing_face_mem_global
      hR hq hr hrq hcube,
    hmate⟩

/-- The source tag loses no multiplicity. -/
theorem squareRootLowPrimeGoStrictCrossingSourceTag_injective :
    Function.Injective squareRootLowPrimeGoStrictCrossingSourceTag := by
  intro a b hab
  rcases a with ⟨⟨r, q⟩, d⟩
  rcases b with ⟨⟨s, t⟩, e⟩
  have hface : ({r} : Finset ℕ) = {s} := congrArg Prod.fst hab
  have hrs : r = s := by simpa using hface
  have hstate : (d, q) = (e, t) := congrArg Prod.snd hab
  have hde : d = e := congrArg Prod.fst hstate
  have hqt : q = t := congrArg Prod.snd hstate
  subst s
  subst e
  subst t
  rfl

/-- The removal mate has the invariant canonical pivot absent from its new
cofactor.  This supplies an orientation label separating the source and mate
populations. -/
theorem squareRootLowPrimeGoFullBirthBoundary_matePivot_not_dvd_cofactor
    {q r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    ¬ lowWheelCanonicalCofactorQuotientPivot
          (lowWheelCanonicalCofactorQuotientToggle (d, q)) ∣
        (lowWheelCanonicalCofactorQuotientToggle (d, q)).1 := by
  have hdgt := squareRootLowPrimeGoFullBirthBoundary_parent_one_lt hr hrq hd
  have hsq := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd).2.2.1
  have hne : d * q ≠ 1 := by nlinarith [hdgt, hq.two_le]
  have hp := lowWheelCanonicalCofactorQuotientPivot_prime hne
  have hpDvd :=
    squareRootLowPrimeGoFullBirthBoundary_canonicalPivot_dvd_parent
      hq hr hrq hd
  rw [lowWheelCanonicalCofactorQuotientPivot_toggle]
  change ¬ lowWheelCanonicalCofactorQuotientPivot (d, q) ∣
    (lowWheelCofactorQuotientToggleAt
      (lowWheelCanonicalCofactorQuotientPivot (d, q)) (d, q)).1
  unfold lowWheelCofactorQuotientToggleAt
  simp only [hpDvd, if_true]
  exact prime_not_dvd_div_of_squarefree hp hsq hpDvd

/-- The mate tag also loses no multiplicity.  Equality of mate states can be
pushed through the canonical involution to recover the unique source state;
the face tag then recovers `r`. -/
theorem squareRootLowPrimeGoStrictCrossingMateTag_injOn
    (R : ℕ) :
    Set.InjOn squareRootLowPrimeGoStrictCrossingMateTag
      (squareRootLowPrimeGoStrictCrossingCarrier R) := by
  intro a ha b hb hab
  rcases a with ⟨⟨r, q⟩, d⟩
  rcases b with ⟨⟨s, t⟩, e⟩
  have hface : ({r} : Finset ℕ) = {s} := congrArg Prod.fst hab
  have hrs : r = s := by simpa using hface
  subst s
  have hmate :
      lowWheelCanonicalCofactorQuotientToggle (d, q) =
        lowWheelCanonicalCofactorQuotientToggle (e, t) :=
    congrArg Prod.snd hab
  rcases mem_squareRootLowPrimeGoStrictCrossingCarrier.mp ha with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, _hcross, _hroot, hd⟩
  rcases mem_squareRootLowPrimeGoStrictCrossingCarrier.mp hb with
    ⟨_hrR', _htR, _heR, _hr', ht, hrt, _hcube', _hcross', _hroot', he⟩
  have hfullD :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hfullE :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp he).1
  have hsqD := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfullD).2.2.1
  have hsqE := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfullE).2.2.1
  have hdgt := squareRootLowPrimeGoFullBirthBoundary_parent_one_lt hr hrq hfullD
  have hegt := squareRootLowPrimeGoFullBirthBoundary_parent_one_lt hr hrt hfullE
  have hneD : d * q ≠ 1 := by nlinarith [hdgt, hq.two_le]
  have hneE : e * t ≠ 1 := by nlinarith [hegt, ht.two_le]
  have hinvD := lowWheelCanonicalCofactorQuotientToggle_involutive hsqD hneD
  have hinvE := lowWheelCanonicalCofactorQuotientToggle_involutive hsqE hneE
  have hsource : (d, q) = (e, t) := by
    calc
      (d, q) = lowWheelCanonicalCofactorQuotientToggle
          (lowWheelCanonicalCofactorQuotientToggle (d, q)) := hinvD.symm
      _ = lowWheelCanonicalCofactorQuotientToggle
          (lowWheelCanonicalCofactorQuotientToggle (e, t)) := by rw [hmate]
      _ = (e, t) := hinvE
  have hde : d = e := congrArg Prod.fst hsource
  have hqt : q = t := congrArg Prod.snd hsource
  subst e
  subst t
  rfl

/-- Source and mate occurrences cannot overlap.  A source has the canonical
pivot in its cofactor; the corresponding removal mate has that invariant pivot
absent. -/
theorem squareRootLowPrimeGoStrictCrossingSourceMate_disjoint
    (R : ℕ) :
    Disjoint
      ((squareRootLowPrimeGoStrictCrossingCarrier R).image
        squareRootLowPrimeGoStrictCrossingSourceTag)
      ((squareRootLowPrimeGoStrictCrossingCarrier R).image
        squareRootLowPrimeGoStrictCrossingMateTag) := by
  classical
  apply Finset.disjoint_left.mpr
  intro y hySource hyMate
  rcases Finset.mem_image.mp hySource with ⟨a, ha, hay⟩
  rcases Finset.mem_image.mp hyMate with ⟨b, hb, hby⟩
  rcases a with ⟨⟨r, q⟩, d⟩
  rcases b with ⟨⟨s, t⟩, e⟩
  have htag :
      squareRootLowPrimeGoStrictCrossingSourceTag ((r, q), d) =
        squareRootLowPrimeGoStrictCrossingMateTag ((s, t), e) :=
    hay.trans hby.symm
  have hstate :
      (d, q) = lowWheelCanonicalCofactorQuotientToggle (e, t) :=
    congrArg Prod.snd htag
  rcases mem_squareRootLowPrimeGoStrictCrossingCarrier.mp ha with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, _hcross, _hroot, hd⟩
  rcases mem_squareRootLowPrimeGoStrictCrossingCarrier.mp hb with
    ⟨_hsR, _htR, _heR, hs, ht, hst, _hcube', _hcross', _hroot', he⟩
  have hfullD :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hfullE :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp he).1
  have hdiv : lowWheelCanonicalCofactorQuotientPivot (d, q) ∣ d :=
    squareRootLowPrimeGoFullBirthBoundary_canonicalPivot_dvd_parent
      hq hr hrq hfullD
  have hnot :
      ¬ lowWheelCanonicalCofactorQuotientPivot
          (lowWheelCanonicalCofactorQuotientToggle (e, t)) ∣
        (lowWheelCanonicalCofactorQuotientToggle (e, t)).1 :=
    squareRootLowPrimeGoFullBirthBoundary_matePivot_not_dvd_cofactor
      ht hs hst hfullE
  have hdiv' :
      lowWheelCanonicalCofactorQuotientPivot (d, q) ∣ (d, q).1 := by
    simpa using hdiv
  rw [hstate] at hdiv'
  exact hnot hdiv'

/-- Source and mate image carriers. -/
def squareRootLowPrimeGoStrictCrossingSourceImage
    (R : ℕ) : Finset LowWheelTaggedCofactorQuotientState :=
  (squareRootLowPrimeGoStrictCrossingCarrier R).image
    squareRootLowPrimeGoStrictCrossingSourceTag

def squareRootLowPrimeGoStrictCrossingMateImage
    (R : ℕ) : Finset LowWheelTaggedCofactorQuotientState :=
  (squareRootLowPrimeGoStrictCrossingCarrier R).image
    squareRootLowPrimeGoStrictCrossingMateTag

/-- Both populations are already occurrences of the existing transport
summand. -/
theorem squareRootLowPrimeGoStrictCrossingSourceImage_subset_transport
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeGoStrictCrossingSourceImage R ⊆
      lowWheelCanonicalTaggedPhysicalCarrier R := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
  exact squareRootLowPrimeGoStrictCrossingSourceTag_mem_transport hR hz

theorem squareRootLowPrimeGoStrictCrossingMateImage_subset_transport
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeGoStrictCrossingMateImage R ⊆
      lowWheelCanonicalTaggedPhysicalCarrier R := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
  exact squareRootLowPrimeGoStrictCrossingMateTag_mem_transport hR hz

/-- Integer source mass of the strict crossing carrier. -/
def squareRootLowPrimeGoStrictCrossingSourceMass (R : ℕ) : ℤ :=
  ∑ z ∈ squareRootLowPrimeGoStrictCrossingCarrier R,
    μ (z.1.2 * z.2)

/-- The same source population written in the exact transport coordinates in
which it occurs in the global physical ledger. -/
def squareRootLowPrimeGoStrictCrossingSourceLedger (R : ℕ) : ℂ :=
  ∑ z ∈ squareRootLowPrimeGoStrictCrossingCarrier R,
    lowWheelTaggedCanonicalWeight
      (squareRootLowPrimeGoStrictCrossingSourceTag z)

/-- The concrete opposite-sign mate population, still indexed by the original
crossing incidences so multiplicity is explicit. -/
def squareRootLowPrimeGoStrictCrossingMateLedger (R : ℕ) : ℂ :=
  ∑ z ∈ squareRootLowPrimeGoStrictCrossingCarrier R,
    lowWheelTaggedCanonicalWeight
      (squareRootLowPrimeGoStrictCrossingMateTag z)

/-- The source transport ledger is exactly the cast of the one-sided Go
crossing census; no sign convention changes in the embedding. -/
theorem squareRootLowPrimeGoStrictCrossingSourceLedger_eq_mass
    (R : ℕ) :
    squareRootLowPrimeGoStrictCrossingSourceLedger R =
      ((squareRootLowPrimeGoStrictCrossingSourceMass R : ℤ) : ℂ) := by
  unfold squareRootLowPrimeGoStrictCrossingSourceLedger
    squareRootLowPrimeGoStrictCrossingSourceMass
  push_cast
  apply Finset.sum_congr rfl
  intro z hz
  rcases z with ⟨⟨r, q⟩, d⟩
  rcases mem_squareRootLowPrimeGoStrictCrossingCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, _hcross, _hroot, hd⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  simpa [lowWheelTaggedCanonicalWeight,
      squareRootLowPrimeGoStrictCrossingSourceTag, canonicalMoebiusWeight] using
    squareRootLowPrimeGoFullBirthBoundary_transportWeight_eq_sourceWeight
      hq hfull

/-- Pointwise source/mate cancellation now sums over the *same* strict crossing
incidences, so no multiplicity has been forgotten. -/
theorem squareRootLowPrimeGoStrictCrossingSource_add_mate_eq_zero
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeGoStrictCrossingSourceLedger R +
      squareRootLowPrimeGoStrictCrossingMateLedger R = 0 := by
  unfold squareRootLowPrimeGoStrictCrossingSourceLedger
    squareRootLowPrimeGoStrictCrossingMateLedger
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro z hz
  rcases z with ⟨⟨r, q⟩, d⟩
  rcases mem_squareRootLowPrimeGoStrictCrossingCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, hcube, _hcross, hroot, hd⟩
  simpa [lowWheelTaggedCanonicalWeight,
      squareRootLowPrimeGoStrictCrossingSourceTag,
      squareRootLowPrimeGoStrictCrossingMateTag] using
    squareRootLowPrimeGoStrictCrossing_globalPartner_cancel
      hR hq hr hrq hcube hroot hd

/-- Because the source tag is injective, the indexed source ledger is literally
the signed sum over its image subcarrier. -/
theorem squareRootLowPrimeGoStrictCrossingSourceLedger_eq_imageSum
    (R : ℕ) :
    squareRootLowPrimeGoStrictCrossingSourceLedger R =
      ∑ y ∈ squareRootLowPrimeGoStrictCrossingSourceImage R,
        lowWheelTaggedCanonicalWeight y := by
  unfold squareRootLowPrimeGoStrictCrossingSourceLedger
    squareRootLowPrimeGoStrictCrossingSourceImage
  rw [Finset.sum_image]
  intro a _ha b _hb hab
  exact squareRootLowPrimeGoStrictCrossingSourceTag_injective hab

/-- Likewise the mate ledger is literally the sum over its image.  This is the
same-multiplicity theorem: no two strict crossing incidences collapse onto one
pre-existing transport occurrence. -/
theorem squareRootLowPrimeGoStrictCrossingMateLedger_eq_imageSum
    (R : ℕ) :
    squareRootLowPrimeGoStrictCrossingMateLedger R =
      ∑ y ∈ squareRootLowPrimeGoStrictCrossingMateImage R,
        lowWheelTaggedCanonicalWeight y := by
  unfold squareRootLowPrimeGoStrictCrossingMateLedger
    squareRootLowPrimeGoStrictCrossingMateImage
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact squareRootLowPrimeGoStrictCrossingMateTag_injOn R ha hb hab

/-- **Mate(C) is an existing summand.**  The witness subcarrier is the concrete
mate image.  It is contained in the tagged support of the global physical
ledger, its image sum is exactly the indexed mate ledger, and the global
physical ledger is already the repository's `squareRootTransportCofactorFirst`
term. -/
theorem squareRootLowPrimeGoStrictCrossingMate_existingTransportSubledger
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeGoStrictCrossingMateImage R ⊆
        lowWheelCanonicalTaggedPhysicalCarrier R ∧
      squareRootLowPrimeGoStrictCrossingMateLedger R =
        ∑ y ∈ squareRootLowPrimeGoStrictCrossingMateImage R,
          lowWheelTaggedCanonicalWeight y ∧
      squareRootTransportCofactorFirst R =
        lowWheelCanonicalPhysicalLedger R := by
  exact ⟨squareRootLowPrimeGoStrictCrossingMateImage_subset_transport hR,
    squareRootLowPrimeGoStrictCrossingMateLedger_eq_imageSum R,
    squareRootTransportCofactorFirst_eq_canonicalPhysicalLedger R hR⟩

/-- **Exact strict-crossing cancellation against an already-present mate
subledger.**  This is the legitimate finite replacement for trying to bound the
one-sided census. -/
theorem squareRootLowPrimeGoStrictCrossingMass_add_existingMate_eq_zero
    {R : ℕ} (hR : 2 ≤ R) :
    ((squareRootLowPrimeGoStrictCrossingSourceMass R : ℤ) : ℂ) +
      squareRootLowPrimeGoStrictCrossingMateLedger R = 0 := by
  rw [← squareRootLowPrimeGoStrictCrossingSourceLedger_eq_mass]
  exact squareRootLowPrimeGoStrictCrossingSource_add_mate_eq_zero hR

/-- The two subcarriers used above are disjoint inside the existing transport
support, so reassembly does not count a source occurrence again as a mate. -/
theorem squareRootLowPrimeGoStrictCrossingImages_disjoint
    (R : ℕ) :
    Disjoint
      (squareRootLowPrimeGoStrictCrossingSourceImage R)
      (squareRootLowPrimeGoStrictCrossingMateImage R) := by
  exact squareRootLowPrimeGoStrictCrossingSourceMate_disjoint R

end RHLean.Proof
