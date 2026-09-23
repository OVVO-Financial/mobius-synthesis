import Mathlib
import RHLean.Proof.LowWheelFullFaceQuotientOthello
import RHLean.Proof.SquareRootLowPrimeGoAncestryClock
import RHLean.Proof.SquareRootLowPrimeGoGlobalPartner

/-!
# Full-face transport partner for every Go second-boundary defect

The singleton Go crossing map only uses the face `{r}` and therefore requires
`R < r*q`.  That is unnecessarily restrictive.  A second-boundary defect
already carries the complete squarefree child `r*d`.  Put *all* prime factors
of that child on the Boolean face, keep cofactor `1`, and retain the outer owner
`q` as the high quotient.

The physical first contact gives the top-product ceiling.  The second contact
forces the full face strictly across the root: otherwise

`q * (r*d) <= R`

would imply `q^2 * (r*d) < R^2`, contradicting
`R^2 - 1 < q^2 * (r*d)`.

Thus every two-boundary defect is a literal occurrence of the complete tagged
low-wheel transport carrier.  Its signed face weight is exactly the defect
source weight `mu(q*d)`.  The already-compiled full face/quotient Othello mate
then gives an opposite-sign physical occurrence, with no extra singleton
crossing hypothesis and no root-equality exception.

No norm, density estimate, PNT input, Mertens estimate, or asymptotic claim is
used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Full tagged transport occurrence attached to one Go defect incidence. -/
def squareRootLowPrimeGoSecondBoundaryFullFaceSource
    (r q d : ℕ) : LowWheelFullTaggedPhysicalState :=
  (squarefreePrimeFace (r * d), (1, q))

/-- A genuinely unfinished Go owner lies strictly below the physical root. -/
theorem squareRootLowPrimeGoFullFace_liveOwner_lt_root
    {R q : ℕ} (hR : 2 ≤ R) (_hq : q.Prime)
    (hcube : q ^ 3 ≤ squareRootEndpoint R) :
    q < R := by
  have hXlt : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    omega
  have hq3lt : q ^ 3 < R ^ 2 := hcube.trans_lt hXlt
  by_contra hnot
  have hRq : R ≤ q := Nat.le_of_not_gt hnot
  have hR2leR3 : R ^ 2 ≤ R ^ 3 := by
    calc
      R ^ 2 = R ^ 2 * 1 := by simp
      _ ≤ R ^ 2 * R := Nat.mul_le_mul_left (R ^ 2) (by omega)
      _ = R ^ 3 := by ring
  have hR3leQ3 : R ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hRq 3
  omega

/-- The full Boolean face recovers exactly the complete Go child product. -/
theorem squareRootLowPrimeGoSecondBoundaryFullFaceSource_faceProduct
    {q r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    primeFaceProduct
        (squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d).1 =
      r * d := by
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth hq hr hrq hd
  exact primeFaceProduct_squarefreePrimeFace hchild.1.2.2.1

/-- **Every Go second-boundary defect is a literal full-face transport state.**
The full face removes the artificial singleton condition `R < r*q`. -/
theorem squareRootLowPrimeGoSecondBoundaryFullFaceSource_mem_transport
    {R q r d : ℕ} (hR : 2 ≤ R)
    (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ squareRootEndpoint R)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q
      (squareRootEndpoint R) r) :
    squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d ∈
      lowWheelFullTaggedPhysicalCarrier R := by
  let y := squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth hq hr hrq hfull
  have hsqChild : Squarefree (r * d) := hchild.1.2.2.1
  have hdom := hchild.1.2.2.2.2
  have hqR : q < R :=
    squareRootLowPrimeGoFullFace_liveOwner_lt_root hR hq hcube
  have hfaceProd : primeFaceProduct y.1 = r * d := by
    simpa [y, squareRootLowPrimeGoSecondBoundaryFullFaceSource] using
      primeFaceProduct_squarefreePrimeFace hsqChild
  have hface : y.1 ∈ (primesUpTo R).powerset := by
    apply Finset.mem_powerset.mpr
    intro p hp
    have hpFactors : p ∈ (r * d).primeFactors := by
      simpa [y, squareRootLowPrimeGoSecondBoundaryFullFaceSource,
        squarefreePrimeFace] using hp
    have hpData := Nat.mem_primeFactors.mp hpFactors
    have hpLtQ : p < q := hdom p hpData.1 hpData.2.1
    exact mem_primesUpTo.mpr ⟨hpData.1, by omega⟩
  have hfirst :=
    squareRootLowPrimeGoFullBirthBoundary_firstContact_le
      hq hrq hcube hfull
  have hsecond :=
    squareRootLowPrimeGoSecondBoundaryDefect_secondContact_gt hq hr hd
  have hroot : R < (r * d) * q := by
    by_contra hnot
    have hle : (r * d) * q ≤ R := Nat.le_of_not_gt hnot
    have hqRmul : q * R < R * R :=
      Nat.mul_lt_mul_of_pos_right hqR (by omega)
    have hlt : q * q * (r * d) < R ^ 2 := by
      calc
        q * q * (r * d) = q * ((r * d) * q) := by ring
        _ ≤ q * R := Nat.mul_le_mul_left q hle
        _ < R * R := hqRmul
        _ = R ^ 2 := by ring
    have hnotSecond : ¬ squareRootEndpoint R < q * q * (r * d) := by
      unfold squareRootEndpoint
      omega
    exact hnotSecond hsecond
  have hcarrier : LowWheelTransportPairCarrier R y.1 y.2 := by
    change LowWheelTransportPairCarrier R y.1 (1, q)
    refine ⟨by simp, by omega, ?_, ?_⟩
    · rw [hfaceProd]
      exact hroot
    · rw [hfaceProd]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hfirst
  have hranges := lowWheelTransportPairCarrier_mem_ranges hcarrier
  apply mem_lowWheelFullTaggedPhysicalCarrier.mpr
  refine ⟨hface, mem_lowWheelCanonicalPhysicalStateSet.mpr ?_⟩
  exact ⟨hranges.1, hranges.2, squarefree_one, hcarrier⟩

/-- The full-face occurrence has exactly the raw Go defect source sign. -/
theorem squareRootLowPrimeGoSecondBoundaryFullFaceSource_weight_eq
    {q r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hd : d ∈ squareRootLowPrimeGoFullBirthBoundaryParents q r) :
    lowWheelFullTaggedPhysicalWeight
        (squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d) =
      canonicalMoebiusWeight (q * d) := by
  have hchild :=
    squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth hq hr hrq hd
  have hsqChild : Squarefree (r * d) := hchild.1.2.2.1
  have hfaceProd :
      primeFaceProduct (squarefreePrimeFace (r * d)) = r * d :=
    primeFaceProduct_squarefreePrimeFace hsqChild
  have hfacePrime : ∀ p ∈ squarefreePrimeFace (r * d), p.Prime := by
    intro p hp
    have hpFactors : p ∈ (r * d).primeFactors := by
      simpa only [squarefreePrimeFace] using hp
    exact (Nat.mem_primeFactors.mp hpFactors).1
  have hfaceMu :=
    moebius_primeFaceProduct_eq_booleanCubeSign
      (squarefreePrimeFace (r * d)) hfacePrime
  have hdgt := squareRootLowPrimeGoFullBirthBoundary_parent_one_lt hr hrq hd
  have hrough :=
    (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hd).2.2.2.1
  have hrNotDvd : ¬ r ∣ d := by
    intro hrd
    have hle :=
      CanonicalGapAncestryBridge.prime_dvd_le_canonicalLargestPrimeFactor
        hdgt hr hrd
    omega
  have hmuR : μ (r * d) = -μ d := by
    exact moebius_prime_mul hr hrNotDvd
  have hmuQ : (μ (q * d) : ℤ) = -(μ d : ℤ) :=
    squareRootLowPrimeGoFullBirthBoundary_parentSourceWeight_eq_neg
      hq hr hrq hd
  have hsign : booleanCubeSign (squarefreePrimeFace (r * d)) = μ (q * d) := by
    calc
      booleanCubeSign (squarefreePrimeFace (r * d)) =
          μ (primeFaceProduct (squarefreePrimeFace (r * d))) := hfaceMu.symm
      _ = μ (r * d) := by rw [hfaceProd]
      _ = -μ d := hmuR
      _ = μ (q * d) := hmuQ.symm
  unfold squareRootLowPrimeGoSecondBoundaryFullFaceSource
    lowWheelFullTaggedPhysicalWeight canonicalMoebiusWeight
  norm_num
  exact_mod_cast hsign

/-- The complete full-face Othello mate moves every defect source and reverses
its sign.  Hence the source and its already-physical transport mate cancel
pointwise, with no `r*q = R` exceptional case. -/
theorem squareRootLowPrimeGoSecondBoundaryFullFaceSource_mate_cancel
    {R q r d : ℕ} (hR : 2 ≤ R)
    (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ squareRootEndpoint R)
    (hd : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q
      (squareRootEndpoint R) r) :
    lowWheelFullTaggedPhysicalWeight
        (squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d) +
      lowWheelFullTaggedPhysicalWeight
        (lowWheelFullFaceQuotientMate R
          (squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d)) = 0 := by
  let y := squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d
  have hy : y ∈ lowWheelFullTaggedPhysicalCarrier R := by
    simpa [y] using
      squareRootLowPrimeGoSecondBoundaryFullFaceSource_mem_transport
        hR hq hr hrq hcube hd
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hdPos : 0 < d := by
    have hd1 := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull).1
    omega
  have hrFace : r ∈ y.1 := by
    have hrDvd : r ∣ r * d := dvd_mul_right r d
    have hrdNe : r * d ≠ 0 := Nat.mul_ne_zero hr.ne_zero (Nat.ne_of_gt hdPos)
    have hrFactors : r ∈ (r * d).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hr, hrDvd, hrdNe⟩
    simpa [y, squareRootLowPrimeGoSecondBoundaryFullFaceSource,
      squarefreePrimeFace] using hrFactors
  have hne : lowWheelFullFaceQuotientMate R y ≠ y := by
    intro hfix
    have hempty := lowWheelFullStable_face_eq_empty hy hfix
    rw [hempty] at hrFace
    simp at hrFace
  have hneg := lowWheelFullFaceQuotientMate_weight_neg hne
  change lowWheelFullTaggedPhysicalWeight y +
      lowWheelFullTaggedPhysicalWeight (lowWheelFullFaceQuotientMate R y) = 0
  rw [hneg]
  ring

/-! ## Global all-defect transport subledger

The pointwise full-face construction loses no incidence multiplicity.  The
source occurrence recovers `q` from its retained quotient and recovers `r` as
the canonical largest prime of the squarefree face product `r*d`; `d` then
follows by cancellation.  Since the full-face mate is involutive on the
physical carrier, the mate map is injective on the same incidence set.

Thus the complete unfinished second-boundary defect census cancels against one
literal subledger of the already-existing full physical transport carrier.
-/

abbrev SquareRootLowPrimeGoFullFaceDefectIncidence := (ℕ × ℕ) × ℕ

/-- Every live second-boundary incidence at the physical square endpoint. -/
def squareRootLowPrimeGoFullFaceDefectCarrier
    (R : ℕ) : Finset SquareRootLowPrimeGoFullFaceDefectIncidence :=
  (((Finset.range R).product (Finset.range R)).product (Finset.range R)).filter
    fun z =>
      z.1.1.Prime ∧ z.1.2.Prime ∧ z.1.1 < z.1.2 ∧
        z.1.2 ^ 3 ≤ squareRootEndpoint R ∧
        z.2 ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
          z.1.2 (squareRootEndpoint R) z.1.1

@[simp] theorem mem_squareRootLowPrimeGoFullFaceDefectCarrier
    {R r q d : ℕ} :
    ((r, q), d) ∈ squareRootLowPrimeGoFullFaceDefectCarrier R ↔
      r < R ∧ q < R ∧ d < R ∧
        r.Prime ∧ q.Prime ∧ r < q ∧
        q ^ 3 ≤ squareRootEndpoint R ∧
        d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
          q (squareRootEndpoint R) r := by
  simp [squareRootLowPrimeGoFullFaceDefectCarrier, and_assoc]

/-- Source occurrence of a global defect incidence. -/
def squareRootLowPrimeGoFullFaceDefectSourceTag
    (z : SquareRootLowPrimeGoFullFaceDefectIncidence) :
    LowWheelFullTaggedPhysicalState :=
  squareRootLowPrimeGoSecondBoundaryFullFaceSource z.1.1 z.1.2 z.2

/-- Existing transport mate occurrence of the same defect incidence. -/
def squareRootLowPrimeGoFullFaceDefectMateTag
    (R : ℕ) (z : SquareRootLowPrimeGoFullFaceDefectIncidence) :
    LowWheelFullTaggedPhysicalState :=
  lowWheelFullFaceQuotientMate R
    (squareRootLowPrimeGoFullFaceDefectSourceTag z)

/-- Every source tag is a literal physical transport occurrence. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceTag_mem_transport
    {R : ℕ} (hR : 2 ≤ R)
    {z : SquareRootLowPrimeGoFullFaceDefectIncidence}
    (hz : z ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    squareRootLowPrimeGoFullFaceDefectSourceTag z ∈
      lowWheelFullTaggedPhysicalCarrier R := by
  rcases z with ⟨⟨r, q⟩, d⟩
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, hcube, hd⟩
  exact squareRootLowPrimeGoSecondBoundaryFullFaceSource_mem_transport
    hR hq hr hrq hcube hd

/-- The full-face source encoding is injective on the defect carrier. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceTag_injOn
    (R : ℕ) :
    Set.InjOn squareRootLowPrimeGoFullFaceDefectSourceTag
      (squareRootLowPrimeGoFullFaceDefectCarrier R) := by
  intro a ha b hb hab
  rcases a with ⟨⟨r, q⟩, d⟩
  rcases b with ⟨⟨s, t⟩, e⟩
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp ha with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, hd⟩
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hb with
    ⟨_hsR, _htR, _heR, hs, ht, hst, _hcube', he⟩
  have hfullD :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  have hfullE :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp he).1
  have hqEq : q = t := by
    have h := congrArg
      (fun y : LowWheelFullTaggedPhysicalState => y.2.2) hab
    simpa [squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoSecondBoundaryFullFaceSource] using h
  have hface :
      squarefreePrimeFace (r * d) = squarefreePrimeFace (s * e) := by
    have h := congrArg
      (fun y : LowWheelFullTaggedPhysicalState => y.1) hab
    simpa [squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoSecondBoundaryFullFaceSource] using h
  have hsqD : Squarefree (r * d) :=
    (squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth
      hq hr hrq hfullD).1.2.2.1
  have hsqE : Squarefree (s * e) :=
    (squareRootLowPrimeGoFullBirthBoundary_child_canonicalSmooth
      ht hs hst hfullE).1.2.2.1
  have hprod : r * d = s * e := by
    have hp := congrArg primeFaceProduct hface
    simpa [primeFaceProduct_squarefreePrimeFace hsqD,
      primeFaceProduct_squarefreePrimeFace hsqE] using hp
  have hdPos : 0 < d := by
    have hd1 := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfullD).1
    omega
  have hePos : 0 < e := by
    have he1 := (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfullE).1
    omega
  have hroughD :=
    (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfullD).2.2.2.1
  have hroughE :=
    (mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfullE).2.2.2.1
  have htopD : canonicalLargestPrimeFactor (r * d) = r := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hdPos hr hroughD
    simpa [Nat.mul_comm] using h
  have htopE : canonicalLargestPrimeFactor (s * e) = s := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hePos hs hroughE
    simpa [Nat.mul_comm] using h
  have hrs : r = s := by
    calc
      r = canonicalLargestPrimeFactor (r * d) := htopD.symm
      _ = canonicalLargestPrimeFactor (s * e) := congrArg _ hprod
      _ = s := htopE
  subst s
  have hde : d = e := Nat.eq_of_mul_eq_mul_left hr.pos hprod
  subst e
  subst t
  rfl

/-- The mate encoding is also injective: apply the same global involution once
more to recover the unique source occurrence. -/
theorem squareRootLowPrimeGoFullFaceDefectMateTag_injOn
    {R : ℕ} (hR : 2 ≤ R) :
    Set.InjOn (squareRootLowPrimeGoFullFaceDefectMateTag R)
      (squareRootLowPrimeGoFullFaceDefectCarrier R) := by
  intro a ha b hb hab
  have hsa := squareRootLowPrimeGoFullFaceDefectSourceTag_mem_transport hR ha
  have hsb := squareRootLowPrimeGoFullFaceDefectSourceTag_mem_transport hR hb
  have hinvA := lowWheelFullFaceQuotientMate_involutive hsa
  have hinvB := lowWheelFullFaceQuotientMate_involutive hsb
  have hmate :
      lowWheelFullFaceQuotientMate R
          (squareRootLowPrimeGoFullFaceDefectSourceTag a) =
        lowWheelFullFaceQuotientMate R
          (squareRootLowPrimeGoFullFaceDefectSourceTag b) := by
    simpa [squareRootLowPrimeGoFullFaceDefectMateTag] using hab
  have hsource :
      squareRootLowPrimeGoFullFaceDefectSourceTag a =
        squareRootLowPrimeGoFullFaceDefectSourceTag b := by
    calc
      squareRootLowPrimeGoFullFaceDefectSourceTag a =
          lowWheelFullFaceQuotientMate R
            (lowWheelFullFaceQuotientMate R
              (squareRootLowPrimeGoFullFaceDefectSourceTag a)) := hinvA.symm
      _ = lowWheelFullFaceQuotientMate R
            (lowWheelFullFaceQuotientMate R
              (squareRootLowPrimeGoFullFaceDefectSourceTag b)) := by
          rw [hmate]
      _ = squareRootLowPrimeGoFullFaceDefectSourceTag b := hinvB
  exact squareRootLowPrimeGoFullFaceDefectSourceTag_injOn R ha hb hsource

/-- Mate occurrences remain inside the pre-existing full physical transport
carrier. -/
theorem squareRootLowPrimeGoFullFaceDefectMateTag_mem_transport
    {R : ℕ} (hR : 2 ≤ R)
    {z : SquareRootLowPrimeGoFullFaceDefectIncidence}
    (hz : z ∈ squareRootLowPrimeGoFullFaceDefectCarrier R) :
    squareRootLowPrimeGoFullFaceDefectMateTag R z ∈
      lowWheelFullTaggedPhysicalCarrier R := by
  unfold squareRootLowPrimeGoFullFaceDefectMateTag
  exact lowWheelFullFaceQuotientMate_mem
    (squareRootLowPrimeGoFullFaceDefectSourceTag_mem_transport hR hz)

/-- Integer mass of the complete live second-boundary defect census. -/
def squareRootLowPrimeGoFullFaceDefectSourceMass (R : ℕ) : ℤ :=
  ∑ z ∈ squareRootLowPrimeGoFullFaceDefectCarrier R,
    μ (z.1.2 * z.2)

/-- The same source census in its literal full-face transport coordinates. -/
def squareRootLowPrimeGoFullFaceDefectSourceLedger (R : ℕ) : ℂ :=
  ∑ z ∈ squareRootLowPrimeGoFullFaceDefectCarrier R,
    lowWheelFullTaggedPhysicalWeight
      (squareRootLowPrimeGoFullFaceDefectSourceTag z)

/-- The corresponding existing physical mate ledger. -/
def squareRootLowPrimeGoFullFaceDefectMateLedger (R : ℕ) : ℂ :=
  ∑ z ∈ squareRootLowPrimeGoFullFaceDefectCarrier R,
    lowWheelFullTaggedPhysicalWeight
      (squareRootLowPrimeGoFullFaceDefectMateTag R z)

/-- The source ledger is exactly the cast of the external raw defect mass. -/
theorem squareRootLowPrimeGoFullFaceDefectSourceLedger_eq_mass
    (R : ℕ) :
    squareRootLowPrimeGoFullFaceDefectSourceLedger R =
      ((squareRootLowPrimeGoFullFaceDefectSourceMass R : ℤ) : ℂ) := by
  unfold squareRootLowPrimeGoFullFaceDefectSourceLedger
    squareRootLowPrimeGoFullFaceDefectSourceMass
  push_cast
  apply Finset.sum_congr rfl
  intro z hz
  rcases z with ⟨⟨r, q⟩, d⟩
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _hcube, hd⟩
  have hfull :=
    (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
  simpa [squareRootLowPrimeGoFullFaceDefectSourceTag,
      canonicalMoebiusWeight] using
    squareRootLowPrimeGoSecondBoundaryFullFaceSource_weight_eq
      hq hr hrq hfull

/-- Pointwise full-face Othello cancellation sums over the exact same defect
incidences. -/
theorem squareRootLowPrimeGoFullFaceDefectSource_add_mate_eq_zero
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeGoFullFaceDefectSourceLedger R +
      squareRootLowPrimeGoFullFaceDefectMateLedger R = 0 := by
  unfold squareRootLowPrimeGoFullFaceDefectSourceLedger
    squareRootLowPrimeGoFullFaceDefectMateLedger
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro z hz
  rcases z with ⟨⟨r, q⟩, d⟩
  rcases mem_squareRootLowPrimeGoFullFaceDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, hcube, hd⟩
  simpa [squareRootLowPrimeGoFullFaceDefectSourceTag,
      squareRootLowPrimeGoFullFaceDefectMateTag] using
    squareRootLowPrimeGoSecondBoundaryFullFaceSource_mate_cancel
      hR hq hr hrq hcube hd

/-- The mate image is a genuine finite subcarrier of the existing transport
support. -/
def squareRootLowPrimeGoFullFaceDefectMateImage
    (R : ℕ) : Finset LowWheelFullTaggedPhysicalState :=
  (squareRootLowPrimeGoFullFaceDefectCarrier R).image
    (squareRootLowPrimeGoFullFaceDefectMateTag R)

theorem squareRootLowPrimeGoFullFaceDefectMateImage_subset_transport
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeGoFullFaceDefectMateImage R ⊆
      lowWheelFullTaggedPhysicalCarrier R := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
  exact squareRootLowPrimeGoFullFaceDefectMateTag_mem_transport hR hz

/-- Injectivity proves that the indexed mate ledger is literally the signed sum
over its image subcarrier; no transport occurrence is charged twice. -/
theorem squareRootLowPrimeGoFullFaceDefectMateLedger_eq_imageSum
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeGoFullFaceDefectMateLedger R =
      ∑ y ∈ squareRootLowPrimeGoFullFaceDefectMateImage R,
        lowWheelFullTaggedPhysicalWeight y := by
  unfold squareRootLowPrimeGoFullFaceDefectMateLedger
    squareRootLowPrimeGoFullFaceDefectMateImage
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact squareRootLowPrimeGoFullFaceDefectMateTag_injOn hR ha hb hab

/-- **Global full-face defect cancellation.**  The complete unfinished Go
second-boundary defect mass cancels exactly against one injectively embedded
subledger of the existing physical transport carrier.  There is no singleton
crossing restriction and no root-equality remainder in this formulation. -/
theorem squareRootLowPrimeGoFullFaceDefectMass_add_existingMate_eq_zero
    {R : ℕ} (hR : 2 ≤ R) :
    ((squareRootLowPrimeGoFullFaceDefectSourceMass R : ℤ) : ℂ) +
      squareRootLowPrimeGoFullFaceDefectMateLedger R = 0 := by
  rw [← squareRootLowPrimeGoFullFaceDefectSourceLedger_eq_mass]
  exact squareRootLowPrimeGoFullFaceDefectSource_add_mate_eq_zero hR

end RHLean.Proof