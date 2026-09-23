import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedTerminalCutoff
import RHLean.Proof.SquareRootLowPrimeGoCrossingMateLedger
import RHLean.Proof.LowWheelCanonicalFrozenReduction
import RHLean.Proof.LowWheelFullFaceQuotientOthello
import RHLean.Proof.LowWheelHighPrimeSurvivor

/-!
# Existing physical mate for the internal repeated-parent terminal boundary

For a terminal state `y = (t,(1,p))` with `p <= R`, the prime `p` is still a
literal coordinate of the inclusive low-wheel cube.  Move that fresh prime into
the Boolean face and collapse the quotient:

`(t,(1,p)) -> (insert p t,(1,1))`.

The first-crossing inequalities are exactly what is needed for the mate to lie
in the already-existing physical transport ledger.  The cofactor remains one
and the Boolean sign flips once.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open FrozenCofactorTopBottom

attribute [local instance] Classical.propDecidable

/-- Terminal low-wheel mate obtained by moving the fresh prime into the Boolean
face. -/
def lowWheelCanonicalRepeatedTerminalInternalMate
    (y : LowWheelTaggedDowncrossState) : LowWheelTaggedCofactorQuotientState :=
  (insert (lowWheelTaggedDowncrossPivot y) y.1, (1, 1))

/-- On the internal terminal part, the fresh pivot is absent from the old face. -/
theorem lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R) :
    lowWheelTaggedDowncrossPivot y ∉ y.1 := by
  have hterminal := (Finset.mem_filter.mp hy).1
  have hgeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
  intro hpMem
  have hlt := hgeom.2.2.2.1 _ hpMem
  exact Nat.lt_irrefl _ hlt

/-- The terminal mate is a literal occurrence of the existing physical
transport ledger. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMate_mem_transport
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R) :
    lowWheelCanonicalRepeatedTerminalInternalMate y ∈
      lowWheelCanonicalTaggedPhysicalCarrier R := by
  let p := lowWheelTaggedDowncrossPivot y
  have hterminal := (Finset.mem_filter.mp hy).1
  have hgeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
  have hp : p.Prime := by simpa [p] using hgeom.2.2.1
  have hpMem : p ∈ primesUpTo R := by
    simpa [p] using lowWheelCanonicalRepeatedTerminalInternal_pivot_mem_primesUpTo hy
  have hpNotFace : p ∉ y.1 := by
    simpa [p] using lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face hy
  have hfrozen := (Finset.mem_filter.mp hterminal).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hfaceMate : insert p y.1 ∈ (primesUpTo R).powerset := by
    apply Finset.mem_powerset.mpr
    exact Finset.insert_subset hpMem (Finset.mem_powerset.mp htag.1)
  have hphysSource := (mem_lowWheelCanonicalDowncrossPart.mp htag.2).1
  have hsourceCarrier :=
    (mem_lowWheelCanonicalPhysicalStateSet.mp hphysSource).2.2.2
  have hRgt : 1 < R := by
    have hcR := hsourceCarrier.2.1
    simpa [hgeom.1] using hcR
  have hprodInsert : primeFaceProduct (insert p y.1) = p * primeFaceProduct y.1 := by
    simp [primeFaceProduct, hpNotFace]
  have hmateCarrier : LowWheelTransportPairCarrier R (insert p y.1) (1, 1) := by
    refine ⟨by simp, hRgt, ?_, ?_⟩
    · rw [hprodInsert]
      simpa [Nat.mul_comm] using hgeom.2.2.2.2.2
    · have htop := hsourceCarrier.2.2.2
      rw [hgeom.1, hgeom.2.1] at htop
      rw [hprodInsert]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using htop
  have hranges := lowWheelTransportPairCarrier_mem_ranges hmateCarrier
  have hmatePhysical : (1, 1) ∈
      lowWheelCanonicalPhysicalStateSet R (insert p y.1) := by
    exact mem_lowWheelCanonicalPhysicalStateSet.mpr
      ⟨hranges.1, hranges.2, squarefree_one, hmateCarrier⟩
  apply mem_lowWheelCanonicalTaggedPhysicalCarrier.mpr
  simpa [lowWheelCanonicalRepeatedTerminalInternalMate, p] using
    And.intro hfaceMate hmatePhysical

/-- Moving the fresh prime into the Boolean face reverses exactly one Boolean
sign, hence the terminal source and existing mate have opposite weights. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMate_weight_neg
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R) :
    lowWheelTaggedCanonicalWeight
        (lowWheelCanonicalRepeatedTerminalInternalMate y) =
      -lowWheelTaggedCanonicalWeight (y.1, y.2) := by
  let p := lowWheelTaggedDowncrossPivot y
  have hterminal := (Finset.mem_filter.mp hy).1
  have hgeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
  have hpNotFace : p ∉ y.1 := by
    simpa [p] using lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face hy
  have hc : y.2.1 = 1 := hgeom.1
  have hsign : booleanCubeSign (insert p y.1) = -booleanCubeSign y.1 := by
    simp [booleanCubeSign, hpNotFace, pow_succ]
  simp [lowWheelTaggedCanonicalWeight,
    lowWheelCanonicalRepeatedTerminalInternalMate, hc, p, hsign]

/-- The mate is pointwise distinct from the terminal source because the fresh
prime was not already in the old Boolean face. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMate_ne
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R) :
    lowWheelCanonicalRepeatedTerminalInternalMate y ≠ (y.1, y.2) := by
  let p := lowWheelTaggedDowncrossPivot y
  have hpNotFace : p ∉ y.1 := by
    simpa [p] using lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face hy
  intro heq
  have hface := congrArg Prod.fst heq
  change insert p y.1 = y.1 at hface
  have hpInsert : p ∈ insert p y.1 := Finset.mem_insert_self p y.1
  rw [hface] at hpInsert
  exact hpNotFace hpInsert

/-! ## Global reassembly of the internal terminal mates -/

/-- The pointwise internal-terminal mate loses no multiplicity.  The fresh
pivot is the unique largest prime in the inserted face, so equality of mate
faces recovers both the pivot and the old face. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMate_injOn
    (R : ℕ) :
    Set.InjOn lowWheelCanonicalRepeatedTerminalInternalMate
      (lowWheelCanonicalRepeatedTerminalInternalPart R) := by
  intro y hy z hz heq
  let p := lowWheelTaggedDowncrossPivot y
  let q := lowWheelTaggedDowncrossPivot z
  have hyTerminal := (Finset.mem_filter.mp hy).1
  have hzTerminal := (Finset.mem_filter.mp hz).1
  have hyGeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hyTerminal
  have hzGeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hzTerminal
  have hpNot : p ∉ y.1 := by
    simpa [p] using lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face hy
  have hqNot : q ∉ z.1 := by
    simpa [q] using lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face hz
  have hface : insert p y.1 = insert q z.1 := by
    simpa [lowWheelCanonicalRepeatedTerminalInternalMate, p, q] using
      congrArg Prod.fst heq
  have hpRight : p ∈ insert q z.1 := by
    rw [← hface]
    exact Finset.mem_insert_self p y.1
  have hqLeft : q ∈ insert p y.1 := by
    rw [hface]
    exact Finset.mem_insert_self q z.1
  have hpq : p = q := by
    rcases Finset.mem_insert.mp hpRight with hpq | hpz
    · exact hpq
    · rcases Finset.mem_insert.mp hqLeft with hqp | hqy
      · exact hqp.symm
      · have hpLtQ : p < q := by
          simpa [q] using hzGeom.2.2.2.1 p hpz
        have hqLtP : q < p := by
          simpa [p] using hyGeom.2.2.2.1 q hqy
        omega
  have hfaceSame : insert p y.1 = insert p z.1 := by
    simpa [hpq] using hface
  have hbase : y.1 = z.1 := by
    have herase := congrArg (fun s : Finset ℕ => s.erase p) hfaceSame
    have hpNotZ : p ∉ z.1 := by simpa [hpq] using hqNot
    simpa [hpNot, hpNotZ] using herase
  have hstate : y.2 = z.2 := by
    apply Prod.ext
    · exact hyGeom.1.trans hzGeom.1.symm
    · calc
        y.2.2 = p := by simpa [p] using hyGeom.2.1
        _ = q := hpq
        _ = z.2.2 := by simpa [q] using hzGeom.2.1.symm
  exact Prod.ext hbase hstate

/-- Image of the internal repeated terminal boundary inside the existing tagged
physical transport carrier. -/
def lowWheelCanonicalRepeatedTerminalInternalMateImage
    (R : ℕ) : Finset LowWheelTaggedCofactorQuotientState :=
  (lowWheelCanonicalRepeatedTerminalInternalPart R).image
    lowWheelCanonicalRepeatedTerminalInternalMate

/-- Every image occurrence is a literal pre-existing transport occurrence. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateImage_subset_transport
    (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalMateImage R ⊆
      lowWheelCanonicalTaggedPhysicalCarrier R := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  exact lowWheelCanonicalRepeatedTerminalInternalMate_mem_transport hy

/-- Signed mate ledger, kept on the source indexing until injectivity is used. -/
def lowWheelCanonicalRepeatedTerminalInternalMateLedger
    (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R,
    lowWheelTaggedCanonicalWeight
      (lowWheelCanonicalRepeatedTerminalInternalMate y)

/-- Injectivity turns the source-indexed mate ledger into the literal image
subledger of the global physical transport carrier. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateLedger_eq_imageSum
    (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalMateLedger R =
      ∑ z ∈ lowWheelCanonicalRepeatedTerminalInternalMateImage R,
        lowWheelTaggedCanonicalWeight z := by
  unfold lowWheelCanonicalRepeatedTerminalInternalMateLedger
    lowWheelCanonicalRepeatedTerminalInternalMateImage
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact lowWheelCanonicalRepeatedTerminalInternalMate_injOn R ha hb hab

/-- **Exact signed reassembly.**  The complete internal repeated-terminal
ledger cancels against its already-present transport mate subledger before any
norm is taken. -/
theorem sum_lowWheelCanonicalRepeatedTerminalInternal_add_mate_eq_zero
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R,
        lowWheelTaggedDowncrossWeight y) +
      lowWheelCanonicalRepeatedTerminalInternalMateLedger R = 0 := by
  unfold lowWheelCanonicalRepeatedTerminalInternalMateLedger
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro y hy
  have hneg := lowWheelCanonicalRepeatedTerminalInternalMate_weight_neg hy
  have hsame :
      lowWheelTaggedCanonicalWeight (y.1, y.2) =
        lowWheelTaggedDowncrossWeight y := by
    rfl
  rw [hneg, hsame]
  ring

/-- Existing frozen-reduction notation for the internal ledger, rewritten as
the negative of its concrete transport mate subledger. -/
theorem lowWheelCanonicalRepeatedTerminalInternalLedger_eq_neg_mateLedger
    (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalLedger R =
      -lowWheelCanonicalRepeatedTerminalInternalMateLedger R := by
  unfold lowWheelCanonicalRepeatedTerminalInternalLedger
  have h := sum_lowWheelCanonicalRepeatedTerminalInternal_add_mate_eq_zero R
  linear_combination h

/-- **Transport-only normal form of the frozen/top/far residual.**  The old
internal terminal term is absorbed by its already-present transport mates, and
the far survivor is restored to the equivalent far-prime transport coordinate.
No norm is taken:

`FrozenTopFarResidual = FarTransport - InternalMate - TopImage`. -/
theorem lowWheelFrozenTopFarResidual_eq_farTransport_sub_internalMate_sub_topImage
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      squareRootFarPrimeTransport R -
        lowWheelCanonicalRepeatedTerminalInternalMateLedger R -
        lowWheelFrozenCofactorTopImageLedger R := by
  unfold lowWheelFrozenTopFarResidual
  rw [lowWheelCanonicalRepeatedTerminalInternalLedger_eq_neg_mateLedger R,
    survivorSixteenFarUpperPrimeMass_pred_eq_neg_farTransport R hR]
  ring

/-! ## Put all three residual terms on the same physical transport carrier -/

/-- High product represented by one tagged physical occurrence. -/
def lowWheelTaggedHighProduct (z : LowWheelFullTaggedPhysicalState) : ℕ :=
  primeFaceProduct z.1 * z.2.2

/-- Literal far part of the complete tagged physical transport carrier. -/
def lowWheelFarTaggedPhysicalCarrier (R : ℕ) :
    Finset LowWheelFullTaggedPhysicalState :=
  (lowWheelFullTaggedPhysicalCarrier R).filter fun z =>
    R + 8 ≤ lowWheelTaggedHighProduct z

@[simp] theorem mem_lowWheelFarTaggedPhysicalCarrier
    {R : ℕ} {z : LowWheelFullTaggedPhysicalState} :
    z ∈ lowWheelFarTaggedPhysicalCarrier R ↔
      z ∈ lowWheelFullTaggedPhysicalCarrier R ∧
        R + 8 ≤ lowWheelTaggedHighProduct z := by
  simp [lowWheelFarTaggedPhysicalCarrier]

/-- The internal-terminal mate image lies on the complete tagged physical
carrier used by the face/quotient Othello move. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateImage_subset_fullPhysical
    (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalMateImage R ⊆
      lowWheelFullTaggedPhysicalCarrier R := by
  intro z hz
  have hz' :=
    lowWheelCanonicalRepeatedTerminalInternalMateImage_subset_transport R hz
  rcases mem_lowWheelCanonicalTaggedPhysicalCarrier.mp hz' with ⟨ht, hx⟩
  exact mem_lowWheelFullTaggedPhysicalCarrier.mpr ⟨ht, hx⟩

/-- The frozen top image also consists of literal occurrences of that carrier. -/
theorem lowWheelFrozenCofactorTopImage_subset_fullPhysical
    (R : ℕ) :
    lowWheelFrozenCofactorTopImage R ⊆ lowWheelFullTaggedPhysicalCarrier R := by
  intro z hz
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  apply mem_lowWheelFullTaggedPhysicalCarrier.mpr
  exact ⟨htag.1, lowWheelFrozenCofactorTopToggle_mem_physical hy⟩

/-- The frozen top relocation is automatically far.  Its source already has
`R < P(t)k`, and the top move multiplies that high product by a prime at least
two. -/
theorem lowWheelFrozenCofactorTopImage_highProduct_ge_far
    {R : ℕ} (hR : 6 ≤ R) {z : LowWheelTaggedDowncrossState}
    (hz : z ∈ lowWheelFrozenCofactorTopImage R) :
    R + 8 ≤ lowWheelTaggedHighProduct z := by
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  let q := lowWheelFrozenCofactorTopPrime y
  have hqPrime : q.Prime := by
    simpa [q] using (lowWheelFrozenCofactorTopPrime_data hy).1
  have hqTwo : 2 ≤ q := hqPrime.two_le
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hphys := (mem_lowWheelCanonicalDowncrossPart.mp htag.2).1
  have hcarrier := (mem_lowWheelCanonicalPhysicalStateSet.mp hphys).2.2.2
  have hhigh : R < primeFaceProduct y.1 * y.2.2 := hcarrier.2.2.1
  have hbase : R + 1 ≤ primeFaceProduct y.1 * y.2.2 := by omega
  have hdouble :
      2 * (primeFaceProduct y.1 * y.2.2) ≤
        q * (primeFaceProduct y.1 * y.2.2) := by
    exact Nat.mul_le_mul_right (primeFaceProduct y.1 * y.2.2) hqTwo
  have hfar :
      R + 8 ≤ q * (primeFaceProduct y.1 * y.2.2) := by
    have hfirst :
        R + 8 ≤ 2 * (primeFaceProduct y.1 * y.2.2) := by omega
    exact hfirst.trans hdouble
  rw [lowWheelFrozenCofactorTopToggle_eq hy]
  simpa [lowWheelTaggedHighProduct, q, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using hfar

/-- Hence the complete frozen top image is a subcarrier of the far physical
region. -/
theorem lowWheelFrozenCofactorTopImage_subset_farPhysical
    (R : ℕ) (hR : 6 ≤ R) :
    lowWheelFrozenCofactorTopImage R ⊆ lowWheelFarTaggedPhysicalCarrier R := by
  intro z hz
  exact mem_lowWheelFarTaggedPhysicalCarrier.mpr
    ⟨lowWheelFrozenCofactorTopImage_subset_fullPhysical R hz,
      lowWheelFrozenCofactorTopImage_highProduct_ge_far hR hz⟩

/-- Internal-terminal mates below the far cutoff. -/
def lowWheelCanonicalRepeatedTerminalInternalMateNearImage
    (R : ℕ) : Finset LowWheelTaggedCofactorQuotientState :=
  (lowWheelCanonicalRepeatedTerminalInternalMateImage R).filter fun z =>
    lowWheelTaggedHighProduct z < R + 8

/-- Complementary far internal-terminal mate image. -/
def lowWheelCanonicalRepeatedTerminalInternalMateFarImage
    (R : ℕ) : Finset LowWheelTaggedCofactorQuotientState :=
  (lowWheelCanonicalRepeatedTerminalInternalMateImage R).filter fun z =>
    R + 8 ≤ lowWheelTaggedHighProduct z

/-- Exact cutoff partition of the internal-terminal mate image. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateImage_eq_near_union_far
    (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalMateImage R =
      lowWheelCanonicalRepeatedTerminalInternalMateNearImage R ∪
        lowWheelCanonicalRepeatedTerminalInternalMateFarImage R := by
  ext z
  simp only [lowWheelCanonicalRepeatedTerminalInternalMateNearImage,
    lowWheelCanonicalRepeatedTerminalInternalMateFarImage,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hz
    by_cases hfar : R + 8 ≤ lowWheelTaggedHighProduct z
    · exact Or.inr ⟨hz, hfar⟩
    · exact Or.inl ⟨hz, by omega⟩
  · rintro (⟨hz, _⟩ | ⟨hz, _⟩)
    · exact hz
    · exact hz

/-- The near and far mate pieces are disjoint. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateNear_disjoint_far
    (R : ℕ) :
    Disjoint
      (lowWheelCanonicalRepeatedTerminalInternalMateNearImage R)
      (lowWheelCanonicalRepeatedTerminalInternalMateFarImage R) := by
  rw [Finset.disjoint_left]
  intro z hnear hfar
  have hlt := (Finset.mem_filter.mp hnear).2
  have hge := (Finset.mem_filter.mp hfar).2
  omega

/-- The far mate image is on the same far physical carrier as the top image. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateFarImage_subset_farPhysical
    (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalMateFarImage R ⊆
      lowWheelFarTaggedPhysicalCarrier R := by
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨himage, hfar⟩
  exact mem_lowWheelFarTaggedPhysicalCarrier.mpr
    ⟨lowWheelCanonicalRepeatedTerminalInternalMateImage_subset_fullPhysical R himage,
      hfar⟩

/-- Every internal-terminal mate has state `(1,1)`. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateImage_state_eq_one
    {R : ℕ} {z : LowWheelTaggedCofactorQuotientState}
    (hz : z ∈ lowWheelCanonicalRepeatedTerminalInternalMateImage R) :
    z.2 = (1, 1) := by
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  rfl

/-- A frozen top image has quotient at least two, so it cannot be an internal
terminal mate occurrence. -/
theorem lowWheelFrozenCofactorTopImage_quotient_two_le
    {R : ℕ} {z : LowWheelTaggedDowncrossState}
    (hz : z ∈ lowWheelFrozenCofactorTopImage R) :
    2 ≤ z.2.2 := by
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  let q := lowWheelFrozenCofactorTopPrime y
  have hqPrime : q.Prime := by
    simpa [q] using (lowWheelFrozenCofactorTopPrime_data hy).1
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hphys := (mem_lowWheelCanonicalDowncrossPart.mp htag.2).1
  have hkOne : 1 ≤ y.2.2 :=
    (Finset.mem_Icc.mp (mem_lowWheelCanonicalPhysicalStateSet.mp hphys).2.1).1
  rw [lowWheelFrozenCofactorTopToggle_eq hy]
  dsimp only
  have hqTwo : 2 ≤ q := hqPrime.two_le
  have hmul : q ≤ q * y.2.2 := by
    exact Nat.le_mul_of_pos_right q (by omega)
  exact hqTwo.trans hmul

/-- The two image populations subtracted in the residual are disjoint. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateImage_disjoint_topImage
    (R : ℕ) :
    Disjoint (lowWheelCanonicalRepeatedTerminalInternalMateImage R)
      (lowWheelFrozenCofactorTopImage R) := by
  rw [Finset.disjoint_left]
  intro z hint htop
  have hone := lowWheelCanonicalRepeatedTerminalInternalMateImage_state_eq_one hint
  have htwo := lowWheelFrozenCofactorTopImage_quotient_two_le htop
  have hquot : z.2.2 = 1 := congrArg Prod.snd hone
  omega

/-- Hence the two far image populations are disjoint subcarriers of one far
physical region. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateFarImage_disjoint_topImage
    (R : ℕ) :
    Disjoint (lowWheelCanonicalRepeatedTerminalInternalMateFarImage R)
      (lowWheelFrozenCofactorTopImage R) := by
  rw [Finset.disjoint_left]
  intro z hfar htop
  have himage : z ∈ lowWheelCanonicalRepeatedTerminalInternalMateImage R :=
    (Finset.mem_filter.mp hfar).1
  have hone := lowWheelCanonicalRepeatedTerminalInternalMateImage_state_eq_one himage
  have htwo := lowWheelFrozenCofactorTopImage_quotient_two_le htop
  have hquot : z.2.2 = 1 := congrArg Prod.snd hone
  omega

/-! ## Far physical Othello reduction -/

/-- Signed mass of the literal far physical carrier. -/
def lowWheelFarTaggedPhysicalLedger (R : ℕ) : ℂ :=
  ∑ z ∈ lowWheelFarTaggedPhysicalCarrier R,
    lowWheelFullTaggedPhysicalWeight z

/-- Stable part of the far carrier under the existing face/quotient Othello
move. -/
def lowWheelFarTaggedPhysicalStableCarrier (R : ℕ) :
    Finset LowWheelFullTaggedPhysicalState :=
  finiteOthelloStablePart (lowWheelFarTaggedPhysicalCarrier R)
    (lowWheelFullFaceQuotientMate R)

@[simp] theorem mem_lowWheelFarTaggedPhysicalStableCarrier
    {R : ℕ} {z : LowWheelFullTaggedPhysicalState} :
    z ∈ lowWheelFarTaggedPhysicalStableCarrier R ↔
      z ∈ lowWheelFarTaggedPhysicalCarrier R ∧
        lowWheelFullFaceQuotientMate R z = z := by
  simp [lowWheelFarTaggedPhysicalStableCarrier, finiteOthelloStablePart]

/-- The state-dependent face/quotient mate preserves the high product exactly. -/
theorem lowWheelFullFaceQuotientMate_highProduct
    (R : ℕ) (z : LowWheelFullTaggedPhysicalState) :
    lowWheelTaggedHighProduct (lowWheelFullFaceQuotientMate R z) =
      lowWheelTaggedHighProduct z := by
  unfold lowWheelFullFaceQuotientMate
  by_cases h : (lowWheelFullActivePrimeSet R z).Nonempty
  · rw [dif_pos h]
    simpa [lowWheelTaggedHighProduct] using
      (lowWheelFullFaceQuotientToggleAt_highProduct
        (lowWheelFullOppositePrime R z) z)
  · rw [dif_neg h]

/-- Hence the existing Othello mate preserves the far filtered physical
region, not only the complete unfiltered carrier. -/
theorem lowWheelFullFaceQuotientMate_mem_far
    {R : ℕ} {z : LowWheelFullTaggedPhysicalState}
    (hz : z ∈ lowWheelFarTaggedPhysicalCarrier R) :
    lowWheelFullFaceQuotientMate R z ∈ lowWheelFarTaggedPhysicalCarrier R := by
  rcases mem_lowWheelFarTaggedPhysicalCarrier.mp hz with ⟨hzFull, hfar⟩
  apply mem_lowWheelFarTaggedPhysicalCarrier.mpr
  refine ⟨lowWheelFullFaceQuotientMate_mem hzFull, ?_⟩
  rw [lowWheelFullFaceQuotientMate_highProduct R z]
  exact hfar

/-- **Exact far Othello cancellation.**  Every moving state of the literal far
physical carrier cancels before any norm; its total signed mass is exactly the
mass of the stable far states. -/
theorem lowWheelFarTaggedPhysicalLedger_eq_stable
    (R : ℕ) :
    lowWheelFarTaggedPhysicalLedger R =
      ∑ z ∈ lowWheelFarTaggedPhysicalStableCarrier R,
        lowWheelFullTaggedPhysicalWeight z := by
  unfold lowWheelFarTaggedPhysicalLedger
    lowWheelFarTaggedPhysicalStableCarrier
  exact sum_finiteOthelloRegion_eq_stable
    (lowWheelFarTaggedPhysicalCarrier R)
    (lowWheelFullFaceQuotientMate R)
    lowWheelFullTaggedPhysicalWeight
    (fun z hz => lowWheelFullFaceQuotientMate_mem_far hz)
    (fun z hz =>
      lowWheelFullFaceQuotientMate_involutive
        (mem_lowWheelFarTaggedPhysicalCarrier.mp hz).1)
    (fun z _hz hne => lowWheelFullFaceQuotientMate_weight_neg hne)

/-- **Stable far geometry.**  A survivor of the second Othello direction has
empty Boolean face and its high quotient is literally a prime in the far
interval.  The low cofactor remains squarefree and satisfies the original
product cutoff. -/
theorem lowWheelFarTaggedPhysicalStable_geometry
    {R : ℕ} (hR : 2 ≤ R) {z : LowWheelFullTaggedPhysicalState}
    (hz : z ∈ lowWheelFarTaggedPhysicalStableCarrier R) :
    z.1 = ∅ ∧ z.2.2.Prime ∧
      R + 8 ≤ z.2.2 ∧ z.2.2 ≤ squareRootEndpoint R ∧
      z.2.1 ∈ Finset.Ico 1 R ∧ Squarefree z.2.1 ∧
      z.2.1 * z.2.2 ≤ squareRootEndpoint R := by
  rcases mem_lowWheelFarTaggedPhysicalStableCarrier.mp hz with
    ⟨hzFar, hstable⟩
  rcases mem_lowWheelFarTaggedPhysicalCarrier.mp hzFar with
    ⟨hzFull, hfar⟩
  have hgeom := lowWheelFullStable_geometry hzFull hstable
  have hprime : z.2.2.Prime :=
    (lowWheelHighSurvivor_iff_prime hR hgeom.2.1 hgeom.2.2.1).mp
      hgeom.2.2.2
  have hfarQ : R + 8 ≤ z.2.2 := by
    simpa [lowWheelTaggedHighProduct, hgeom.1, primeFaceProduct] using hfar
  have hphys := (mem_lowWheelFullTaggedPhysicalCarrier.mp hzFull).2
  have hdata := mem_lowWheelCanonicalPhysicalStateSet.mp hphys
  have hcarrier := hdata.2.2.2
  have htop : z.2.1 * z.2.2 ≤ squareRootEndpoint R := by
    have h := hcarrier.2.2.2
    rw [hgeom.1] at h
    simpa [primeFaceProduct] using h
  exact ⟨hgeom.1, hprime, hfarQ, hgeom.2.2.1,
    hdata.1, hdata.2.2.1, htop⟩

/-- Conversely every squarefree low cofactor paired with a far prime under the
physical product cutoff is a stable state of the same far carrier. -/
theorem lowWheelFarTaggedPhysicalStable_of_prime
    {R c q : ℕ} (hR : 2 ≤ R)
    (hc : c ∈ Finset.Ico 1 R) (hsq : Squarefree c)
    (hq : q.Prime) (hqFar : R + 8 ≤ q)
    (hqX : q ≤ squareRootEndpoint R)
    (hcq : c * q ≤ squareRootEndpoint R) :
    ((∅ : Finset ℕ), (c, q)) ∈ lowWheelFarTaggedPhysicalStableCarrier R := by
  have hRq : R < q := by omega
  have hsurv : lowWheelHighSurvivor R q :=
    (lowWheelHighSurvivor_iff_prime hR hRq hqX).mpr hq
  have hface : (∅ : Finset ℕ) ∈ (primesUpTo R).powerset := by simp
  have hqI : q ∈ Finset.Icc 1 (squareRootEndpoint R) := by
    exact Finset.mem_Icc.mpr ⟨by omega, hqX⟩
  have hcData := Finset.mem_Ico.mp hc
  have hpair : LowWheelTransportPairCarrier R (∅ : Finset ℕ) (c, q) := by
    refine ⟨hcData.1, hcData.2, ?_, ?_⟩
    · simpa [primeFaceProduct] using hRq
    · simpa [primeFaceProduct] using hcq
  have hphys : (c, q) ∈ lowWheelCanonicalPhysicalStateSet R (∅ : Finset ℕ) :=
    mem_lowWheelCanonicalPhysicalStateSet.mpr ⟨hc, hqI, hsq, hpair⟩
  have hfull : ((∅ : Finset ℕ), (c, q)) ∈ lowWheelFullTaggedPhysicalCarrier R :=
    mem_lowWheelFullTaggedPhysicalCarrier.mpr ⟨hface, hphys⟩
  have hfar : ((∅ : Finset ℕ), (c, q)) ∈ lowWheelFarTaggedPhysicalCarrier R := by
    apply mem_lowWheelFarTaggedPhysicalCarrier.mpr
    refine ⟨hfull, ?_⟩
    simpa [lowWheelTaggedHighProduct, primeFaceProduct] using hqFar
  have hactiveEmpty :
      ¬ (lowWheelFullActivePrimeSet R ((∅ : Finset ℕ), (c, q))).Nonempty := by
    intro hne
    rcases hne with ⟨p, hp⟩
    rcases mem_lowWheelFullActivePrimeSet.mp hp with ⟨hpR, hpActive⟩
    rcases hpActive with hpFace | hpDvd
    · simp at hpFace
    · exact hsurv p hpR hpDvd
  have hstable :
      lowWheelFullFaceQuotientMate R ((∅ : Finset ℕ), (c, q)) =
        ((∅ : Finset ℕ), (c, q)) := by
    unfold lowWheelFullFaceQuotientMate
    rw [dif_neg hactiveEmpty]
  exact mem_lowWheelFarTaggedPhysicalStableCarrier.mpr ⟨hfar, hstable⟩

end RHLean.Proof
