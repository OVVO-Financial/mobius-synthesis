import Mathlib
import RHLean.Analysis.PartialMomentSchurTarget
import RHLean.Analysis.PhysicalDegreeOneTransitionEstimate
import RHLean.Analysis.PhysicalSquareCRTPeriodNoGo
import RHLean.Analysis.ThreeSlotMertensDegreeOneProjection

/-!
# Physical T-row partial moments and Schur target invariance

This module instantiates the arbitrary-target partial-moment identity on the
actual eight-state zero-free physical transition rows.  The observations are
the three Mobius sign coordinates of the destination state and the weights are
the exact transition counts `N_{u,v}(K)`.

The resulting target second moment therefore admits the exact four-block
reassembly for every target, while its scaled Schur covariance is independent
of target.  The final statements identify the Mertens-visible degree-one row
mass with the corresponding first-moment projection and show exactly where a
target shift goes: into the rank-one first-moment term, not into the Schur
covariance.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Three physical Mobius coordinates of a ternary state, cast to `ℝ`. -/
def physicalThreeCoordinateVector (v : Fin 27) : Fin 3 → ℝ :=
  fun i =>
    if i.1 = 0 then ((chiA v : ℤ) : ℝ)
    else if i.1 = 1 then ((chiB v : ℤ) : ℝ)
    else ((chiC v : ℤ) : ℝ)

@[simp] theorem physicalThreeCoordinateVector_zero (v : Fin 27) :
    physicalThreeCoordinateVector v 0 = ((chiA v : ℤ) : ℝ) := by
  simp [physicalThreeCoordinateVector]

@[simp] theorem physicalThreeCoordinateVector_one (v : Fin 27) :
    physicalThreeCoordinateVector v 1 = ((chiB v : ℤ) : ℝ) := by
  simp [physicalThreeCoordinateVector]

@[simp] theorem physicalThreeCoordinateVector_two (v : Fin 27) :
    physicalThreeCoordinateVector v 2 = ((chiC v : ℤ) : ℝ) := by
  simp [physicalThreeCoordinateVector]

/-- Exact transition-count weight in one physical source row. -/
def physicalTRowWeight (K : ℕ) (u v : Fin 27) : ℝ :=
  (physicalTransitionN K u v : ℝ)

/-- Arbitrary-target first moment of one physical zero-free destination row. -/
def physicalTRowTargetFirstMoment
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : Fin 3 → ℝ :=
  finiteTargetFirstMoment physicalThreeSlotNonzeroStates
    (physicalTRowWeight K u) physicalThreeCoordinateVector t

/-- Arbitrary-target second-moment matrix of one physical zero-free destination row. -/
def physicalTRowTargetSecondMoment
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteTargetSecondMoment physicalThreeSlotNonzeroStates
    (physicalTRowWeight K u) physicalThreeCoordinateVector t

/-- Physical row co-lower partial moment. -/
def physicalTRowCLPM
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteCLPM physicalThreeSlotNonzeroStates
    (physicalTRowWeight K u) physicalThreeCoordinateVector t

/-- Physical row co-upper partial moment. -/
def physicalTRowCUPM
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteCUPM physicalThreeSlotNonzeroStates
    (physicalTRowWeight K u) physicalThreeCoordinateVector t

/-- Physical row divergent lower-to-upper partial moment. -/
def physicalTRowDLPM
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteDLPM physicalThreeSlotNonzeroStates
    (physicalTRowWeight K u) physicalThreeCoordinateVector t

/-- Physical row divergent upper-to-lower partial moment. -/
def physicalTRowDUPM
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteDUPM physicalThreeSlotNonzeroStates
    (physicalTRowWeight K u) physicalThreeCoordinateVector t

/-- **Physical arbitrary-target PM reassembly.** -/
theorem physicalTRowTargetSecondMoment_eq_partial_reassembly
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) :
    physicalTRowTargetSecondMoment K u t =
      physicalTRowCLPM K u t + physicalTRowCUPM K u t -
        physicalTRowDLPM K u t - physicalTRowDUPM K u t := by
  exact finiteTargetSecondMoment_eq_partial_reassembly
    physicalThreeSlotNonzeroStates (physicalTRowWeight K u)
      physicalThreeCoordinateVector t

/-- Scaled Schur covariance of one physical destination row. -/
def physicalTRowScaledSchur
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteTargetScaledSchur physicalThreeSlotNonzeroStates
    (physicalTRowWeight K u) physicalThreeCoordinateVector t

/-- **The physical row Schur covariance is exactly target invariant.** -/
theorem physicalTRowScaledSchur_target_invariant
    (K : ℕ) (u : Fin 27) (s t : Fin 3 → ℝ) :
    physicalTRowScaledSchur K u t = physicalTRowScaledSchur K u s := by
  exact finiteTargetScaledSchur_target_invariant
    physicalThreeSlotNonzeroStates (physicalTRowWeight K u)
      physicalThreeCoordinateVector s t

/-- Mertens-visible degree-one functional on the three physical coordinates. -/
def physicalDegreeOneFunctional (z : Fin 3 → ℝ) : ℝ :=
  z 0 + z 1 + z 2

/-- The physical coordinate vector recombines to the repository's degree-one
 observable. -/
theorem physicalDegreeOneFunctional_coordinateVector (v : Fin 27) :
    physicalDegreeOneFunctional (physicalThreeCoordinateVector v) =
      ((threeSlotDegreeOneValue v : ℤ) : ℝ) := by
  simp [physicalDegreeOneFunctional, physicalThreeCoordinateVector,
    threeSlotDegreeOneValue]

/-- Apply the degree-one functional to a physical row first moment. -/
def physicalTRowTargetDegreeOneFirstMoment
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : ℝ :=
  physicalDegreeOneFunctional (physicalTRowTargetFirstMoment K u t)

/-- The zero-target degree-one first moment is exactly the physical row
 transition moment against `threeSlotDegreeOneValue`. -/
theorem physicalTRowTargetDegreeOneFirstMoment_zero
    (K : ℕ) (u : Fin 27) :
    physicalTRowTargetDegreeOneFirstMoment K u (fun _ => 0) =
      ((threeSlotTransitionMomentOn
          (Finset.range K) u threeSlotDegreeOneValue : ℤ) : ℝ) := by
  unfold physicalTRowTargetDegreeOneFirstMoment physicalDegreeOneFunctional
    physicalTRowTargetFirstMoment finiteTargetFirstMoment physicalTRowWeight
  simp only [physicalThreeCoordinateVector_zero,
    physicalThreeCoordinateVector_one, physicalThreeCoordinateVector_two,
    sub_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp [physicalThreeSlotNonzeroStates, physicalTransitionN,
    threeSlotTransitionCount, threeSlotTransitionMomentOn,
    threeSlotDegreeOneValue]
  ring

/-- **Exact target-shift law for the hard degree-one row mass.**  The Schur
 covariance is target invariant, but the Mertens-visible first moment is not
 discarded: shifting target by `t` moves precisely row-mass times the degree-one
 target projection into the rank-one first-moment block. -/
theorem physicalTRowTargetDegreeOneFirstMoment_eq_zeroTarget_sub
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) :
    physicalTRowTargetDegreeOneFirstMoment K u t =
      physicalTRowTargetDegreeOneFirstMoment K u (fun _ => 0) -
        finiteTotalWeight physicalThreeSlotNonzeroStates
          (physicalTRowWeight K u) * physicalDegreeOneFunctional t := by
  have h0 := finiteTargetFirstMoment_target_shift
    physicalThreeSlotNonzeroStates (physicalTRowWeight K u)
      physicalThreeCoordinateVector (fun _ : Fin 3 => 0) t
  unfold physicalTRowTargetDegreeOneFirstMoment physicalTRowTargetFirstMoment
    physicalDegreeOneFunctional
  have hzero := h0 (0 : Fin 3)
  have hone := h0 (1 : Fin 3)
  have htwo := h0 (2 : Fin 3)
  simp at hzero hone htwo
  linarith

/-! ## Finite q^2 affine-contact incidence frame

This section deliberately proves only the finite tag geometry.  It does not
identify the tag-dependent affine pullback field with the recovered Mobius
daughter.  That reconstruction is the separate arithmetic seam exposed by the
q=3 no-go result.
-/

/-- The four residue labels seen by the six affine offsets modulo four. -/
abbrev Q2AffineResidue := Fin 4

/-- Residue label attached to one of the six physical contact offsets. -/
def q2AffineContactResidue (a : ℕ) : Q2AffineResidue :=
  ⟨a % 4, Nat.mod_lt _ (by norm_num)⟩

/-- Incidence pullback of a four-coordinate test field by one affine tag. -/
def q2AffineTagPullback (a : ℕ) (x : Q2AffineResidue → ℚ) : ℚ :=
  x (q2AffineContactResidue a)

/-- Energy after all six affine tags read the finite incidence field. -/
def q2AffineTagEnergy (x : Q2AffineResidue → ℚ) : ℚ :=
  ∑ a ∈ physicalTransitionActiveOffsets, (q2AffineTagPullback a x) ^ 2

/-- Ambient energy on the four residue labels. -/
def q2AffineResidueEnergy (x : Q2AffineResidue → ℚ) : ℚ :=
  ∑ r : Q2AffineResidue, (x r) ^ 2

/-- Finite incidence Gram of the six affine tags. -/
def q2AffineGram : Matrix Q2AffineResidue Q2AffineResidue ℚ := fun r s =>
  ∑ a ∈ physicalTransitionActiveOffsets,
    (if q2AffineContactResidue a = r then (1 : ℚ) else 0) *
      (if q2AffineContactResidue a = s then (1 : ℚ) else 0)

/-- The six offsets occupy exactly the three nonzero residue labels. -/
theorem physicalTransitionActiveOffsets_contactResidues :
    physicalTransitionActiveOffsets.image q2AffineContactResidue =
      ({(1 : Q2AffineResidue), (2 : Q2AffineResidue), (3 : Q2AffineResidue)} :
        Finset Q2AffineResidue) := by
  native_decide

/-- Every finite residue label is represented by at most two of the six tags. -/
theorem physicalTransitionActiveOffsets_residueFiber_card_le_two
    (r : Q2AffineResidue) :
    (physicalTransitionActiveOffsets.filter fun a =>
      q2AffineContactResidue a = r).card ≤ 2 := by
  fin_cases r <;> native_decide

/-- Explicit finite Gram: zero residue is absent and each nonzero residue occurs twice. -/
theorem q2AffineGram_entries (r s : Q2AffineResidue) :
    q2AffineGram r s =
      if r = s then (if r = (0 : Q2AffineResidue) then 0 else 2) else 0 := by
  fin_cases r <;> fin_cases s <;> native_decide

/-- The six-tag incidence energy is exactly twice the energy on residues 1,2,3. -/
theorem q2AffineTagEnergy_eq
    (x : Q2AffineResidue → ℚ) :
    q2AffineTagEnergy x =
      2 * ((x (1 : Q2AffineResidue)) ^ 2 +
        (x (2 : Q2AffineResidue)) ^ 2 +
        (x (3 : Q2AffineResidue)) ^ 2) := by
  simp [q2AffineTagEnergy, q2AffineTagPullback,
    q2AffineContactResidue, physicalTransitionActiveOffsets]
  ring

/-- The ambient four-residue energy is the sum of four coordinate squares. -/
theorem q2AffineResidueEnergy_eq
    (x : Q2AffineResidue → ℚ) :
    q2AffineResidueEnergy x =
      (x (0 : Q2AffineResidue)) ^ 2 +
      (x (1 : Q2AffineResidue)) ^ 2 +
      (x (2 : Q2AffineResidue)) ^ 2 +
      (x (3 : Q2AffineResidue)) ^ 2 := by
  simp [q2AffineResidueEnergy, Fin.sum_univ_succ]
  ring

/-- The pure six-tag incidence Gram has squared operator norm at most two. -/
theorem q2AffineTagEnergy_le_two_residueEnergy
    (x : Q2AffineResidue → ℚ) :
    q2AffineTagEnergy x ≤ 2 * q2AffineResidueEnergy x := by
  rw [q2AffineTagEnergy_eq, q2AffineResidueEnergy_eq]
  nlinarith [sq_nonneg (x (0 : Q2AffineResidue))]

/-- In particular the finite incidence geometry lies below the factor four
accepted by the odd-owner energy induction. -/
theorem q2AffineTagEnergy_le_four_residueEnergy
    (x : Q2AffineResidue → ℚ) :
    q2AffineTagEnergy x ≤ 4 * q2AffineResidueEnergy x := by
  have h2 := q2AffineTagEnergy_le_two_residueEnergy x
  have hE : 0 ≤ q2AffineResidueEnergy x := by
    unfold q2AffineResidueEnergy
    positivity
  nlinarith

/-! ## Explicit synthesis span of the nonzero residue sector -/

/-- Synthesis from the six physical affine tags back to the four residue
coordinates.  This is the transpose of the incidence analysis map above. -/
def q2AffineSynthesis (c : ℕ → ℚ) (r : Q2AffineResidue) : ℚ :=
  ∑ a ∈ physicalTransitionActiveOffsets,
    if q2AffineContactResidue a = r then c a else 0

/-- Squared coefficient norm on the six active tags. -/
def q2AffineCoefficientEnergy (c : ℕ → ℚ) : ℚ :=
  ∑ a ∈ physicalTransitionActiveOffsets, (c a) ^ 2

/-- The canonical coefficient vector for a residue field.  Each nonzero residue
has two physical tags, so its mass is split evenly between them. -/
def q2AffineCanonicalCoefficients
    (x : Q2AffineResidue → ℚ) (a : ℕ) : ℚ :=
  x (q2AffineContactResidue a) / 2

@[simp] theorem q2AffineSynthesis_zero (c : ℕ → ℚ) :
    q2AffineSynthesis c (0 : Q2AffineResidue) = 0 := by
  simp [q2AffineSynthesis, q2AffineContactResidue,
    physicalTransitionActiveOffsets]

@[simp] theorem q2AffineSynthesis_one (c : ℕ → ℚ) :
    q2AffineSynthesis c (1 : Q2AffineResidue) = c 1 + c 5 := by
  simp [q2AffineSynthesis, q2AffineContactResidue,
    physicalTransitionActiveOffsets]

@[simp] theorem q2AffineSynthesis_two (c : ℕ → ℚ) :
    q2AffineSynthesis c (2 : Q2AffineResidue) = c 2 + c 6 := by
  simp [q2AffineSynthesis, q2AffineContactResidue,
    physicalTransitionActiveOffsets]

@[simp] theorem q2AffineSynthesis_three (c : ℕ → ℚ) :
    q2AffineSynthesis c (3 : Q2AffineResidue) = c 3 + c 7 := by
  simp [q2AffineSynthesis, q2AffineContactResidue,
    physicalTransitionActiveOffsets]

/-- **Incidence span theorem.** Every four-residue field with zero residue-zero
component lies in the six-tag residue-incidence synthesis range.  This statement
does not yet identify the two tags in a pair with the same physical source cell. -/
theorem q2AffineSynthesis_canonicalCoefficients
    (x : Q2AffineResidue → ℚ)
    (h0 : x (0 : Q2AffineResidue) = 0) :
    q2AffineSynthesis (q2AffineCanonicalCoefficients x) = x := by
  funext r
  fin_cases r <;>
    simp [q2AffineCanonicalCoefficients, q2AffineContactResidue, h0]

/-- The canonical residue-incidence coefficient vector costs exactly half of
the residue energy on the nonzero sector. -/
theorem q2AffineCanonicalCoefficientEnergy_eq_half
    (x : Q2AffineResidue → ℚ)
    (h0 : x (0 : Q2AffineResidue) = 0) :
    q2AffineCoefficientEnergy (q2AffineCanonicalCoefficients x) =
      (1 / 2 : ℚ) * q2AffineResidueEnergy x := by
  rw [q2AffineResidueEnergy_eq]
  simp [q2AffineCoefficientEnergy, q2AffineCanonicalCoefficients,
    q2AffineContactResidue, physicalTransitionActiveOffsets, h0]
  ring

/-- The residue-incidence synthesis operator itself has squared norm at most two. -/
theorem q2AffineSynthesis_energy_le_two
    (c : ℕ → ℚ) :
    q2AffineResidueEnergy (q2AffineSynthesis c) ≤
      2 * q2AffineCoefficientEnergy c := by
  rw [q2AffineResidueEnergy_eq]
  simp [q2AffineCoefficientEnergy, physicalTransitionActiveOffsets]
  nlinarith [sq_nonneg (c 1 - c 5), sq_nonneg (c 2 - c 6),
    sq_nonneg (c 3 - c 7)]

/-- The complete four-cell recovered `raw - 2*smooth` degree-one field occupies
exactly the three nonzero residue coordinates. -/
def q2RecoveredDegreeOneBulk (K : ℕ) : Q2AffineResidue → ℚ := fun r =>
  if r = (1 : Q2AffineResidue) then
    (threeSlotSignedFieldPrefix 1 K : ℚ)
  else if r = (2 : Q2AffineResidue) then
    (threeSlotSignedFieldPrefix 2 K : ℚ)
  else if r = (3 : Q2AffineResidue) then
    (threeSlotSignedFieldPrefix 3 K : ℚ)
  else 0

@[simp] theorem q2RecoveredDegreeOneBulk_zero (K : ℕ) :
    q2RecoveredDegreeOneBulk K (0 : Q2AffineResidue) = 0 := by
  simp [q2RecoveredDegreeOneBulk]

/-- **Recovered-bulk residue span certificate.** At every complete four-cell
endpoint, the exact `raw - 2*smooth` degree-one residue vector lies in the
incidence synthesis range.  The physical source-cell translation is handled by
the separate two-tap frame below. -/
theorem q2RecoveredDegreeOneBulk_in_affineSynthesisRange (K : ℕ) :
    q2AffineSynthesis
        (q2AffineCanonicalCoefficients (q2RecoveredDegreeOneBulk K)) =
      q2RecoveredDegreeOneBulk K := by
  exact q2AffineSynthesis_canonicalCoefficients
    (q2RecoveredDegreeOneBulk K) (q2RecoveredDegreeOneBulk_zero K)

/-- The recovered bulk has the universal half-split incidence coefficients. -/
theorem q2RecoveredDegreeOneBulk_coefficientEnergy
    (K : ℕ) :
    q2AffineCoefficientEnergy
        (q2AffineCanonicalCoefficients (q2RecoveredDegreeOneBulk K)) =
      (1 / 2 : ℚ) * q2AffineResidueEnergy (q2RecoveredDegreeOneBulk K) := by
  exact q2AffineCanonicalCoefficientEnergy_eq_half
    (q2RecoveredDegreeOneBulk K) (q2RecoveredDegreeOneBulk_zero K)

/-! ## Physical affine source-cell translation and the true pair frame -/

/-- Offsets paired modulo four differ by exactly one predecessor source cell.
This is the finite-cutoff feature suppressed by the residue-only Gram. -/
theorem qSquareOffsetSourceCell_add_four
    (q a d : ℕ) (h : a + 4 ≤ q * q * d) :
    qSquareOffsetSourceCell q (a + 4) d + 1 =
      qSquareOffsetSourceCell q a d := by
  unfold qSquareOffsetSourceCell
  omega

/-- Pointwise two-tap estimate.  It is sharp at aligned inputs. -/
theorem q2AffineTwoTap_sq_le
    (x y : ℚ) :
    (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- **True affine-pair frame bound.**  If the second tag in a pair is an
energy-nonexpanding translate of the first, the `I + S` synthesis has squared
operator norm at most four.  Complete cyclic super-orbits satisfy the premise by
translation invariance; incomplete pieces are to be charged to the endpoint
boundary before applying this theorem. -/
theorem q2AffineTwoTapFrame_le_four
    {ι : Type*} [Fintype ι]
    (f g : ι → ℚ)
    (hshift : (∑ i, (g i) ^ 2) ≤ ∑ i, (f i) ^ 2) :
    (∑ i, (f i + g i) ^ 2) ≤ 4 * ∑ i, (f i) ^ 2 := by
  have hpair :
      (∑ i, (f i + g i) ^ 2) ≤
        ∑ i, (2 * (f i) ^ 2 + 2 * (g i) ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    exact q2AffineTwoTap_sq_le (f i) (g i)
  rw [Finset.sum_add_distrib] at hpair
  have hf : (∑ i, 2 * (f i) ^ 2) = 2 * ∑ i, (f i) ^ 2 := by
    rw [Finset.mul_sum]
  have hg : (∑ i, 2 * (g i) ^ 2) = 2 * ∑ i, (g i) ^ 2 := by
    rw [Finset.mul_sum]
  rw [hf, hg] at hpair
  nlinarith

/-- Cyclic predecessor translation on a complete finite residue coordinate. -/
def q2ZModPredEquiv (M : ℕ) : ZMod M ≃ ZMod M where
  toFun z := z - 1
  invFun z := z + 1
  left_inv z := by simp
  right_inv z := by simp

/-- Predecessor translation preserves square energy exactly on a complete
finite CRT coordinate. -/
theorem q2ZModPred_energy_eq
    (M : ℕ) [NeZero M] (f : ZMod M → ℚ) :
    (∑ z : ZMod M, (f (z - 1)) ^ 2) =
      ∑ z : ZMod M, (f z) ^ 2 := by
  exact Fintype.sum_equiv
    (q2ZModPredEquiv M)
    (fun z : ZMod M => (f (z - 1)) ^ 2)
    (fun z : ZMod M => (f z) ^ 2)
    (by intro z; rfl)

/-- The actual paired affine source translation has the required factor-four
frame on every complete cyclic complementary coordinate. -/
theorem q2ZModTwoTapFrame_le_four
    (M : ℕ) [NeZero M] (f : ZMod M → ℚ) :
    (∑ z : ZMod M, (f z + f (z - 1)) ^ 2) ≤
      4 * ∑ z : ZMod M, (f z) ^ 2 := by
  apply q2AffineTwoTapFrame_le_four f (fun z => f (z - 1))
  rw [q2ZModPred_energy_eq M f]

/-- The three physical offset pairs share the same factor-four constant; summing
the three channels does not enlarge it. -/
theorem q2ZModThreePairFrame_le_four
    (M : ℕ) [NeZero M] (f : Fin 3 → ZMod M → ℚ) :
    (∑ i : Fin 3, ∑ z : ZMod M,
        (f i z + f i (z - 1)) ^ 2) ≤
      4 * ∑ i : Fin 3, ∑ z : ZMod M, (f i z) ^ 2 := by
  calc
    (∑ i : Fin 3, ∑ z : ZMod M,
        (f i z + f i (z - 1)) ^ 2) ≤
      ∑ i : Fin 3, 4 * ∑ z : ZMod M, (f i z) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact q2ZModTwoTapFrame_le_four M (f i)
    _ = 4 * ∑ i : Fin 3, ∑ z : ZMod M, (f i z) ^ 2 := by
      rw [Finset.mul_sum]

/-! ## Cross-owner Gram checkpoint

The least-square owner split is disjoint on the parent carrier, but after each
owner is transported to its own daughter coordinate the scalar first moments
live in a common target space.  This section records two finite facts needed
before using CRT as a frame argument.

First, a completely unconstrained block of the three exceptional owners
`{3,5,7}` has the all-ones synthesis Gram.  Its sharp frame constant is `3`.
Any smaller constant therefore has to use arithmetic information about the
recovered daughter fields; it cannot follow merely from there being three
owners.

Second, independent CRT coordinates alone do not force transported owner
cross-terms to vanish.  If the complementary field for one owner is allowed to
depend on the other owner's coordinate, the cross term factors into two local
responses.  Even centered local kernels can then have a positive cross term.
Thus the desired generic `epsilon`-frame requires the forward recovered-packet
intertwining (or an equivalent conditional-centering statement); it is not a
formal consequence of coprime moduli alone.
-/

/-- Owner labels for the finite exceptional block. -/
def q2ExceptionalOwner (i : Fin 3) : ℕ :=
  if i = 0 then 3 else if i = 1 then 5 else 7

@[simp] theorem q2ExceptionalOwner_zero : q2ExceptionalOwner 0 = 3 := by
  simp [q2ExceptionalOwner]

@[simp] theorem q2ExceptionalOwner_one : q2ExceptionalOwner 1 = 5 := by
  simp [q2ExceptionalOwner]

@[simp] theorem q2ExceptionalOwner_two : q2ExceptionalOwner 2 = 7 := by
  simp [q2ExceptionalOwner]

/-- The synthesis Gram for three unconstrained owner amplitudes. -/
def q2ExceptionalOwnerGram : Matrix (Fin 3) (Fin 3) ℚ := fun _ _ => 1

@[simp] theorem q2ExceptionalOwnerGram_entry (i j : Fin 3) :
    q2ExceptionalOwnerGram i j = 1 := rfl

/-- The exceptional Gram quadratic form is the square of the three-owner sum. -/
theorem q2ExceptionalOwnerGram_quadratic
    (x : Fin 3 → ℚ) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      x i * q2ExceptionalOwnerGram i j * x j) =
      (x 0 + x 1 + x 2) ^ 2 := by
  simp [q2ExceptionalOwnerGram, Fin.sum_univ_succ]
  ring

/-- **Sharp universal exceptional frame.**  The largest quadratic-form
constant of the unconstrained three-owner synthesis Gram is at most `3`. -/
theorem q2ExceptionalOwnerGram_le_three
    (x : Fin 3 → ℚ) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      x i * q2ExceptionalOwnerGram i j * x j) ≤
      3 * ∑ i : Fin 3, (x i) ^ 2 := by
  rw [q2ExceptionalOwnerGram_quadratic]
  simp [Fin.sum_univ_succ]
  nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2),
    sq_nonneg (x 1 - x 2)]

/-- The constant `3` is attained by the constant owner vector, so no smaller
field-independent exceptional frame constant is possible. -/
theorem q2ExceptionalOwnerGram_three_sharp :
    (∑ i : Fin 3, ∑ j : Fin 3,
      (1 : ℚ) * q2ExceptionalOwnerGram i j * 1) =
      3 * ∑ _i : Fin 3, (1 : ℚ) ^ 2 := by
  norm_num [q2ExceptionalOwnerGram, Fin.sum_univ_succ]

/-- On a product of two finite CRT coordinates, a cross-owner term whose
complementary fields may depend on the opposite coordinate factors into the two
local responses.  Coprimeness is what realizes the arithmetic orbit as such a
product; the factorization itself is finite Fubini. -/
theorem q2TwoOwnerTensorCross_factorization
    {α β : Type*} [Fintype α] [Fintype β]
    (u h : α → ℚ) (v g : β → ℚ) :
    (∑ a : α, ∑ b : β, (u a * g b) * (v b * h a)) =
      (∑ a : α, u a * h a) * (∑ b : β, v b * g b) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- A two-point centered local kernel used to show that local zero mean is not
sufficient once the complementary fields cross-depend on the other owner. -/
def q2CenteredToy (i : Fin 2) : ℚ := if i = 0 then 1 else -1

@[simp] theorem q2CenteredToy_sum_eq_zero :
    (∑ i : Fin 2, q2CenteredToy i) = 0 := by
  norm_num [q2CenteredToy, Fin.sum_univ_succ]

/-- **CRT-centering no-go.**  Both local kernels have zero mean, but taking each
complementary field to be the other owner's centered kernel gives cross energy
`4`, not `0`.  Therefore pairwise coprime CRT coordinates plus local centering
do not imply the desired generic-owner orthogonality for arbitrary transported
fields. -/
theorem q2CenteredToy_cross_eq_four :
    (∑ a : Fin 2, ∑ b : Fin 2,
      (q2CenteredToy a * q2CenteredToy b) *
        (q2CenteredToy b * q2CenteredToy a)) = 4 := by
  norm_num [q2CenteredToy, Fin.sum_univ_succ]

/-- The exact weighted two-owner ratio for aligned generic owner fields at
`q=13` and `q'=17`.  This is a finite numerical obstruction to deriving an
arbitrarily small `epsilon` cross-frame from the reciprocal-square weights
alone: the ratio is about `0.8715`. -/
theorem q2GenericAlignedThirteenSeventeen_ratio :
    (2 * ((1 : ℚ) / 13 ^ 2) * ((1 : ℚ) / 17 ^ 2)) /
        (((1 : ℚ) / 13 ^ 4) + ((1 : ℚ) / 17 ^ 4)) =
      (48841 : ℚ) / 56041 := by
  norm_num

/-- In particular the proposed generic cross-frame with `epsilon = 1/2` is
false for arbitrary aligned daughter fields, even though both owners are in the
generic `q >= 11` range.  A proof for the physical recovered daughters must use
their additional arithmetic structure. -/
theorem q2GenericAlignedThirteenSeventeen_not_halfFrame :
    ¬ (2 * ((1 : ℚ) / 13 ^ 2) * ((1 : ℚ) / 17 ^ 2) ≤
        (1 / 2 : ℚ) *
          (((1 : ℚ) / 13 ^ 4) + ((1 : ℚ) / 17 ^ 4))) := by
  norm_num

end RHLean.Analysis
