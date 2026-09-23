import RHLean.Analysis.PhysicalDegreeOneHigherSquareRecurrences
import RHLean.Analysis.PhysicalSquareCRTPeriodNoGo
import RHLean.Proof.ExceptionalOwnerEnergyClosure
import RHLean.Proof.JointDaughterCrossEnergyAudit
import RHLean.Proof.SquareRootAncestryRoot

/-!
# The six-contact frame constant is counting, not Mobius cancellation

A recurring proposal is to close the exceptional owner schedule `{3,5,7}` by
computing a frame constant `alpha_q` for the six-contact `q^2` pullback on the
finite super-orbit `Z/q^2 x Z/11^2`, proving `alpha_q <= 3`, and feeding that
into `ExceptionalOwnerEnergyStep` through the budget
`3*(1/9+1/25+1/49) = 1891/3675 < 1`.

This module records why that route supplies no arithmetic content.  Three exact
finite facts are certified.

1. **The contact classes are pullbacks of the offsets, not the offsets.**
   `physicalTransitionActiveOffsets = {1,2,3,5,6,7}` are offsets `a` inside the
   physical site `4*k+a`.  The cell classes carrying a forced `q^2` hit are
   their images under `a` mapsto `-a/4 mod q^2`: `{1,...,6}` mod `9`,
   `{5,6,11,12,17,18}` mod `25`, `{11,12,23,24,35,36}` mod `49`.  Those six
   element sets are not the offset set, and the identifications below prevent a
   repeat of that conflation.

2. **The frame constant is two, for every field.**  Since `q` is odd,
   `q^2*d` and `d` agree modulo four, and the six offsets split into the three
   mod-four pairs `{1,5}`, `{2,6}`, `{3,7}`.  A daughter therefore has exactly
   two tagged contact preimages off the zero class and none on it.
   `contact_frame_two` is stated for an arbitrary field `w : ℕ → ℤ`, so the
   proposed `alpha_q <= 3` estimate is a corollary of fibre counting
   (`contact_frame_three`) with no Mobius input at all.  Two is attained on the
   all-ones field, so no field-independent constant is smaller.  A least-owner
   restriction can only delete preimages, so `<= 2` persists and the route is
   not helped there either.

3. **Assembled coefficient norm and recursive Mertens energy are different
   objects.**  `contactDaughterCoefficientNorm q Y` is the squared mass of the
   assembled `q^2` children over the daughter range, which is what a frame
   estimate bounds.  The induction instead consumes `E (X / q^2)`.  With the
   recursive Mertens energy `E Y = mertensSummatoryInt Y ^ 2` the two are
   separated by an exact finite witness: `mertensSummatoryInt 2 = 0` while the
   assembled coefficient norm is already positive at `Y = 2` for all three
   exceptional owners.  So no constant compares them, at any scale.  This is a
   type mismatch, not a bad constant.

What is *not* claimed.  The finite mask operator exists and is perfectly well
defined; its norm is just the fibre-counting constant above.  What does not
exist is a fixed finite Mobius vector on the residue torus whose spectral data
could be computed once and reused at every physical period: the masks are
periodic, the Mobius observable is not, and the repository's transported field
reconstructs its value by pulling back to the physical source cell
(`selectedDegreeOneOffsetDaughterField`) instead of assigning a value to a
residue class.  Nothing here refutes the coefficient-level compensation
identities, the `q^2` transport, or RH.  The operative consequence is narrow:
the `q^2` children must be reassembled with their signs before any norm is
taken, never squared first.
-/

open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis

/-! ## 1. The contact classes are the pullbacks of the active offsets -/

/-- The nine-channel classes are the active offsets pulled back by `4` mod `9`. -/
theorem physicalNineChannelResidues_eq_image_activeOffsets :
    physicalNineChannelResidues =
      physicalTransitionActiveOffsets.image (fun a => 2 * a % 9) := by
  decide

/-- The twenty-five hit classes are the offsets pulled back by `4` mod `25`. -/
theorem physicalTwentyFiveHitResidues_eq_image_activeOffsets :
    physicalTwentyFiveHitResidues =
      physicalTransitionActiveOffsets.image (fun a => 6 * a % 25) := by
  decide

/-- The forty-nine hit classes are the offsets pulled back by `4` mod `49`. -/
theorem physicalFortyNineHitResidues_eq_image_activeOffsets :
    physicalFortyNineHitResidues =
      physicalTransitionActiveOffsets.image (fun a => 12 * a % 49) := by
  decide

/-- The contact classes are never the offset set itself. -/
theorem physicalNineChannelResidues_ne_activeOffsets :
    physicalNineChannelResidues ≠ physicalTransitionActiveOffsets := by
  decide

theorem physicalTwentyFiveHitResidues_ne_activeOffsets :
    physicalTwentyFiveHitResidues ≠ physicalTransitionActiveOffsets := by
  decide

theorem physicalFortyNineHitResidues_ne_activeOffsets :
    physicalFortyNineHitResidues ≠ physicalTransitionActiveOffsets := by
  decide

/-! ## 2. The six-contact fibre and its field-independent frame constant -/

/-- The active offsets compatible with a physical site in the class `r` modulo
four.  Because `4*k+a` determines `a` modulo four, this is the exact fibre of
the tagged contact map over one daughter. -/
def activeOffsetsOfResidue (r : ℕ) : Finset ℕ :=
  physicalTransitionActiveOffsets.filter fun a => a % 4 = r

theorem activeOffsetsOfResidue_zero : activeOffsetsOfResidue 0 = ∅ := by decide

theorem activeOffsetsOfResidue_one :
    activeOffsetsOfResidue 1 = ({1, 5} : Finset ℕ) := by decide

theorem activeOffsetsOfResidue_two :
    activeOffsetsOfResidue 2 = ({2, 6} : Finset ℕ) := by decide

theorem activeOffsetsOfResidue_three :
    activeOffsetsOfResidue 3 = ({3, 7} : Finset ℕ) := by decide

/-- Exact fibre sizes: three mod-four pairs, nothing over the zero class. -/
theorem card_activeOffsetsOfResidue (r : ℕ) (hr : r < 4) :
    (activeOffsetsOfResidue r).card = if r = 0 then 0 else 2 := by
  interval_cases r <;> decide

private theorem sum_pair_int (a b : ℕ) (hab : a ≠ b) (f : ℕ → ℤ) :
    ∑ x ∈ ({a, b} : Finset ℕ), f x = f a + f b := by
  rw [Finset.sum_insert (by simpa using hab), Finset.sum_singleton]

/-- Two-term Cauchy-Schwarz: the entire content of the frame bound. -/
private theorem sq_add_le_two_mul_sq_add_sq (x y : ℤ) :
    (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y)]

private theorem sq_sum_activeOffsetsOfResidue_le_two_mul
    (r : ℕ) (hr : r < 4) (w : ℕ → ℤ) :
    (∑ a ∈ activeOffsetsOfResidue r, w a) ^ 2 ≤
      2 * ∑ a ∈ activeOffsetsOfResidue r, (w a) ^ 2 := by
  interval_cases r
  · rw [activeOffsetsOfResidue_zero]
    simp
  · rw [activeOffsetsOfResidue_one, sum_pair_int 1 5 (by norm_num),
      sum_pair_int 1 5 (by norm_num)]
    exact sq_add_le_two_mul_sq_add_sq _ _
  · rw [activeOffsetsOfResidue_two, sum_pair_int 2 6 (by norm_num),
      sum_pair_int 2 6 (by norm_num)]
    exact sq_add_le_two_mul_sq_add_sq _ _
  · rw [activeOffsetsOfResidue_three, sum_pair_int 3 7 (by norm_num),
      sum_pair_int 3 7 (by norm_num)]
    exact sq_add_le_two_mul_sq_add_sq _ _

/-- The tagged contact fibre over the daughter `d` of owner `q`. -/
def contactFibre (q d : ℕ) : Finset ℕ :=
  activeOffsetsOfResidue (q * q * d % 4)

/-- Exact fibre size: two tagged preimages off the zero class, none on it. -/
theorem card_contactFibre (q d : ℕ) :
    (contactFibre q d).card = if q * q * d % 4 = 0 then 0 else 2 := by
  unfold contactFibre
  exact card_activeOffsetsOfResidue _ (Nat.mod_lt _ (by norm_num))

/-- Every actual tagged `q^2` contact of a physical cell lies in the fibre of
its own daughter: the fibre is the literal contact set, not a model of it. -/
theorem mem_contactFibre_of_contact {q a k : ℕ}
    (ha : a ∈ physicalTransitionActiveOffsets) (hdiv : q * q ∣ 4 * k + a) :
    a ∈ contactFibre q (qSquareOffsetDaughter q a k) := by
  have hx : q * q * qSquareOffsetDaughter q a k = 4 * k + a :=
    qSquareOffsetDaughter_exact hdiv
  unfold contactFibre activeOffsetsOfResidue
  refine Finset.mem_filter.mpr ⟨ha, ?_⟩
  rw [hx]
  omega

/-- Conversely each fibre element reconstructs its physical source cell. -/
theorem contactFibre_sourceCell_spec {q a d : ℕ}
    (ha : a ∈ contactFibre q d) (hle : a ≤ q * q * d) :
    4 * qSquareOffsetSourceCell q a d + a = q * q * d := by
  unfold contactFibre activeOffsetsOfResidue at ha
  have hmod : a % 4 = q * q * d % 4 := (Finset.mem_filter.mp ha).2
  unfold qSquareOffsetSourceCell
  omega

/-- **Field-independent frame constant two.**  The bound holds for an arbitrary
field `w`, so it uses no property of Mobius whatsoever. -/
theorem contact_frame_two (q d : ℕ) (w : ℕ → ℤ) :
    (∑ a ∈ contactFibre q d, w a) ^ 2 ≤
      2 * ∑ a ∈ contactFibre q d, (w a) ^ 2 := by
  unfold contactFibre
  exact sq_sum_activeOffsetsOfResidue_le_two_mul _ (Nat.mod_lt _ (by norm_num)) w

/-- **The proposed `alpha_q <= 3` estimate is a corollary of fibre counting.**
It is therefore not a cancellation theorem, and cannot carry arithmetic content
into the exceptional induction. -/
theorem contact_frame_three (q d : ℕ) (w : ℕ → ℤ) :
    (∑ a ∈ contactFibre q d, w a) ^ 2 ≤
      3 * ∑ a ∈ contactFibre q d, (w a) ^ 2 := by
  have h := contact_frame_two q d w
  have hnn : (0 : ℤ) ≤ ∑ a ∈ contactFibre q d, (w a) ^ 2 :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  linarith

/-- Two is attained on the all-ones field, so no field-independent constant is
smaller.  The gap between the proposed three and the observed value near one is
not arithmetic content; it is an assumption about Mobius signs. -/
theorem contact_frame_two_sharp :
    (∑ _a ∈ activeOffsetsOfResidue 1, (1 : ℤ)) ^ 2 =
      2 * ∑ _a ∈ activeOffsetsOfResidue 1, (1 : ℤ) ^ 2 := by
  rw [activeOffsetsOfResidue_one, sum_pair_int 1 5 (by norm_num),
    sum_pair_int 1 5 (by norm_num)]
  norm_num

/-! ## 3. Assembled coefficient norm versus recursive Mertens energy -/

/-- Computable form of the true physical degree-one source observable. -/
def physicalSourceCellValue (k : ℕ) : ℤ :=
  μ (4 * k + 1) + μ (4 * k + 2) + μ (4 * k + 3)

/-- It is exactly the repository's degree-one source observable. -/
theorem physicalSourceCellValue_eq_threeSlotDegreeOneValue (k : ℕ) :
    physicalSourceCellValue k = threeSlotDegreeOneValue (threeSlotState k) :=
  (threeSlotDegreeOneValue_threeSlotState k).symm

/-- The assembled `q^2` child of one daughter: the signed sum over the tagged
contact fibre, taken *before* any norm. -/
def contactDaughterCoefficient (q d : ℕ) : ℤ :=
  ∑ a ∈ contactFibre q d, physicalSourceCellValue (qSquareOffsetSourceCell q a d)

/-- The squared mass of the assembled children over the daughter range.  This
is the quantity a frame estimate bounds. -/
def contactDaughterCoefficientNorm (q Y : ℕ) : ℤ :=
  ∑ d ∈ Finset.Icc 1 Y, (contactDaughterCoefficient q d) ^ 2

/-- The recursive energy profile the exceptional induction actually consumes. -/
def mertensEnergy (Y : ℕ) : ℚ := ((mertensSummatoryInt Y : ℚ)) ^ 2

/-- The daughter terms of the exceptional step are that recursive energy at the
smaller cutoff, never an assembled coefficient norm. -/
theorem exceptionalOwnerEnergyStep_mertensEnergy (C alpha3 alpha5 alpha7 : ℚ) :
    ExceptionalOwnerEnergyStep mertensEnergy C alpha3 alpha5 alpha7 ↔
      ∀ X : ℕ, mertensEnergy X ≤ C * (X : ℚ) +
        alpha3 * mertensEnergy (X / 9) + alpha5 * mertensEnergy (X / 25) +
        alpha7 * mertensEnergy (X / 49) :=
  Iff.rfl

/-- Computable evaluator for the daughter Mertens value. -/
def mertensEval (Y : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (Y + 1), μ n

theorem mertensEval_eq_mertensSummatoryInt (Y : ℕ) :
    mertensEval Y = mertensSummatoryInt Y := rfl

/-- Finite certificate: the daughter Mertens value vanishes at the cutoff two. -/
theorem mertensEval_two : mertensEval 2 = 0 := by
  native_decide

theorem mertensSummatoryInt_two : mertensSummatoryInt 2 = 0 := by
  rw [← mertensEval_eq_mertensSummatoryInt]
  exact mertensEval_two

/-- Finite certificates: the assembled coefficient norm is already positive at
the same cutoff, for every exceptional owner. -/
theorem contactDaughterCoefficientNorm_three_two :
    contactDaughterCoefficientNorm 3 2 = 2 := by
  native_decide

theorem contactDaughterCoefficientNorm_five_two :
    contactDaughterCoefficientNorm 5 2 = 5 := by
  native_decide

theorem contactDaughterCoefficientNorm_seven_two :
    contactDaughterCoefficientNorm 7 2 = 5 := by
  native_decide

/-- **Type mismatch between the two energies.**  No constant compares the
assembled `q^2` coefficient norm with the recursive Mertens energy at the same
daughter cutoff: the latter vanishes at `Y = 2` while the former does not.  The
frame route therefore cannot produce the `alpha_q * E (X / q^2)` term of
`ExceptionalOwnerEnergyStep`, whatever frame constant is proved. -/
theorem no_contactDaughterCoefficientNorm_mertensEnergy_constant
    {q : ℕ} (hq : q = 3 ∨ q = 5 ∨ q = 7) :
    ¬ ∃ alpha : ℚ, ∀ Y : ℕ,
      (contactDaughterCoefficientNorm q Y : ℚ) ≤ alpha * mertensEnergy Y := by
  rintro ⟨alpha, halpha⟩
  have hpos : 0 < contactDaughterCoefficientNorm q 2 := by
    rcases hq with rfl | rfl | rfl
    · rw [contactDaughterCoefficientNorm_three_two]; norm_num
    · rw [contactDaughterCoefficientNorm_five_two]; norm_num
    · rw [contactDaughterCoefficientNorm_seven_two]; norm_num
  have hzero : mertensEnergy 2 = 0 := by
    unfold mertensEnergy
    rw [mertensSummatoryInt_two]
    norm_num
  have h := halpha 2
  rw [hzero, mul_zero] at h
  have hposQ : (0 : ℚ) < (contactDaughterCoefficientNorm q 2 : ℚ) := by
    exact_mod_cast hpos
  linarith

/-- The same separation against an arbitrary dominating profile: no energy
profile dominating the assembled coefficient norm is the recursive Mertens
energy. -/
theorem dominating_profile_ne_mertensEnergy
    {q : ℕ} (hq : q = 3 ∨ q = 5 ∨ q = 7) {E : ℕ → ℚ}
    (hdom : ∀ Y : ℕ, (contactDaughterCoefficientNorm q Y : ℚ) ≤ E Y) :
    E ≠ mertensEnergy := by
  intro hE
  refine no_contactDaughterCoefficientNorm_mertensEnergy_constant hq ⟨1, fun Y => ?_⟩
  have := hdom Y
  rw [hE] at this
  linarith

/-! ## 4. Signed exceptional owner reassembly before energy -/

open RHLean.Arithmetic

/-- Restrict any physical cell carrier to a specified least square-prime owner. -/
def physicalCellsOwnedBy (S : Finset ℕ) (owner : ℕ) : Finset ℕ :=
  S.filter fun k => physicalLeastOddSquarePrime k = some owner

@[simp] theorem mem_physicalCellsOwnedBy
    {S : Finset ℕ} {owner k : ℕ} :
    k ∈ physicalCellsOwnedBy S owner ↔
      k ∈ S ∧ physicalLeastOddSquarePrime k = some owner := by
  simp [physicalCellsOwnedBy]

/-- Distinct least owners give disjoint subcarriers. -/
theorem physicalCellsOwnedBy_disjoint_of_ne
    (S : Finset ℕ) {a b : ℕ} (hab : a ≠ b) :
    Disjoint (physicalCellsOwnedBy S a) (physicalCellsOwnedBy S b) := by
  rw [Finset.disjoint_left]
  intro k hka hkb
  have ha := (mem_physicalCellsOwnedBy.mp hka).2
  have hb := (mem_physicalCellsOwnedBy.mp hkb).2
  have hs : (some a : Option ℕ) = some b := ha.symm.trans hb
  exact hab (Option.some.inj hs)

/-- Owner-5 Buchstab partition: every `5^2` contact is owned by 5 or 3. -/
theorem fiveHitCarrier_eq_ownerPartition
    (S : Finset ℕ)
    (h5 : ∀ k ∈ S, physicalSquarePrimeAtEdge k 5) :
    S = physicalCellsOwnedBy S 5 ∪ physicalCellsOwnedBy S 3 := by
  ext k
  simp only [Finset.mem_union, mem_physicalCellsOwnedBy]
  constructor
  · intro hk
    by_cases howner : physicalLeastOddSquarePrime k = some 5
    · exact Or.inl ⟨hk, howner⟩
    · have hthree := fiveContact_not_fiveOwner_implies_threeOwner (h5 k hk) howner
      exact Or.inr ⟨hk, hthree⟩
  · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk

/-- The owner-5 partition preserves an arbitrary additive signed observable. -/
theorem fiveHitCarrier_sum_reassemble
    {A : Type*} [AddCommMonoid A]
    (S : Finset ℕ) (h5 : ∀ k ∈ S, physicalSquarePrimeAtEdge k 5)
    (f : ℕ → A) :
    (∑ k ∈ S, f k) =
      (∑ k ∈ physicalCellsOwnedBy S 5, f k) +
        ∑ k ∈ physicalCellsOwnedBy S 3, f k := by
  have hpart := fiveHitCarrier_eq_ownerPartition S h5
  have hsum :
      (∑ k ∈ S, f k) =
        ∑ k ∈ physicalCellsOwnedBy S 5 ∪ physicalCellsOwnedBy S 3, f k :=
    congrArg (fun T : Finset ℕ => ∑ k ∈ T, f k) hpart
  exact hsum.trans
    (Finset.sum_union (physicalCellsOwnedBy_disjoint_of_ne S (by norm_num : 5 ≠ 3)))

/-- Owner-7 Buchstab partition: every `7^2` contact is owned by 7, 3, or 5. -/
theorem sevenHitCarrier_eq_ownerPartition
    (S : Finset ℕ)
    (h7 : ∀ k ∈ S, physicalSquarePrimeAtEdge k 7) :
    S = (physicalCellsOwnedBy S 7 ∪ physicalCellsOwnedBy S 3) ∪
      physicalCellsOwnedBy S 5 := by
  ext k
  simp only [Finset.mem_union, mem_physicalCellsOwnedBy]
  constructor
  · intro hk
    by_cases howner : physicalLeastOddSquarePrime k = some 7
    · exact Or.inl (Or.inl ⟨hk, howner⟩)
    · rcases sevenContact_not_sevenOwner_implies_threeOrFiveOwner
        (h7 k hk) howner with hthree | hfive
      · exact Or.inl (Or.inr ⟨hk, hthree⟩)
      · exact Or.inr ⟨hk, hfive⟩
  · rintro ((⟨hk, _⟩ | ⟨hk, _⟩) | ⟨hk, _⟩) <;> exact hk

/-- The owner-7 partition preserves an arbitrary additive signed observable. -/
theorem sevenHitCarrier_sum_reassemble
    {A : Type*} [AddCommMonoid A]
    (S : Finset ℕ) (h7 : ∀ k ∈ S, physicalSquarePrimeAtEdge k 7)
    (f : ℕ → A) :
    (∑ k ∈ S, f k) =
      ((∑ k ∈ physicalCellsOwnedBy S 7, f k) +
        ∑ k ∈ physicalCellsOwnedBy S 3, f k) +
          ∑ k ∈ physicalCellsOwnedBy S 5, f k := by
  have h73 : Disjoint (physicalCellsOwnedBy S 7) (physicalCellsOwnedBy S 3) :=
    physicalCellsOwnedBy_disjoint_of_ne S (by norm_num : 7 ≠ 3)
  have hUnion5 :
      Disjoint (physicalCellsOwnedBy S 7 ∪ physicalCellsOwnedBy S 3)
        (physicalCellsOwnedBy S 5) := by
    rw [Finset.disjoint_union_left]
    exact ⟨
      physicalCellsOwnedBy_disjoint_of_ne S (by norm_num : 7 ≠ 5),
      physicalCellsOwnedBy_disjoint_of_ne S (by norm_num : 3 ≠ 5)⟩
  have hpart := sevenHitCarrier_eq_ownerPartition S h7
  have hsum :
      (∑ k ∈ S, f k) =
        ∑ k ∈ (physicalCellsOwnedBy S 7 ∪ physicalCellsOwnedBy S 3) ∪
          physicalCellsOwnedBy S 5, f k :=
    congrArg (fun T : Finset ℕ => ∑ k ∈ T, f k) hpart
  calc
    (∑ k ∈ S, f k) =
        ∑ k ∈ (physicalCellsOwnedBy S 7 ∪ physicalCellsOwnedBy S 3) ∪
          physicalCellsOwnedBy S 5, f k := hsum
    _ = (∑ k ∈ physicalCellsOwnedBy S 7 ∪ physicalCellsOwnedBy S 3, f k) +
          ∑ k ∈ physicalCellsOwnedBy S 5, f k := Finset.sum_union hUnion5
    _ = ((∑ k ∈ physicalCellsOwnedBy S 7, f k) +
          ∑ k ∈ physicalCellsOwnedBy S 3, f k) +
          ∑ k ∈ physicalCellsOwnedBy S 5, f k := by
      rw [Finset.sum_union h73]

/-- The six physical `5^2` contact cells in period `L`. -/
def q5FullContactPeriodCells (L : ℕ) : Finset ℕ :=
  physicalTwentyFiveHitResidues.image fun r => 25 * L + r

/-- The six physical `7^2` contact cells in period `L`. -/
def q7FullContactPeriodCells (L : ℕ) : Finset ℕ :=
  physicalFortyNineHitResidues.image fun r => 49 * L + r

/-- Every displayed `5^2` period cell is a genuine `5^2` contact. -/
theorem q5FullContactPeriodCells_hit
    {L k : ℕ} (hk : k ∈ q5FullContactPeriodCells L) :
    physicalSquarePrimeAtEdge k 5 := by
  rcases Finset.mem_image.mp hk with ⟨r, hr, rfl⟩
  rw [physicalSquarePrimeAtEdge_five_iff]
  have hrlt : r < 25 := by
    simp [physicalTwentyFiveHitResidues] at hr
    omega
  simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hrlt] using hr

/-- Every displayed `7^2` period cell is a genuine `7^2` contact. -/
theorem q7FullContactPeriodCells_hit
    {L k : ℕ} (hk : k ∈ q7FullContactPeriodCells L) :
    physicalSquarePrimeAtEdge k 7 := by
  rcases Finset.mem_image.mp hk with ⟨r, hr, rfl⟩
  rw [physicalSquarePrimeAtEdge_seven_iff]
  have hrlt : r < 49 := by
    simp [physicalFortyNineHitResidues] at hr
    omega
  simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hrlt] using hr

/-- Reindex the existing owner-5 full-contact unit descent onto physical cells. -/
theorem q5_fullContactPeriodCells_q2Daughter_eq_lowerFourSlotCell (L : ℕ) :
    (∑ k ∈ q5FullContactPeriodCells L,
      physicalQ2DaughterCellIncrement 5 k) = fourSlotCellSum L := by
  unfold q5FullContactPeriodCells
  rw [Finset.sum_image]
  · exact q5_fullContactPeriod_q2Daughter_eq_lowerFourSlotCell L
  · intro a _ha b _hb hab
    exact Nat.add_left_cancel hab

/-- Reindex the existing owner-7 full-contact unit descent onto physical cells. -/
theorem q7_fullContactPeriodCells_q2Daughter_eq_lowerFourSlotCell (L : ℕ) :
    (∑ k ∈ q7FullContactPeriodCells L,
      physicalQ2DaughterCellIncrement 7 k) = fourSlotCellSum L := by
  unfold q7FullContactPeriodCells
  rw [Finset.sum_image]
  · exact q7_fullContactPeriod_q2Daughter_eq_lowerFourSlotCell L
  · intro a _ha b _hb hab
    exact Nat.add_left_cancel hab

/-- The `5^2` full daughter is restored exactly by adding owner-3 overlap cells. -/
theorem q5_completePeriod_q2Daughter_reassembled_by_owner (L : ℕ) :
    (∑ k ∈ physicalCellsOwnedBy (q5FullContactPeriodCells L) 5,
        physicalQ2DaughterCellIncrement 5 k) +
      (∑ k ∈ physicalCellsOwnedBy (q5FullContactPeriodCells L) 3,
        physicalQ2DaughterCellIncrement 5 k) =
      fourSlotCellSum L := by
  calc
    (∑ k ∈ physicalCellsOwnedBy (q5FullContactPeriodCells L) 5,
        physicalQ2DaughterCellIncrement 5 k) +
      (∑ k ∈ physicalCellsOwnedBy (q5FullContactPeriodCells L) 3,
        physicalQ2DaughterCellIncrement 5 k) =
        ∑ k ∈ q5FullContactPeriodCells L,
          physicalQ2DaughterCellIncrement 5 k :=
      (fiveHitCarrier_sum_reassemble (q5FullContactPeriodCells L)
        (fun k hk => q5FullContactPeriodCells_hit hk)
        (physicalQ2DaughterCellIncrement 5)).symm
    _ = fourSlotCellSum L :=
      q5_fullContactPeriodCells_q2Daughter_eq_lowerFourSlotCell L

/-- The `7^2` full daughter is restored exactly by owner-3 and owner-5 overlaps. -/
theorem q7_completePeriod_q2Daughter_reassembled_by_owner (L : ℕ) :
    ((∑ k ∈ physicalCellsOwnedBy (q7FullContactPeriodCells L) 7,
        physicalQ2DaughterCellIncrement 7 k) +
      (∑ k ∈ physicalCellsOwnedBy (q7FullContactPeriodCells L) 3,
        physicalQ2DaughterCellIncrement 7 k)) +
      (∑ k ∈ physicalCellsOwnedBy (q7FullContactPeriodCells L) 5,
        physicalQ2DaughterCellIncrement 7 k) =
      fourSlotCellSum L := by
  calc
    ((∑ k ∈ physicalCellsOwnedBy (q7FullContactPeriodCells L) 7,
        physicalQ2DaughterCellIncrement 7 k) +
      (∑ k ∈ physicalCellsOwnedBy (q7FullContactPeriodCells L) 3,
        physicalQ2DaughterCellIncrement 7 k)) +
      (∑ k ∈ physicalCellsOwnedBy (q7FullContactPeriodCells L) 5,
        physicalQ2DaughterCellIncrement 7 k) =
        ∑ k ∈ q7FullContactPeriodCells L,
          physicalQ2DaughterCellIncrement 7 k :=
      (sevenHitCarrier_sum_reassemble (q7FullContactPeriodCells L)
        (fun k hk => q7FullContactPeriodCells_hit hk)
        (physicalQ2DaughterCellIncrement 7)).symm
    _ = fourSlotCellSum L :=
      q7_fullContactPeriodCells_q2Daughter_eq_lowerFourSlotCell L

/-! ## 5. Exact q² support and telescope onto the recursive signed packet -/

/-- The coefficient-level `q²` daughter is a discrete derivative, so its sum
across *all* physical cells telescopes exactly to the lower positive Möbius
prefix.  No contact geometry or estimate is used in this step. -/
theorem physicalQ2Daughter_range_sum_eq_moebiusPositivePrefix
    (q K : ℕ) :
    (∑ k ∈ Finset.range K, physicalQ2DaughterCellIncrement q k) =
      moebiusPositivePrefix (4 * K / (q * q)) := by
  induction K with
  | zero =>
      simp [physicalQ2DaughterCellIncrement_eq, moebiusPositivePrefix,
        positivePrefix]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, physicalQ2DaughterCellIncrement_eq]
      ring

/-- **Exact support lemma.**  For an odd prime `q`, a nonzero `q²` daughter
increment can occur only on one of the six physical `q²` contact sites.  The
only extra floor-crossing position would be offset four; at that position the
crossed integer is divisible by `4`, hence is not squarefree and has zero
Möbius weight. -/
theorem physicalQ2Daughter_nonzero_implies_squarePrimeAtEdge
    {q k : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q)
    (hD : physicalQ2DaughterCellIncrement q k ≠ 0) :
    physicalSquarePrimeAtEdge k q := by
  let Q : ℕ := q * q
  let lo : ℕ := 4 * k / Q
  let hi : ℕ := 4 * (k + 1) / Q
  have hQpos : 0 < Q := by
    dsimp [Q]
    positivity
  have hQgt4 : 4 < Q := by
    dsimp [Q]
    nlinarith
  have hlo_le_hi : lo ≤ hi := by
    dsimp [lo, hi]
    exact Nat.div_le_div_right (by omega)
  have hhi_le : hi ≤ lo + 1 := by
    have hxlt : 4 * k < Q * (lo + 1) := by
      have hdiv : 4 * k / Q < lo + 1 := by
        dsimp [lo]
        omega
      have h := (Nat.div_lt_iff_lt_mul hQpos).1 hdiv
      simpa [Nat.mul_comm] using h
    have hsumlt : 4 * (k + 1) < Q * (lo + 2) := by
      calc
        4 * (k + 1) = 4 * k + 4 := by omega
        _ < Q * (lo + 1) + Q := Nat.add_lt_add hxlt hQgt4
        _ = Q * (lo + 2) := by ring
    have hdivHi : hi < lo + 2 := by
      dsimp [hi]
      have hsumlt' : 4 * (k + 1) < (lo + 2) * Q := by
        rw [Nat.mul_comm (lo + 2) Q]
        exact hsumlt
      exact (Nat.div_lt_iff_lt_mul hQpos).2 hsumlt'
    omega
  have hne : hi ≠ lo := by
    intro heq
    apply hD
    rw [physicalQ2DaughterCellIncrement_eq]
    change moebiusPositivePrefix hi - moebiusPositivePrefix lo = 0
    rw [heq]
    ring
  have hstep : hi = lo + 1 := by
    omega
  have hD' : moebiusPositivePrefix hi - moebiusPositivePrefix lo ≠ 0 := by
    simpa [physicalQ2DaughterCellIncrement_eq, hi, lo] using hD
  rw [hstep, moebiusPositivePrefix_succ_sub_self] at hD'
  have hsfStep : Squarefree (lo + 1) :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hD'
  have hsf : Squarefree hi := by
    rw [hstep]
    exact hsfStep
  have hloSpec : lo * Q ≤ 4 * k ∧ 4 * k ≤ lo * Q + Q - 1 := by
    exact (Nat.div_eq_iff hQpos).mp (by rfl)
  have hhiSpec : hi * Q ≤ 4 * (k + 1) ∧
      4 * (k + 1) ≤ hi * Q + Q - 1 := by
    exact (Nat.div_eq_iff hQpos).mp (by rfl)
  have hhiProd : hi * Q = lo * Q + Q := by
    rw [hstep]
    ring
  have hcrossLo : 4 * k < hi * Q := by
    rw [hhiProd]
    omega
  have hcrossHi : hi * Q ≤ 4 * k + 4 := by
    have := hhiSpec.1
    omega
  let a : ℕ := hi * Q - 4 * k
  have ha1 : 1 ≤ a := by
    dsimp [a]
    omega
  have ha4 : a ≤ 4 := by
    dsimp [a]
    omega
  have hsum : 4 * k + a = hi * Q := by
    dsimp [a]
    omega
  have hqodd : Odd q := by
    rcases hq.eq_two_or_odd' with hq2 | hodd
    · omega
    · exact hodd
  have hcop2q : Nat.Coprime 2 q := hqodd.coprime_two_left
  have hcop4Q : Nat.Coprime 4 Q := by
    dsimp [Q]
    simpa [pow_two] using hcop2q.pow 2 2
  have hane4 : a ≠ 4 := by
    intro haeq
    have h4prod : 4 ∣ Q * hi := by
      refine ⟨k + 1, ?_⟩
      rw [Nat.mul_comm Q hi, ← hsum, haeq]
      omega
    have h4hi : 4 ∣ hi := hcop4Q.dvd_of_dvd_mul_left h4prod
    have h22 : 2 * 2 ∣ hi := by simpa using h4hi
    have hunit : IsUnit (2 : ℕ) := hsf 2 h22
    norm_num at hunit
  have ha3 : a ≤ 3 := by omega
  have haActive : a ∈ physicalTransitionActiveOffsets := by
    simp [physicalTransitionActiveOffsets]
    omega
  refine ⟨hq, a, haActive, ?_⟩
  refine ⟨hi, ?_⟩
  calc
    4 * k + a = hi * Q := hsum
    _ = q * q * hi := by
      dsimp [Q]
      ring

/-- Summing only over the genuine physical `q²` contact carrier loses nothing:
every omitted cell has zero daughter increment. -/
theorem physicalQ2Daughter_squareHit_sum_eq_range
    {q K : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    (∑ k ∈ physicalSquareHitCells K q,
      physicalQ2DaughterCellIncrement q k) =
      ∑ k ∈ Finset.range K, physicalQ2DaughterCellIncrement q k := by
  have hsub : physicalSquareHitCells K q ⊆ Finset.range K := by
    intro k hk
    exact Finset.mem_range.mpr ((mem_physicalSquareHitCells_iff hq).mp hk).1
  apply Finset.sum_subset hsub
  intro k hkRange hkNotHit
  by_contra hne
  apply hkNotHit
  exact (mem_physicalSquareHitCells_iff hq).mpr
    ⟨Finset.mem_range.mp hkRange,
      physicalQ2Daughter_nonzero_implies_squarePrimeAtEdge hq hq3 hne⟩

/-- **Exact recursive Mertens daughter.**  After signed physical reassembly,
the complete `q²` contact packet is literally the same lower-scale Mertens
prefix required by the recursive energy.  There is no incomplete-period error. -/
theorem physicalQ2Daughter_squareHit_sum_eq_mertens
    {q K : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    (∑ k ∈ physicalSquareHitCells K q,
      physicalQ2DaughterCellIncrement q k) =
      mertensSummatoryInt (4 * K / (q * q)) := by
  rw [physicalQ2Daughter_squareHit_sum_eq_range hq hq3,
    physicalQ2Daughter_range_sum_eq_moebiusPositivePrefix]
  rw [mertensSummatoryInt_eq_Icc]
  rfl

/-- The same exact packet is the already-compiled intact signed predecessor
state `F_{q^-}-T_{q^-}`.  This makes the no-norm-before-reassembly dictionary
literal at arbitrary cutoffs. -/
theorem physicalQ2Daughter_squareHit_sum_eq_signedPredecessorState
    {q K : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    (∑ k ∈ physicalSquareHitCells K q,
      physicalQ2DaughterCellIncrement q k) =
      exceptionalSignedPredecessorState q (4 * K / (q * q)) := by
  rw [physicalQ2Daughter_squareHit_sum_eq_mertens hq hq3,
    exceptionalSignedPredecessorState_eq_mertens hq]

/-- The `3²` hit carrier is already exactly the least-owner-3 carrier. -/
theorem q3_squareHitCells_eq_ownerThree (K : ℕ) :
    physicalCellsOwnedBy (physicalSquareHitCells K 3) 3 =
      physicalSquareHitCells K 3 := by
  ext k
  simp only [mem_physicalCellsOwnedBy]
  constructor
  · exact And.left
  · intro hk
    refine ⟨hk, ?_⟩
    have hcontact :=
      ((mem_physicalSquareHitCells_iff (by norm_num : Nat.Prime 3)).mp hk).2
    exact (physicalLeastOddSquarePrime_eq_three_iff k).2 hcontact

/-- Exact owner-3 recursive daughter at an arbitrary physical cutoff. -/
theorem q3_ownedPrefix_q2Daughter_eq_mertens (K : ℕ) :
    (∑ k ∈ physicalCellsOwnedBy (physicalSquareHitCells K 3) 3,
      physicalQ2DaughterCellIncrement 3 k) =
      mertensSummatoryInt (4 * K / 9) := by
  rw [q3_squareHitCells_eq_ownerThree]
  simpa using physicalQ2Daughter_squareHit_sum_eq_mertens
    (q := 3) (K := K) (by norm_num) (by norm_num)

/-- **Exact owner-5 reassembly at arbitrary cutoff.**  The least-owner-5 packet
plus its earlier-owner-3 overlap is exactly the recursive Mertens daughter. -/
theorem q5_reassembledPrefix_q2Daughter_eq_mertens (K : ℕ) :
    (∑ k ∈ physicalCellsOwnedBy (physicalSquareHitCells K 5) 5,
        physicalQ2DaughterCellIncrement 5 k) +
      (∑ k ∈ physicalCellsOwnedBy (physicalSquareHitCells K 5) 3,
        physicalQ2DaughterCellIncrement 5 k) =
      mertensSummatoryInt (4 * K / 25) := by
  have hcontact : ∀ k ∈ physicalSquareHitCells K 5,
      physicalSquarePrimeAtEdge k 5 := by
    intro k hk
    exact ((mem_physicalSquareHitCells_iff (by norm_num : Nat.Prime 5)).mp hk).2
  calc
    (∑ k ∈ physicalCellsOwnedBy (physicalSquareHitCells K 5) 5,
        physicalQ2DaughterCellIncrement 5 k) +
      (∑ k ∈ physicalCellsOwnedBy (physicalSquareHitCells K 5) 3,
        physicalQ2DaughterCellIncrement 5 k) =
        ∑ k ∈ physicalSquareHitCells K 5,
          physicalQ2DaughterCellIncrement 5 k :=
      (fiveHitCarrier_sum_reassemble (physicalSquareHitCells K 5) hcontact
        (physicalQ2DaughterCellIncrement 5)).symm
    _ = mertensSummatoryInt (4 * K / 25) := by
      simpa using physicalQ2Daughter_squareHit_sum_eq_mertens
        (q := 5) (K := K) (by norm_num) (by norm_num)

/-- **Exact owner-7 reassembly at arbitrary cutoff.**  The least-owner-7 packet
plus its owner-3 and owner-5 overlaps is exactly the recursive Mertens daughter. -/
theorem q7_reassembledPrefix_q2Daughter_eq_mertens (K : ℕ) :
    ((∑ k ∈ physicalCellsOwnedBy (physicalSquareHitCells K 7) 7,
        physicalQ2DaughterCellIncrement 7 k) +
      (∑ k ∈ physicalCellsOwnedBy (physicalSquareHitCells K 7) 3,
        physicalQ2DaughterCellIncrement 7 k)) +
      (∑ k ∈ physicalCellsOwnedBy (physicalSquareHitCells K 7) 5,
        physicalQ2DaughterCellIncrement 7 k) =
      mertensSummatoryInt (4 * K / 49) := by
  have hcontact : ∀ k ∈ physicalSquareHitCells K 7,
      physicalSquarePrimeAtEdge k 7 := by
    intro k hk
    exact ((mem_physicalSquareHitCells_iff (by norm_num : Nat.Prime 7)).mp hk).2
  calc
    ((∑ k ∈ physicalCellsOwnedBy (physicalSquareHitCells K 7) 7,
        physicalQ2DaughterCellIncrement 7 k) +
      (∑ k ∈ physicalCellsOwnedBy (physicalSquareHitCells K 7) 3,
        physicalQ2DaughterCellIncrement 7 k)) +
      (∑ k ∈ physicalCellsOwnedBy (physicalSquareHitCells K 7) 5,
        physicalQ2DaughterCellIncrement 7 k) =
        ∑ k ∈ physicalSquareHitCells K 7,
          physicalQ2DaughterCellIncrement 7 k :=
      (sevenHitCarrier_sum_reassemble (physicalSquareHitCells K 7) hcontact
        (physicalQ2DaughterCellIncrement 7)).symm
    _ = mertensSummatoryInt (4 * K / 49) := by
      simpa using physicalQ2Daughter_squareHit_sum_eq_mertens
        (q := 7) (K := K) (by norm_num) (by norm_num)