import Mathlib
import RHLean.Analysis.OutsidePrimeDeletionMask
import RHLean.Analysis.PhysicalDegreeOneLeastSquareChannels

/-!
# Least-square aggregation and endpoint control for outside-prime deletion

The outside-prime deletion mask is already an exact signed difference between
selected-prime and actual Mobius zero-free populations.  This file makes the
next structural move without introducing another independence hypothesis:

* every deleted cell has a least square-prime channel;
* the signed deletion mass is exactly the disjoint sum of those least channels;
* for a cell owned by `q`, the relevant complete super-orbit contains the
  selected CRT primes together with every smaller prime and `q` itself;
* in one physical square block the deletion population splits exactly into
  complete least-square super-orbits and a literal endpoint residue;
* the aggregate endpoint residue, after the disjoint least-square ownership has
  already been imposed, has only `O(R)` cells and hence `O(R)` signed mass.

The endpoint estimate is deliberately taken only after aggregation.  There is
no channelwise triangle inequality and no claim that the raw uncentered
selected field has zero mean.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-- The explicit eight-state carrier is exactly the predicate used by the
physical square-transfer modules. -/
theorem isThreeSlotNonzeroState_iff_mem_physicalThreeSlotNonzeroStates
    (s : Fin 27) :
    IsThreeSlotNonzeroState s ↔ s ∈ physicalThreeSlotNonzeroStates := by
  fin_cases s <;> native_decide

/-- A cell in the outside-prime deletion mask cannot have an all-squarefree
physical edge, so its least square-prime channel is present. -/
theorem outsidePrimeDeletion_leastSquare_ne_none
    {P O : Finset ℕ} {k : ℕ}
    (hk : k ∈ outsidePrimeDeletionCells P O) :
    physicalLeastOddSquarePrime k ≠ none := by
  intro hnone
  have hedge :=
    (physicalLeastOddSquarePrime_eq_none_iff_nonzeroEdge k).mp hnone
  have hactual : outsidePrimeActualZeroFreeAt k := by
    constructor
    · exact
        (isThreeSlotNonzeroState_iff_mem_physicalThreeSlotNonzeroStates
          (threeSlotState k)).2 hedge.1
    · exact
        (isThreeSlotNonzeroState_iff_mem_physicalThreeSlotNonzeroStates
          (threeSlotState (k + 1))).2 hedge.2
  exact (mem_outsidePrimeDeletionCells_iff.mp hk).2.2 hactual

/-- Every deleted cell therefore has an actual least square-prime owner. -/
theorem outsidePrimeDeletion_leastSquare_exists
    {P O : Finset ℕ} {k : ℕ}
    (hk : k ∈ outsidePrimeDeletionCells P O) :
    ∃ q : ℕ, physicalLeastOddSquarePrime k = some q := by
  have hne := outsidePrimeDeletion_leastSquare_ne_none hk
  cases h : physicalLeastOddSquarePrime k with
  | none => exact (hne h).elim
  | some q => exact ⟨q, rfl⟩

/-- Least square-prime labels that actually occur in one outside-prime deletion
population. -/
def outsidePrimeLeastDeletionPrimes
    (P O : Finset ℕ) : Finset ℕ :=
  (outsidePrimeDeletionCells P O).image fun k =>
    (physicalLeastOddSquarePrime k).getD 0

/-- Signed deletion mass owned by one least square-prime label.  The `getD 0`
is harmless on this carrier because `outsidePrimeDeletion_leastSquare_ne_none`
proves that `none` never occurs. -/
def outsidePrimeLeastDeletionChannel
    (P O : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ k ∈ outsidePrimeDeletionCells P O with
      (physicalLeastOddSquarePrime k).getD 0 = q,
    selectedDegreeOneProjection P k

/-- **Exact least-square aggregation.**  The outside-prime deletion mass is the
disjoint sum of its least square-prime channels.  No absolute values are used. -/
theorem outsidePrimeDeletionT_eq_sum_leastSquareChannels
    (P O : Finset ℕ) :
    outsidePrimeDeletionT P O =
      ∑ q ∈ outsidePrimeLeastDeletionPrimes P O,
        outsidePrimeLeastDeletionChannel P O q := by
  classical
  let E : Finset ℕ := outsidePrimeDeletionCells P O
  let owner : ℕ → ℕ := fun k =>
    (physicalLeastOddSquarePrime k).getD 0
  have hmaps : ∀ k ∈ E, owner k ∈ outsidePrimeLeastDeletionPrimes P O := by
    intro k hk
    unfold outsidePrimeLeastDeletionPrimes
    exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := E)
    (t := outsidePrimeLeastDeletionPrimes P O)
    (g := owner)
    hmaps
    (selectedDegreeOneProjection P)
  simpa [E, owner, outsidePrimeDeletionT,
    outsidePrimeLeastDeletionChannel] using hfiber.symm

/-! ## Least-square super-orbits -/

/-- All primes strictly below `q`.  These are exactly the square channels whose
absence is decided before the least channel `q`. -/
def outsidePrimeEarlierPrimes (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter Nat.Prime

/-- Prime coordinates already visible before the least channel `q`: the
selected set together with every smaller prime. -/
def outsidePrimeLeastStagePrimes
    (P : Finset ℕ) (q : ℕ) : Finset ℕ :=
  P ∪ outsidePrimeEarlierPrimes q

/-- The complete prime set whose square modulus resolves the selected CRT state,
all smaller square-deletion channels, and the current least channel `q`. -/
def outsidePrimeLeastSuperPrimeSet
    (P : Finset ℕ) (q : ℕ) : Finset ℕ :=
  insert q (outsidePrimeLeastStagePrimes P q)

/-- Aligned complete super-orbit for the least channel `q`.  Reusing
`finitePrimeCRTOrbit` keeps the square-clock alignment identical to the earlier
physical CRT transfer layer. -/
def outsidePrimeLeastSuperOrbit
    (P : Finset ℕ) (q k : ℕ) : Finset ℕ :=
  finitePrimeCRTOrbit (outsidePrimeLeastSuperPrimeSet P q) k

/-- Outside-prime deletions occurring inside one physical square-block
transition carrier. -/
def squareBlockOutsidePrimeDeletionCells
    (P : Finset ℕ) (R : ℕ) : Finset ℕ :=
  outsidePrimeDeletionCells P (threeSlotSquareBlockTransitionCells R)

/-- Deleted cells whose entire least-square super-orbit lies inside the physical
square-clock carrier. -/
def squareBlockOutsidePrimeLeastCompleteCells
    (P : Finset ℕ) (R : ℕ) : Finset ℕ :=
  (squareBlockOutsidePrimeDeletionCells P R).filter fun k =>
    outsidePrimeLeastSuperOrbit P
        ((physicalLeastOddSquarePrime k).getD 0) k ⊆
      threeSlotSquareBlockTransitionCells R

/-- Literal incomplete-super-orbit endpoint residue, after least-square
ownership has already made the deletion channels disjoint. -/
def squareBlockOutsidePrimeLeastEndpointCells
    (P : Finset ℕ) (R : ℕ) : Finset ℕ :=
  squareBlockOutsidePrimeDeletionCells P R \
    squareBlockOutsidePrimeLeastCompleteCells P R

/-- Signed complete-super-orbit deletion mass in one square block. -/
def squareBlockOutsidePrimeLeastCompleteT
    (P : Finset ℕ) (R : ℕ) : ℝ :=
  ∑ k ∈ squareBlockOutsidePrimeLeastCompleteCells P R,
    selectedDegreeOneProjection P k

/-- Signed aggregate least-square endpoint residue in one square block. -/
def squareBlockOutsidePrimeLeastEndpointT
    (P : Finset ℕ) (R : ℕ) : ℝ :=
  ∑ k ∈ squareBlockOutsidePrimeLeastEndpointCells P R,
    selectedDegreeOneProjection P k

/-- **Exact least-square endpoint decomposition.**  The full outside-prime
deletion mass in a physical square block is the complete-super-orbit mass plus
one aggregate endpoint residue. -/
theorem squareBlockOutsidePrimeDeletionT_eq_complete_add_endpoint
    (P : Finset ℕ) (R : ℕ) :
    outsidePrimeDeletionT P (threeSlotSquareBlockTransitionCells R) =
      squareBlockOutsidePrimeLeastCompleteT P R +
        squareBlockOutsidePrimeLeastEndpointT P R := by
  classical
  have hsub :
      squareBlockOutsidePrimeLeastCompleteCells P R ⊆
        squareBlockOutsidePrimeDeletionCells P R :=
    Finset.filter_subset _ _
  unfold outsidePrimeDeletionT
  change
    (∑ k ∈ squareBlockOutsidePrimeDeletionCells P R,
      selectedDegreeOneProjection P k) = _
  unfold squareBlockOutsidePrimeLeastCompleteT
    squareBlockOutsidePrimeLeastEndpointT
    squareBlockOutsidePrimeLeastEndpointCells
  rw [← Finset.sum_sdiff hsub]
  ring

/-- Every aggregate endpoint cell is still a cell of the single physical square
block.  This is the key reason one should bound the endpoint only after the
least-square aggregation. -/
theorem squareBlockOutsidePrimeLeastEndpointCells_subset_carrier
    (P : Finset ℕ) (R : ℕ) :
    squareBlockOutsidePrimeLeastEndpointCells P R ⊆
      threeSlotSquareBlockTransitionCells R := by
  intro k hk
  have hkdel : k ∈ squareBlockOutsidePrimeDeletionCells P R :=
    (Finset.mem_sdiff.mp hk).1
  exact (mem_outsidePrimeDeletionCells_iff.mp hkdel).1

/-- One square-block transition carrier has only linearly many cells. -/
theorem threeSlotSquareBlockTransitionCells_card_le_linear
    (R : ℕ) :
    (threeSlotSquareBlockTransitionCells R).card ≤ 2 * R + 1 := by
  rw [threeSlotSquareBlockTransitionCells_eq_Ico]
  have hcard :
      (Finset.Ico (threeSlotSquareBlockLower R)
        (threeSlotSquareBlockUpper R)).card =
        threeSlotSquareBlockUpper R - threeSlotSquareBlockLower R := by
    simp
  rw [hcard]
  unfold threeSlotSquareBlockLower threeSlotSquareBlockUpper
  have hpoly : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
  omega

/-- Consequently the **aggregate** least-square endpoint population has linear
size.  There is no sum of per-prime endpoint cardinalities here. -/
theorem squareBlockOutsidePrimeLeastEndpointCells_card_le_linear
    (P : Finset ℕ) (R : ℕ) :
    (squareBlockOutsidePrimeLeastEndpointCells P R).card ≤ 2 * R + 1 := by
  calc
    (squareBlockOutsidePrimeLeastEndpointCells P R).card ≤
        (threeSlotSquareBlockTransitionCells R).card :=
      Finset.card_le_card
        (squareBlockOutsidePrimeLeastEndpointCells_subset_carrier P R)
    _ ≤ 2 * R + 1 := threeSlotSquareBlockTransitionCells_card_le_linear R

private theorem selectedPrimeSign_eq_one_or_neg_one
    (P : Finset ℕ) (n : ℕ) :
    selectedPrimeSign P n = 1 ∨ selectedPrimeSign P n = -1 := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [selectedPrimeSign]
  | @insert p P hp ih =>
      have hinsert :
          selectedPrimeSign (insert p P) n =
            (if p ∣ n then (-1 : ℤ) else 1) * selectedPrimeSign P n := by
        simp [selectedPrimeSign, hp]
      rw [hinsert]
      rcases ih with h | h
      · rw [h]
        by_cases hdiv : p ∣ n <;> simp [hdiv]
      · rw [h]
        by_cases hdiv : p ∣ n <;> simp [hdiv]

/-- The selected degree-one observable is pointwise bounded by three. -/
theorem abs_selectedDegreeOneProjection_le_three
    (P : Finset ℕ) (k : ℕ) :
    |selectedDegreeOneProjection P k| ≤ 3 := by
  rcases selectedPrimeSign_eq_one_or_neg_one P
      (tActiveForm (0 : Fin 3) k) with h0 | h0 <;>
    rcases selectedPrimeSign_eq_one_or_neg_one P
      (tActiveForm (1 : Fin 3) k) with h1 | h1 <;>
    rcases selectedPrimeSign_eq_one_or_neg_one P
      (tActiveForm (2 : Fin 3) k) with h2 | h2
  all_goals
    simp only [tActiveForm_zero] at h0
    simp only [tActiveForm_one] at h1
    simp only [tActiveForm_two] at h2
    simp [selectedDegreeOneProjection, h0, h1, h2]

private theorem abs_selectedDegreeOneProjection_sum_le_three_mul_card
    (P : Finset ℕ) (S : Finset ℕ) :
    |∑ k ∈ S, selectedDegreeOneProjection P k| ≤
      3 * (S.card : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      calc
        |selectedDegreeOneProjection P a +
            ∑ k ∈ S, selectedDegreeOneProjection P k| ≤
          |selectedDegreeOneProjection P a| +
            |∑ k ∈ S, selectedDegreeOneProjection P k| :=
          abs_add_le _ _
        _ ≤ 3 + 3 * (S.card : ℝ) :=
          add_le_add (abs_selectedDegreeOneProjection_le_three P a) ih
        _ = 3 * (((S.card + 1 : ℕ) : ℝ)) := by
          push_cast
          ring

/-- **Root-scale endpoint control.**  After disjoint least-square aggregation,
the entire incomplete square-clock residue has signed mass at most linear in
`R`.  The absolute value is applied once to the final endpoint sum, not to the
individual prime channels. -/
theorem abs_squareBlockOutsidePrimeLeastEndpointT_le_linear
    (P : Finset ℕ) (R : ℕ) :
    |squareBlockOutsidePrimeLeastEndpointT P R| ≤
      3 * (((2 * R + 1 : ℕ) : ℝ)) := by
  have hsum :=
    abs_selectedDegreeOneProjection_sum_le_three_mul_card P
      (squareBlockOutsidePrimeLeastEndpointCells P R)
  have hcardNat :=
    squareBlockOutsidePrimeLeastEndpointCells_card_le_linear P R
  have hcardReal :
      ((squareBlockOutsidePrimeLeastEndpointCells P R).card : ℝ) ≤
        ((2 * R + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  unfold squareBlockOutsidePrimeLeastEndpointT
  calc
    |∑ k ∈ squareBlockOutsidePrimeLeastEndpointCells P R,
        selectedDegreeOneProjection P k| ≤
      3 * ((squareBlockOutsidePrimeLeastEndpointCells P R).card : ℝ) := hsum
    _ ≤ 3 * (((2 * R + 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hcardReal (by norm_num)

end RHLean.Analysis
