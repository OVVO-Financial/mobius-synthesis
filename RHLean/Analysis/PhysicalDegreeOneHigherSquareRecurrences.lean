import Mathlib
import RHLean.Analysis.PhysicalDegreeOneLeastSquareChannels

/-!
# Higher physical least-square channel recurrences

This module continues the exact least-square decomposition with the next two
channels.  A `5^2` channel edge is a `25`-hit with no `9`-hit; a `7^2` channel
edge is a `49`-hit with neither a `9`-hit nor a `25`-hit.  The resulting masks
have periods `225` and `11025` respectively.

The recurrences below are exact finite signed sums.  They deliberately preserve
all signs and introduce no channelwise absolute values or cancellation
hypotheses.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- The six edge residues modulo `25` on which one active site is divisible by
`5^2`. -/
def physicalTwentyFiveHitResidues : Finset ℕ :=
  {5, 6, 11, 12, 17, 18}

/-- The six edge residues modulo `49` on which one active site is divisible by
`7^2`. -/
def physicalFortyNineHitResidues : Finset ℕ :=
  {11, 12, 23, 24, 35, 36}

/-- The least-`5` channel mask over its full CRT period `lcm(9,25)=225`. -/
def physicalTwentyFiveChannelResidues : Finset ℕ :=
  (Finset.range 225).filter fun r =>
    r % 25 ∈ physicalTwentyFiveHitResidues ∧
      r % 9 ∉ physicalNineChannelResidues

/-- The least-`7` channel mask over its full CRT period
`lcm(9,25,49)=11025`. -/
def physicalFortyNineChannelResidues : Finset ℕ :=
  (Finset.range 11025).filter fun r =>
    r % 49 ∈ physicalFortyNineHitResidues ∧
      r % 25 ∉ physicalTwentyFiveHitResidues ∧
      r % 9 ∉ physicalNineChannelResidues

/-- The `5^2` least-square channel. -/
def physicalD25 (K : ℕ) : ℤ :=
  physicalLeastSquareChannel K 5

/-- The `7^2` least-square channel. -/
def physicalD49 (K : ℕ) : ℤ :=
  physicalLeastSquareChannel K 7

/-- A `5^2` hit occurs exactly on the six displayed residues modulo `25`. -/
theorem physicalSquarePrimeAtEdge_five_iff (k : ℕ) :
    physicalSquarePrimeAtEdge k 5 ↔
      k % 25 ∈ physicalTwentyFiveHitResidues := by
  constructor
  · rintro ⟨_, a, ha, hdiv⟩
    norm_num at hdiv
    simp [physicalTransitionActiveOffsets] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rw [Nat.dvd_iff_mod_eq_zero] at hdiv
      simp [Nat.add_mod, Nat.mul_mod] at hdiv
      simp [physicalTwentyFiveHitResidues]
      omega
  · intro hk
    simp [physicalTwentyFiveHitResidues] at hk
    rcases hk with h5 | h6 | h11 | h12 | h17 | h18
    · refine ⟨by norm_num, 5, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h5]
    · refine ⟨by norm_num, 1, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h6]
    · refine ⟨by norm_num, 6, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h11]
    · refine ⟨by norm_num, 2, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h12]
    · refine ⟨by norm_num, 7, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h17]
    · refine ⟨by norm_num, 3, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h18]

/-- A `7^2` hit occurs exactly on the six displayed residues modulo `49`. -/
theorem physicalSquarePrimeAtEdge_seven_iff (k : ℕ) :
    physicalSquarePrimeAtEdge k 7 ↔
      k % 49 ∈ physicalFortyNineHitResidues := by
  constructor
  · rintro ⟨_, a, ha, hdiv⟩
    norm_num at hdiv
    simp [physicalTransitionActiveOffsets] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rw [Nat.dvd_iff_mod_eq_zero] at hdiv
      simp [Nat.add_mod, Nat.mul_mod] at hdiv
      simp [physicalFortyNineHitResidues]
      omega
  · intro hk
    simp [physicalFortyNineHitResidues] at hk
    rcases hk with h11 | h12 | h23 | h24 | h35 | h36
    · refine ⟨by norm_num, 5, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h11]
    · refine ⟨by norm_num, 1, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h12]
    · refine ⟨by norm_num, 6, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h23]
    · refine ⟨by norm_num, 2, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h24]
    · refine ⟨by norm_num, 7, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h35]
    · refine ⟨by norm_num, 3, by simp [physicalTransitionActiveOffsets], ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.mul_mod, h36]

/-- The least square-prime channel is `5` exactly when a `25`-hit occurs and
the lower `9`-channel does not. -/
theorem physicalLeastOddSquarePrime_eq_five_iff (k : ℕ) :
    physicalLeastOddSquarePrime k = some 5 ↔
      physicalSquarePrimeAtEdge k 5 ∧
        ¬ physicalSquarePrimeAtEdge k 3 := by
  constructor
  · intro h5
    have hspec := physicalLeastOddSquarePrime_some_spec h5
    refine ⟨hspec, ?_⟩
    intro h3
    have hle := physicalLeastOddSquarePrime_le h5 h3
    omega
  · rintro ⟨h5, h3⟩
    classical
    have hex : ∃ p, physicalSquarePrimeAtEdge k p := ⟨5, h5⟩
    have hspec := Nat.find_spec hex
    have hle : Nat.find hex ≤ 5 := Nat.find_min' hex h5
    have htwo : 2 ≤ Nat.find hex := hspec.1.two_le
    have hodd : Nat.find hex % 2 = 1 := physicalSquarePrimeAtEdge_odd hspec
    have hne3 : Nat.find hex ≠ 3 := by
      intro heq
      apply h3
      rw [← heq]
      exact hspec
    have heq : Nat.find hex = 5 := by omega
    simp [physicalLeastOddSquarePrime, hex, heq]

/-- The least square-prime channel is `7` exactly when a `49`-hit occurs and
neither lower channel occurs. -/
theorem physicalLeastOddSquarePrime_eq_seven_iff (k : ℕ) :
    physicalLeastOddSquarePrime k = some 7 ↔
      physicalSquarePrimeAtEdge k 7 ∧
        ¬ physicalSquarePrimeAtEdge k 5 ∧
        ¬ physicalSquarePrimeAtEdge k 3 := by
  constructor
  · intro h7
    have hspec := physicalLeastOddSquarePrime_some_spec h7
    refine ⟨hspec, ?_, ?_⟩
    · intro h5
      have hle := physicalLeastOddSquarePrime_le h7 h5
      omega
    · intro h3
      have hle := physicalLeastOddSquarePrime_le h7 h3
      omega
  · rintro ⟨h7, h5, h3⟩
    classical
    have hex : ∃ p, physicalSquarePrimeAtEdge k p := ⟨7, h7⟩
    have hspec := Nat.find_spec hex
    have hle : Nat.find hex ≤ 7 := Nat.find_min' hex h7
    have htwo : 2 ≤ Nat.find hex := hspec.1.two_le
    have hodd : Nat.find hex % 2 = 1 := physicalSquarePrimeAtEdge_odd hspec
    have hne5 : Nat.find hex ≠ 5 := by
      intro heq
      apply h5
      rw [← heq]
      exact hspec
    have hne3 : Nat.find hex ≠ 3 := by
      intro heq
      apply h3
      rw [← heq]
      exact hspec
    have heq : Nat.find hex = 7 := by omega
    simp [physicalLeastOddSquarePrime, hex, heq]

/-- CRT form of the least-`5` mask, with period `225`. -/
theorem physicalLeastOddSquarePrime_eq_five_iff_mod (k : ℕ) :
    physicalLeastOddSquarePrime k = some 5 ↔
      k % 225 ∈ physicalTwentyFiveChannelResidues := by
  rw [physicalLeastOddSquarePrime_eq_five_iff,
    physicalSquarePrimeAtEdge_five_iff,
    physicalSquarePrimeAtEdge_three_iff]
  have h25 : k % 225 % 25 = k % 25 :=
    Nat.mod_mod_of_dvd k (by norm_num)
  have h9 : k % 225 % 9 = k % 9 :=
    Nat.mod_mod_of_dvd k (by norm_num)
  constructor
  · rintro ⟨h5, h3⟩
    rw [physicalTwentyFiveChannelResidues, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)), ?_⟩
    simpa [h25, h9] using (show
      k % 25 ∈ physicalTwentyFiveHitResidues ∧
        k % 9 ∉ physicalNineChannelResidues from ⟨h5, h3⟩)
  · intro h
    rw [physicalTwentyFiveChannelResidues, Finset.mem_filter] at h
    rcases h with ⟨_, h5, h3⟩
    constructor
    · simpa [h25] using h5
    · simpa [h9] using h3

/-- CRT form of the least-`7` mask, with period `11025`. -/
theorem physicalLeastOddSquarePrime_eq_seven_iff_mod (k : ℕ) :
    physicalLeastOddSquarePrime k = some 7 ↔
      k % 11025 ∈ physicalFortyNineChannelResidues := by
  rw [physicalLeastOddSquarePrime_eq_seven_iff,
    physicalSquarePrimeAtEdge_seven_iff,
    physicalSquarePrimeAtEdge_five_iff,
    physicalSquarePrimeAtEdge_three_iff]
  have h49 : k % 11025 % 49 = k % 49 :=
    Nat.mod_mod_of_dvd k (by norm_num)
  have h25 : k % 11025 % 25 = k % 25 :=
    Nat.mod_mod_of_dvd k (by norm_num)
  have h9 : k % 11025 % 9 = k % 9 :=
    Nat.mod_mod_of_dvd k (by norm_num)
  constructor
  · rintro ⟨h7, h5, h3⟩
    rw [physicalFortyNineChannelResidues, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)), ?_⟩
    simpa [h49, h25, h9] using (show
      k % 49 ∈ physicalFortyNineHitResidues ∧
        k % 25 ∉ physicalTwentyFiveHitResidues ∧
        k % 9 ∉ physicalNineChannelResidues from ⟨h7, h5, h3⟩)
  · intro h
    rw [physicalFortyNineChannelResidues, Finset.mem_filter] at h
    rcases h with ⟨_, h7, h5, h3⟩
    constructor
    · simpa [h49] using h7
    · constructor
      · simpa [h25] using h5
      · simpa [h9] using h3

/-- Exact residue-mask form of the `5^2` least channel. -/
theorem physicalD25_eq_residueSum (K : ℕ) :
    physicalD25 K =
      ∑ k ∈ Finset.range K with
        k % 225 ∈ physicalTwentyFiveChannelResidues,
        physicalDefectEdgeValue k := by
  unfold physicalD25 physicalLeastSquareChannel
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [physicalLeastOddSquarePrime_eq_five_iff_mod]
  · intro k hk
    rfl

/-- Exact residue-mask form of the `7^2` least channel. -/
theorem physicalD49_eq_residueSum (K : ℕ) :
    physicalD49 K =
      ∑ k ∈ Finset.range K with
        k % 11025 ∈ physicalFortyNineChannelResidues,
        physicalDefectEdgeValue k := by
  unfold physicalD49 physicalLeastSquareChannel
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [physicalLeastOddSquarePrime_eq_seven_iff_mod]
  · intro k hk
    rfl

/-- There are exactly `18` least-`5` edge residues in one period. -/
theorem physicalTwentyFiveChannelResidues_card :
    physicalTwentyFiveChannelResidues.card = 18 := by
  native_decide

/-- There are exactly `342` least-`7` edge residues in one period. -/
theorem physicalFortyNineChannelResidues_card :
    physicalFortyNineChannelResidues.card = 342 := by
  native_decide

/-- **Exact `5^2` recurrence.**  One full `225`-edge CRT period is the signed
sum over the fixed least-`5` mask. -/
theorem physicalD25_225_step_recurrence (L : ℕ) :
    physicalD25 (225 * (L + 1)) - physicalD25 (225 * L) =
      ∑ r ∈ physicalTwentyFiveChannelResidues,
        physicalDefectEdgeValue (225 * L + r) := by
  let f : ℕ → ℤ := fun k =>
    if k % 225 ∈ physicalTwentyFiveChannelResidues then
      physicalDefectEdgeValue k
    else 0
  have hD25 : ∀ N : ℕ, physicalD25 N = ∑ k ∈ Finset.range N, f k := by
    intro N
    rw [physicalD25_eq_residueSum]
    simp [f, Finset.sum_filter]
  rw [hD25, hD25]
  calc
    (∑ k ∈ Finset.range (225 * (L + 1)), f k) -
          ∑ k ∈ Finset.range (225 * L), f k =
        ∑ r ∈ Finset.range 225, f (225 * L + r) := by
          rw [show 225 * (L + 1) = 225 * L + 225 by omega]
          exact Finset.sum_range_add_sub_sum_range f (225 * L) 225
    _ = ∑ r ∈ physicalTwentyFiveChannelResidues,
          physicalDefectEdgeValue (225 * L + r) := by
      rw [physicalTwentyFiveChannelResidues, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r hr
      have hrlt : r < 225 := Finset.mem_range.mp hr
      have hmod : (225 * L + r) % 225 = r := by omega
      have h25 : (225 * L + r) % 25 = r % 25 := by omega
      have h9 : (225 * L + r) % 9 = r % 9 := by omega
      simp [f, hmod, physicalTwentyFiveChannelResidues, hrlt, h25, h9]

/-- Four-cell form of the exact `5^2` recurrence.  Expanding `fourSlotCellSum`
gives a fixed signed Möbius mask inside each interval of length `900`. -/
theorem physicalD25_225_step_fourSlot_recurrence (L : ℕ) :
    physicalD25 (225 * (L + 1)) - physicalD25 (225 * L) =
      ∑ r ∈ physicalTwentyFiveChannelResidues,
        fourSlotCellSum (225 * L + r + 1) := by
  rw [physicalD25_225_step_recurrence]
  apply Finset.sum_congr rfl
  intro r hr
  simpa using physicalDefectEdgeValue_eq_fourSlotCellSum (225 * L + r)

/-- **Exact `7^2` recurrence.**  One full `11025`-edge CRT period is the signed
sum over the fixed least-`7` mask. -/
theorem physicalD49_11025_step_recurrence (L : ℕ) :
    physicalD49 (11025 * (L + 1)) - physicalD49 (11025 * L) =
      ∑ r ∈ physicalFortyNineChannelResidues,
        physicalDefectEdgeValue (11025 * L + r) := by
  let f : ℕ → ℤ := fun k =>
    if k % 11025 ∈ physicalFortyNineChannelResidues then
      physicalDefectEdgeValue k
    else 0
  have hD49 : ∀ N : ℕ, physicalD49 N = ∑ k ∈ Finset.range N, f k := by
    intro N
    rw [physicalD49_eq_residueSum]
    simp [f, Finset.sum_filter]
  rw [hD49, hD49]
  calc
    (∑ k ∈ Finset.range (11025 * (L + 1)), f k) -
          ∑ k ∈ Finset.range (11025 * L), f k =
        ∑ r ∈ Finset.range 11025, f (11025 * L + r) := by
          rw [show 11025 * (L + 1) = 11025 * L + 11025 by omega]
          exact Finset.sum_range_add_sub_sum_range f (11025 * L) 11025
    _ = ∑ r ∈ physicalFortyNineChannelResidues,
          physicalDefectEdgeValue (11025 * L + r) := by
      rw [physicalFortyNineChannelResidues, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r hr
      have hrlt : r < 11025 := Finset.mem_range.mp hr
      have hmod : (11025 * L + r) % 11025 = r := by omega
      have h49 : (11025 * L + r) % 49 = r % 49 := by omega
      have h25 : (11025 * L + r) % 25 = r % 25 := by omega
      have h9 : (11025 * L + r) % 9 = r % 9 := by omega
      simp [f, hmod, physicalFortyNineChannelResidues, hrlt, h49, h25, h9]

/-- Four-cell form of the exact `7^2` recurrence.  Expanding `fourSlotCellSum`
gives a fixed signed Möbius mask inside each interval of length `44100`. -/
theorem physicalD49_11025_step_fourSlot_recurrence (L : ℕ) :
    physicalD49 (11025 * (L + 1)) - physicalD49 (11025 * L) =
      ∑ r ∈ physicalFortyNineChannelResidues,
        fourSlotCellSum (11025 * L + r + 1) := by
  rw [physicalD49_11025_step_recurrence]
  apply Finset.sum_congr rfl
  intro r hr
  simpa using physicalDefectEdgeValue_eq_fourSlotCellSum (11025 * L + r)

end RHLean.Analysis
