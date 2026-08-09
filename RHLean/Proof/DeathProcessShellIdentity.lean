import Mathlib
import RHLean.Proof.DeathProcessArithmetic

/-!
# Exact death-process shell identity

For a nonnegative cutoff parameter, the lifetime-active birth-high mass is the
same as the cumulative moving-high mass, and the only moving-high entries at the
next stage are the high atoms in the new square block.  Combining those two
identities with the exact birth and moving recurrences proves that the discrete
death increment is exactly the Möbius mass of the crossed height shell.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- A source high at a later stage was high at every earlier stage when the
cutoff parameter is nonnegative. -/
theorem movingHigh_anti_stage
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {j t m : ℕ} (hjt : j ≤ t)
    (hm : IsMovingCanonicalHigh Λ t m) :
    IsMovingCanonicalHigh Λ j m := by
  unfold IsMovingCanonicalHigh at hm ⊢
  have hjtR : (j : ℝ) ≤ (t : ℝ) := by exact_mod_cast hjt
  have hcoeff : 0 ≤ 2 * Λ := by positivity
  have hthreshold : 2 * Λ * (j : ℝ) ≤ 2 * Λ * (t : ℝ) :=
    mul_le_mul_of_nonneg_left hjtR hcoeff
  exact lt_of_le_of_lt hthreshold hm

/-- Moving-high membership at stage `t` implies birth-high membership for an
atom born in block `j ≤ t`. -/
theorem movingHigh_implies_birthHigh
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {j t m : ℕ} (hjt : j ≤ t)
    (hm : IsMovingCanonicalHigh Λ t m) :
    IsCanonicalHighHeight Λ j m := by
  unfold IsCanonicalHighHeight IsCanonicalLowHeight
  intro hlow
  have hhigh := movingHigh_anti_stage hΛ hjt hm
  unfold IsMovingCanonicalHigh at hhigh
  exact (not_lt_of_ge hlow) hhigh

/-- A generic iterated sum over canonical square blocks equals the sum over the
whole square prefix. -/
theorem sum_squareBlocks_eq_sum_range_squarePrefix
    (f : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), ∑ m ∈ canonicalSquareBlock j, f m) =
      ∑ m ∈ Finset.range ((n + 1) ^ 2), f m := by
  induction n with
  | zero => simp [canonicalSquareBlock]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      have hle : (n + 1) ^ 2 ≤ (n + 2) ^ 2 := by
        exact Nat.pow_le_pow_left (by omega) 2
      simpa [canonicalSquareBlock, Nat.add_assoc] using
        (Finset.sum_range_add_sum_Ico f hle)

/-- For a nonnegative cutoff parameter, the birth-high atoms still alive at
stage `t` are exactly the cumulative moving-high population at that stage. -/
theorem lifetimeActiveAtomMass_eq_movingCanonicalHighSum
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (t : ℕ) :
    lifetimeActiveAtomMass Λ t = movingCanonicalHighSum Λ t := by
  classical
  rw [lifetimeActiveAtomMass_eq_stillHighMass]
  unfold birthCanonicalStillHighAtomMass canonicalAtomMass
    birthCanonicalStillHighAtomSet birthCanonicalHighAtomSet
    movingCanonicalHighSum canonicalMoebiusMass movingCanonicalHighSet
    cumulativeSquarePrefixSet
  rw [Finset.sum_filter, Finset.sum_sigma]
  simp only [Finset.sum_filter]
  rw [← sum_squareBlocks_eq_sum_range_squarePrefix
    (fun m => if IsMovingCanonicalHigh Λ t m then canonicalMoebiusWeight m else 0) t]
  apply Finset.sum_congr rfl
  intro j hj
  have hjt : j ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hmove : IsMovingCanonicalHigh Λ t m
  · have hbirth : IsCanonicalHighHeight Λ j m :=
      movingHigh_implies_birthHigh hΛ hjt hmove
    simp [hmove, hbirth]
  · simp [hmove]

/-- The high part of the square block born at stage `t+1`. -/
noncomputable def newCanonicalHighBlock (Λ : ℝ) (t : ℕ) : Finset ℕ := by
  classical
  exact (canonicalSquareBlock (t + 1)).filter
    (IsCanonicalHighHeight Λ (t + 1))

/-- The moving-high entry population is exactly the high part of the newly born
square block. -/
theorem movingCanonicalEntrySet_eq_newHighBlock
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (t : ℕ) :
    movingCanonicalEntrySet Λ t = newCanonicalHighBlock Λ t := by
  classical
  ext m
  constructor
  · intro hm
    rcases (mem_movingCanonicalEntrySet_iff Λ t m).1 hm with ⟨hmNew, hmNotOld⟩
    rcases Finset.mem_filter.mp hmNew with ⟨hmNewRange, hmNewHigh⟩
    have hmLt : m < (t + 2) ^ 2 := Finset.mem_range.mp hmNewRange
    have hmGe : (t + 1) ^ 2 ≤ m := by
      by_contra hnot
      have hmOldRange : m ∈ cumulativeSquarePrefixSet t := by
        apply Finset.mem_range.mpr
        omega
      have hmOldHigh : IsMovingCanonicalHigh Λ t m :=
        movingHigh_anti_stage hΛ (Nat.le_succ t) hmNewHigh
      exact hmNotOld (Finset.mem_filter.mpr ⟨hmOldRange, hmOldHigh⟩)
    unfold newCanonicalHighBlock
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨hmGe, hmLt⟩, ?_⟩
    unfold IsCanonicalHighHeight IsCanonicalLowHeight
    intro hlow
    exact (not_lt_of_ge hlow) hmNewHigh
  · intro hm
    unfold newCanonicalHighBlock at hm
    rcases Finset.mem_filter.mp hm with ⟨hmBlock, hmBirthHigh⟩
    rcases Finset.mem_Ico.mp hmBlock with ⟨hmGe, hmLt⟩
    apply (mem_movingCanonicalEntrySet_iff Λ t m).2
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hmLt, ?_⟩
      unfold IsMovingCanonicalHigh
      unfold IsCanonicalHighHeight IsCanonicalLowHeight at hmBirthHigh
      exact lt_of_not_ge hmBirthHigh
    · intro hmOld
      have hmOldLt : m < (t + 1) ^ 2 :=
        Finset.mem_range.mp (Finset.mem_filter.mp hmOld).1
      omega

/-- Consequently, the moving entry mass is the canonical high increment of the
new square block. -/
theorem movingCanonicalEntryMass_eq_canonicalHighIncrement
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (t : ℕ) :
    movingCanonicalEntryMass Λ t = canonicalHighIncrement Λ (t + 1) := by
  classical
  unfold movingCanonicalEntryMass canonicalMoebiusMass canonicalHighIncrement
  rw [movingCanonicalEntrySet_eq_newHighBlock hΛ]
  unfold newCanonicalHighBlock
  rw [Finset.sum_filter]

/-- Exact set-level bridge: for nonnegative `Λ`, the discrete increment of the
absorbed birth-high mass is the Möbius mass of the crossed moving-height shell. -/
theorem lifetimeDeathIncrement_eq_deathHeightShellMass
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (t : ℕ) :
    lifetimeDeathIncrement Λ t = deathHeightShellMass Λ t := by
  rw [deathHeightShellMass_eq_crossingMass]
  unfold lifetimeDeathIncrement
  have hdeath_t :
      lifetimeDeathMass Λ t =
        lifetimeBirthMass Λ t - lifetimeActiveAtomMass Λ t := by
    rw [lifetimeBirthMass_eq_active_add_death]
    ring
  have hdeath_succ :
      lifetimeDeathMass Λ (t + 1) =
        lifetimeBirthMass Λ (t + 1) - lifetimeActiveAtomMass Λ (t + 1) := by
    rw [lifetimeBirthMass_eq_active_add_death]
    ring
  have hbirthIncrement :
      lifetimeBirthMass Λ (t + 1) =
        lifetimeBirthMass Λ t + canonicalHighIncrement Λ (t + 1) := by
    rw [lifetimeBirthMass_eq_canonicalHighPrefix,
      lifetimeBirthMass_eq_canonicalHighPrefix]
    unfold canonicalHighPrefix
    rw [Finset.sum_range_succ]
  rw [hdeath_succ, hdeath_t, hbirthIncrement,
    lifetimeActiveAtomMass_eq_movingCanonicalHighSum hΛ (t + 1),
    lifetimeActiveAtomMass_eq_movingCanonicalHighSum hΛ t,
    movingCanonicalHighSum_succ,
    movingCanonicalEntryMass_eq_canonicalHighIncrement hΛ]
  ring

end RHLean.Proof
