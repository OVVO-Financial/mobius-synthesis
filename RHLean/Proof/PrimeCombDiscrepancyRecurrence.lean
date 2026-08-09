import Mathlib

/-!
# Prime-comb discrepancy recurrence

This module records the exact bookkeeping exposed by the progressive square-block
comb sweep.  When a new prime coordinate is added, the signed parity total can
change in only five ways:

* a previously untouched position receives its first prime hit and enters with
  sign `-1`;
* an existing positive squarefree state is hit and flips from `+1` to `-1`;
* an existing negative squarefree state is hit and flips from `-1` to `+1`;
* a positive state is killed by a repeated-prime collision;
* a negative state is killed by a repeated-prime collision.

The exact recurrence is purely finite.  The asymptotic PNT/RH burden is isolated
in quantitative estimates for the signed imbalance of these channels; no such
estimate is assumed to be automatic from cardinality alone.
-/

noncomputable section

namespace RHLean.Proof

structure PrimeCombUpdate where
  before : ℤ
  after : ℤ
  firstHits : ℕ
  positiveCollisions : ℕ
  negativeCollisions : ℕ
  positiveDeaths : ℕ
  negativeDeaths : ℕ
  updateLaw :
    after = before
      - (firstHits : ℤ)
      - 2 * (positiveCollisions : ℤ)
      + 2 * (negativeCollisions : ℤ)
      - (positiveDeaths : ℤ)
      + (negativeDeaths : ℤ)

def PrimeCombUpdate.collisionImbalance (u : PrimeCombUpdate) : ℤ :=
  (u.negativeCollisions : ℤ) - (u.positiveCollisions : ℤ)

def PrimeCombUpdate.deathImbalance (u : PrimeCombUpdate) : ℤ :=
  (u.negativeDeaths : ℤ) - (u.positiveDeaths : ℤ)

theorem PrimeCombUpdate.after_eq_compact (u : PrimeCombUpdate) :
    u.after = u.before - (u.firstHits : ℤ)
      + 2 * u.collisionImbalance + u.deathImbalance := by
  rw [u.updateLaw]
  unfold PrimeCombUpdate.collisionImbalance PrimeCombUpdate.deathImbalance
  ring

theorem PrimeCombUpdate.increment_eq (u : PrimeCombUpdate) :
    u.after - u.before =
      -(u.firstHits : ℤ) + 2 * u.collisionImbalance + u.deathImbalance := by
  rw [u.after_eq_compact]
  ring

theorem PrimeCombUpdate.abs_after_le (u : PrimeCombUpdate) :
    |u.after| ≤ |u.before| + (u.firstHits : ℤ)
      + 2 * |u.collisionImbalance| + |u.deathImbalance| := by
  rw [u.after_eq_compact]
  calc
    |u.before - (u.firstHits : ℤ) + 2 * u.collisionImbalance + u.deathImbalance|
        ≤ |u.before - (u.firstHits : ℤ) + 2 * u.collisionImbalance|
          + |u.deathImbalance| := abs_add_le _ _
    _ ≤ (|u.before - (u.firstHits : ℤ)| + |2 * u.collisionImbalance|)
          + |u.deathImbalance| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ ((|u.before| + |-(u.firstHits : ℤ)|)
          + |2 * u.collisionImbalance|) + |u.deathImbalance| := by
          gcongr
          simpa [sub_eq_add_neg] using abs_add_le u.before (-(u.firstHits : ℤ))
    _ = |u.before| + (u.firstHits : ℤ)
          + 2 * |u.collisionImbalance| + |u.deathImbalance| := by
          simp [abs_mul]

def PrimeCombUpdate.HasRestoringEstimate
    (u : PrimeCombUpdate) (alpha error : ℝ) : Prop :=
  |((u.after : ℝ))| ≤ (1 - alpha) * |((u.before : ℝ))| + error

theorem PrimeCombUpdate.abs_after_le_of_restoring
    (u : PrimeCombUpdate) {alpha error : ℝ}
    (h : u.HasRestoringEstimate alpha error) :
    |((u.after : ℝ))| ≤ (1 - alpha) * |((u.before : ℝ))| + error := h

def blockTenPrimeFiveUpdate : PrimeCombUpdate where
  before := -3
  after := 0
  firstHits := 1
  positiveCollisions := 0
  negativeCollisions := 2
  positiveDeaths := 0
  negativeDeaths := 0
  updateLaw := by norm_num

theorem blockTenPrimeFive_increment :
    blockTenPrimeFiveUpdate.after - blockTenPrimeFiveUpdate.before = 3 := by
  norm_num [blockTenPrimeFiveUpdate]

theorem blockTenPrimeFive_after : blockTenPrimeFiveUpdate.after = 0 := by
  norm_num [blockTenPrimeFiveUpdate]

end RHLean.Proof
