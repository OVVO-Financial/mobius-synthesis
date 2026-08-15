import Mathlib
import RHLean.Analysis.PrimeSievePNTResidualEnvelope

/-!
# One-step structure of the deep packet residual envelope

The preceding residual-envelope layer localizes every recursive packet residual
into an arbitrarily small relative regime. Its deep state is nevertheless a tail
maximum: advancing the cutoff by one level deletes only the current level, while
a larger residual at a deeper level survives unchanged.

This module makes that point exact. It defines the maximum residual at one
specified tree level and proves the decomposition

`deep(J) = max(level(J), deep(J+1))`.

Consequently the deep envelope is monotone in the cutoff, but any strict cubic
step with a positive state forces the current level itself to attain the entire
tail maximum. Thus the existing cubic contraction statement contains a
genuinely new arithmetic requirement: qualitative PNT smallness plus the
recursive max identity do not by themselves rule out positive plateaus.
-/

noncomputable section

namespace RHLean.Analysis

/-- Maximum dimensionless packet residual at exactly one recursive tree level.
`level = 0` is the root packet.  When the requested level lies beyond the
available tree depth the value is zero. -/
def primeSieveDyadicPacketIntervalLevelRelativeEnvelope
    (y x : ℕ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | _, 0, _, _ => 0
  | 0, _depth + 1, a, b =>
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        primeSieveDyadicPacketRelativeResidual y x a m b
      else 0
  | level + 1, depth + 1, a, b =>
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        max
          (primeSieveDyadicPacketIntervalLevelRelativeEnvelope
            y x level depth a m)
          (primeSieveDyadicPacketIntervalLevelRelativeEnvelope
            y x level depth m b)
      else 0

@[simp] theorem primeSieveDyadicPacketIntervalLevelRelativeEnvelope_depth_zero
    (y x level a b : ℕ) :
    primeSieveDyadicPacketIntervalLevelRelativeEnvelope y x level 0 a b = 0 := by
  cases level <;> rfl

/-- Exact root-level formula. -/
theorem primeSieveDyadicPacketIntervalLevelRelativeEnvelope_zero_succ
    (y x depth a b : ℕ) :
    primeSieveDyadicPacketIntervalLevelRelativeEnvelope
        y x 0 (depth + 1) a b =
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        primeSieveDyadicPacketRelativeResidual y x a m b
      else 0 := by
  rfl

/-- Exact recursion for a positive requested level. -/
theorem primeSieveDyadicPacketIntervalLevelRelativeEnvelope_succ_succ
    (y x level depth a b : ℕ) :
    primeSieveDyadicPacketIntervalLevelRelativeEnvelope
        y x (level + 1) (depth + 1) a b =
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        max
          (primeSieveDyadicPacketIntervalLevelRelativeEnvelope
            y x level depth a m)
          (primeSieveDyadicPacketIntervalLevelRelativeEnvelope
            y x level depth m b)
      else 0 := by
  rfl

/-- Every dimensionless packet residual is nonnegative. -/
theorem primeSieveDyadicPacketRelativeResidual_nonneg
    (y x a m b : ℕ) :
    0 ≤ primeSieveDyadicPacketRelativeResidual y x a m b := by
  unfold primeSieveDyadicPacketRelativeResidual
  exact div_nonneg (norm_nonneg _) (by positivity)

/-- Exact-level maxima are nonnegative. -/
theorem primeSieveDyadicPacketIntervalLevelRelativeEnvelope_nonneg
    (y x level depth a b : ℕ) :
    0 ≤ primeSieveDyadicPacketIntervalLevelRelativeEnvelope
      y x level depth a b := by
  induction level generalizing depth a b with
  | zero =>
      cases depth with
      | zero => simp
      | succ depth =>
          rw [primeSieveDyadicPacketIntervalLevelRelativeEnvelope_zero_succ]
          by_cases hsplit : a + 1 < b
          · simp only [hsplit, if_true]
            exact primeSieveDyadicPacketRelativeResidual_nonneg _ _ _ _ _
          · simp [hsplit]
  | succ level ih =>
      cases depth with
      | zero => simp
      | succ depth =>
          rw [primeSieveDyadicPacketIntervalLevelRelativeEnvelope_succ_succ]
          by_cases hsplit : a + 1 < b
          · simp only [hsplit, if_true]
            let m := dyadicPacketMidpoint a b
            exact (ih depth a m).trans (le_max_left _ _)
          · simp [hsplit]

/-- **Exact tail decomposition.**  The deep envelope at cutoff `J` is the
maximum of the residuals on level `J` and the tail that remains after deleting
that level. -/
theorem primeSieveDyadicPacketIntervalDeepRelativeEnvelope_eq_max_level_succ
    (y x cutoff depth a b : ℕ) :
    primeSieveDyadicPacketIntervalDeepRelativeEnvelope
        y x cutoff depth a b =
      max
        (primeSieveDyadicPacketIntervalLevelRelativeEnvelope
          y x cutoff depth a b)
        (primeSieveDyadicPacketIntervalDeepRelativeEnvelope
          y x (cutoff + 1) depth a b) := by
  induction cutoff generalizing depth a b with
  | zero =>
      cases depth with
      | zero => simp
      | succ depth =>
          by_cases hsplit : a + 1 < b
          · rw [primeSieveDyadicPacketIntervalDeepRelativeEnvelope_cutoff_zero,
              primeSieveDyadicPacketIntervalRelativeEnvelope_succ,
              primeSieveDyadicPacketIntervalLevelRelativeEnvelope_zero_succ,
              primeSieveDyadicPacketIntervalDeepRelativeEnvelope_succ]
            simp only [hsplit, if_true]
            simp [primeSieveDyadicPacketIntervalDeepRelativeEnvelope_cutoff_zero]
          · simp [primeSieveDyadicPacketIntervalDeepRelativeEnvelope_cutoff_zero,
              primeSieveDyadicPacketIntervalRelativeEnvelope_succ,
              primeSieveDyadicPacketIntervalLevelRelativeEnvelope_zero_succ,
              primeSieveDyadicPacketIntervalDeepRelativeEnvelope_succ,
              hsplit]
  | succ cutoff ih =>
      cases depth with
      | zero => simp
      | succ depth =>
          by_cases hsplit : a + 1 < b
          · rw [primeSieveDyadicPacketIntervalDeepRelativeEnvelope_succ,
              primeSieveDyadicPacketIntervalLevelRelativeEnvelope_succ_succ,
              primeSieveDyadicPacketIntervalDeepRelativeEnvelope_succ]
            simp only [hsplit, if_true]
            let m := dyadicPacketMidpoint a b
            rw [ih depth a m, ih depth m b]
            simp only [m, max_assoc, max_left_comm, max_comm]
          · simp [primeSieveDyadicPacketIntervalDeepRelativeEnvelope_succ,
              primeSieveDyadicPacketIntervalLevelRelativeEnvelope_succ_succ,
              hsplit]

/-- Exact-level envelope on one dyadic block. The `min J j` convention matches
the existing shallow/deep block wrapper. -/
def primeSieveDyadicPacketBlockLevelRelativeEnvelope
    (y x j J : ℕ) : ℝ :=
  primeSieveDyadicPacketIntervalLevelRelativeEnvelope y x (min J j) j
    (primeSieveDyadicBlockLeft j)
    (primeSieveDyadicBlockRight y x j + 1)

/-- On a live cutoff `J < j`, the block tail is exactly the maximum of the
current level and the next tail. -/
theorem primeSieveDyadicPacketBlockDeepRelativeEnvelope_eq_max_level_succ
    {y x j J : ℕ} (hJ : J < j) :
    primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J =
      max
        (primeSieveDyadicPacketBlockLevelRelativeEnvelope y x j J)
        (primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j (J + 1)) := by
  unfold primeSieveDyadicPacketBlockDeepRelativeEnvelope
    primeSieveDyadicPacketBlockLevelRelativeEnvelope
  have hmin : min J j = J := min_eq_left hJ.le
  have hminSucc : min (J + 1) j = J + 1 := min_eq_left (by omega)
  rw [hmin, hminSucc]
  exact primeSieveDyadicPacketIntervalDeepRelativeEnvelope_eq_max_level_succ
    y x J j (primeSieveDyadicBlockLeft j)
      (primeSieveDyadicBlockRight y x j + 1)

/-- Deleting one live level can only decrease the deep max-envelope. -/
theorem primeSieveDyadicPacketBlockDeepRelativeEnvelope_succ_le
    {y x j J : ℕ} (hJ : J < j) :
    primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j (J + 1) ≤
      primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J := by
  rw [primeSieveDyadicPacketBlockDeepRelativeEnvelope_eq_max_level_succ hJ]
  exact le_max_right _ _

/-- A positive cubic decrement necessarily gives a strict one-step decrease. -/
theorem primeSieveDyadicPacketBlockDeepRelativeEnvelope_strict_of_cubic_step
    {c : ℝ} {y x j J : ℕ}
    (hc : 0 < c)
    (hpos : 0 < primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J)
    (hstep :
      primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j (J + 1) ≤
        primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J -
          c * (primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J) ^ 3) :
    primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j (J + 1) <
      primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J := by
  have hdrop :
      0 < c * (primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J) ^ 3 :=
    mul_pos hc (pow_pos hpos 3)
  linarith

/-- If a live tail decreases strictly, its old maximum must have been attained
on the level that was just removed. -/
theorem primeSieveDyadicPacketBlockLevelRelativeEnvelope_eq_deep_of_strict
    {y x j J : ℕ} (hJ : J < j)
    (hstrict :
      primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j (J + 1) <
        primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J) :
    primeSieveDyadicPacketBlockLevelRelativeEnvelope y x j J =
      primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J := by
  have hdecomp :=
    primeSieveDyadicPacketBlockDeepRelativeEnvelope_eq_max_level_succ
      (y := y) (x := x) hJ
  have htailLe :
      primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j (J + 1) ≤
        primeSieveDyadicPacketBlockLevelRelativeEnvelope y x j J := by
    rcases le_total
        (primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j (J + 1))
        (primeSieveDyadicPacketBlockLevelRelativeEnvelope y x j J) with h | h
    · exact h
    · have heq :
          primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J =
            primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j (J + 1) := by
        rw [hdecomp, max_eq_right h]
      linarith
  calc
    primeSieveDyadicPacketBlockLevelRelativeEnvelope y x j J =
        max
          (primeSieveDyadicPacketBlockLevelRelativeEnvelope y x j J)
          (primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j (J + 1)) :=
      (max_eq_left htailLe).symm
    _ = primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J := hdecomp.symm

/-- Necessary qualitative consequence of the cubic statement: eventually every
positive live tail maximum is attained on the current frontier level, and hence
there are no positive cutoff plateaus. -/
def DyadicPacketDeepEnvelopeFrontierAttainmentStatement : Prop :=
  ∃ Y : ℕ, ∀ (y x j J : ℕ),
    Y ≤ y → J < j →
      0 < primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J →
        primeSieveDyadicPacketBlockLevelRelativeEnvelope y x j J =
            primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J ∧
          primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j (J + 1) <
            primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J

/-- The cubic contraction can hold only if the new frontier-attainment
property holds. This property is not supplied by the PNT smallness theorem. -/
theorem dyadicPacketDeepEnvelopeFrontierAttainment_of_cubicContraction
    (hCubic : DyadicPacketDeepEnvelopeCubicContractionStatement) :
    DyadicPacketDeepEnvelopeFrontierAttainmentStatement := by
  unfold DyadicPacketDeepEnvelopeCubicContractionStatement at hCubic
  rcases hCubic with ⟨c, hc, Y, hstep⟩
  unfold DyadicPacketDeepEnvelopeFrontierAttainmentStatement
  refine ⟨Y, ?_⟩
  intro y x j J hy hJ hpos
  have hs := hstep y x j J hy hJ
  have hstrict :=
    primeSieveDyadicPacketBlockDeepRelativeEnvelope_strict_of_cubic_step
      hc hpos hs
  exact ⟨
    primeSieveDyadicPacketBlockLevelRelativeEnvelope_eq_deep_of_strict
      hJ hstrict,
    hstrict⟩

/-! ## The cumulative energy state has an exact one-step decrement -/

/-- Packet energy added exactly at cutoff level `J`, summed over all occupied
dyadic blocks. Equivalently, this is the amount removed from the deep energy
when the cutoff advances from `J` to `J+1`. -/
def primeSieveDyadicPacketLevelEnergy (y x J : ℕ) : ℝ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    (primeSieveDyadicPacketTreeBlockEnergy y x j (min (J + 1) j) -
      primeSieveDyadicPacketTreeBlockEnergy y x j (min J j))

/-- One packet level carries nonnegative energy. -/
theorem primeSieveDyadicPacketLevelEnergy_nonneg
    (y x J : ℕ) :
    0 ≤ primeSieveDyadicPacketLevelEnergy y x J := by
  unfold primeSieveDyadicPacketLevelEnergy
  apply Finset.sum_nonneg
  intro j _hj
  apply sub_nonneg.mpr
  unfold primeSieveDyadicPacketTreeBlockEnergy
  exact primeSieveDyadicPacketIntervalTreeEnergy_mono y x (by omega)

/-- **Exact energy decrement.**  Unlike the max envelope, the cumulative deep
energy cannot hide a deeper maximizer: deleting level `J` subtracts precisely
that level's packet energy. -/
theorem primeSieveDyadicPacketDeepEnergy_eq_level_add_succ
    (y x J : ℕ) :
    primeSieveDyadicPacketDeepEnergy y x J =
      primeSieveDyadicPacketLevelEnergy y x J +
        primeSieveDyadicPacketDeepEnergy y x (J + 1) := by
  unfold primeSieveDyadicPacketDeepEnergy primeSieveDyadicPacketLevelEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Hence cumulative deep packet energy is monotone in the cutoff. -/
theorem primeSieveDyadicPacketDeepEnergy_succ_le
    (y x J : ℕ) :
    primeSieveDyadicPacketDeepEnergy y x (J + 1) ≤
      primeSieveDyadicPacketDeepEnergy y x J := by
  have hlevel := primeSieveDyadicPacketLevelEnergy_nonneg y x J
  have hdecomp := primeSieveDyadicPacketDeepEnergy_eq_level_add_succ y x J
  linarith

/-- A cubic lower bound for the deleted level is exactly the missing input for a
cubic one-step inequality on the cumulative energy state.  This theorem is
purely deterministic and does not assert such a lower bound. -/
theorem primeSieveDyadicPacketDeepEnergy_cubic_step_of_level_lower_bound
    {c : ℝ} {y x J : ℕ}
    (hlevel :
      c * (primeSieveDyadicPacketDeepEnergy y x J) ^ 3 ≤
        primeSieveDyadicPacketLevelEnergy y x J) :
    primeSieveDyadicPacketDeepEnergy y x (J + 1) ≤
      primeSieveDyadicPacketDeepEnergy y x J -
        c * (primeSieveDyadicPacketDeepEnergy y x J) ^ 3 := by
  have hdecomp := primeSieveDyadicPacketDeepEnergy_eq_level_add_succ y x J
  linarith

/-- Arbitrarily small max-tail states may still have a positive plateau.  This
simple scalar model isolates why qualitative smallness plus a max recursion is
insufficient to force a cubic decrement. -/
theorem small_max_tail_plateau_obstructs_cubic
    {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    max (δ / 2) δ ≤ δ ∧
      ¬ δ ≤ max (δ / 2) δ - c * (max (δ / 2) δ) ^ 3 := by
  have hhalf : δ / 2 ≤ δ := by linarith
  rw [max_eq_right hhalf]
  constructor
  · exact le_rfl
  · intro h
    have hdrop : 0 < c * δ ^ 3 := mul_pos hc (pow_pos hδ 3)
    linarith

end RHLean.Analysis
