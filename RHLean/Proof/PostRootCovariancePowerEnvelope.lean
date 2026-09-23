import Mathlib
import RHLean.Proof.EndpointCubeAnalyticClosure
import RHLean.Proof.PostRootCovarianceLcmBoundaryClosure
import RHLean.Proof.PostRootCovarianceLcmInteriorPacking

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open Finset Nat

/-- The nonnegative normalized seat value for the signed post-root remainder.
Seats below the protected bootstrap onset `W = 2` are set to zero. -/
def postRootCovariancePowerSeat (ε : ℝ) (W : ℕ) : ℝ :=
  if 2 ≤ W then
    max 0
      (postRootCovarianceRemainder W /
        Real.rpow (W : ℝ) (1 + ε))
  else 0

/-- The running finite-horizon envelope of normalized signed remainders.
This is the explicit tether for the power-remainder seam: it is finite at every
horizon, monotone in the horizon, and contains every earlier normalized seat. -/
def postRootCovariancePowerEnvelope (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | N + 1 =>
      max (postRootCovariancePowerEnvelope ε N)
        (postRootCovariancePowerSeat ε (N + 1))

theorem postRootCovariancePowerSeat_nonneg (ε : ℝ) (W : ℕ) :
    0 ≤ postRootCovariancePowerSeat ε W := by
  unfold postRootCovariancePowerSeat
  by_cases hW : 2 ≤ W
  · rw [if_pos hW]
    exact le_max_left _ _
  · rw [if_neg hW]

theorem postRootCovariancePowerEnvelope_nonneg (ε : ℝ) (N : ℕ) :
    0 ≤ postRootCovariancePowerEnvelope ε N := by
  induction N with
  | zero => simp [postRootCovariancePowerEnvelope]
  | succ N ih =>
      rw [postRootCovariancePowerEnvelope]
      exact ih.trans (le_max_left _ _)

theorem postRootCovariancePowerEnvelope_le_succ (ε : ℝ) (N : ℕ) :
    postRootCovariancePowerEnvelope ε N ≤
      postRootCovariancePowerEnvelope ε (N + 1) := by
  rw [postRootCovariancePowerEnvelope]
  exact le_max_left _ _

theorem postRootCovariancePowerEnvelope_mono
    (ε : ℝ) {N M : ℕ} (hNM : N ≤ M) :
    postRootCovariancePowerEnvelope ε N ≤
      postRootCovariancePowerEnvelope ε M := by
  induction M, hNM using Nat.le_induction with
  | base => exact le_rfl
  | succ M hNM ih =>
      exact ih.trans (postRootCovariancePowerEnvelope_le_succ ε M)

theorem postRootCovariancePowerSeat_le_selfEnvelope
    (ε : ℝ) (W : ℕ) :
    postRootCovariancePowerSeat ε W ≤
      postRootCovariancePowerEnvelope ε W := by
  cases W with
  | zero => simp [postRootCovariancePowerSeat, postRootCovariancePowerEnvelope]
  | succ N =>
      rw [postRootCovariancePowerEnvelope]
      exact le_max_right _ _

theorem postRootCovariancePowerSeat_le_envelope
    (ε : ℝ) {W N : ℕ} (hWN : W ≤ N) :
    postRootCovariancePowerSeat ε W ≤
      postRootCovariancePowerEnvelope ε N :=
  (postRootCovariancePowerSeat_le_selfEnvelope ε W).trans
    (postRootCovariancePowerEnvelope_mono ε hWN)

/-- The positive amount by which the next normalized remainder seat sets a new
record above the previous finite-horizon envelope.  Non-record seats cost zero. -/
def postRootCovariancePowerRecordExcess (ε : ℝ) (N : ℕ) : ℝ :=
  max 0
    (postRootCovariancePowerSeat ε (N + 1) -
      postRootCovariancePowerEnvelope ε N)

theorem postRootCovariancePowerRecordExcess_nonneg (ε : ℝ) (N : ℕ) :
    0 ≤ postRootCovariancePowerRecordExcess ε N := by
  unfold postRootCovariancePowerRecordExcess
  exact le_max_left _ _

/-- The running envelope advances by exactly the positive new-record excess. -/
theorem postRootCovariancePowerEnvelope_succ_eq_add_recordExcess
    (ε : ℝ) (N : ℕ) :
    postRootCovariancePowerEnvelope ε (N + 1) =
      postRootCovariancePowerEnvelope ε N +
        postRootCovariancePowerRecordExcess ε N := by
  rw [postRootCovariancePowerEnvelope]
  unfold postRootCovariancePowerRecordExcess
  by_cases h :
      postRootCovariancePowerSeat ε (N + 1) ≤
        postRootCovariancePowerEnvelope ε N
  · have hdiff :
        postRootCovariancePowerSeat ε (N + 1) -
            postRootCovariancePowerEnvelope ε N ≤ 0 :=
      sub_nonpos.mpr h
    rw [max_eq_left h, max_eq_left hdiff]
    ring
  · have hlt :
        postRootCovariancePowerEnvelope ε N <
          postRootCovariancePowerSeat ε (N + 1) :=
      lt_of_not_ge h
    have hrev :
        postRootCovariancePowerEnvelope ε N ≤
          postRootCovariancePowerSeat ε (N + 1) := hlt.le
    have hdiff :
        0 ≤ postRootCovariancePowerSeat ε (N + 1) -
          postRootCovariancePowerEnvelope ε N :=
      sub_nonneg.mpr hrev
    rw [max_eq_right hrev, max_eq_right hdiff]
    ring

/-- **Record-excess telescope.**  The whole finite-horizon envelope is exactly
the cumulative mass of its positive record-breaking increments.  This is the
string to tighten: local sequential inequalities only need to control new
records, not re-bound every old seat. -/
theorem postRootCovariancePowerEnvelope_eq_sum_recordExcess
    (ε : ℝ) (N : ℕ) :
    postRootCovariancePowerEnvelope ε N =
      ∑ j ∈ Finset.range N, postRootCovariancePowerRecordExcess ε j := by
  induction N with
  | zero => simp [postRootCovariancePowerEnvelope]
  | succ N ih =>
      rw [Finset.sum_range_succ, ← ih]
      simpa only [Nat.succ_eq_add_one] using
        postRootCovariancePowerEnvelope_succ_eq_add_recordExcess ε N

/-- **Anchored tail form of the tether.**  Any verified finite prefix can be
frozen permanently; only the record excesses after the anchor remain to be
tightened. -/
theorem postRootCovariancePowerEnvelope_eq_anchor_add_tailRecordExcess
    (ε : ℝ) {A N : ℕ} (hAN : A ≤ N) :
    postRootCovariancePowerEnvelope ε N =
      postRootCovariancePowerEnvelope ε A +
        ∑ j ∈ Finset.Ico A N, postRootCovariancePowerRecordExcess ε j := by
  induction N, hAN using Nat.le_induction with
  | base => simp
  | succ N hAN ih =>
      rw [postRootCovariancePowerEnvelope_succ_eq_add_recordExcess, ih,
        Finset.sum_Ico_succ_top hAN]
      ring

/-- Any summable finite majorant for the record excesses bounds the running
envelope.  This is the plug-in interface for later Euler, LCM-wall, covariance,
or square-wheel inequalities. -/
theorem postRootCovariancePowerEnvelope_le_of_recordExcess_majorant
    (ε : ℝ) (g : ℕ → ℝ) {D : ℝ}
    (hexcess : ∀ j : ℕ, postRootCovariancePowerRecordExcess ε j ≤ g j)
    (hpartial : ∀ N : ℕ, (∑ j ∈ Finset.range N, g j) ≤ D) :
    ∀ N : ℕ, postRootCovariancePowerEnvelope ε N ≤ D := by
  intro N
  rw [postRootCovariancePowerEnvelope_eq_sum_recordExcess]
  calc
    (∑ j ∈ Finset.range N, postRootCovariancePowerRecordExcess ε j) ≤
        ∑ j ∈ Finset.range N, g j :=
      Finset.sum_le_sum fun j _hj => hexcess j
    _ ≤ D := hpartial N

/-- Every real Möbius pair weight is at most one. -/
private theorem realMoebiusPairWeight_le_one (m n : ℕ) :
    realMoebiusStep m * realMoebiusStep n ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or m with hm | hm | hm <;>
    rcases ArithmeticFunction.moebius_eq_or n with hn | hn | hn <;>
      simp [realMoebiusStep, hm, hn]

/-- The exact physical remainder carrier is contained in the full endpoint
square. -/
private theorem postRootCovarianceRemainderPhysicalPairCarrier_subset_endpointSquare
    (W : ℕ) :
    postRootCovarianceRemainderPhysicalPairCarrier W ⊆
      (Finset.Icc 1 W).product (Finset.Icc 1 W) := by
  intro mn hmn
  have hphysical :=
    (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp hmn).1
  rcases mem_mertensPositivePhysicalPairCarrier.mp hphysical with
    ⟨hm1, hmW, hn1, hnW, _hmn⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hm1, hmW⟩,
      Finset.mem_Icc.mpr ⟨hn1, hnW⟩⟩

/-- **Coarse unconditional attachment point.**  Before using any cancellation,
the signed post-root remainder is bounded by the cardinality of its physical
pair carrier, hence by the endpoint square.  This is deliberately weak but
fully unconditional: later work only tightens this same tether. -/
theorem postRootCovarianceRemainder_le_endpoint_sq (W : ℕ) :
    postRootCovarianceRemainder W ≤ (W : ℝ) ^ 2 := by
  have hsubset :=
    postRootCovarianceRemainderPhysicalPairCarrier_subset_endpointSquare W
  have hcard :
      (postRootCovarianceRemainderPhysicalPairCarrier W).card ≤ W * W := by
    have h := Finset.card_le_card hsubset
    simpa [Nat.card_Icc] using h
  rw [postRootCovarianceRemainder_eq_physicalPairCarrier]
  calc
    (∑ mn ∈ postRootCovarianceRemainderPhysicalPairCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) ≤
      ∑ _mn ∈ postRootCovarianceRemainderPhysicalPairCarrier W, (1 : ℝ) :=
        Finset.sum_le_sum fun mn _hmn => realMoebiusPairWeight_le_one mn.1 mn.2
    _ = ((postRootCovarianceRemainderPhysicalPairCarrier W).card : ℝ) := by simp
    _ ≤ ((W * W : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (W : ℝ) ^ 2 := by push_cast; ring

/-- For every positive power loss, the normalized seat is already bounded by
one physical endpoint.  The remaining task is to replace this growing ceiling
by a uniform one. -/
theorem postRootCovariancePowerSeat_le_endpoint
    (ε : ℝ) (hε : 0 < ε) (W : ℕ) :
    postRootCovariancePowerSeat ε W ≤ (W : ℝ) := by
  unfold postRootCovariancePowerSeat
  by_cases hW : 2 ≤ W
  · rw [if_pos hW]
    apply max_le
    · positivity
    · have hWpos : (0 : ℝ) < (W : ℝ) := by
        exact_mod_cast (show 0 < W by omega)
      have hbase : (1 : ℝ) ≤ (W : ℝ) := by
        exact_mod_cast (show 1 ≤ W by omega)
      have hpow :
          (W : ℝ) ≤ Real.rpow (W : ℝ) (1 + ε) := by
        have h := Real.rpow_le_rpow_of_exponent_le hbase
          (by linarith : (1 : ℝ) ≤ 1 + ε)
        simpa only [Real.rpow_one] using h
      have hpowpos : 0 < Real.rpow (W : ℝ) (1 + ε) :=
        Real.rpow_pos_of_pos hWpos _
      apply (div_le_iff₀ hpowpos).2
      calc
        postRootCovarianceRemainder W ≤ (W : ℝ) ^ 2 :=
          postRootCovarianceRemainder_le_endpoint_sq W
        _ = (W : ℝ) * (W : ℝ) := by ring
        _ ≤ (W : ℝ) * Real.rpow (W : ℝ) (1 + ε) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  · rw [if_neg hW]
    positivity

/-- The explicit running envelope therefore has an unconditional linear
finite-horizon ceiling.  This is the initial string: all later synthesis can be
measured as an improvement from `N` toward a constant. -/
theorem postRootCovariancePowerEnvelope_le_endpoint
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    postRootCovariancePowerEnvelope ε N ≤ (N : ℝ) := by
  induction N with
  | zero => simp [postRootCovariancePowerEnvelope]
  | succ N ih =>
      rw [postRootCovariancePowerEnvelope]
      apply max_le
      · have hcast : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ N
        exact ih.trans hcast
      · simpa only [Nat.succ_eq_add_one] using
          postRootCovariancePowerSeat_le_endpoint ε hε (N + 1)

/-- **Finite-horizon tether.** Every signed remainder up to `N` is bounded by
the explicit running envelope times the target power. No arithmetic estimate is
used here; the theorem only packages the exact finite obstruction into a single
monotone scalar. -/
theorem postRootCovarianceRemainder_le_powerEnvelope
    (ε : ℝ) {W N : ℕ} (hW : 2 ≤ W) (hWN : W ≤ N) :
    postRootCovarianceRemainder W ≤
      postRootCovariancePowerEnvelope ε N *
        Real.rpow (W : ℝ) (1 + ε) := by
  have hWpos : (0 : ℝ) < (W : ℝ) := by
    exact_mod_cast (show 0 < W by omega)
  have hpowpos : 0 < Real.rpow (W : ℝ) (1 + ε) :=
    Real.rpow_pos_of_pos hWpos _
  have hseat := postRootCovariancePowerSeat_le_envelope ε hWN
  have hratioSeat :
      postRootCovarianceRemainder W /
          Real.rpow (W : ℝ) (1 + ε) ≤
        postRootCovariancePowerSeat ε W := by
    unfold postRootCovariancePowerSeat
    rw [if_pos hW]
    exact le_max_right _ _
  have hratio :
      postRootCovarianceRemainder W /
          Real.rpow (W : ℝ) (1 + ε) ≤
        postRootCovariancePowerEnvelope ε N :=
    hratioSeat.trans hseat
  exact (div_le_iff₀ hpowpos).1 hratio

/-- Uniform boundedness of the concrete finite-horizon envelope. This is the
same arithmetic content as the positive-power remainder hypothesis, but now in
a form that can be tightened by any later coordinate-wise inequality. -/
def PostRootCovariancePowerEnvelopeBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ N : ℕ, postRootCovariancePowerEnvelope ε N ≤ D

/-- Uniform boundedness of the cumulative positive record excesses. -/
def PostRootCovariancePowerRecordExcessBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ N : ℕ,
        (∑ j ∈ Finset.range N, postRootCovariancePowerRecordExcess ε j) ≤ D

/-- The abstract power-remainder hypothesis bounds the explicit running
envelope. -/
theorem postRootCovariancePowerEnvelopeBounded_of_powerRemainder
    (hpower : PostRootCovariancePowerRemainderStatement) :
    PostRootCovariancePowerEnvelopeBoundedStatement := by
  intro ε hε
  rcases hpower ε hε with ⟨D, hD, hrem⟩
  refine ⟨D, hD, ?_⟩
  intro N
  induction N with
  | zero => simpa [postRootCovariancePowerEnvelope] using hD
  | succ N ih =>
      rw [postRootCovariancePowerEnvelope]
      apply max_le ih
      unfold postRootCovariancePowerSeat
      by_cases hW : 2 ≤ N + 1
      · rw [if_pos hW]
        apply max_le hD
        have hWpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < N + 1 by omega)
        have hpowpos :
            0 < Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) :=
          Real.rpow_pos_of_pos hWpos _
        exact (div_le_iff₀ hpowpos).2 (hrem (N + 1) hW)
      · rw [if_neg hW]
        exact hD

/-- Conversely, a uniform bound on the concrete running envelope supplies the
power-remainder hypothesis with exactly the same constant. -/
theorem postRootCovariancePowerRemainder_of_powerEnvelopeBounded
    (henv : PostRootCovariancePowerEnvelopeBoundedStatement) :
    PostRootCovariancePowerRemainderStatement := by
  intro ε hε
  rcases henv ε hε with ⟨D, hD, hbound⟩
  refine ⟨D, hD, ?_⟩
  intro W hW
  have htether :=
    postRootCovarianceRemainder_le_powerEnvelope ε hW (le_refl W)
  have hWpos : (0 : ℝ) < (W : ℝ) := by
    exact_mod_cast (show 0 < W by omega)
  have hpow_nonneg :
      0 ≤ Real.rpow (W : ℝ) (1 + ε) :=
    (Real.rpow_pos_of_pos hWpos _).le
  exact htether.trans
    (mul_le_mul_of_nonneg_right (hbound W) hpow_nonneg)

/-- The record-excess partial sums and the running envelope are exactly the same
quantity, so boundedness of either formulation is equivalent. -/
theorem postRootCovariancePowerRecordExcessBounded_iff_powerEnvelopeBounded :
    PostRootCovariancePowerRecordExcessBoundedStatement ↔
      PostRootCovariancePowerEnvelopeBoundedStatement := by
  constructor
  · intro hexcess ε hε
    rcases hexcess ε hε with ⟨D, hD, hbound⟩
    refine ⟨D, hD, ?_⟩
    intro N
    rw [postRootCovariancePowerEnvelope_eq_sum_recordExcess]
    exact hbound N
  · intro henv ε hε
    rcases henv ε hε with ⟨D, hD, hbound⟩
    refine ⟨D, hD, ?_⟩
    intro N
    rw [← postRootCovariancePowerEnvelope_eq_sum_recordExcess]
    exact hbound N

/-- **Exact tether equivalence.** The new running envelope is not a stronger
assumption and not a heuristic replacement: its uniform boundedness is exactly
the positive-power signed remainder seam from an earlier layer. -/
theorem postRootCovariancePowerEnvelopeBounded_iff_powerRemainder :
    PostRootCovariancePowerEnvelopeBoundedStatement ↔
      PostRootCovariancePowerRemainderStatement :=
  ⟨postRootCovariancePowerRemainder_of_powerEnvelopeBounded,
    postRootCovariancePowerEnvelopeBounded_of_powerRemainder⟩

/-- The same terminal seam in record-excess form: bounding only the cumulative
new-record increments is already sufficient for the power remainder. -/
theorem postRootCovariancePowerRecordExcessBounded_iff_powerRemainder :
    PostRootCovariancePowerRecordExcessBoundedStatement ↔
      PostRootCovariancePowerRemainderStatement := by
  rw [postRootCovariancePowerRecordExcessBounded_iff_powerEnvelopeBounded,
    postRootCovariancePowerEnvelopeBounded_iff_powerRemainder]

/-- The exact scalar post-root Euler finite difference from the complete LCM
boundary, written as the falling-factorial Mertens field `M(M-1)`. -/
def postRootFallingEnergyFiniteDifference (W : ℕ) : ℝ :=
  (realMertensLength (W + 1) ^ 2 - realMertensLength (W + 1)) -
    ∑ p ∈ postRootPrimeFamilySet W,
      (realMertensLength (W / p + 1) ^ 2 -
        realMertensLength (W / p + 1))

/-- The scalar falling-energy finite difference is exactly twice the literal
post-root super-endpoint LCM-boundary mass. -/
theorem postRootFallingEnergyFiniteDifference_eq_two_mul_boundaryLcmMass
    (W : ℕ) :
    postRootFallingEnergyFiniteDifference W =
      2 * (∑ mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) := by
  unfold postRootFallingEnergyFiniteDifference
  exact
    (two_mul_sum_postRootCovarianceRemainderBoundaryLcmCarrier_eq_lengthFiniteDifference W).symm

/-- Positive power scale dominates one endpoint unit. -/
theorem endpoint_le_postRootPowerScale
    {ε : ℝ} (hε : 0 < ε) {W : ℕ} (hW : 2 ≤ W) :
    (W : ℝ) ≤ Real.rpow (W : ℝ) (1 + ε) := by
  have hbase : (1 : ℝ) ≤ (W : ℝ) := by
    exact_mod_cast (show 1 ≤ W by omega)
  have h := Real.rpow_le_rpow_of_exponent_le hbase
    (by linarith : (1 : ℝ) ≤ 1 + ε)
  simpa only [Real.rpow_one] using h

/-! ## New-record one-step innovation -/

/-- The positive part is 1-Lipschitz under a simultaneous growth of the
normalizing denominator.  This is the elementary order fact that turns a
normalized record event into a raw one-step remainder increment. -/
private theorem max_zero_normalized_jump_le_raw_increment
    {a b S T : ℝ} (hS : 0 < S) (hT : 0 < T) (hST : S ≤ T) :
    max 0 (max 0 (b / T) - max 0 (a / S)) ≤
      max 0 ((b - a) / T) := by
  by_cases ha : a ≤ 0
  · have haDiv : a / S ≤ 0 := by
      rw [div_le_iff₀ hS]
      simpa using ha
    have hab : b ≤ b - a := by linarith
    have hdiv : b / T ≤ (b - a) / T := by
      rw [div_le_div_iff₀ hT hT]
      exact mul_le_mul_of_nonneg_right hab hT.le
    rw [max_eq_left haDiv]
    simp only [sub_zero]
    apply max_le
    · exact le_max_left _ _
    · apply max_le
      · exact le_max_left _ _
      · exact hdiv.trans (le_max_right _ _)
  · have haPos : 0 < a := lt_of_not_ge ha
    have haDiv : 0 ≤ a / S := div_nonneg haPos.le hS.le
    rw [max_eq_right haDiv]
    by_cases hb : b ≤ 0
    · have hbDiv : b / T ≤ 0 := by
        rw [div_le_iff₀ hT]
        simpa using hb
      rw [max_eq_left hbDiv]
      have hleft : 0 - a / S ≤ 0 := by linarith
      rw [max_eq_left hleft]
      exact le_max_left _ _
    · have hbPos : 0 < b := lt_of_not_ge hb
      have hbDiv : 0 ≤ b / T := div_nonneg hbPos.le hT.le
      rw [max_eq_right hbDiv]
      have haFrac : a / T ≤ a / S := by
        rw [div_le_div_iff₀ hT hS]
        exact mul_le_mul_of_nonneg_left hST haPos.le
      have hdiff : b / T - a / S ≤ (b - a) / T := by
        rw [sub_div]
        linarith
      apply max_le
      · exact le_max_left _ _
      · exact hdiff.trans (le_max_right _ _)

/-- The positive raw remainder created on the single step `N -> N+1`, measured
at the new endpoint scale.  Unlike the running envelope this object contains no
old record mass. -/
def postRootCovariancePowerRawIncrementBudget (ε : ℝ) (N : ℕ) : ℝ :=
  max 0
    ((postRootCovarianceRemainder (N + 1) -
        postRootCovarianceRemainder N) /
      Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε))

/-- **Record excess is paid only by new raw remainder mass.**  Once `N >= 2`,
monotonicity of the positive power scale and the fact that the old envelope
already dominates the old seat imply that a new normalized record can gain no
more than the positive one-step increment of the unnormalized remainder. -/
theorem postRootCovariancePowerRecordExcess_le_rawIncrementBudget
    (ε : ℝ) (hε : 0 < ε) {N : ℕ} (hN : 2 ≤ N) :
    postRootCovariancePowerRecordExcess ε N ≤
      postRootCovariancePowerRawIncrementBudget ε N := by
  have hNext : 2 ≤ N + 1 := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hNextPos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < N + 1 by omega)
  have hS : 0 < Real.rpow (N : ℝ) (1 + ε) :=
    Real.rpow_pos_of_pos hNpos _
  have hT : 0 < Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) :=
    Real.rpow_pos_of_pos hNextPos _
  have hST :
      Real.rpow (N : ℝ) (1 + ε) ≤
        Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) := by
    apply Real.rpow_le_rpow (by positivity)
    · exact_mod_cast Nat.le_succ N
    · linarith
  have hlocal :
      postRootCovariancePowerRecordExcess ε N ≤
        max 0
          (postRootCovariancePowerSeat ε (N + 1) -
            postRootCovariancePowerSeat ε N) := by
    unfold postRootCovariancePowerRecordExcess
    apply max_le
    · exact le_max_left _ _
    · exact
        (sub_le_sub_left
          (postRootCovariancePowerSeat_le_selfEnvelope ε N) _).trans
          (le_max_right _ _)
  calc
    postRootCovariancePowerRecordExcess ε N ≤
        max 0
          (postRootCovariancePowerSeat ε (N + 1) -
            postRootCovariancePowerSeat ε N) := hlocal
    _ = max 0
        (max 0
            (postRootCovarianceRemainder (N + 1) /
              Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε)) -
          max 0
            (postRootCovarianceRemainder N /
              Real.rpow (N : ℝ) (1 + ε))) := by
        unfold postRootCovariancePowerSeat
        rw [if_pos hNext, if_pos hN]
    _ ≤ max 0
        ((postRootCovarianceRemainder (N + 1) -
            postRootCovarianceRemainder N) /
          Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε)) :=
      max_zero_normalized_jump_le_raw_increment hS hT hST
    _ = postRootCovariancePowerRawIncrementBudget ε N := rfl

/-- The one-step change in covariance inherited from all complete post-root
prime families.  Keeping this signed is essential: it is the old lower-scale
material that must be removed from the new same-scale covariance shell. -/
def postRootPrimeFamilyCovarianceIncrement (W : ℕ) : ℝ :=
  postRootPrimeFamilyCovarianceTotal (W + 1) -
    postRootPrimeFamilyCovarianceTotal W

/-- **Local covariance innovation.**  This is the genuinely new signed mass at
the step `W -> W+1`: the new Möbius covariance row minus the simultaneous
change in all inherited post-root family copies. -/
def postRootCovarianceLocalInnovation (W : ℕ) : ℝ :=
  realMoebiusStep (W + 1) * realMertensLength (W + 1) -
    postRootPrimeFamilyCovarianceIncrement W

/-- The raw remainder increment is exactly the local covariance innovation.
Thus differencing `E` does not introduce a new global object: it exposes the
new same-scale Möbius row and the inherited-family wall motion. -/
theorem postRootCovarianceRemainder_succ_sub_eq_localInnovation (W : ℕ) :
    postRootCovarianceRemainder (W + 1) -
        postRootCovarianceRemainder W =
      postRootCovarianceLocalInnovation W := by
  unfold postRootCovarianceRemainder postRootCovarianceLocalInnovation
    postRootPrimeFamilyCovarianceIncrement
  have hsucc := realMertensPositiveLagPairSum_succ (W + 1)
  rw [hsucc]
  ring

/-- On any fixed prime coordinate, the inherited lower covariance changes at a
unit endpoint step exactly when that prime divides the new endpoint.  This is
the precise reciprocal-wall indicator behind the local innovation. -/
theorem postRootLowerCovariance_succQuotient_sub (W p : ℕ) :
    realMertensPositiveLagPairSum ((W + 1) / p + 1) -
        realMertensPositiveLagPairSum (W / p + 1) =
      if p ∣ W + 1 then
        realMoebiusStep (W / p + 1) * realMertensLength (W / p + 1)
      else 0 := by
  by_cases hdvd : p ∣ W + 1
  · have hdiv : (W + 1) / p = W / p + 1 := by
      rw [Nat.succ_div, if_pos hdvd]
    rw [if_pos hdvd, hdiv]
    have hsucc := realMertensPositiveLagPairSum_succ (W / p + 1)
    rw [hsucc]
    ring
  · have hdiv : (W + 1) / p = W / p := by
      rw [Nat.succ_div, if_neg hdvd, add_zero]
    rw [if_neg hdvd, hdiv]
    ring

/-- A post-root prime coordinate that appears for the first time at a unit
endpoint step can only be the new endpoint itself.  No interior post-root
coordinate is born between `W` and `W+1`. -/
theorem postRootPrimeFamilySet_succ_new_eq_endpoint
    {W p : ℕ}
    (hpNext : p ∈ postRootPrimeFamilySet (W + 1))
    (hpOld : p ∉ postRootPrimeFamilySet W) :
    p = W + 1 := by
  rcases mem_postRootPrimeFamilySet.mp hpNext with
    ⟨hpRootNext, hpLeNext, hpPrime⟩
  by_contra hne
  have hpLeW : p ≤ W := by omega
  have hrootMono : Nat.sqrt W ≤ Nat.sqrt (W + 1) :=
    Nat.sqrt_le_sqrt (by omega)
  have hpRootOld : Nat.sqrt W < p :=
    lt_of_le_of_lt hrootMono hpRootNext
  exact hpOld (mem_postRootPrimeFamilySet.mpr
    ⟨hpRootOld, hpLeW, hpPrime⟩)

/-- A post-root coordinate can leave the family set at a unit endpoint step
only by hitting the square-root wall exactly.  Thus every deletion is a prime
square event `p^2 = W+1`. -/
theorem postRootPrimeFamilySet_succ_removed_eq_square
    {W p : ℕ}
    (hpOld : p ∈ postRootPrimeFamilySet W)
    (hpNext : p ∉ postRootPrimeFamilySet (W + 1)) :
    p * p = W + 1 := by
  rcases mem_postRootPrimeFamilySet.mp hpOld with
    ⟨hpRootOld, hpLeW, hpPrime⟩
  have hpRootNextNot : ¬ Nat.sqrt (W + 1) < p := by
    intro hpRootNext
    exact hpNext (mem_postRootPrimeFamilySet.mpr
      ⟨hpRootNext, hpLeW.trans (by omega), hpPrime⟩)
  have hpLeRootNext : p ≤ Nat.sqrt (W + 1) :=
    Nat.le_of_not_gt hpRootNextNot
  have hWlt : W < p * p := (Nat.sqrt_lt).1 hpRootOld
  have hpSqLe : p * p ≤ W + 1 := by
    simpa [pow_two] using (Nat.le_sqrt).1 hpLeRootNext
  omega

/-- At a fixed endpoint there is at most one active post-root prime divisor.
This turns every reciprocal quotient jump in the local innovation into a
single channel rather than a sum over the whole post-root family. -/
theorem postRootPrimeFamily_divisor_unique
    {W p q : ℕ}
    (hp : p ∈ postRootPrimeFamilySet W)
    (hq : q ∈ postRootPrimeFamilySet W)
    (hpdvd : p ∣ W) (hqdvd : q ∣ W) :
    p = q := by
  by_contra hpq
  have hWpos : 0 < W := by
    rcases mem_postRootPrimeFamilySet.mp hp with
      ⟨_hpRoot, hpW, hpPrime⟩
    exact hpPrime.pos.trans_le hpW
  exact (no_common_distinct_postRootPrime_divisors hp hq hpq
    hWpos (le_refl W) hpdvd hqdvd).elim

/-- The record budget after the raw remainder increment has been replaced by
its exact local covariance innovation. -/
def postRootCovariancePowerLocalInnovationBudget (ε : ℝ) (N : ℕ) : ℝ :=
  max 0
    (postRootCovarianceLocalInnovation N /
      Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε))

/-- **New record -> local innovation.**  A positive normalized record can be
paid only by the newly created covariance row after subtracting the motion of
the inherited post-root family copies.  No accumulated old remainder remains. -/
theorem postRootCovariancePowerRecordExcess_le_localInnovationBudget
    (ε : ℝ) (hε : 0 < ε) {N : ℕ} (hN : 2 ≤ N) :
    postRootCovariancePowerRecordExcess ε N ≤
      postRootCovariancePowerLocalInnovationBudget ε N := by
  have hraw :=
    postRootCovariancePowerRecordExcess_le_rawIncrementBudget ε hε hN
  unfold postRootCovariancePowerRawIncrementBudget at hraw
  unfold postRootCovariancePowerLocalInnovationBudget
  rw [postRootCovarianceRemainder_succ_sub_eq_localInnovation] at hraw
  exact hraw

/-! ## New-record first-wall discharge -/

/-- The total signed mass of the complete lower post-root physical parent
cubes from an earlier layer.  These are the cubes on which the physical top escape has
already vanished, leaving only the negative first-LCM-wall contribution. -/
def postRootCovarianceCompleteFirstWallCubeMass (W : ℕ) : ℝ :=
  ∑ p ∈ postRootPrimeFamilySet W,
    ∑ mn ∈ mertensPositivePhysicalPairCarrier (W / p),
      realMoebiusPhysicalSuperLcmFourCorner W p mn.1 mn.2

/-- The complete lower cube mass is exactly minus the sum of the lower scalar
LCM boundary kernels. -/
theorem postRootCovarianceCompleteFirstWallCubeMass_eq_neg_lowerBoundarySum
    (W : ℕ) :
    postRootCovarianceCompleteFirstWallCubeMass W =
      -(∑ p ∈ postRootPrimeFamilySet W, fullLcmBoundaryKernel (W / p)) := by
  unfold postRootCovarianceCompleteFirstWallCubeMass
  calc
    (∑ p ∈ postRootPrimeFamilySet W,
        ∑ mn ∈ mertensPositivePhysicalPairCarrier (W / p),
          realMoebiusPhysicalSuperLcmFourCorner W p mn.1 mn.2) =
      ∑ p ∈ postRootPrimeFamilySet W, -fullLcmBoundaryKernel (W / p) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact sum_realMoebiusPhysicalSuperLcmFourCorner_postRoot_eq_neg_lower hp
    _ = -(∑ p ∈ postRootPrimeFamilySet W, fullLcmBoundaryKernel (W / p)) := by
      rw [Finset.sum_neg_distrib]

/-- The amount gained from the complete first-wall cubes.  It is defined with
the favorable sign, so later bounds can subtract it directly. -/
def postRootCovarianceCompleteFirstWallGain (W : ℕ) : ℝ :=
  -postRootCovarianceCompleteFirstWallCubeMass W

theorem postRootCovarianceCompleteFirstWallGain_eq_lowerBoundarySum
    (W : ℕ) :
    postRootCovarianceCompleteFirstWallGain W =
      ∑ p ∈ postRootPrimeFamilySet W, fullLcmBoundaryKernel (W / p) := by
  unfold postRootCovarianceCompleteFirstWallGain
  rw [postRootCovarianceCompleteFirstWallCubeMass_eq_neg_lowerBoundarySum]
  ring

/-- Every complete first-wall cube helps the desired one-sided estimate in the
aggregate: the total gain is nonnegative. -/
theorem postRootCovarianceCompleteFirstWallGain_nonneg (W : ℕ) :
    0 ≤ postRootCovarianceCompleteFirstWallGain W := by
  rw [postRootCovarianceCompleteFirstWallGain_eq_lowerBoundarySum]
  exact Finset.sum_nonneg fun p _hp => fullLcmBoundaryKernel_nonneg (W / p)

/-- **Exact wall decomposition.**  The literal post-root LCM-boundary mass is
the full physical outer boundary minus the complete first-wall gain.  This is
an equality, not a global reindexing claim about clipped cubes. -/
theorem sum_postRootCovarianceRemainderBoundaryLcmCarrier_eq_outerBoundary_sub_completeFirstWallGain
    (W : ℕ) :
    (∑ mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      fullLcmBoundaryKernel W - postRootCovarianceCompleteFirstWallGain W := by
  rw [sum_postRootCovarianceRemainderBoundaryLcmCarrier_eq_finiteDifference,
    postRootCovarianceCompleteFirstWallGain_eq_lowerBoundarySum]

/-- The whole post-root remainder is therefore the packed complete-LCM interior,
plus the physical outer boundary, minus the favorable complete first-wall gain. -/
theorem postRootCovarianceRemainder_eq_interior_add_outerBoundary_sub_completeFirstWallGain
    (W : ℕ) :
    postRootCovarianceRemainder W =
      (∑ mn ∈ postRootCovarianceRemainderInteriorLcmCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) +
      fullLcmBoundaryKernel W - postRootCovarianceCompleteFirstWallGain W := by
  rw [postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm,
    sum_postRootCovarianceRemainderBoundaryLcmCarrier_eq_outerBoundary_sub_completeFirstWallGain]
  ring

/-- After discarding the favorable complete cubes, only one endpoint unit of
packed interior plus the physical outer boundary can create a positive record. -/
theorem postRootCovarianceRemainder_le_endpoint_add_outerBoundary (W : ℕ) :
    postRootCovarianceRemainder W ≤ (W : ℝ) + fullLcmBoundaryKernel W := by
  have hsplit :=
    postRootCovarianceRemainder_eq_interior_add_outerBoundary_sub_completeFirstWallGain W
  have hinterior :=
    sum_postRootCovarianceRemainderInteriorLcmCarrier_le_endpoint W
  have hgain := postRootCovarianceCompleteFirstWallGain_nonneg W
  linarith

/-- The record-only residual budget after complete first-wall cubes are removed.
The packed interior costs at most one unit on the `W^(1+ε)` scale. -/
def postRootCovariancePowerOuterBoundaryRecordBudget (ε : ℝ) (N : ℕ) : ℝ :=
  max 0
    (fullLcmBoundaryKernel (N + 1) /
        Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) +
      1 - postRootCovariancePowerEnvelope ε N)

/-- **New-record -> outer-wall residual.**  Every positive record increment is
paid for by the normalized physical outer LCM boundary above the old record,
with only the already-packed one-unit interior allowance.  The complete
first-wall cube gain has disappeared from the upper bound with its correct sign. -/
theorem postRootCovariancePowerRecordExcess_le_outerBoundaryRecordBudget
    (ε : ℝ) (hε : 0 < ε) {N : ℕ} (hN : 1 ≤ N) :
    postRootCovariancePowerRecordExcess ε N ≤
      postRootCovariancePowerOuterBoundaryRecordBudget ε N := by
  have hW : 2 ≤ N + 1 := by omega
  have hWpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < N + 1 by omega)
  have hpowpos :
      0 < Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) :=
    Real.rpow_pos_of_pos hWpos _
  have hpowne : Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) ≠ 0 :=
    ne_of_gt hpowpos
  have hscale := endpoint_le_postRootPowerScale hε hW
  have hrem := postRootCovarianceRemainder_le_endpoint_add_outerBoundary (N + 1)
  have hcancel :
      (fullLcmBoundaryKernel (N + 1) /
          Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε)) *
          Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) =
        fullLcmBoundaryKernel (N + 1) := by
    exact div_mul_cancel₀ _ hpowne
  have hratio :
      postRootCovarianceRemainder (N + 1) /
          Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) ≤
        fullLcmBoundaryKernel (N + 1) /
            Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) + 1 := by
    apply (div_le_iff₀ hpowpos).2
    calc
      postRootCovarianceRemainder (N + 1) ≤
          (((N + 1 : ℕ) : ℝ) + fullLcmBoundaryKernel (N + 1)) := hrem
      _ ≤ Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) +
          fullLcmBoundaryKernel (N + 1) := by linarith
      _ = (fullLcmBoundaryKernel (N + 1) /
              Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) + 1) *
            Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) := by
        rw [add_mul, hcancel, one_mul]
        ring
  have hseat :
      postRootCovariancePowerSeat ε (N + 1) ≤
        fullLcmBoundaryKernel (N + 1) /
            Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) + 1 := by
    unfold postRootCovariancePowerSeat
    rw [if_pos hW]
    apply max_le
    · have hboundary : 0 ≤ fullLcmBoundaryKernel (N + 1) :=
        fullLcmBoundaryKernel_nonneg (N + 1)
      have hdiv :
          0 ≤ fullLcmBoundaryKernel (N + 1) /
            Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) :=
        div_nonneg hboundary hpowpos.le
      linarith
    · exact hratio
  unfold postRootCovariancePowerRecordExcess
    postRootCovariancePowerOuterBoundaryRecordBudget
  apply max_le
  · exact le_max_left _ _
  · exact (sub_le_sub_right hseat _).trans (le_max_right _ _)

/-- A genuine new record forces the normalized outer LCM boundary to clear the
old envelope, up to the single packed-interior unit.  This is the extremality
condition to feed into the other deterministic coordinate inequalities. -/
theorem postRootCovariancePowerEnvelope_lt_outerBoundaryNormalized_add_one_of_recordExcess_pos
    (ε : ℝ) (hε : 0 < ε) {N : ℕ} (hN : 1 ≤ N)
    (hrecord : 0 < postRootCovariancePowerRecordExcess ε N) :
    postRootCovariancePowerEnvelope ε N <
      fullLcmBoundaryKernel (N + 1) /
        Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) + 1 := by
  have hle :=
    postRootCovariancePowerRecordExcess_le_outerBoundaryRecordBudget ε hε hN
  have hbudget :
      0 < postRootCovariancePowerOuterBoundaryRecordBudget ε N :=
    lt_of_lt_of_le hrecord hle
  unfold postRootCovariancePowerOuterBoundaryRecordBudget at hbudget
  by_contra hnot
  have hnonpos :
      fullLcmBoundaryKernel (N + 1) /
          Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) +
        1 - postRootCovariancePowerEnvelope ε N ≤ 0 := by
    linarith
  rw [max_eq_left hnonpos] at hbudget
  linarith

/-- Positive-power control of the exact scalar falling-energy finite difference.
This is the boundary seam with the weaker exponent needed by an earlier layer. -/
def PostRootFallingEnergyFiniteDifferencePowerStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ W : ℕ, 2 ≤ W →
        postRootFallingEnergyFiniteDifference W ≤
          D * Real.rpow (W : ℝ) (1 + ε)

/-- A positive-power bound on the scalar falling-energy finite difference gives
the post-root covariance power remainder.  The only loss is one endpoint unit
from the already-packed complete-LCM interior. -/
theorem postRootCovariancePowerRemainder_of_fallingEnergyFiniteDifferencePower
    (hfall : PostRootFallingEnergyFiniteDifferencePowerStatement) :
    PostRootCovariancePowerRemainderStatement := by
  intro ε hε
  rcases hfall ε hε with ⟨D, hD, hfallBound⟩
  refine ⟨D / 2 + 1, by positivity, ?_⟩
  intro W hW
  have hf := hfallBound W hW
  have hboundary :=
    postRootFallingEnergyFiniteDifference_eq_two_mul_boundaryLcmMass W
  have hinterior :=
    sum_postRootCovarianceRemainderInteriorLcmCarrier_le_endpoint W
  have hsplit :=
    postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm W
  have hscale := endpoint_le_postRootPowerScale hε hW
  nlinarith

/-- Conversely, the post-root covariance power remainder controls the scalar
falling-energy finite difference.  The lower complete-LCM interior bound costs
one endpoint unit, and the scalar boundary identity contributes the factor two. -/
theorem postRootFallingEnergyFiniteDifferencePower_of_powerRemainder
    (hpower : PostRootCovariancePowerRemainderStatement) :
    PostRootFallingEnergyFiniteDifferencePowerStatement := by
  intro ε hε
  rcases hpower ε hε with ⟨D, hD, hrem⟩
  refine ⟨2 * (D + 1), by positivity, ?_⟩
  intro W hW
  have hr := hrem W hW
  have hboundary :=
    postRootFallingEnergyFiniteDifference_eq_two_mul_boundaryLcmMass W
  have hinterior :=
    neg_endpoint_le_sum_postRootCovarianceRemainderInteriorLcmCarrier W
  have hsplit :=
    postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm W
  have hscale := endpoint_le_postRootPowerScale hε hW
  nlinarith

/-- **Exact scalar tether equivalence.**  Up to the already-proved linear
complete-LCM interior, the positive-power covariance seam and the falling-energy
Euler finite-difference seam are the same quantitative problem. -/
theorem postRootFallingEnergyFiniteDifferencePower_iff_powerRemainder :
    PostRootFallingEnergyFiniteDifferencePowerStatement ↔
      PostRootCovariancePowerRemainderStatement :=
  ⟨postRootCovariancePowerRemainder_of_fallingEnergyFiniteDifferencePower,
    postRootFallingEnergyFiniteDifferencePower_of_powerRemainder⟩

/-- The finite-horizon running envelope is uniformly bounded exactly when the
scalar falling-energy finite difference has the target positive-power bound. -/
theorem postRootCovariancePowerEnvelopeBounded_iff_fallingEnergyFiniteDifferencePower :
    PostRootCovariancePowerEnvelopeBoundedStatement ↔
      PostRootFallingEnergyFiniteDifferencePowerStatement := by
  rw [postRootCovariancePowerEnvelopeBounded_iff_powerRemainder,
    ← postRootFallingEnergyFiniteDifferencePower_iff_powerRemainder]

/-- **Arrow/string endpoint.**  Bounded cumulative new-record excesses are
exactly equivalent to positive-power control of the explicit scalar
falling-energy finite difference.  Future inequalities may therefore tighten
the record-excess tail or the scalar finite difference interchangeably. -/
theorem postRootCovariancePowerRecordExcessBounded_iff_fallingEnergyFiniteDifferencePower :
    PostRootCovariancePowerRecordExcessBoundedStatement ↔
      PostRootFallingEnergyFiniteDifferencePowerStatement := by
  rw [postRootCovariancePowerRecordExcessBounded_iff_powerRemainder,
    ← postRootFallingEnergyFiniteDifferencePower_iff_powerRemainder]

/-- Bounding the explicit running envelope therefore reaches the protected
Mertens energy criterion through the bootstrap. -/
theorem mertensEnergyBounded_of_postRootCovariancePowerEnvelopeBounded
    (henv : PostRootCovariancePowerEnvelopeBoundedStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_postRootCovariancePowerRemainder
    (postRootCovariancePowerRemainder_of_powerEnvelopeBounded henv)

/-- A bounded cumulative record-excess majorant therefore reaches the protected
Mertens energy criterion as well. -/
theorem mertensEnergyBounded_of_postRootCovariancePowerRecordExcessBounded
    (hexcess : PostRootCovariancePowerRecordExcessBoundedStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_postRootCovariancePowerEnvelopeBounded
    (postRootCovariancePowerRecordExcessBounded_iff_powerEnvelopeBounded.mp hexcess)

/-- Positive-power control of the explicit falling-energy finite difference
therefore feeds the protected Mertens-energy criterion through an earlier layer. -/
theorem mertensEnergyBounded_of_postRootFallingEnergyFiniteDifferencePower
    (hfall : PostRootFallingEnergyFiniteDifferencePowerStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_postRootCovariancePowerRemainder
    (postRootCovariancePowerRemainder_of_fallingEnergyFiniteDifferencePower hfall)

end RHLean.Proof
