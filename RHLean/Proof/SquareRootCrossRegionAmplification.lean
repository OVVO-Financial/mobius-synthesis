import Mathlib
import RHLean.Proof.SquareRootAmplificationClosure
import RHLean.Analysis.SquareRootPositiveSmoothCollapse
import RHLean.Proof.MatchedFarSurvivorBridge

/-!
# Cross-region sufficient targets for square-root amplification

The legal root/successor cancellation is overwhelmingly cross-region rather than
fixed-prime fibrewise.  The exact square-root decomposition already packages the
relevant signed interactions into two channels:

* `squareRootPositiveSmoothMass R`, the complete positive-orientation smooth
  channel; and
* `squareRootMatchedBornSmoothTransport R`, the born-smooth/high-transport
  matched channel.

The endpoint identity is

`M(R^2-1) = positiveSmooth(R) + matched(R)`.

Because the ancestry universe omits the exceptional source `m=1`, the shifted
endpoint numerator is

`M(R^2-1)-1 = positiveSmooth(R) + (matched(R)-1)`.

This module proves that fixed critical-envelope amplification bounds for those
two already-signed channels imply the full endpoint amplification theorem.  It
does not bound raw root or successor diagonals and does not split the matched
channel by distinguished prime.
-/

noncomputable section

namespace RHLean.Proof

/-- Fixed amplification for the positive-orientation signed channel. -/
def SquareRootPositiveSmoothAmplificationStatement : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ R : ℕ, ∀ K : ℝ,
      2 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖squareRootPositiveSmoothMass R‖ ^ 2 ≤
        A * (R : ℝ) ^ 2 * K

/-- Fixed amplification for the complete matched born-smooth/high-transport
channel after the same exceptional-source shift as the ancestry renewal. -/
def SquareRootMatchedShiftedAmplificationStatement : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ R : ℕ, ∀ K : ℝ,
      2 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖squareRootMatchedBornSmoothTransport R - 1‖ ^ 2 ≤
        A * (R : ℝ) ^ 2 * K

/-- Pair of signed cross-region amplification targets. -/
def SquareRootCrossRegionAmplificationStatement : Prop :=
  SquareRootPositiveSmoothAmplificationStatement ∧
    SquareRootMatchedShiftedAmplificationStatement

private theorem cross_region_norm_sq_add_le_two (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hnorm := norm_add_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u + v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/-- Every nontrivial lower critical envelope is at least one, because the
shifted Mertens value at `y=0` is exactly `-1`. -/
theorem one_le_of_lowerMertensCriticalEnvelope
    {R : ℕ} {K : ℝ} (hR : 1 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    1 ≤ K := by
  have h0 := hK.2 0 (by omega)
  have hm0 : mertensSummatoryInt 0 = 0 := by
    simp [mertensSummatoryInt]
  rw [hm0] at h0
  norm_num at h0
  exact h0

/-- Exact shifted endpoint decomposition into the two cross-region channels. -/
theorem shiftedMertensEndpoint_eq_positive_add_matchedShift
    (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) - 1 =
      squareRootPositiveSmoothMass R +
        (squareRootMatchedBornSmoothTransport R - 1) := by
  have hR1 : 1 ≤ R := by omega
  have hend :
      RHLean.Analysis.squarePrefixEndpoint (R - 1) = squareRootEndpoint R :=
    squarePrefixEndpoint_pred_eq_squareRootEndpoint R hR1
  have hsplit := squarePrefixMertens_eq_positiveSmooth_add_matched R hR1
  unfold RHLean.Analysis.squarePrefixMertens at hsplit
  rw [hend] at hsplit
  rw [hsplit]
  ring

/-- Fixed amplification of the two signed cross-region channels is sufficient
for the complete endpoint amplification theorem. -/
theorem squareRootEndpointAmplification_of_crossRegion
    (hcross : SquareRootCrossRegionAmplificationStatement) :
    SquareRootMertensEndpointAmplificationStatement := by
  rcases hcross.1 with ⟨AP, hAP, hpos⟩
  rcases hcross.2 with ⟨AJ, hAJ, hmatched⟩
  refine ⟨2 * (AP + AJ), by positivity, ?_⟩
  intro R K hR hK
  have hp := hpos R K hR hK
  have hj := hmatched R K hR hK
  have hsum := cross_region_norm_sq_add_le_two
    (squareRootPositiveSmoothMass R)
    (squareRootMatchedBornSmoothTransport R - 1)
  rw [← shiftedMertensEndpoint_eq_positive_add_matchedShift R hR] at hsum
  have hendEnergy :
      ‖RHLean.Analysis.mertensSummatory (squareRootEndpoint R) - 1‖ ^ 2 =
        (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) := by
    simpa [shiftedMertensEnergy] using
      shiftedMertensEnergy_eq_intSquare (squareRootEndpoint R)
  rw [hendEnergy] at hsum
  calc
    (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) ≤
        2 * ‖squareRootPositiveSmoothMass R‖ ^ 2 +
          2 * ‖squareRootMatchedBornSmoothTransport R - 1‖ ^ 2 := hsum
    _ ≤ 2 * (AP * (R : ℝ) ^ 2 * K) +
          2 * (AJ * (R : ℝ) ^ 2 * K) := by
      linarith
    _ = (2 * (AP + AJ)) * (R : ℝ) ^ 2 * K := by ring

/-- Consequently the two cross-region targets already imply the full repository
Mertens energy criterion through the fixed-amplification closure theorem. -/
theorem mertensEnergyBounded_of_crossRegionAmplification
    (hcross : SquareRootCrossRegionAmplificationStatement) :
    RHLean.Analysis.MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_squareRootEndpointAmplification
    (squareRootEndpointAmplification_of_crossRegion hcross)

/-! ## Localizing the matched channel to the far-survivor core -/

/-- The genuinely large matched core after removing the seven-coordinate near
transport strip.  The same exceptional-source shift is included. -/
def squareRootMatchedFarSurvivorCore (R : ℕ) : ℂ :=
  squareRootBornSmoothMass R +
    survivorSixteenFarUpperPrimeMass (R - 1) - 1

/-- Fixed critical-envelope amplification for the matched far-survivor core,
from the range where the far-upper rigidity theorem applies. -/
def SquareRootMatchedFarSurvivorCoreAmplificationAbove56 : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖squareRootMatchedFarSurvivorCore R‖ ^ 2 ≤
        A * (R : ℝ) ^ 2 * K

/-- Corresponding eventual matched-channel amplification statement. -/
def SquareRootMatchedShiftedAmplificationAbove56 : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖squareRootMatchedBornSmoothTransport R - 1‖ ^ 2 ≤
        A * (R : ℝ) ^ 2 * K

/-- The near strip costs only an explicit constant in the fixed-amplification
budget.  Thus the analytic matched target is the signed born-smooth plus
far-survivor core, not the near transport. -/
theorem matchedShiftedAmplificationAbove56_of_farSurvivorCore
    (hcore : SquareRootMatchedFarSurvivorCoreAmplificationAbove56) :
    SquareRootMatchedShiftedAmplificationAbove56 := by
  rcases hcore with ⟨A, hA, hbound⟩
  refine ⟨2 * A + 98, by positivity, ?_⟩
  intro R K hR hK
  have hcoreR := hbound R K hR hK
  have hnear := norm_squareRootNearPrimeTransport_le R hR
  have hnearSq : ‖squareRootNearPrimeTransport R‖ ^ 2 ≤
      49 * (R : ℝ) ^ 2 := by
    have hn : 0 ≤ ‖squareRootNearPrimeTransport R‖ := norm_nonneg _
    have hR0 : 0 ≤ (R : ℝ) := by positivity
    nlinarith
  have hK1 : 1 ≤ K :=
    one_le_of_lowerMertensCriticalEnvelope (by omega) hK
  have hnearAbsorb :
      98 * (R : ℝ) ^ 2 ≤ 98 * (R : ℝ) ^ 2 * K := by
    have hnonneg : 0 ≤ 98 * (R : ℝ) ^ 2 := by positivity
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hK1 hnonneg
  have hsplit :
      squareRootMatchedBornSmoothTransport R - 1 =
        squareRootMatchedFarSurvivorCore R - squareRootNearPrimeTransport R := by
    rw [squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_farSurvivor_sub_near
      R hR]
    unfold squareRootMatchedFarSurvivorCore
    ring
  have hsum := cross_region_norm_sq_add_le_two
    (squareRootMatchedFarSurvivorCore R) (-squareRootNearPrimeTransport R)
  have hsum' :
      ‖squareRootMatchedBornSmoothTransport R - 1‖ ^ 2 ≤
        2 * ‖squareRootMatchedFarSurvivorCore R‖ ^ 2 +
          2 * ‖squareRootNearPrimeTransport R‖ ^ 2 := by
    rw [hsplit]
    simpa [sub_eq_add_neg] using hsum
  calc
    ‖squareRootMatchedBornSmoothTransport R - 1‖ ^ 2 ≤
        2 * ‖squareRootMatchedFarSurvivorCore R‖ ^ 2 +
          2 * ‖squareRootNearPrimeTransport R‖ ^ 2 := hsum'
    _ ≤ 2 * (A * (R : ℝ) ^ 2 * K) + 98 * (R : ℝ) ^ 2 := by
      nlinarith
    _ ≤ 2 * (A * (R : ℝ) ^ 2 * K) +
          98 * (R : ℝ) ^ 2 * K := add_le_add_left hnearAbsorb _
    _ = (2 * A + 98) * (R : ℝ) ^ 2 * K := by ring

end RHLean.Proof
