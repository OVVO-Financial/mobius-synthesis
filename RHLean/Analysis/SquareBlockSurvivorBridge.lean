import Mathlib
import RHLean.Analysis.SquareBlockDeathProcess
import RHLean.Proof.SurvivorResidueCovariance

/-!
# Paper-facing square-block survivor bridge

This module exposes only the square-block lifetime survivor statements needed by
the standalone squared-complex paper. It deliberately introduces no additional
block architecture and no new analytic estimate.

The underlying proof module realizes the current active high population as the
explicit canonical cofactor operator and proves that its local energy is exactly
the lifetime-active local energy. Combined with the already-proved divisor-window
death estimate, this is the paper-facing endpoint after the completed death
process has been removed.
-/

noncomputable section

namespace RHLean.Analysis

/-- The paper's nonnegative survivor kernel in the fixed canonical cofactor
fibre. -/
abbrev squareBlockSurvivorKernel (Λ : ℝ) (t c : ℕ) : ℕ :=
  RHLean.Proof.survivorZeroModeKernel Λ t c

/-- The paper's explicit signed active-survivor cofactor operator. -/
abbrev squareBlockSurvivor (Λ : ℝ) (t : ℕ) : ℂ :=
  RHLean.Proof.survivorZeroMode Λ t

/-- RH-scale translated-window power saving for the explicit active survivor. -/
abbrev SquareBlockSurvivorPowerSavingStatement (Λ : ℝ) : Prop :=
  RHLean.Proof.SurvivorZeroModePowerSavingStatement Λ

/-- The explicit square-block survivor has exactly the local energy of the
lifetime-active sequence. -/
theorem squareBlockSurvivor_localEnergy_eq_lifetimeActive
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (N H : ℕ) :
    localSequenceEnergy (squareBlockSurvivor Λ) N H =
      localSequenceEnergy (RHLean.Proof.lifetimeActiveAtomMass Λ) N H := by
  exact RHLean.Proof.survivorZeroMode_localEnergy_eq_lifetimeActive hΛ N H

/-- The explicit survivor power-saving statement is exactly the lifetime-active
survivor premise. -/
theorem squareBlockSurvivorPowerSaving_iff_lifetimeActive
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    SquareBlockSurvivorPowerSavingStatement Λ ↔
      RHLean.Proof.LifetimeActiveUniformLocalBoundedStatement Λ := by
  exact RHLean.Proof.survivorZeroModePowerSaving_iff_lifetimeActive hΛ

/-- Endpoint-language form: the explicit survivor estimate is exactly the
birth-minus-death discrepancy estimate. -/
theorem squareBlockSurvivorPowerSaving_iff_endpointDiscrepancy
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    SquareBlockSurvivorPowerSavingStatement Λ ↔
      RHLean.Proof.LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ := by
  calc
    SquareBlockSurvivorPowerSavingStatement Λ ↔
        RHLean.Proof.LifetimeActiveUniformLocalBoundedStatement Λ :=
      squareBlockSurvivorPowerSaving_iff_lifetimeActive hΛ
    _ ↔ RHLean.Proof.LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ :=
      RHLean.Proof.lifetimeActiveUniformLocalBounded_iff_endpointDiscrepancy Λ

/-- After the unconditional death-process estimate, a survivor power saving
implies the protected square-prefix uniform-local criterion. -/
theorem squareBlockSurvivorPowerSaving_implies_squarePrefixUniformLocal
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hsurvivor : SquareBlockSurvivorPowerSavingStatement Λ) :
    SquarePrefixUniformLocalBoundedStatement := by
  have hdiscrepancy :
      RHLean.Proof.LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ :=
    (squareBlockSurvivorPowerSaving_iff_endpointDiscrepancy
      (le_of_lt hΛ)).1 hsurvivor
  exact
    RHLean.Proof.lifetimeEndpointDiscrepancy_implies_squarePrefixUniformLocal
      hΛ hdiscrepancy

/-- Conditional terminal composition with the ordinary classical Mertens--RH
criterion. -/
theorem squareBlockSurvivorPowerSaving_implies_riemannHypothesis
    {Λ : ℝ} (hΛ : 0 < Λ)
    (criterion : ClassicalMertensRHCriterion)
    (hsurvivor : SquareBlockSurvivorPowerSavingStatement Λ) :
    RiemannHypothesisStatement := by
  have hdiscrepancy :
      RHLean.Proof.LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ :=
    (squareBlockSurvivorPowerSaving_iff_endpointDiscrepancy
      (le_of_lt hΛ)).1 hsurvivor
  exact
    RHLean.Proof.lifetimeEndpointDiscrepancy_implies_riemannHypothesis
      hΛ criterion hdiscrepancy

end RHLean.Analysis