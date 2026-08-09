import Mathlib
import RHLean.Proof.DeathShellSubpolynomial

/-!
# Paper-facing square-block death-process bounds

This Analysis-layer wrapper exposes the completed divisor-window estimate used
by the standalone square-block paper. The underlying proof is the exact finite
death-shell argument: bounded-width doubled-height windows are majorized by
divisor counts, the divisor function is subpolynomial, and the accumulated
death mass therefore satisfies the protected RH-scale translated-window bound.

No survivor power saving and no unconditional RH theorem is introduced here.
-/

noncomputable section

namespace RHLean.Analysis

/-- Paper-facing name for the divisor-window majorant. -/
abbrev squareBlockDeathShellDivisorMajorant (Λ : ℝ) (t : ℕ) : ℝ :=
  RHLean.Proof.deathShellDivisorMajorant Λ t

/-- The divisor-window majorant is subpolynomial at every positive exponent. -/
theorem squareBlockDeathShellDivisorMajorant_subpolynomial
    {Λ : ℝ} (hΛ : 0 < Λ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℕ,
        squareBlockDeathShellDivisorMajorant Λ t ≤
          C * Real.rpow ((t + 1 : ℕ) : ℝ) ε := by
  exact RHLean.Proof.deathShellDivisorMajorant_subpolynomial hΛ hε

/-- Each lifetime death increment is subpolynomial. -/
theorem squareBlockDeathIncrement_subpolynomial
    {Λ : ℝ} (hΛ : 0 < Λ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℕ,
        ‖RHLean.Proof.lifetimeDeathIncrement Λ t‖ ≤
          C * Real.rpow ((t + 1 : ℕ) : ℝ) ε := by
  exact RHLean.Proof.norm_lifetimeDeathIncrement_subpolynomial hΛ hε

/-- The accumulated lifetime death mass has the expected pointwise
`(n+1)^(1+ε)` bound. -/
theorem squareBlockDeathMass_le_rpow
    {Λ : ℝ} (hΛ : 0 < Λ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ,
        ‖RHLean.Proof.lifetimeDeathMass Λ n‖ ≤
          C * Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε) := by
  exact RHLean.Proof.norm_lifetimeDeathMass_le_rpow hΛ hε

/-- The completed death process satisfies the RH-scale local-energy bound
unconditionally for positive `Λ`. -/
theorem squareBlockDeathUniformLocalBounded
    {Λ : ℝ} (hΛ : 0 < Λ) :
    RHLean.Proof.LifetimeDeathUniformLocalBoundedStatement Λ := by
  exact RHLean.Proof.lifetimeDeathUniformLocalBounded hΛ

/-- Once the death process is discharged, the lifetime endpoint criterion is
exactly the active birth-minus-death discrepancy criterion. -/
theorem squareBlockEndpointUniformLocalBounded_iff_discrepancy
    {Λ : ℝ} (hΛ : 0 < Λ) :
    RHLean.Proof.LifetimeEndpointUniformLocalBoundedStatement Λ ↔
      RHLean.Proof.LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ := by
  exact RHLean.Proof.lifetimeEndpointUniformLocalBounded_iff_discrepancy hΛ

end RHLean.Analysis
