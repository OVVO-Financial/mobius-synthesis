import Mathlib
import RHLean.Proof.DeathProcessShellIdentity

/-!
# Death-shell cardinality and centering framework

This module records two unconditional reductions for the death process.

* The absolute Möbius mass of a death shell is bounded by its cardinality.
* Any chosen bias profile splits the shell increment and the cumulative death
  process exactly into bias and centered parts.

The standard analytic estimate `#S_t ≪_{ε,Λ} t^ε` is not asserted here:
mathlib currently provides finite divisor sets and divisor-count identities,
but not the classical subpolynomial divisor bound in the form needed for that
corollary.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The norm of a death-shell Möbius mass is bounded by the number of sources
in that shell. -/
theorem norm_deathHeightShellMass_le_card
    (Λ : ℝ) (t : ℕ) :
    ‖deathHeightShellMass Λ t‖ ≤ (deathHeightShellSet Λ t).card := by
  unfold deathHeightShellMass movingCanonicalCrossingMass canonicalMoebiusMass
    deathHeightShellSet
  calc
    ‖∑ m ∈ movingCanonicalCrossingSet Λ t, canonicalMoebiusWeight m‖ ≤
        ∑ m ∈ movingCanonicalCrossingSet Λ t, ‖canonicalMoebiusWeight m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ movingCanonicalCrossingSet Λ t, (1 : ℝ) := by
      exact Finset.sum_le_sum fun m _ => norm_canonicalMoebiusWeight_le_one m
    _ = (movingCanonicalCrossingSet Λ t).card := by simp

/-- Through the exact shell identity, shell cardinality controls the discrete
death increment. -/
theorem norm_lifetimeDeathIncrement_le_card
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (t : ℕ) :
    ‖lifetimeDeathIncrement Λ t‖ ≤ (deathHeightShellSet Λ t).card := by
  rw [lifetimeDeathIncrement_eq_deathHeightShellMass hΛ]
  exact norm_deathHeightShellMass_le_card Λ t

/-- A typed pointwise majorant for death-shell cardinalities. -/
structure DeathShellCardinalityControl (Λ : ℝ) where
  majorant : ℕ → ℝ
  majorant_nonneg : ∀ t, 0 ≤ majorant t
  card_le : ∀ t, (deathHeightShellSet Λ t).card ≤ majorant t

/-- Any shell-cardinality majorant immediately controls the shell increment. -/
theorem norm_lifetimeDeathIncrement_le_majorant
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (control : DeathShellCardinalityControl Λ) (t : ℕ) :
    ‖lifetimeDeathIncrement Λ t‖ ≤ control.majorant t := by
  exact le_trans (norm_lifetimeDeathIncrement_le_card hΛ t) (control.card_le t)

/-- A cardinality majorant gives the corresponding cumulative pointwise bound
for the death process. -/
theorem norm_lifetimeDeathMass_le_initial_add_sum_majorant
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (control : DeathShellCardinalityControl Λ) (n : ℕ) :
    ‖lifetimeDeathMass Λ n‖ ≤
      ‖lifetimeDeathMass Λ 0‖ +
        ∑ t ∈ Finset.range n, control.majorant t := by
  rw [lifetimeDeathMass_eq_zero_add_sum_increments]
  calc
    ‖lifetimeDeathMass Λ 0 +
        ∑ t ∈ Finset.range n, lifetimeDeathIncrement Λ t‖ ≤
      ‖lifetimeDeathMass Λ 0‖ +
        ‖∑ t ∈ Finset.range n, lifetimeDeathIncrement Λ t‖ := norm_add_le _ _
    _ ≤ ‖lifetimeDeathMass Λ 0‖ +
        ∑ t ∈ Finset.range n, ‖lifetimeDeathIncrement Λ t‖ := by
      exact add_le_add_left (norm_sum_le _ _) _
    _ ≤ ‖lifetimeDeathMass Λ 0‖ +
        ∑ t ∈ Finset.range n, control.majorant t := by
      exact add_le_add_left
        (Finset.sum_le_sum fun t _ =>
          norm_lifetimeDeathIncrement_le_majorant hΛ control t) _

/-- Centered shell increment relative to an arbitrary deterministic bias
profile `b`. -/
def centeredDeathShellIncrement
    (Λ : ℝ) (b : ℕ → ℂ) (t : ℕ) : ℂ :=
  lifetimeDeathIncrement Λ t - b t

/-- Exact shell-level bias plus centered decomposition. -/
theorem lifetimeDeathIncrement_eq_bias_add_centered
    (Λ : ℝ) (b : ℕ → ℂ) (t : ℕ) :
    lifetimeDeathIncrement Λ t =
      b t + centeredDeathShellIncrement Λ b t := by
  unfold centeredDeathShellIncrement
  ring

/-- Cumulative bias profile through stage `n`. -/
def deathShellBiasPrefix (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ t ∈ Finset.range n, b t

/-- Cumulative centered shell process through stage `n`. -/
def centeredDeathShellPrefix
    (Λ : ℝ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ t ∈ Finset.range n, centeredDeathShellIncrement Λ b t

/-- Exact cumulative decomposition of the death process into its initial value,
bias prefix, and centered shell prefix. -/
theorem lifetimeDeathMass_eq_initial_add_bias_add_centered
    (Λ : ℝ) (b : ℕ → ℂ) (n : ℕ) :
    lifetimeDeathMass Λ n =
      lifetimeDeathMass Λ 0 + deathShellBiasPrefix b n +
        centeredDeathShellPrefix Λ b n := by
  rw [lifetimeDeathMass_eq_zero_add_sum_increments]
  unfold deathShellBiasPrefix centeredDeathShellPrefix
  calc
    lifetimeDeathMass Λ 0 +
        ∑ t ∈ Finset.range n, lifetimeDeathIncrement Λ t =
      lifetimeDeathMass Λ 0 +
        ∑ t ∈ Finset.range n,
          (b t + centeredDeathShellIncrement Λ b t) := by
      apply congrArg (fun z => lifetimeDeathMass Λ 0 + z)
      apply Finset.sum_congr rfl
      intro t ht
      exact lifetimeDeathIncrement_eq_bias_add_centered Λ b t
    _ = lifetimeDeathMass Λ 0 +
          ∑ t ∈ Finset.range n, b t +
          ∑ t ∈ Finset.range n, centeredDeathShellIncrement Λ b t := by
      rw [Finset.sum_add_distrib]
      ring

/-- RH-scale local energy for a cumulative deterministic bias profile. -/
def DeathShellBiasUniformLocalBoundedStatement (b : ℕ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        RHLean.Analysis.localSequenceEnergy (deathShellBiasPrefix b) N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- RH-scale local energy for the cumulative centered shell process. -/
def CenteredDeathShellUniformLocalBoundedStatement
    (Λ : ℝ) (b : ℕ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        RHLean.Analysis.localSequenceEnergy
            (centeredDeathShellPrefix Λ b) N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

end RHLean.Proof
