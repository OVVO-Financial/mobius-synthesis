import Mathlib
import RHLean.Analysis.PrimeWheelDirichletResponse
import RHLean.Analysis.PrimeWheelHarmonicCriterion

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- The remaining RH-scale theorem stated directly on the explicit
phase-adjusted arithmetic coefficient vector and finite Dirichlet response. -/
def PrimorialWheelDirichletNonconcentration : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ k N : ℕ,
        0 < N →
        primorialBlockLower k + N ≤ primorialBlockUpper k →
        ‖primeWheelDirichletPrefix (primorialWheelSystem k) N‖ ^ 2 ≤
          C * Real.rpow
            (((primorialBlockLower k + N) + 1 : ℕ) : ℝ) (1 + ε)

/-- The explicit Dirichlet formulation is exactly the finite harmonic
nonconcentration proposition. -/
theorem primorialWheelDirichletNonconcentration_iff_harmonic :
    PrimorialWheelDirichletNonconcentration ↔
      PrimeWheelHarmonicNonconcentration primorialWheelFamily := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro k x hlower hupper
    let N := x - primorialBlockLower k
    have hNpos : 0 < N := by
      dsimp [N]
      exact Nat.sub_pos_of_lt hlower
    have hx : primorialBlockLower k + N = x := by
      dsimp [N]
      exact Nat.add_sub_of_le (Nat.le_of_lt hlower)
    have hNupper : primorialBlockLower k + N ≤ primorialBlockUpper k := by
      simpa [hx] using hupper
    have hD := hbound k N hNpos hNupper
    rw [← spectralPrefix_lower_add_eq_dirichletPrefix
      (primorialWheelSystem k) N hNupper] at hD
    simpa [primorialWheelFamily, primorialWheelSystem, hx] using hD
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro k N hNpos hupper
    have hlower :
        primorialBlockLower k < primorialBlockLower k + N := by omega
    have hH := hbound k (primorialBlockLower k + N) hlower hupper
    change
      ‖(primorialWheelSystem k).spectralPrefix
          ((primorialWheelSystem k).lower + N)‖ ^ 2 ≤
        C * Real.rpow
          ((((primorialWheelSystem k).lower + N) + 1 : ℕ) : ℝ) (1 + ε) at hH
    rw [spectralPrefix_lower_add_eq_dirichletPrefix
      (primorialWheelSystem k) N hupper] at hH
    simpa [primorialWheelSystem] using hH

end RHLean.Analysis
