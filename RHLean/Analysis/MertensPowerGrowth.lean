import Mathlib
import RHLean.Analysis.SquarePrefixMertensBridge

/-!
# Unsquared Mertens power growth from the energy criterion

The repository's terminal arithmetic statement is naturally squared:

`‖M(x)‖^2 <= C * (x+1)^(1+epsilon)`.

For Mellin and Abel continuation it is more convenient to use an unsquared
power bound.  This file proves the exact elementary conversion needed later:
for every `r > 1/2`, the Mertens summatory function is bounded by a constant
times `(x+1)^r`.

No zeta-function input is used here.
-/

noncomputable section

namespace RHLean.Analysis

/-- The squared Mertens energy criterion implies ordinary pointwise power growth
at every exponent strictly larger than one half. -/
theorem mertensPowerGrowth_of_energy
    (hM : MertensEnergyBoundedStatement) {r : ℝ}
    (hr : (1 : ℝ) / 2 < r) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : ℕ,
        ‖mertensSummatory x‖ ≤
          K * Real.rpow ((x + 1 : ℕ) : ℝ) r := by
  let ε : ℝ := 2 * r - 1
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  rcases hM ε hε with ⟨C, hC, hbound⟩
  have hK : 0 ≤ C + 1 := by linarith
  refine ⟨C + 1, hK, ?_⟩
  intro x
  let z : ℝ := Real.rpow ((x + 1 : ℕ) : ℝ) r
  have hbase : 0 < ((x + 1 : ℕ) : ℝ) := by positivity
  have hz : 0 ≤ z := by
    dsimp [z]
    exact Real.rpow_nonneg (le_of_lt hbase) r
  have hpow :
      Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) = z ^ 2 := by
    calc
      Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) =
          Real.rpow ((x + 1 : ℕ) : ℝ) (r + r) := by
            congr 1
            dsimp [ε]
            ring
      _ = Real.rpow ((x + 1 : ℕ) : ℝ) r *
          Real.rpow ((x + 1 : ℕ) : ℝ) r :=
        Real.rpow_add hbase r r
      _ = z ^ 2 := by
        dsimp [z]
        ring
  have hsquare := hbound x
  rw [hpow] at hsquare
  have hcoeff : C ≤ (C + 1) ^ 2 := by
    nlinarith [sq_nonneg C]
  have hscaled : C * z ^ 2 ≤ (C + 1) ^ 2 * z ^ 2 :=
    mul_le_mul_of_nonneg_right hcoeff (sq_nonneg z)
  have htarget : 0 ≤ (C + 1) * z := mul_nonneg hK hz
  have hnorm : 0 ≤ ‖mertensSummatory x‖ := norm_nonneg _
  dsimp [z] at hsquare hscaled htarget ⊢
  nlinarith

end RHLean.Analysis
