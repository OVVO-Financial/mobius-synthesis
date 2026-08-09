import Mathlib
import RHLean.Analysis.MertensPowerGrowth

/-!
# The Mertens floor-step function for Abel and Mellin transforms

The ordered Dirichlet-series continuation is naturally expressed through the
step function `t ↦ M(floor t)`.  In Lean it is convenient to define the same
object directly as the finite Möbius sum over `Icc 1 floor(t)`.  This definition
vanishes automatically below `1`, is locally integrable on the positive real
axis, agrees exactly with the repository's `mertensSummatory`, and inherits the
pointwise power growth supplied by the Mertens energy criterion.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open Finset Set MeasureTheory

/-- Complex-valued Mertens step function on the reals.  The natural floor makes
it identically zero on `(-∞,1)`. -/
def mertensStep (t : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊t⌋₊, (((μ n : ℤ) : ℂ))

/-- The interval form of the finite Möbius sum agrees with the repository's
range-based Mertens summatory function. -/
theorem sum_Icc_one_moebius_eq_mertensSummatory (n : ℕ) :
    (∑ k ∈ Icc 1 n, (((μ k : ℤ) : ℂ))) = mertensSummatory n := by
  unfold mertensSummatory
  rw [Nat.range_succ_eq_Icc_zero]
  rw [← Finset.insert_Icc_add_one_left_eq_Icc n.zero_le,
    Finset.sum_insert (by aesop)]
  simp

/-- Hence the real step function is literally `M(floor t)`. -/
theorem mertensStep_eq_mertensSummatory_floor (t : ℝ) :
    mertensStep t = mertensSummatory ⌊t⌋₊ := by
  exact sum_Icc_one_moebius_eq_mertensSummatory ⌊t⌋₊

/-- Below one the natural floor is zero, so the Mertens step function vanishes. -/
theorem mertensStep_eq_zero_of_lt_one {t : ℝ} (ht : t < 1) :
    mertensStep t = 0 := by
  rw [mertensStep_eq_mertensSummatory_floor]
  rw [Nat.floor_eq_zero.mpr ht]
  exact mertensSummatory_zero

/-- The Mertens step function is locally integrable on the positive real axis.
This is the regularity input needed by the Mellin-transform API. -/
theorem mertensStep_locallyIntegrableOn :
    LocallyIntegrableOn mertensStep (Ioi 0) := by
  have hconst :
      LocallyIntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ici 0) :=
    continuous_const.continuousOn.locallyIntegrableOn measurableSet_Ici
  have hsum :=
    locallyIntegrableOn_mul_sum_Icc
      (c := fun n : ℕ => (((μ n : ℤ) : ℂ)))
      (m := 1) (a := 0) le_rfl hconst
  have hIci : LocallyIntegrableOn mertensStep (Ici 0) := by
    simpa [mertensStep] using hsum
  exact hIci.mono_set Set.Ioi_subset_Ici_self

/-- The Mertens energy criterion transfers directly to the floor-step function:
for every exponent `r > 1/2`, the step value at `t` is bounded at the natural
integer scale `floor(t)+1`.  This is the pointwise input for the later
at-infinity `O(t^r)` Mellin estimate. -/
theorem mertensStep_powerGrowth_of_energy
    (hM : MertensEnergyBoundedStatement) {r : ℝ}
    (hr : (1 : ℝ) / 2 < r) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ t : ℝ,
        ‖mertensStep t‖ ≤
          K * Real.rpow (((⌊t⌋₊ + 1 : ℕ) : ℝ)) r := by
  rcases mertensPowerGrowth_of_energy hM hr with ⟨K, hK, hbound⟩
  refine ⟨K, hK, ?_⟩
  intro t
  rw [mertensStep_eq_mertensSummatory_floor]
  exact hbound ⌊t⌋₊

end RHLean.Analysis
