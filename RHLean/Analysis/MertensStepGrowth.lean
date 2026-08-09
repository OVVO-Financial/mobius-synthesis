import Mathlib
import RHLean.Analysis.MertensStepFunction

/-!
# Power growth of the Mertens step function

The pointwise `r > 1/2` Mertens bound is converted into the Landau form used by
Abel summation and Mellin transforms.  We first absorb the harmless `n + 1`
shift on the natural summatory function, then pass directly to the real
floor-step function.  Near zero the step function vanishes identically.
-/

noncomputable section

namespace RHLean.Analysis

open Filter Asymptotics Set

/-- The Mertens summatory function is `O(n^r)` on the naturals for every
`r > 1/2`. -/
theorem mertensSummatory_isBigO_rpow
    (hM : MertensEnergyBoundedStatement) {r : ℝ}
    (hr : (1 : ℝ) / 2 < r) :
    (fun n : ℕ => mertensSummatory n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by
  rcases mertensPowerGrowth_of_energy hM hr with ⟨K, hK, hbound⟩
  have hr0 : 0 ≤ r := by linarith
  refine IsBigO.of_bound (K * Real.rpow (2 : ℝ) r) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hshift : (((n + 1 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hrpow :
      Real.rpow (((n + 1 : ℕ) : ℝ)) r ≤
        Real.rpow (2 * (n : ℝ)) r :=
    Real.rpow_le_rpow (by positivity) hshift hr0
  have hmul :
      K * Real.rpow (((n + 1 : ℕ) : ℝ)) r ≤
        K * Real.rpow (2 * (n : ℝ)) r :=
    mul_le_mul_of_nonneg_left hrpow hK
  have hfactor :
      Real.rpow (2 * (n : ℕ) : ℝ) r =
        Real.rpow (2 : ℝ) r * Real.rpow (n : ℝ) r := by
    exact Real.mul_rpow (by positivity) (by positivity)
  calc
    ‖mertensSummatory n‖ ≤
        K * Real.rpow (((n + 1 : ℕ) : ℝ)) r := hbound n
    _ ≤ K * Real.rpow (2 * (n : ℝ)) r := hmul
    _ = (K * Real.rpow (2 : ℝ) r) * Real.rpow (n : ℝ) r := by
      rw [hfactor]
      ring
    _ = (K * Real.rpow (2 : ℝ) r) * ‖Real.rpow (n : ℝ) r‖ := by
      congr 1
      exact (abs_of_nonneg (Real.rpow_nonneg (by positivity) r)).symm

/-- The real floor-step Mertens function inherits the same power growth at
infinity.  This proof uses only the elementary bound `floor(t) + 1 ≤ 2t` for
`t ≥ 1`, avoiding any extra asymptotic floor API. -/
theorem mertensStep_isBigO_rpow_atTop
    (hM : MertensEnergyBoundedStatement) {r : ℝ}
    (hr : (1 : ℝ) / 2 < r) :
    mertensStep =O[atTop] (fun t : ℝ => t ^ r) := by
  rcases mertensPowerGrowth_of_energy hM hr with ⟨K, hK, hbound⟩
  have hr0 : 0 ≤ r := by linarith
  refine IsBigO.of_bound (K * Real.rpow (2 : ℝ) r) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 ≤ t := by linarith
  rw [mertensStep_eq_mertensSummatory_floor]
  have hfloor : (((⌊t⌋₊ : ℕ) : ℝ)) ≤ t :=
    Nat.floor_le ht0
  have hshift : ((((⌊t⌋₊ + 1 : ℕ) : ℝ))) ≤ 2 * t := by
    push_cast
    linarith
  have hrpow :
      Real.rpow ((((⌊t⌋₊ + 1 : ℕ) : ℝ))) r ≤
        Real.rpow (2 * t) r :=
    Real.rpow_le_rpow (by positivity) hshift hr0
  have hmul :
      K * Real.rpow ((((⌊t⌋₊ + 1 : ℕ) : ℝ))) r ≤
        K * Real.rpow (2 * t) r :=
    mul_le_mul_of_nonneg_left hrpow hK
  have hfactor :
      Real.rpow (2 * t) r =
        Real.rpow (2 : ℝ) r * Real.rpow t r :=
    Real.mul_rpow (by positivity) ht0
  calc
    ‖mertensSummatory ⌊t⌋₊‖ ≤
        K * Real.rpow ((((⌊t⌋₊ + 1 : ℕ) : ℝ))) r := hbound ⌊t⌋₊
    _ ≤ K * Real.rpow (2 * t) r := hmul
    _ = (K * Real.rpow (2 : ℝ) r) * Real.rpow t r := by
      rw [hfactor]
      ring
    _ = (K * Real.rpow (2 : ℝ) r) * ‖Real.rpow t r‖ := by
      congr 1
      exact (abs_of_nonneg (Real.rpow_nonneg ht0 r)).symm

/-- Near zero the Mertens step function is zero, hence it is `O(t^a)` for every
real exponent `a`. -/
theorem mertensStep_isBigO_rpow_zero (a : ℝ) :
    mertensStep =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun t : ℝ => t ^ a) := by
  refine IsBigO.of_bound 0 ?_
  have hIio : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) :=
    isOpen_Iio.mem_nhds (by norm_num)
  have hIio' : Set.Iio (1 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_nhdsWithin_of_mem_nhds hIio
  filter_upwards [hIio'] with t ht
  rw [mertensStep_eq_zero_of_lt_one ht]
  simp

end RHLean.Analysis
