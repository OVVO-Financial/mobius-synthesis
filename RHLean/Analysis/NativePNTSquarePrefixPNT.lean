import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixCubic

/-!
# Full square-prefix Möbius rederivation of the Chebyshev PNT

This file closes the square-prefix contraction through the fully rederived
cubic sequence.  Its dependency path is:

* exact fresh-prime Möbius cancellation;
* exact `mu * log = Lambda` reciprocal-fibre reindexing;
* rederived one-log and squared Selberg recurrences;
* complete-square PNT1/PNT2 good-fibre supply;
* square-prefix quadratic good-mass density;
* rederived compensated affine contraction;
* explicit cubic iteration budget.

Thus the final normalized Chebyshev limit does not route through the
previous dyadic selector or previous compensated squared recurrence.
-/

noncomputable section

open Filter
open scoped Topology

namespace RHLean.Analysis

/-- Explicit number of fully rederived square-prefix cubic contractions
sufficient for target slope `eta`. -/
def nativePNTSquarePrefixFullIterationBudget (eta : ℝ) : ℕ :=
  ⌊6 / (nativePNTSquarePrefixRederivedCubicConstant * eta ^ 3)⌋₊ + 1

/-- The explicit square-prefix iteration budget satisfies the finite cubic
criterion. -/
theorem nativePNTSquarePrefixFullIterationBudget_spec
    (eta : ℝ) (heta : 0 < eta) :
    6 < nativePNTSquarePrefixRederivedCubicConstant *
        (nativePNTSquarePrefixFullIterationBudget eta : ℝ) * eta ^ 3 := by
  have hC : 0 < nativePNTSquarePrefixRederivedCubicConstant := by
    norm_num [nativePNTSquarePrefixRederivedCubicConstant]
  have hcoef : 0 < nativePNTSquarePrefixRederivedCubicConstant * eta ^ 3 :=
    mul_pos hC (pow_pos heta 3)
  have hfloor :
      6 / (nativePNTSquarePrefixRederivedCubicConstant * eta ^ 3) <
        (nativePNTSquarePrefixFullIterationBudget eta : ℝ) := by
    unfold nativePNTSquarePrefixFullIterationBudget
    push_cast
    simpa using
      (Nat.lt_floor_add_one
        (6 / (nativePNTSquarePrefixRederivedCubicConstant * eta ^ 3)))
  have hmul := (div_lt_iff₀ hcoef).mp hfloor
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Every positive target slope is attained by the fully rederived
square-prefix affine contraction, with an explicit finite iteration count. -/
theorem nativePNTSquarePrefixHasAffineEnvelope_arbitrarily_small
    (eta : ℝ) (heta : 0 < eta) :
    nativePNTHasAffineEnvelope eta := by
  exact nativePNTSquarePrefixRederivedHasAffineEnvelope_of_cubic_budget
    eta heta (nativePNTSquarePrefixFullIterationBudget eta)
      (nativePNTSquarePrefixFullIterationBudget_spec eta heta)

/-- Arbitrarily small square-prefix-derived affine slopes force the normalized
absolute Chebyshev error to zero. -/
theorem nativePNTSquarePrefixPNTError_abs_div_atTop_zero :
    Tendsto (fun N : ℕ => |nativePNTError N| / (N : ℝ)) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 0 < N by omega)
    have hnonneg : 0 ≤ |nativePNTError N| / (N : ℝ) :=
      div_nonneg (abs_nonneg _) hNpos.le
    linarith
  · intro b hb
    let eta : ℝ := b / 2
    have heta : 0 < eta := by
      dsimp [eta]
      positivity
    rcases nativePNTSquarePrefixHasAffineEnvelope_arbitrarily_small eta heta with
      ⟨D, hD, henv⟩
    obtain ⟨M : ℕ, hMnat⟩ := exists_nat_gt (D / eta)
    have hM : D / eta < (M : ℝ) := by exact_mod_cast hMnat
    filter_upwards [eventually_ge_atTop (max 1 M)] with N hN
    have hN1 : 1 ≤ N := (le_max_left 1 M).trans hN
    have hMN : M ≤ N := (le_max_right 1 M).trans hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 0 < N by omega)
    have hMNcast : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
    have hfrac : D / eta < (N : ℝ) := hM.trans_le hMNcast
    have hDlt : D < (N : ℝ) * eta :=
      (div_lt_iff₀ heta).mp hfrac
    have herr := henv N
    have hnum : |nativePNTError N| < b * (N : ℝ) := by
      dsimp [eta] at hDlt herr ⊢
      nlinarith
    rw [div_lt_iff₀ hNpos]
    exact hnum

/-- Signed normalized Chebyshev error tends to zero along the fully rederived
square-prefix route. -/
theorem nativePNTSquarePrefixPNTError_div_atTop_zero :
    Tendsto (fun N : ℕ => nativePNTError N / (N : ℝ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine nativePNTSquarePrefixPNTError_abs_div_atTop_zero.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  change |nativePNTError N| / (N : ℝ) = |nativePNTError N / (N : ℝ)|
  rw [abs_div, abs_of_nonneg hN0]

/-- **Fully rederived square-prefix Möbius Chebyshev PNT:**
`psi(N) / N -> 1`. -/
theorem nativePNTSquarePrefixPsi_div_atTop_one :
    Tendsto (fun N : ℕ => nativePsi N / (N : ℝ)) atTop (𝓝 1) := by
  have hsum : Tendsto
      (fun N : ℕ => nativePNTError N / (N : ℝ) + 1)
      atTop (𝓝 1) := by
    simpa using
      nativePNTSquarePrefixPNTError_div_atTop_zero.add tendsto_const_nhds
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  unfold nativePNTError
  field_simp [hNne]
  ring

end RHLean.Analysis
