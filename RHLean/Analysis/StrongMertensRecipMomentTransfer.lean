import Mathlib
import RHLean.Analysis.K2CenteredFinite
import RHLean.Analysis.NativePNTAxer
import RHLean.Analysis.NativePNTMobiusSecondMoment

/-!
# Finite Abel transfer from the Mertens summatory to the reciprocal moments

The strong Mertens contour stack ends at a bound on the Mertens summatory
function `M(N) = sum_{n <= N} mu(n)`, while the centered K2 argument consumes
the *reciprocal logarithmic* Mobius moments

  `A_m(N) = sum_{n <= N} mu(n) (log n)^m / n`,

of which `k2A2` is `A_2` and `k2C3` is `A_3`.  This module is the finite bridge
between the two.

Nothing here is asymptotic.  The Abel identity is exact for every `N`, and the
convergence statement takes the two analytic facts it needs -- summability of
the Abel increments and vanishing of the endpoint term -- as hypotheses.  Both
are what a Mertens decay estimate supplies: a bound

  `|M(x)| <= C x exp (-c (log x) ^ (1/10))`

dominates the increment `M(n) (w_m(n) - w_m(n+1))` by
`exp (-c (log n) ^ (1/10)) (log n)^m / n` and kills the endpoint term
`M(N) (log N)^m / N`.  Discharging them belongs to the analytic layer; keeping
them as hypotheses is what makes this bridge itself unconditional.

No prime number theorem or reciprocal-zeta estimate is used in this file.
-/

noncomputable section

open Filter Finset Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Reciprocal logarithmic weight of order `m`: the Abel weight against which
the Mertens summatory is transformed. -/
def k2LogRecipWeight (m n : ℕ) : ℝ := (Real.log (n : ℝ)) ^ m / (n : ℝ)

/-- Reciprocal logarithmic Mobius moment of order `m`. -/
def k2MobiusLogMoment (m N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ((μ n : ℤ) : ℝ) * k2LogRecipWeight m n

/-- The Abel increment of the reciprocal logarithmic weight, paired with the
Mertens summatory.  Absolute convergence of this series is the whole content of
the reciprocal-decay step. -/
def k2MertensAbelTerm (m n : ℕ) : ℝ :=
  nativeMertensSummatory n *
    (k2LogRecipWeight m n - k2LogRecipWeight m (n + 1))

theorem nativeMertensSummatory_zero : nativeMertensSummatory 0 = 0 := by
  have hempty : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  unfold nativeMertensSummatory
  rw [hempty, Finset.sum_empty]

theorem k2MertensAbelTerm_zero (m : ℕ) : k2MertensAbelTerm m 0 = 0 := by
  unfold k2MertensAbelTerm
  rw [nativeMertensSummatory_zero, zero_mul]

/-- The centered K2 second prefix is the order-two moment. -/
theorem k2A2_eq_moment (N : ℕ) : k2A2 N = k2MobiusLogMoment 2 N := by
  unfold k2A2 k2MobiusLogMoment k2LogRecipWeight nativeMobiusLogSquareRecipWeight
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [ArithmeticFunction.intCoe_apply, mul_div_assoc]

/-- The centered K2 third prefix is the order-three moment. -/
theorem k2C3_eq_moment (N : ℕ) : k2C3 N = k2MobiusLogMoment 3 N := by
  unfold k2C3 k2MobiusLogMoment k2LogRecipWeight nativeMobiusLogSquareRecipWeight
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [ArithmeticFunction.intCoe_apply]
  ring

/-- **Finite Abel transfer.**  Every reciprocal logarithmic Mobius moment is
determined by the Mertens summatory function, exactly and for every `N`. -/
theorem k2MobiusLogMoment_abel (m N : ℕ) :
    k2MobiusLogMoment m N =
      nativeMertensSummatory N * k2LogRecipWeight m N +
        ∑ n ∈ Finset.Ico 1 N, k2MertensAbelTerm m n :=
  nativeAbelIccOne (fun n => ((μ n : ℤ) : ℝ)) (k2LogRecipWeight m) N

/-- The Abel tail over `Ico 1 N` is the tail over `range N`: the only extra
term is the empty Mertens prefix, which vanishes. -/
theorem k2MertensAbelTerm_sum_Ico_eq_range (m N : ℕ) :
    ∑ n ∈ Finset.Ico 1 N, k2MertensAbelTerm m n =
      ∑ n ∈ Finset.range N, k2MertensAbelTerm m n := by
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    rw [Finset.mem_Ico] at hx
    exact Finset.mem_range.mpr hx.2
  · intro x hx hnot
    rw [Finset.mem_range] at hx
    rw [Finset.mem_Ico] at hnot
    have hx0 : x = 0 := by omega
    rw [hx0, k2MertensAbelTerm_zero]

/-- **Reciprocal moment convergence.**  Once the Abel increments are summable
and the endpoint term vanishes, the reciprocal logarithmic Mobius moment
converges, with the Abel series as its limit. -/
theorem k2MobiusLogMoment_tendsto_of_summable (m : ℕ)
    (hsum : Summable (k2MertensAbelTerm m))
    (hend : Tendsto
      (fun N : ℕ => nativeMertensSummatory N * k2LogRecipWeight m N)
      atTop (𝓝 0)) :
    Tendsto (k2MobiusLogMoment m) atTop
      (𝓝 (∑' n : ℕ, k2MertensAbelTerm m n)) := by
  have htail : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, k2MertensAbelTerm m n)
      atTop (𝓝 (∑' n : ℕ, k2MertensAbelTerm m n)) :=
    hsum.hasSum.tendsto_sum_nat
  have hcombined := hend.add htail
  rw [zero_add] at hcombined
  refine hcombined.congr fun N => ?_
  rw [k2MobiusLogMoment_abel, k2MertensAbelTerm_sum_Ico_eq_range]

/-- The order-three moment converges: the `c3_tendsto` field of
`K2ClassicalMomentInput`. -/
theorem k2C3_tendsto_of_summable
    (hsum : Summable (k2MertensAbelTerm 3))
    (hend : Tendsto
      (fun N : ℕ => nativeMertensSummatory N * k2LogRecipWeight 3 N)
      atTop (𝓝 0)) :
    ∃ L : ℝ, Tendsto k2C3 atTop (𝓝 L) :=
  ⟨_, (k2MobiusLogMoment_tendsto_of_summable 3 hsum hend).congr
    fun N => (k2C3_eq_moment N).symm⟩

/-- The centered second prefix converges to `A_2(infinity) + 2 gamma`.

Identifying that limit as zero -- equivalently `A_2(infinity) = -2 gamma`, read
off the Laurent expansion of `1 / zeta` at one -- is the remaining analytic
input of the centered K2 route; it is what turns this into the
`r_tendsto_zero` field of `K2ClassicalMomentInput`. -/
theorem k2r_tendsto_of_summable
    (hsum : Summable (k2MertensAbelTerm 2))
    (hend : Tendsto
      (fun N : ℕ => nativeMertensSummatory N * k2LogRecipWeight 2 N)
      atTop (𝓝 0)) :
    Tendsto k2r atTop
      (𝓝 ((∑' n : ℕ, k2MertensAbelTerm 2 n) +
        2 * Real.eulerMascheroniConstant)) := by
  have h2 : Tendsto k2A2 atTop (𝓝 (∑' n : ℕ, k2MertensAbelTerm 2 n)) :=
    (k2MobiusLogMoment_tendsto_of_summable 2 hsum hend).congr
      fun N => (k2A2_eq_moment N).symm
  exact h2.add_const (2 * Real.eulerMascheroniConstant)

end RHLean.Analysis
