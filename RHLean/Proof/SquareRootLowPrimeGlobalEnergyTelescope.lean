import Mathlib
import RHLean.Proof.SquareRootLowPrimeRunningTelescope

/-!
# Exact global energy telescope for the low-prime sequential state

The local ordered energy identity is

`T(p-1)^2 - T(p)^2 = 2*T(p-1)*Delta_p - Delta_p^2`

at every prime `p`.  The running-state telescope already proves that composite
cutoffs contribute no change.  Therefore the quadratic energy also telescopes
exactly over an entire fresh-prime interval:

`sum_{K<p<=U, p prime} (2*T(p-1)*Delta_p - Delta_p^2)
  = T(K)^2 - T(U)^2`.

This is an exact identity, not a quantitative estimate.  In particular, a
global energy decrement lower bound

`sum_p (...) >= T(K)^2 - B`

is equivalent to the terminal square bound `T(U)^2 <= B`.  Thus a genuinely
independent energy proof must establish dissipation before invoking the endpoint
bound; merely assuming terminal control and rewriting this identity does not
cross the quantitative gate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- **Exact global quadratic energy telescope.**  Composite arithmetic cutoffs
have zero running-state step, while each prime cutoff contributes the exact
local quadratic decrement. -/
theorem squareRootLowPrimeGlobalEnergyTelescope
    {R K j U : ℕ} (hK : 1 ≤ K) (hKU : K ≤ U) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
      (2 * squareRootLowPrimeRunningImbalanceReal R K j (p - 1) *
          squareRootLowPrimeFreshIncrementReal R K j p -
        squareRootLowPrimeFreshIncrementReal R K j p ^ 2)) =
      squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        squareRootLowPrimeRunningImbalanceReal R K j U ^ 2 := by
  have htelescope := real_pred_sub_telescope_Ioc
    (fun p => squareRootLowPrimeRunningImbalanceReal R K j p ^ 2) hKU
  calc
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
      (2 * squareRootLowPrimeRunningImbalanceReal R K j (p - 1) *
          squareRootLowPrimeFreshIncrementReal R K j p -
        squareRootLowPrimeFreshIncrementReal R K j p ^ 2)) =
      ∑ p ∈ Finset.Ioc K U,
        if p.Prime then
          (2 * squareRootLowPrimeRunningImbalanceReal R K j (p - 1) *
              squareRootLowPrimeFreshIncrementReal R K j p -
            squareRootLowPrimeFreshIncrementReal R K j p ^ 2)
        else 0 := by
          unfold squareRootLowPrimeFreshPrimeSet
          rw [Finset.sum_filter]
    _ = ∑ p ∈ Finset.Ioc K U,
        (squareRootLowPrimeRunningImbalanceReal R K j (p - 1) ^ 2 -
          squareRootLowPrimeRunningImbalanceReal R K j p ^ 2) := by
      apply Finset.sum_congr rfl
      intro p hpIoc
      have hpGt : 1 < p := by
        have hKp := (Finset.mem_Ioc.mp hpIoc).1
        omega
      by_cases hpPrime : p.Prime
      · rw [if_pos hpPrime]
        exact
          (squareRootLowPrimeRunningEnergyReal_step R K j p hpPrime).symm
      · rw [if_neg hpPrime,
          squareRootLowPrimeRunningImbalanceReal_eq_pred_of_not_prime
            R K j p hpGt hpPrime]
        ring
    _ = squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        squareRootLowPrimeRunningImbalanceReal R K j U ^ 2 := htelescope

/-- A global energy lower bound is exactly the corresponding terminal square
bound.  This theorem is deliberately an equivalence so an endpoint assumption
cannot be mistaken for an independent dissipation estimate. -/
theorem squareRootLowPrimeGlobalEnergyDecrement_ge_iff_terminal_sq_le
    {R K j U : ℕ} (B : ℝ) (hK : 1 ≤ K) (hKU : K ≤ U) :
    ((∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        (2 * squareRootLowPrimeRunningImbalanceReal R K j (p - 1) *
            squareRootLowPrimeFreshIncrementReal R K j p -
          squareRootLowPrimeFreshIncrementReal R K j p ^ 2)) ≥
        squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 - B) ↔
      squareRootLowPrimeRunningImbalanceReal R K j U ^ 2 ≤ B := by
  rw [squareRootLowPrimeGlobalEnergyTelescope hK hKU]
  constructor <;> intro h <;> linarith

/-- One-way convenience form of the exact equivalence. -/
theorem squareRootLowPrimeGlobalEnergyDecrement_ge_of_terminal_sq_le
    {R K j U : ℕ} (B : ℝ) (hK : 1 ≤ K) (hKU : K ≤ U)
    (hterminal : squareRootLowPrimeRunningImbalanceReal R K j U ^ 2 ≤ B) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
      (2 * squareRootLowPrimeRunningImbalanceReal R K j (p - 1) *
          squareRootLowPrimeFreshIncrementReal R K j p -
        squareRootLowPrimeFreshIncrementReal R K j p ^ 2)) ≥
      squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 - B := by
  exact
    (squareRootLowPrimeGlobalEnergyDecrement_ge_iff_terminal_sq_le
      B hK hKU).2 hterminal

end RHLean.Proof
