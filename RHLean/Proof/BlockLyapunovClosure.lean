import Mathlib
import RHLean.Proof.ResonantLeakage

namespace RHLean.Analysis

/-- Nonnegative weights for the resonant and nonresonant components. -/
structure BlockLyapunovWeights where
  resonant : ℝ
  nonresonant : ℝ
  resonant_nonneg : 0 ≤ resonant
  nonresonant_nonneg : 0 ≤ nonresonant

/--
The weighted Lyapunov value of a separately typed resonant/nonresonant state.
The component size functions remain abstract so later number-theoretic layers can
instantiate them with the exact norms or energies that they prove contractive.
-/
def weightedBlockLyapunov
    {R N : Type*}
    (weights : BlockLyapunovWeights)
    (resonantSize : R → ℝ)
    (nonresonantSize : N → ℝ)
    (state : ResonantNonresonantState R N) : ℝ :=
  weights.resonant * resonantSize state.resonant +
    weights.nonresonant * nonresonantSize state.nonresonant

/-- Nonnegative component sizes give a nonnegative weighted Lyapunov value. -/
theorem weightedBlockLyapunov_nonneg
    {R N : Type*}
    (weights : BlockLyapunovWeights)
    (resonantSize : R → ℝ)
    (nonresonantSize : N → ℝ)
    (state : ResonantNonresonantState R N)
    (hresonant : 0 ≤ resonantSize state.resonant)
    (hnonresonant : 0 ≤ nonresonantSize state.nonresonant) :
    0 ≤ weightedBlockLyapunov weights resonantSize nonresonantSize state := by
  exact add_nonneg
    (mul_nonneg weights.resonant_nonneg hresonant)
    (mul_nonneg weights.nonresonant_nonneg hnonresonant)

/--
The invariant upper bound for an affine recurrence with contraction factor
`rho`, uniform forcing bound `forcingBound`, and initial-range bound `baseBound`.
-/
noncomputable def affineInvariantBound (rho forcingBound baseBound : ℝ) : ℝ :=
  max baseBound (forcingBound / (1 - rho))

/--
A descending affine recurrence with `0 ≤ rho < 1` and uniformly bounded forcing
stays below the explicit invariant bound. Every descent, base-range, contraction,
and forcing hypothesis is exposed. No number-theoretic input is used.
-/
theorem uniform_bound_of_affine_descent
    (ancestor : ℕ → ℕ)
    (value forcing : ℕ → ℝ)
    (N0 : ℕ)
    (rho forcingBound baseBound : ℝ)
    (hrho_nonneg : 0 ≤ rho)
    (hrho_lt_one : rho < 1)
    (hbase : ∀ n, n ≤ N0 → value n ≤ baseBound)
    (hdesc : ∀ n, N0 < n → ancestor n < n)
    (hcontract : ∀ n, N0 < n →
      value n ≤ rho * value (ancestor n) + forcing n)
    (hforcing : ∀ n, N0 < n → forcing n ≤ forcingBound) :
    ∀ n, value n ≤ affineInvariantBound rho forcingBound baseBound := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      by_cases hn : n ≤ N0
      · calc
          value n ≤ baseBound := hbase n hn
          _ ≤ affineInvariantBound rho forcingBound baseBound := by
            unfold affineInvariantBound
            exact le_max_left _ _
      · have hn_gt : N0 < n := by omega
        have hparent :
            value (ancestor n) ≤ affineInvariantBound rho forcingBound baseBound :=
          ih (ancestor n) (hdesc n hn_gt)
        have hstep :
            value n ≤
              rho * affineInvariantBound rho forcingBound baseBound + forcingBound := by
          calc
            value n ≤ rho * value (ancestor n) + forcing n := hcontract n hn_gt
            _ ≤ rho * affineInvariantBound rho forcingBound baseBound + forcingBound :=
              add_le_add
                (mul_le_mul_of_nonneg_left hparent hrho_nonneg)
                (hforcing n hn_gt)
        have hden : 0 < 1 - rho := by linarith
        have hquotient :
            forcingBound / (1 - rho) ≤
              affineInvariantBound rho forcingBound baseBound := by
          unfold affineInvariantBound
          exact le_max_right _ _
        have hinvariant :
            forcingBound ≤
              affineInvariantBound rho forcingBound baseBound * (1 - rho) :=
          (div_le_iff₀ hden).mp hquotient
        calc
          value n ≤
              rho * affineInvariantBound rho forcingBound baseBound + forcingBound := hstep
          _ ≤ affineInvariantBound rho forcingBound baseBound := by
            nlinarith

/--
Full weighted block contraction implies a uniform bound for the entire
resonant/nonresonant state. The leakage blocks may be nonzero; their combined
effect must already be included in the stated weighted contraction inequality.
-/
theorem uniform_bound_of_affine_block_contraction
    {R N : Type*}
    (weights : BlockLyapunovWeights)
    (resonantSize : R → ℝ)
    (nonresonantSize : N → ℝ)
    (ancestor : ℕ → ℕ)
    (state : ℕ → ResonantNonresonantState R N)
    (forcing : ℕ → ℝ)
    (N0 : ℕ)
    (rho forcingBound baseBound : ℝ)
    (hrho_nonneg : 0 ≤ rho)
    (hrho_lt_one : rho < 1)
    (hbase : ∀ n, n ≤ N0 →
      weightedBlockLyapunov weights resonantSize nonresonantSize (state n) ≤ baseBound)
    (hdesc : ∀ n, N0 < n → ancestor n < n)
    (hcontract : ∀ n, N0 < n →
      weightedBlockLyapunov weights resonantSize nonresonantSize (state n) ≤
        rho * weightedBlockLyapunov weights resonantSize nonresonantSize
          (state (ancestor n)) + forcing n)
    (hforcing : ∀ n, N0 < n → forcing n ≤ forcingBound) :
    ∀ n,
      weightedBlockLyapunov weights resonantSize nonresonantSize (state n) ≤
        affineInvariantBound rho forcingBound baseBound := by
  exact uniform_bound_of_affine_descent
    ancestor
    (fun n => weightedBlockLyapunov weights resonantSize nonresonantSize (state n))
    forcing N0 rho forcingBound baseBound hrho_nonneg hrho_lt_one
    hbase hdesc hcontract hforcing

/--
A decay-weighted forcing estimate closes the full block recurrence whenever the
decay factor is at most one and the forcing scale is nonnegative.
-/
theorem uniform_bound_of_decaying_affine_block_contraction
    {R N : Type*}
    (weights : BlockLyapunovWeights)
    (resonantSize : R → ℝ)
    (nonresonantSize : N → ℝ)
    (ancestor : ℕ → ℕ)
    (state : ℕ → ResonantNonresonantState R N)
    (forcing decay : ℕ → ℝ)
    (N0 : ℕ)
    (rho forcingScale baseBound : ℝ)
    (hrho_nonneg : 0 ≤ rho)
    (hrho_lt_one : rho < 1)
    (hforcingScale_nonneg : 0 ≤ forcingScale)
    (hbase : ∀ n, n ≤ N0 →
      weightedBlockLyapunov weights resonantSize nonresonantSize (state n) ≤ baseBound)
    (hdesc : ∀ n, N0 < n → ancestor n < n)
    (hcontract : ∀ n, N0 < n →
      weightedBlockLyapunov weights resonantSize nonresonantSize (state n) ≤
        rho * weightedBlockLyapunov weights resonantSize nonresonantSize
          (state (ancestor n)) + forcing n)
    (hforcing : ∀ n, N0 < n → forcing n ≤ forcingScale * decay n)
    (hdecay : ∀ n, N0 < n → decay n ≤ 1) :
    ∀ n,
      weightedBlockLyapunov weights resonantSize nonresonantSize (state n) ≤
        affineInvariantBound rho forcingScale baseBound := by
  have hforcingBound : ∀ n, N0 < n → forcing n ≤ forcingScale := by
    intro n hn
    calc
      forcing n ≤ forcingScale * decay n := hforcing n hn
      _ ≤ forcingScale * 1 :=
        mul_le_mul_of_nonneg_left (hdecay n hn) hforcingScale_nonneg
      _ = forcingScale := mul_one forcingScale
  exact uniform_bound_of_affine_block_contraction
    weights resonantSize nonresonantSize ancestor state forcing
    N0 rho forcingScale baseBound hrho_nonneg hrho_lt_one
    hbase hdesc hcontract hforcingBound

end RHLean.Analysis
