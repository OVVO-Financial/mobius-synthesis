import Mathlib
import RHLean.Analysis.CanonicalLowOccupancy
import RHLean.Analysis.SquareWheelCenteredIncrement
import RHLean.Proof.DeathProcessArithmetic
import RHLean.Proof.DeathShellSubpolynomial
import RHLean.Proof.LifetimeEndpointDecomposition
import RHLean.Proof.SurvivorZeroMode

/-!
# Survivor increment inside the centered square-wheel response

The centered square-wheel theorem writes the protected nonzero-response
increment as

```text
Delta H = canonicalTotalIncrement - endpointDrift.
```

The lifetime architecture gives a second exact decomposition of the same square
block.  At any fixed height cutoff `Lambda`, the high prefix is birth mass, and
birth mass is current active survivor plus absorbed death mass.  Differentiating
that endpoint identity yields

```text
canonicalTotalIncrement
  = canonicalLowIncrement
    + Delta lifetimeActive
    + Delta lifetimeDeath.
```

For nonnegative `Lambda`, the active term is exactly the explicit survivor
zero-mode operator.  At the repository's concrete `Lambda = 16`, therefore,

```text
Delta H
  = (Delta survivorZeroMode - endpointDrift)
    + canonicalLowIncrement
    + Delta lifetimeDeath.
```

This is a strict localization of the analytic obstruction.  The low-height
increment has the repository's unconditional uniform occupancy control, and the
death process is handled by the existing subpolynomial death-shell theorem.
The final section inserts those two proved estimates and leaves the survivor
increment together with the rank-one wheel-end drift as the sole unresolved
local term.

No estimate for that survivor-centered term is assumed or proved here, and no
triangle inequality is applied to it.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- A cumulative canonical high prefix changes by exactly the high increment of
the newly appended square block. -/
theorem canonicalHighIncrement_eq_prefix_sub_pred
    (Λ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    canonicalHighIncrement Λ n =
      canonicalHighPrefix Λ n - canonicalHighPrefix Λ (n - 1) := by
  unfold canonicalHighPrefix
  rw [Nat.sub_add_cancel hn, Finset.sum_range_succ]
  ring

/-- Exact lifetime derivative of the canonical high increment: new high mass is
the change in current survivors plus the change in absorbed deaths. -/
theorem canonicalHighIncrement_eq_activeDiff_add_deathDiff
    (Λ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    canonicalHighIncrement Λ n =
      (lifetimeActiveAtomMass Λ n -
        lifetimeActiveAtomMass Λ (n - 1)) +
      (lifetimeDeathMass Λ n - lifetimeDeathMass Λ (n - 1)) := by
  calc
    canonicalHighIncrement Λ n =
        canonicalHighPrefix Λ n - canonicalHighPrefix Λ (n - 1) :=
      canonicalHighIncrement_eq_prefix_sub_pred Λ n hn
    _ = lifetimeBirthMass Λ n - lifetimeBirthMass Λ (n - 1) := by
      rw [lifetimeBirthMass_eq_canonicalHighPrefix,
        lifetimeBirthMass_eq_canonicalHighPrefix]
    _ =
        (lifetimeActiveAtomMass Λ n + lifetimeDeathMass Λ n) -
          (lifetimeActiveAtomMass Λ (n - 1) +
            lifetimeDeathMass Λ (n - 1)) := by
      rw [lifetimeBirthMass_eq_active_add_death,
        lifetimeBirthMass_eq_active_add_death]
    _ =
      (lifetimeActiveAtomMass Λ n -
        lifetimeActiveAtomMass Λ (n - 1)) +
      (lifetimeDeathMass Λ n - lifetimeDeathMass Λ (n - 1)) := by
        ring

/-- Exact low/survivor/death decomposition of one complete square-block
increment. -/
theorem canonicalTotalIncrement_eq_low_add_activeDiff_add_deathDiff
    (Λ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    canonicalTotalIncrement n =
      canonicalLowIncrement Λ n +
        (lifetimeActiveAtomMass Λ n -
          lifetimeActiveAtomMass Λ (n - 1)) +
        (lifetimeDeathMass Λ n - lifetimeDeathMass Λ (n - 1)) := by
  rw [canonicalTotalIncrement_eq_low_add_high Λ n,
    canonicalHighIncrement_eq_activeDiff_add_deathDiff Λ n hn]
  ring

/-- For nonnegative cutoff, replace the abstract active-survivor state by the
explicit signed survivor zero-mode operator. -/
theorem canonicalTotalIncrement_eq_low_add_survivorDiff_add_deathDiff
    (Λ : ℝ) (n : ℕ) (hn : 1 ≤ n) (hΛ : 0 ≤ Λ) :
    canonicalTotalIncrement n =
      canonicalLowIncrement Λ n +
        (survivorZeroMode Λ n - survivorZeroMode Λ (n - 1)) +
        (lifetimeDeathMass Λ n - lifetimeDeathMass Λ (n - 1)) := by
  rw [canonicalTotalIncrement_eq_low_add_activeDiff_add_deathDiff Λ n hn,
    lifetimeActiveAtomMass_eq_survivorZeroMode (Λ := Λ) hΛ n,
    lifetimeActiveAtomMass_eq_survivorZeroMode (Λ := Λ) hΛ (n - 1)]

/-- The genuinely hard local coordinate after removing the already-separated
low and death pieces: full survivor change minus the common rank-one wheel-end
drift. -/
def primorialMinimalSquareWheelSurvivorCenteredIncrement
    (k n : ℕ) : ℂ :=
  (survivorZeroMode 16 n - survivorZeroMode 16 (n - 1)) -
    primorialMinimalSquareWheelEndpointDrift k n

/-- **Centered `H` increment in lifetime coordinates.**  Within one primorial
block, the protected nonzero-response increment is the survivor-centered term
plus the low-height increment and the death-process increment. -/
theorem primorialMinimalSquareWheelNonzeroResponse_sub_pred_eq_survivorCentered_add_low_add_death
    (k n : ℕ) (hn : 1 ≤ n)
    (hleftLower :
      primorialBlockLower k < squarePrefixEndpoint (n - 1))
    (hleftUpper :
      squarePrefixEndpoint (n - 1) ≤ primorialBlockUpper k)
    (hrightUpper :
      squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n -
        squareWheelNonzeroSampleResponse
          (primorialMinimalWheelSystem k) (n - 1) =
      primorialMinimalSquareWheelSurvivorCenteredIncrement k n +
        canonicalLowIncrement 16 n +
        (lifetimeDeathMass 16 n - lifetimeDeathMass 16 (n - 1)) := by
  calc
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n -
        squareWheelNonzeroSampleResponse
          (primorialMinimalWheelSystem k) (n - 1) =
      canonicalTotalIncrement n -
        primorialMinimalSquareWheelEndpointDrift k n := by
          simpa [primorialMinimalSquareWheelCenteredIncrement] using
            primorialMinimalSquareWheelNonzeroResponse_sub_pred_eq_centeredIncrement
              k n hn hleftLower hleftUpper hrightUpper
    _ =
      (canonicalLowIncrement 16 n +
        (survivorZeroMode 16 n - survivorZeroMode 16 (n - 1)) +
        (lifetimeDeathMass 16 n - lifetimeDeathMass 16 (n - 1))) -
          primorialMinimalSquareWheelEndpointDrift k n := by
            rw [canonicalTotalIncrement_eq_low_add_survivorDiff_add_deathDiff
              16 n hn (by norm_num)]
    _ =
      primorialMinimalSquareWheelSurvivorCenteredIncrement k n +
        canonicalLowIncrement 16 n +
        (lifetimeDeathMass 16 n - lifetimeDeathMass 16 (n - 1)) := by
          unfold primorialMinimalSquareWheelSurvivorCenteredIncrement
          ring

/-- Removing the survivor-centered term leaves only the two pieces whose
analytic control is already separated elsewhere in the repository. -/
theorem norm_nonzeroResponseIncrement_sub_survivorCentered_le_low_add_death
    (k n : ℕ) (hn : 1 ≤ n)
    (hleftLower :
      primorialBlockLower k < squarePrefixEndpoint (n - 1))
    (hleftUpper :
      squarePrefixEndpoint (n - 1) ≤ primorialBlockUpper k)
    (hrightUpper :
      squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    ‖(squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n -
        squareWheelNonzeroSampleResponse
          (primorialMinimalWheelSystem k) (n - 1)) -
        primorialMinimalSquareWheelSurvivorCenteredIncrement k n‖ ≤
      ‖canonicalLowIncrement 16 n‖ +
        ‖lifetimeDeathMass 16 n - lifetimeDeathMass 16 (n - 1)‖ := by
  calc
    ‖(squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n -
        squareWheelNonzeroSampleResponse
          (primorialMinimalWheelSystem k) (n - 1)) -
        primorialMinimalSquareWheelSurvivorCenteredIncrement k n‖ =
      ‖canonicalLowIncrement 16 n +
        (lifetimeDeathMass 16 n - lifetimeDeathMass 16 (n - 1))‖ := by
          rw [primorialMinimalSquareWheelNonzeroResponse_sub_pred_eq_survivorCentered_add_low_add_death
            k n hn hleftLower hleftUpper hrightUpper]
          congr 1
          ring
    _ ≤ ‖canonicalLowIncrement 16 n‖ +
        ‖lifetimeDeathMass 16 n - lifetimeDeathMass 16 (n - 1)‖ :=
      norm_add_le _ _

/-- Any existing uniform low-height increment control can be inserted directly
without touching the survivor-centered sign structure. -/
theorem norm_nonzeroResponseIncrement_sub_survivorCentered_le_control_add_death
    (control : CanonicalLowIncrementControl 16)
    (k n : ℕ) (hn : 1 ≤ n)
    (hleftLower :
      primorialBlockLower k < squarePrefixEndpoint (n - 1))
    (hleftUpper :
      squarePrefixEndpoint (n - 1) ≤ primorialBlockUpper k)
    (hrightUpper :
      squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    ‖(squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n -
        squareWheelNonzeroSampleResponse
          (primorialMinimalWheelSystem k) (n - 1)) -
        primorialMinimalSquareWheelSurvivorCenteredIncrement k n‖ ≤
      control.bound +
        ‖lifetimeDeathMass 16 n - lifetimeDeathMass 16 (n - 1)‖ := by
  exact (norm_nonzeroResponseIncrement_sub_survivorCentered_le_low_add_death
    k n hn hleftLower hleftUpper hrightUpper).trans
      (add_le_add_right (control.norm_increment_le n) _)

/-- The predecessor death-mass difference is exactly the existing one-step
death increment. -/
theorem lifetimeDeathMass_sub_pred_eq_deathIncrement
    (Λ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    lifetimeDeathMass Λ n - lifetimeDeathMass Λ (n - 1) =
      lifetimeDeathIncrement Λ (n - 1) := by
  unfold lifetimeDeathIncrement
  rw [Nat.sub_add_cancel hn]

/-- **Unconditional localization to the survivor-centered term.**  At
`Lambda = 16`, all non-survivor pieces of one centered `H` increment are bounded
by an absolute constant `17` plus a subpolynomial death-shell error.  Thus the
survivor change minus the rank-one wheel-end drift is the sole unresolved local
term. -/
theorem norm_nonzeroResponseIncrement_sub_survivorCentered_subpolynomial
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ k n : ℕ, 1 ≤ n →
        primorialBlockLower k < squarePrefixEndpoint (n - 1) →
        squarePrefixEndpoint (n - 1) ≤ primorialBlockUpper k →
        squarePrefixEndpoint n ≤ primorialBlockUpper k →
        ‖(squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n -
            squareWheelNonzeroSampleResponse
              (primorialMinimalWheelSystem k) (n - 1)) -
            primorialMinimalSquareWheelSurvivorCenteredIncrement k n‖ ≤
          17 + C * Real.rpow (n : ℝ) ε := by
  rcases norm_lifetimeDeathIncrement_subpolynomial
      (Λ := (16 : ℝ)) (ε := ε) (by norm_num) hε with
    ⟨C, hC, hdeath⟩
  refine ⟨C, hC, ?_⟩
  intro k n hn hleftLower hleftUpper hrightUpper
  have hbase :=
    norm_nonzeroResponseIncrement_sub_survivorCentered_le_low_add_death
      k n hn hleftLower hleftUpper hrightUpper
  have hlow : ‖canonicalLowIncrement 16 n‖ ≤ (17 : ℝ) := by
    have h := norm_canonicalLowIncrement_le_floor_add_one (16 : ℝ) n
    norm_num at h ⊢
    exact h
  have hdeathAt := hdeath (n - 1)
  have hdeathBound :
      ‖lifetimeDeathMass 16 n - lifetimeDeathMass 16 (n - 1)‖ ≤
        C * Real.rpow (n : ℝ) ε := by
    rw [lifetimeDeathMass_sub_pred_eq_deathIncrement 16 n hn]
    have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
    simpa [hpred] using hdeathAt
  exact hbase.trans (add_le_add hlow hdeathBound)

end RHLean.Proof
