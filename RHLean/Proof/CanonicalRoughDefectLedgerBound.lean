import Mathlib
import RHLean.Proof.CanonicalRoughCriticalDefectWindows
import RHLean.Proof.CanonicalRoughReciprocalCompression
import RHLean.Analysis.CanonicalLowOccupancy

/-!
# Signed defect ledger bound for the reciprocal Euler compression

`CanonicalRoughReciprocalCompression` proves the exact one-prime reciprocal
Euler law

```text
v_R(c) + v_R(c*p) = (1 - 1/p) * v_R(c) + mu(c)/(c*p) * (T + E - B),
```

where `T`, `E` and `B` are the order-threshold, top-escape and lower-root birth
boundaries of the fresh-prime move.  The three cardinalities there are exact but
completely unbounded, so the identity on its own produces no covariance
estimate.

This file supplies the missing global estimate.  Each of the three signed
channels injects into an explicit reciprocal window of natural numbers.  With
`X_R = R^2 - 1` the square-root endpoint:

```text
T  into  ((R-1)/c,     p],
E  into  (X_R/(p*c),   X_R/c],
B  into  ((R-1)/(p*c), (R-1)/c].
```

The three windows are exactly the arithmetic content of the three channels.  A
threshold loss is a partner below the newly adjoined prime; a top escape is a
partner in the reciprocal band that adjoining `p` pushes through the terminal
wall; a birth is a partner in the reciprocal band that adjoining `p` pulls up
across the root.  Hence the signed ledger obeys

```text
‖defect R c p‖ <= ledgerWindow R c p / (c*p).
```

Summing over the legal parents of a fresh prime turns the exact carrier-level
compression identity into a quantitative estimate: the reciprocal covariance
potential is bounded by the contracted parent mass, plus an explicit arithmetic
ledger, plus the still-unpaired survivor mass.

## What this bound is worth, and what it is not

The step from the three window cardinalities to a single ledger is a triangle
inequality, `‖T + E - B‖ <= T + E + B`, and that discards the Euler sign
structure the compression was built to preserve.  `boundary/dead_lanes.json`
records this route as one not to repeat: an unsigned count of surviving pairs
leaves `F^2` scale, and a capacity theorem has to be a signed identity or
recurrence taken *before* absolute values.  `CanonicalRoughCriticalDefectWindows`
declines the same step for the same reason.

So the ledger below is an honest global estimate on `T`, `E` and `B` -- the
first one in the development, and enough to turn the exact identities into
inequalities -- but it is not expected to reach the critical scale on its own,
and no claim that it does is made here.  What survives that objection is the
signed material it supports: the exact many-prime cube identity in
`CanonicalRoughManyPrimeContraction`, which is taken before any norm, and the
Euler product decay attached to it.

Nothing here is asymptotic and no analytic input is used.  Every bound is a
finite counting inequality followed by one triangle inequality.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughFreshPrimeDifference
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Numerator monotonicity of a quotient at a fixed positive denominator.  It is
proved here from `mul_le_mul_of_nonneg_right` so that none of the ledger
estimates below depends on the exact spelling of the ambient order-field
lemma. -/
private theorem reciprocalLedgerDivMono {a b N : ℝ} (h : a ≤ b) (hN : 0 < N) :
    a / N ≤ b / N := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos.mpr hN))

/-- Cancelling a nonzero factor against its own reciprocal weight. -/
private theorem reciprocalLedgerMulDivCancel {α : Type*} [Field α] {N : α} (hN : N ≠ 0)
    (a : α) : N * (a / N) = a := by
  rw [mul_comm N (a / N), div_mul_eq_mul_div, mul_div_assoc, div_self hN, mul_one]

/-- Reinstating a nonzero weight and its reciprocal. -/
private theorem reciprocalLedgerEqMulDiv {α : Type*} [Field α] {N : α} (hN : N ≠ 0)
    (a : α) : a = N * a / N := by
  rw [mul_comm N a, mul_div_assoc, div_self hN, mul_one]

/-! ## The three reciprocal windows

`CanonicalRoughCriticalDefectWindows` proves the three support inclusions

```text
T  into  ((R-1)/c,     p],
E  into  (X_R/(p*c),   X_R/c],
B  into  ((R-1)/(p*c), (R-1)/c],
```

and they are reused here rather than restated.  What this file adds on top of
them is the step from support to a count, and from a count to a norm. -/

/-! ## Cardinality of the three channels -/

/-- Order-threshold losses are at most the length of their reciprocal window. -/
theorem card_squareRootCanonicalRoughFreshThresholdLossBoundary_le
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    (squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card ≤ p - (R - 1) / c := by
  have h := Finset.card_le_card
    (squareRootCanonicalRoughFreshThresholdLossBoundary_subset_Ioc hR hc hp hfresh)
  rwa [Nat.card_Ioc] at h

/-- Genuine top escapes are at most the length of the reciprocal band that the
fresh prime removes from the terminal wall. -/
theorem card_squareRootCanonicalRoughFreshTopEscapeBoundary_le
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    (squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card ≤
      squareRootEndpoint R / c - squareRootEndpoint R / (p * c) := by
  have h := Finset.card_le_card
    (squareRootCanonicalRoughFreshTopEscapeBoundary_subset_Ioc hR hc hp hfresh)
  rwa [Nat.card_Ioc] at h

/-- Births are at most the length of the reciprocal band that the fresh prime
lifts across the root. -/
theorem card_squareRootCanonicalRoughFreshBirthBoundary_le
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    (squareRootCanonicalRoughFreshBirthBoundary R c p).card ≤
      (R - 1) / c - (R - 1) / (p * c) := by
  have h := Finset.card_le_card
    (squareRootCanonicalRoughFreshBirthBoundary_subset_Ioc hR hc hp hfresh)
  rwa [Nat.card_Ioc] at h

/-- **The signed defect ledger.**  Total reciprocal-window length available to
the three physical channels of one fresh-prime compression step. -/
def squareRootCanonicalRoughFreshPrimeLedgerWindow (R c p : ℕ) : ℕ :=
  (p - (R - 1) / c) +
    (squareRootEndpoint R / c - squareRootEndpoint R / (p * c)) +
    ((R - 1) / c - (R - 1) / (p * c))

/-- The three exact channel cardinalities are jointly bounded by the ledger. -/
theorem card_squareRootCanonicalRoughFreshPrimeChannels_le_ledgerWindow
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    (squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card +
        (squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card +
        (squareRootCanonicalRoughFreshBirthBoundary R c p).card ≤
      squareRootCanonicalRoughFreshPrimeLedgerWindow R c p :=
  Nat.add_le_add
    (Nat.add_le_add
      (card_squareRootCanonicalRoughFreshThresholdLossBoundary_le hR hc hp hfresh)
      (card_squareRootCanonicalRoughFreshTopEscapeBoundary_le hR hc hp hfresh))
    (card_squareRootCanonicalRoughFreshBirthBoundary_le hR hc hp hfresh)

/-- A coarse but completely explicit form of the ledger: one fresh prime plus
twice the reciprocal band of the parent. -/
theorem squareRootCanonicalRoughFreshPrimeLedgerWindow_le
    {R : ℕ} (hR : 2 ≤ R) (c p : ℕ) :
    squareRootCanonicalRoughFreshPrimeLedgerWindow R c p ≤
      p + 2 * (squareRootEndpoint R / c) := by
  have hle : R - 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : R ≤ R ^ 2 := by nlinarith
    omega
  have hdiv : (R - 1) / c ≤ squareRootEndpoint R / c := Nat.div_le_div_right hle
  unfold squareRootCanonicalRoughFreshPrimeLedgerWindow
  calc
    (p - (R - 1) / c) +
          (squareRootEndpoint R / c - squareRootEndpoint R / (p * c)) +
        ((R - 1) / c - (R - 1) / (p * c)) ≤
        p + squareRootEndpoint R / c + squareRootEndpoint R / c :=
      Nat.add_le_add (Nat.add_le_add (Nat.sub_le _ _) (Nat.sub_le _ _))
        (le_trans (Nat.sub_le _ _) hdiv)
    _ = p + 2 * (squareRootEndpoint R / c) := by ring

/-! ## The reciprocal-weighted defect estimate -/

/-- Norm of the signed ledger scalar `T + E - B`. -/
theorem norm_squareRootCanonicalRoughFreshPrimeSignedLedger_le
    (R c p : ℕ) :
    ‖((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℂ) +
        ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℂ) -
        ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)‖ ≤
      ((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℝ) +
        ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℝ) +
        ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℝ) := by
  refine le_trans (norm_sub_le _ _) ?_
  have hadd :
      ‖((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℂ) +
          ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℂ)‖ ≤
        ((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℝ) +
          ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℝ) := by
    refine le_trans (norm_add_le _ _) ?_
    simp
  have hbirth :
      ‖((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)‖ =
        ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℝ) := by
    simp
  rw [hbirth]
  linarith

/-- **Cleared form of the one-step defect estimate.**  Multiplying the
reciprocal defect by its own child cofactor removes every division, and what is
left is bounded by the three exact channel cardinalities. -/
theorem natCast_mul_norm_squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect_le
    {R c p : ℕ} (hc : 0 < c) (hp : 0 < p) :
    ((c * p : ℕ) : ℝ) *
        ‖squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p‖ ≤
      ((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℝ) +
        ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℝ) +
        ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℝ) := by
  have hNne : ((c * p : ℕ) : ℂ) ≠ 0 := by
    have hne : c * p ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hc) (Nat.ne_of_gt hp)
    exact_mod_cast hne
  have hkey :
      ((c * p : ℕ) : ℂ) *
          squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p =
        canonicalMoebiusWeight c *
          (((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℂ) +
            ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℂ) -
            ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)) := by
    unfold squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect
    rw [div_mul_eq_mul_div]
    exact reciprocalLedgerMulDivCancel hNne _
  have hnorm :
      ((c * p : ℕ) : ℝ) *
          ‖squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p‖ =
        ‖canonicalMoebiusWeight c *
          (((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℂ) +
            ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℂ) -
            ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ))‖ := by
    rw [← hkey, norm_mul, Complex.norm_natCast]
  rw [hnorm, norm_mul]
  calc
    ‖canonicalMoebiusWeight c‖ *
        ‖((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℂ) +
          ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)‖ ≤
        1 *
          (((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℝ) +
            ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℝ) +
            ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℝ)) := by
        refine mul_le_mul (norm_canonicalMoebiusWeight_le_one c)
          (norm_squareRootCanonicalRoughFreshPrimeSignedLedger_le R c p)
          (norm_nonneg _) (by norm_num)
    _ = ((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℝ) +
          ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℝ) +
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℝ) := one_mul _

/-- **The signed defect ledger bound.**  One reciprocal Euler compression step
leaves a defect of size at most the total reciprocal-window length divided by
the child cofactor.  This is the estimate the exact identity was missing. -/
theorem norm_squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect_le_ledgerWindow
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    ‖squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p‖ ≤
      (squareRootCanonicalRoughFreshPrimeLedgerWindow R c p : ℝ) / ((c * p : ℕ) : ℝ) := by
  have hNpos : (0 : ℝ) < ((c * p : ℕ) : ℝ) := by
    have hpos : 0 < c * p := Nat.mul_pos hc hp.pos
    exact_mod_cast hpos
  have hNne : ((c * p : ℕ) : ℝ) ≠ 0 := ne_of_gt hNpos
  have hcleared :=
    natCast_mul_norm_squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect_le
      (R := R) hc hp.pos
  have hledger :
      ((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℝ) +
          ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℝ) +
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℝ) ≤
        (squareRootCanonicalRoughFreshPrimeLedgerWindow R c p : ℝ) := by
    exact_mod_cast card_squareRootCanonicalRoughFreshPrimeChannels_le_ledgerWindow
      hR hc hp hfresh
  have hstep :
      ((c * p : ℕ) : ℝ) *
          ‖squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p‖ ≤
        (squareRootCanonicalRoughFreshPrimeLedgerWindow R c p : ℝ) :=
    le_trans hcleared hledger
  calc
    ‖squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p‖ =
        ((c * p : ℕ) : ℝ) *
            ‖squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p‖ /
          ((c * p : ℕ) : ℝ) := reciprocalLedgerEqMulDiv hNne _
    _ ≤ (squareRootCanonicalRoughFreshPrimeLedgerWindow R c p : ℝ) / ((c * p : ℕ) : ℝ) :=
        reciprocalLedgerDivMono hstep hNpos

/-! ## Global ledger on a whole active carrier -/

/-- Aggregate reciprocal ledger of one fresh prime on an active carrier. -/
def squareRootCanonicalRoughFreshPrimeReciprocalLedgerMass
    (R p : ℕ) (U : Finset ℕ) : ℝ :=
  ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
    (squareRootCanonicalRoughFreshPrimeLedgerWindow R c p : ℝ) / ((c * p : ℕ) : ℝ)

/-- **Global signed defect estimate.**  The complete reciprocal physical defect
generated by one fresh prime on any active carrier is bounded by the sum of the
per-parent reciprocal ledgers. -/
theorem norm_squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass_le
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (hR : 2 ≤ R) (hp : p.Prime) :
    ‖squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U‖ ≤
      squareRootCanonicalRoughFreshPrimeReciprocalLedgerMass R p U := by
  unfold squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass
    squareRootCanonicalRoughFreshPrimeReciprocalLedgerMass
  refine norm_sum_le_of_le _ ?_
  intro c hcParent
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
    ⟨_hcU, hcpos, hcrough, _hcchild⟩
  exact norm_squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect_le_ledgerWindow
    hR hcpos hp hcrough

/-- **Quantitative one-step reciprocal compression.**  This is the exact
carrier-level compression law of `CanonicalRoughReciprocalCompression` with its
defect term now genuinely estimated: the reciprocal covariance potential of an
active carrier is controlled by the contracted parent mass, an explicit finite
arithmetic ledger, and the still-unpaired survivor mass. -/
theorem norm_sum_squareRootCanonicalRoughResponseCenteredReciprocal_le_compressed_add_ledger
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (hR : 2 ≤ R) (hp : p.Prime) :
    ‖∑ n ∈ U, squareRootCanonicalRoughResponseCenteredReciprocalSummand R n‖ ≤
      ‖squareRootCanonicalRoughFreshPrimeReciprocalCompressedMass R p U‖ +
        squareRootCanonicalRoughFreshPrimeReciprocalLedgerMass R p U +
        ‖∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R n‖ := by
  rw [sum_squareRootCanonicalRoughResponseCenteredReciprocal_eq_compressed_add_defect_add_survivors
    R U hR hp]
  refine le_trans (norm_add_le _ _) ?_
  refine add_le_add ?_ le_rfl
  refine le_trans (norm_add_le _ _) ?_
  exact add_le_add le_rfl
    (norm_squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass_le R U hR hp)

end RHLean.Proof
