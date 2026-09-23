import RHLean.Proof.SquareRootLowPrimeTSectorQ2Renormalization

/-!
# Exact restricted-owner energy budgets

The complete interior owner schedule under investigation is `{3,5,7}`.  Its
square-scale budget is `1891/11025`; replacing it by the unit budget discards
most of the available margin.  Unequal channel coefficients are admissible
precisely when the sufficient induction budget

`alpha3/9 + alpha5/25 + alpha7/49 < 1`

holds.  This file keeps the three coefficients separate and proves the resulting
linear envelope, with the exact constant `C/(1-beta)`.

These are conditional induction and finite algebra theorems.  No physical
packet estimate, recovery identity, or arithmetic cancellation theorem is
asserted.  In every application the energy must still retain its signed
`F-T` state; the scalar recurrence remains an explicit hypothesis.

The last section optimizes the three-channel Cauchy step.  The resulting
reciprocal-amplitude criterion is sharper than a factor-three estimate.  Its
exact numerical audit also records that local frame loss four followed only
by arbitrary owner alignment still exceeds the available margin.
-/

noncomputable section

namespace RHLean.Proof

/-- The literal square-scale budget of the three exceptional owners. -/
def exceptionalOwnerEnergyBudget (alpha3 alpha5 alpha7 : ℚ) : ℚ :=
  alpha3 / 9 + alpha5 / 25 + alpha7 / 49

/-- The required arithmetic recurrence, with its signed energy left abstract. -/
def ExceptionalOwnerEnergyStep
    (E : ℕ → ℚ) (C alpha3 alpha5 alpha7 : ℚ) : Prop :=
  ∀ X : ℕ, E X ≤ C * (X : ℚ) +
    alpha3 * E (X / 9) + alpha5 * E (X / 25) + alpha7 * E (X / 49)

private theorem exceptionalOwner_natCast_div_le
    (X d : ℕ) (hd : 0 < d) :
    ((X / d : ℕ) : ℚ) ≤ (X : ℚ) / (d : ℚ) := by
  apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℚ) < (d : ℚ))).2
  exact_mod_cast Nat.div_mul_le_self X d

/-- **Restricted fixed-point induction.**  Only the weighted daughter budget,
not any individual channel coefficient, must fit the linear envelope.  The
zero value is explicit because all three fixed owners remain in the recurrence
at `X=0`. -/
theorem exceptionalOwnerEnergyStep_implies_linear_of_fixedPointBudget
    {E : ℕ → ℚ} {C alpha3 alpha5 alpha7 K : ℚ}
    (hzero : E 0 = 0) (hK : 0 ≤ K)
    (h3 : 0 ≤ alpha3) (h5 : 0 ≤ alpha5) (h7 : 0 ≤ alpha7)
    (hfixed : C + exceptionalOwnerEnergyBudget alpha3 alpha5 alpha7 * K ≤ K)
    (hstep : ExceptionalOwnerEnergyStep E C alpha3 alpha5 alpha7) :
    ∀ X : ℕ, E X ≤ K * (X : ℚ) := by
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
    by_cases hX : X = 0
    · subst X
      simp [hzero]
    · have hXpos : 0 < X := Nat.pos_of_ne_zero hX
      have hchild {d : ℕ} (hd : 1 < d) :
          E (X / d) ≤ K * ((X : ℚ) / (d : ℚ)) := by
        have hind := ih (X / d) (Nat.div_lt_self hXpos hd)
        exact hind.trans (mul_le_mul_of_nonneg_left
          (exceptionalOwner_natCast_div_le X d (by omega)) hK)
      have hw3 := mul_le_mul_of_nonneg_left (hchild (d := 9) (by norm_num)) h3
      have hw5 := mul_le_mul_of_nonneg_left (hchild (d := 25) (by norm_num)) h5
      have hw7 := mul_le_mul_of_nonneg_left (hchild (d := 49) (by norm_num)) h7
      calc
        E X ≤ C * (X : ℚ) + alpha3 * E (X / 9) +
            alpha5 * E (X / 25) + alpha7 * E (X / 49) := hstep X
        _ ≤ C * (X : ℚ) + alpha3 * (K * ((X : ℚ) / 9)) +
            alpha5 * (K * ((X : ℚ) / 25)) +
            alpha7 * (K * ((X : ℚ) / 49)) := by
          exact add_le_add (add_le_add (add_le_add_left hw3 _) hw5) hw7
        _ = (C + exceptionalOwnerEnergyBudget alpha3 alpha5 alpha7 * K) *
            (X : ℚ) := by
          unfold exceptionalOwnerEnergyBudget
          ring
        _ ≤ K * (X : ℚ) :=
          mul_le_mul_of_nonneg_right hfixed (by positivity)

/-- **Full restricted margin.**  The explicit sufficient criterion is
`beta < 1`, yielding the linear constant `C/(1-beta)`.  This does not supply
the physical recurrence assumed in `hstep`. -/
theorem exceptionalOwnerEnergyStep_implies_linear
    {E : ℕ → ℚ} {C alpha3 alpha5 alpha7 : ℚ}
    (hzero : E 0 = 0) (hC : 0 ≤ C)
    (h3 : 0 ≤ alpha3) (h5 : 0 ≤ alpha5) (h7 : 0 ≤ alpha7)
    (hbudget : exceptionalOwnerEnergyBudget alpha3 alpha5 alpha7 < 1)
    (hstep : ExceptionalOwnerEnergyStep E C alpha3 alpha5 alpha7) :
    ∀ X : ℕ, E X ≤
      (C / (1 - exceptionalOwnerEnergyBudget alpha3 alpha5 alpha7)) * (X : ℚ) := by
  have hden : 0 < 1 - exceptionalOwnerEnergyBudget alpha3 alpha5 alpha7 := by
    linarith
  apply exceptionalOwnerEnergyStep_implies_linear_of_fixedPointBudget hzero
    (div_nonneg hC (le_of_lt hden)) h3 h5 h7 ?_ hstep
  apply le_of_eq
  field_simp [ne_of_gt hden]
  ring

/-- Exact common-coefficient budget. -/
theorem exceptionalOwnerEnergyBudget_common (alpha : ℚ) :
    exceptionalOwnerEnergyBudget alpha alpha alpha = (1891 : ℚ) / 11025 * alpha := by
  unfold exceptionalOwnerEnergyBudget
  ring

/-- The common energy coefficient may be as large as `11025/1891`, strictly. -/
theorem exceptionalOwnerEnergyBudget_common_lt_one_iff (alpha : ℚ) :
    exceptionalOwnerEnergyBudget alpha alpha alpha < 1 ↔
      alpha < (11025 : ℚ) / 1891 := by
  rw [exceptionalOwnerEnergyBudget_common]
  constructor <;> intro h <;> linarith

/-- Eight units of frame loss after the exact `11` factor still fit the
restricted daughter schedule.  This is a numerical budget, not a physical
frame estimate. -/
theorem exceptionalOwner_eightFrame_budget :
    exceptionalOwnerEnergyBudget
      (8 * elevenWeightOneEnergyFactor) (8 * elevenWeightOneEnergyFactor)
      (8 * elevenWeightOneEnergyFactor) = (5461208 : ℚ) / 5832225 := by
  rw [exceptionalOwnerEnergyBudget_common, elevenWeightOneEnergyFactor_eq]
  norm_num

theorem exceptionalOwner_eightFrame_budget_lt_one :
    exceptionalOwnerEnergyBudget
      (8 * elevenWeightOneEnergyFactor) (8 * elevenWeightOneEnergyFactor)
      (8 * elevenWeightOneEnergyFactor) < 1 := by
  rw [exceptionalOwner_eightFrame_budget]
  norm_num

/-- A local factor four followed by factor-three owner Cauchy costs twelve;
even the exact restricted schedule does not absorb that numerical loss. -/
theorem exceptionalOwner_fourFrame_threeOwner_budget_gt_one :
    1 < exceptionalOwnerEnergyBudget
      (12 * elevenWeightOneEnergyFactor) (12 * elevenWeightOneEnergyFactor)
      (12 * elevenWeightOneEnergyFactor) := by
  rw [exceptionalOwnerEnergyBudget_common, elevenWeightOneEnergyFactor_eq]
  norm_num

/-- Scale-aware synthesis depends on the sum of reciprocal amplitude gains. -/
def exceptionalOwnerAmplitudeBudget (a3 a5 a7 : ℚ) : ℚ :=
  a3 / 3 + a5 / 5 + a7 / 7

/-- Weighted three-channel Cauchy, keeping each input as a whole signed scalar.
The proof is a finite sum of three nonnegative squares. -/
theorem exceptionalOwner_weighted_synthesis_sq_le
    {a3 a5 a7 : ℚ} (h3 : 0 ≤ a3) (h5 : 0 ≤ a5) (h7 : 0 ≤ a7)
    (u3 u5 u7 : ℚ) :
    (a3 * u3 + a5 * u5 + a7 * u7) ^ 2 ≤
      exceptionalOwnerAmplitudeBudget a3 a5 a7 *
        (3 * a3 * u3 ^ 2 + 5 * a5 * u5 ^ 2 + 7 * a7 * u7 ^ 2) := by
  have h35 := mul_nonneg (mul_nonneg h3 h5) (sq_nonneg (3 * u3 - 5 * u5))
  have h37 := mul_nonneg (mul_nonneg h3 h7) (sq_nonneg (3 * u3 - 7 * u7))
  have h57 := mul_nonneg (mul_nonneg h5 h7) (sq_nonneg (5 * u5 - 7 * u7))
  unfold exceptionalOwnerAmplitudeBudget
  nlinarith

/-- The scale-aware Cauchy coefficients consume exactly the square of the
reciprocal-amplitude budget. -/
theorem exceptionalOwner_weighted_synthesis_budget (a3 a5 a7 : ℚ) :
    exceptionalOwnerEnergyBudget
      (exceptionalOwnerAmplitudeBudget a3 a5 a7 * (3 * a3))
      (exceptionalOwnerAmplitudeBudget a3 a5 a7 * (5 * a5))
      (exceptionalOwnerAmplitudeBudget a3 a5 a7 * (7 * a7)) =
      (exceptionalOwnerAmplitudeBudget a3 a5 a7) ^ 2 := by
  unfold exceptionalOwnerEnergyBudget exceptionalOwnerAmplitudeBudget
  ring

/-- **Scale-aware conditional synthesis closure.**  Given three complete
signed channel states with daughter energy bounds, the sufficient condition is
`a3/3 + a5/5 + a7/7 < 1`.  Neither these daughter bounds nor the physical
decomposition is proved here. -/
theorem exceptionalOwner_weighted_synthesis_implies_linear
    {E u3 u5 u7 : ℕ → ℚ} {C a3 a5 a7 : ℚ}
    (hzero : E 0 = 0) (hC : 0 ≤ C)
    (h3 : 0 ≤ a3) (h5 : 0 ≤ a5) (h7 : 0 ≤ a7)
    (hbudget : exceptionalOwnerAmplitudeBudget a3 a5 a7 < 1)
    (hdecomp : ∀ X, E X ≤ C * (X : ℚ) +
      (a3 * u3 X + a5 * u5 X + a7 * u7 X) ^ 2)
    (hu3 : ∀ X, (u3 X) ^ 2 ≤ E (X / 9))
    (hu5 : ∀ X, (u5 X) ^ 2 ≤ E (X / 25))
    (hu7 : ∀ X, (u7 X) ^ 2 ≤ E (X / 49)) :
    ∀ X : ℕ, E X ≤
      (C / (1 - (exceptionalOwnerAmplitudeBudget a3 a5 a7) ^ 2)) * (X : ℚ) := by
  have hg0 : 0 ≤ exceptionalOwnerAmplitudeBudget a3 a5 a7 := by
    unfold exceptionalOwnerAmplitudeBudget
    positivity
  have hg2 : (exceptionalOwnerAmplitudeBudget a3 a5 a7) ^ 2 < 1 := by
    nlinarith
  have hstep : ExceptionalOwnerEnergyStep E C
      (exceptionalOwnerAmplitudeBudget a3 a5 a7 * (3 * a3))
      (exceptionalOwnerAmplitudeBudget a3 a5 a7 * (5 * a5))
      (exceptionalOwnerAmplitudeBudget a3 a5 a7 * (7 * a7)) := by
    intro X
    have hs := exceptionalOwner_weighted_synthesis_sq_le h3 h5 h7
      (u3 X) (u5 X) (u7 X)
    have hsum := add_le_add
      (add_le_add
        (mul_le_mul_of_nonneg_left (hu3 X) (by positivity : 0 ≤ 3 * a3))
        (mul_le_mul_of_nonneg_left (hu5 X) (by positivity : 0 ≤ 5 * a5)))
      (mul_le_mul_of_nonneg_left (hu7 X) (by positivity : 0 ≤ 7 * a7))
    have hw := mul_le_mul_of_nonneg_left hsum hg0
    have hd := hdecomp X
    nlinarith
  have h := exceptionalOwnerEnergyStep_implies_linear hzero hC
    (mul_nonneg hg0 (by positivity)) (mul_nonneg hg0 (by positivity))
    (mul_nonneg hg0 (by positivity))
    (by rw [exceptionalOwner_weighted_synthesis_budget]; exact hg2) hstep
  simpa only [exceptionalOwner_weighted_synthesis_budget] using h

/-- The scale-aware Cauchy bound is attained by the reciprocal-owner vector;
the displayed equality uses arbitrary amplitude gains. -/
theorem exceptionalOwner_weighted_synthesis_equality (a3 a5 a7 : ℚ) :
    (a3 * ((1 : ℚ) / 3) + a5 * ((1 : ℚ) / 5) + a7 * ((1 : ℚ) / 7)) ^ 2 =
      exceptionalOwnerAmplitudeBudget a3 a5 a7 *
        (3 * a3 * ((1 : ℚ) / 3) ^ 2 +
         5 * a5 * ((1 : ℚ) / 5) ^ 2 +
         7 * a7 * ((1 : ℚ) / 7) ^ 2) := by
  unfold exceptionalOwnerAmplitudeBudget
  ring

/-- Even optimized arbitrary-alignment Cauchy does not absorb local frame
factor four and the `19/23` amplitude.  Actual arithmetic Gram cancellation
could improve it; this is only an obstruction to that generic estimate. -/
theorem exceptionalOwner_fourFrame_weighted_budget_gt_one :
    1 < (exceptionalOwnerAmplitudeBudget
      ((2 : ℚ) * (19 / 23)) (2 * (19 / 23)) (2 * (19 / 23))) ^ 2 := by
  norm_num [exceptionalOwnerAmplitudeBudget]

/-- A numerical interpolation between diagonal and coherent energy budgets.
To use this number, the actual arithmetic must bound its aggregate signed
cross-energy by the corresponding fraction `rho` of the coherent comparison.
No pairwise sign condition or physical Gram estimate is asserted here. -/
def exceptionalOwnerCorrelationEnergyBudget (rho : ℚ) : ℚ :=
  4 * elevenWeightOneEnergyFactor *
    ((1 - rho) * exceptionalOwnerEnergyBudget 1 1 1 +
      rho * (exceptionalOwnerAmplitudeBudget 1 1 1) ^ 2)

/-- The interpolated budget has explicit unequal channel coefficients, ready
for the restricted induction once an arithmetic estimate supplies them. -/
theorem exceptionalOwnerCorrelationEnergyBudget_eq_channelBudget (rho : ℚ) :
    exceptionalOwnerCorrelationEnergyBudget rho =
      exceptionalOwnerEnergyBudget
        (4 * elevenWeightOneEnergyFactor *
          ((1 - rho) + rho * 3 * exceptionalOwnerAmplitudeBudget 1 1 1))
        (4 * elevenWeightOneEnergyFactor *
          ((1 - rho) + rho * 5 * exceptionalOwnerAmplitudeBudget 1 1 1))
        (4 * elevenWeightOneEnergyFactor *
          ((1 - rho) + rho * 7 * exceptionalOwnerAmplitudeBudget 1 1 1)) := by
  unfold exceptionalOwnerCorrelationEnergyBudget exceptionalOwnerEnergyBudget
    exceptionalOwnerAmplitudeBudget
  ring

/-- Exact remaining aggregate-correlation allowance for local frame loss four. -/
theorem exceptionalOwnerCorrelationEnergyBudget_lt_one_iff (rho : ℚ) :
    exceptionalOwnerCorrelationEnergyBudget rho < 1 ↔
      rho < (3101621 : ℚ) / 4548600 := by
  norm_num [exceptionalOwnerCorrelationEnergyBudget, exceptionalOwnerEnergyBudget,
    exceptionalOwnerAmplitudeBudget, elevenWeightOneEnergyFactor_eq]
  constructor <;> intro h <;> linarith

/-- An aggregate cross-energy comparison with coefficient `2/3` would fit the
restricted scale budget.  Establishing that comparison on the physical signed
packet remains an arithmetic task. -/
theorem exceptionalOwner_twoThirdsCorrelation_budget :
    exceptionalOwnerCorrelationEnergyBudget (2 / 3) = (5763004 : ℚ) / 5832225 := by
  norm_num [exceptionalOwnerCorrelationEnergyBudget, exceptionalOwnerEnergyBudget,
    exceptionalOwnerAmplitudeBudget, elevenWeightOneEnergyFactor_eq]

theorem exceptionalOwner_twoThirdsCorrelation_budget_lt_one :
    exceptionalOwnerCorrelationEnergyBudget (2 / 3) < 1 := by
  rw [exceptionalOwner_twoThirdsCorrelation_budget]
  norm_num

end RHLean.Proof
