import RHLean.Proof.PostRootCovarianceRecordSquareCharge

/-!
# Low/high closure of the record square charge

The high-prime record bound in `PostRootCovarianceRecordSquareCharge` charges an
active transported row to the literal cumulative Mertens-square gap between the
physical endpoint and its lower cofactor prefix.  This file records the
complementary low case.

If no post-root prime divides the new endpoint, the inherited high row is
literally zero.  The physical covariance row is then no larger than half of its
own discrete Mertens-square increment, because

`Delta M^2 = mu^2 + 2 mu M`.

Together with the prime-square departure seat this yields an exhaustive
low/high record-step dichotomy: every positive record is charged either to a
high transported cumulative square gap, or to the local physical square step
plus the already-isolated square-wall departure.  No family norm, prime count,
or cancellation hypothesis is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The normalized half square-step charge of the physical new Mobius atom. -/
def postRootRecordPhysicalSquareStepSeat (ε : ℝ) (W : ℕ) : ℝ :=
  max 0
    ((realMertensSquareStep (W + 1) / 2) /
      Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε))

theorem postRootRecordPhysicalSquareStepSeat_nonneg (ε : ℝ) (W : ℕ) :
    0 ≤ postRootRecordPhysicalSquareStepSeat ε W := by
  unfold postRootRecordPhysicalSquareStepSeat
  exact le_max_left _ _

/-- If no post-root prime divides the new endpoint, there is no inherited high
covariance row at that unit step. -/
theorem postRootPrimeFamilyCovarianceRowTotal_eq_zero_of_no_active_divisor
    {W : ℕ}
    (hno : ∀ p ∈ postRootPrimeFamilySet (W + 1), ¬ p ∣ W + 1) :
    postRootPrimeFamilyCovarianceRowTotal W = 0 := by
  unfold postRootPrimeFamilyCovarianceRowTotal
  apply Finset.sum_eq_zero
  intro p hp
  rw [postRootLowerCovarianceRow_eq_ite, if_neg (hno p hp)]

/-- In the low/no-active-high case, the physical row is bounded by half of the
single atom's cumulative Mertens-square increment. -/
theorem postRootRecordOuterRowSeat_le_physicalSquareStepSeat_of_no_active_divisor
    (ε : ℝ) {W : ℕ}
    (hno : ∀ p ∈ postRootPrimeFamilySet (W + 1), ¬ p ∣ W + 1) :
    postRootRecordOuterRowSeat ε W ≤
      postRootRecordPhysicalSquareStepSeat ε W := by
  have hrows :=
    postRootPrimeFamilyCovarianceRowTotal_eq_zero_of_no_active_divisor hno
  have hscale :
      0 ≤ Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hstep := realMertensSquareStep_eq_diagonal_add_two_mul_row (W + 1)
  have hdiag : 0 ≤ realMoebiusStep (W + 1) ^ 2 := sq_nonneg _
  have hrow :
      realMoebiusStep (W + 1) * realMertensLength (W + 1) ≤
        realMertensSquareStep (W + 1) / 2 := by
    nlinarith
  unfold postRootRecordOuterRowSeat postRootRecordPhysicalSquareStepSeat
  rw [hrows, sub_zero]
  exact max_le_max le_rfl (div_le_div_of_nonneg_right hrow hscale)

/-- **Low record square charge.**  When no post-root prime is active, every
record excess is paid by the physical atom's half square-step plus the explicit
prime-square departure seat. -/
theorem postRootCovariancePowerRecordExcess_le_lowSquareCharge_of_no_active_divisor
    (ε : ℝ) (hε : 0 < ε) {W : ℕ} (hW : 2 ≤ W)
    (hno : ∀ p ∈ postRootPrimeFamilySet (W + 1), ¬ p ∣ W + 1) :
    postRootCovariancePowerRecordExcess ε W ≤
      postRootRecordPhysicalSquareStepSeat ε W +
        postRootRecordDepartureSeat ε W := by
  have hlocal :=
    postRootCovariancePowerRecordExcess_le_localInnovationBudget ε hε hW
  rw [postRootCovariancePowerLocalInnovationBudget_eq_outerRow_add_departure] at hlocal
  exact hlocal.trans
    (add_le_add_right
      (postRootRecordOuterRowSeat_le_physicalSquareStepSeat_of_no_active_divisor
        ε hno)
      (postRootRecordDepartureSeat ε W))

/-- **Exhaustive low/high record-step bound.**  A positive record is charged in
one of exactly two ways:

* an active post-root divisor `p` charges it to the cumulative square gap from
  the lower cofactor prefix `c = (W+1)/p` to the physical endpoint;
* if there is no active high divisor, the physical atom is charged to half its
  own square increment, with only the separately isolated prime-square departure
  added.

This is the per-Mobius bound in the same low/high split used throughout the
repository. -/
theorem postRootCovariancePowerRecordExcess_squareCharge_dichotomy
    (ε : ℝ) (hε : 0 < ε) {W : ℕ} (hW : 2 ≤ W)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W) :
    (∃ p : ℕ,
        p.Prime ∧ p ∈ postRootPrimeFamilySet (W + 1) ∧ p ∣ W + 1 ∧
        postRootCovariancePowerRecordExcess ε W ≤
          (realMertensLength (W + 2) ^ 2 -
            realMertensLength ((W + 1) / p + 1) ^ 2) /
              Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε)) ∨
      postRootCovariancePowerRecordExcess ε W ≤
        postRootRecordPhysicalSquareStepSeat ε W +
          postRootRecordDepartureSeat ε W := by
  by_cases hex : ∃ p ∈ postRootPrimeFamilySet (W + 1), p ∣ W + 1
  · left
    obtain ⟨p, hpMem, hpDvd⟩ := hex
    have hpPrime := (mem_postRootPrimeFamilySet.mp hpMem).2.2
    refine ⟨p, hpPrime, hpMem, hpDvd, ?_⟩
    exact postRootCovariancePowerRecordExcess_le_currentSquareGap
      ε hε hW hpPrime hpMem hpDvd hrec
  · right
    apply postRootCovariancePowerRecordExcess_le_lowSquareCharge_of_no_active_divisor
      ε hε hW
    intro p hpMem hpDvd
    exact hex ⟨p, hpMem, hpDvd⟩

end RHLean.Proof
