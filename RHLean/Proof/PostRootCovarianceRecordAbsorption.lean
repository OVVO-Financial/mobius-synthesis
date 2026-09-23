import RHLean.Proof.PostRootCovarianceRowEnergy

/-!
# Record-to-record absorption for the post-root covariance envelope

The finite-horizon envelope of an earlier layer advances only at a positive record, and its
whole mass is the cumulative record excess.  This module makes the record step
itself the carrier of the remaining quantitative problem.

Three things are proved here.

* **Exact wall split.**  The one-step innovation budget of an earlier layer splits *without
  any triangle inequality* into a physical outer row seat and a square-wall
  departure seat.  The split is an equality because the two mechanisms have
  disjoint support: at a prime-square endpoint `W + 1 = p^2` the physical
  Möbius row and the whole active inherited row total both vanish, and away
  from a prime square the departure vanishes.

* **Record threshold.**  A positive record at `N` forces
  `envelope(N) * (scale(N+1) - scale(N)) < innovation(N)`, hence
  `envelope(N) * N^ε < innovation(N)` and
  `envelope(N+1) * (N+1)^ε < innovation(N)`.  That is a full endpoint power
  stronger than the naive `innovation / (N+1)^(1+ε)` localization, and the gain
  comes from the record hypothesis, not from an absolute value.  At a fresh
  prime the threshold reads `M(N) < -envelope(N) * N^ε`, so a record there needs
  a deeply negative Mertens prefix.

* **Departure absorption.**  The square-wall departure is supported exactly on
  prime squares, equals the complete lower covariance at scale `p` there, and
  its whole normalized sum over any horizon is bounded by
  `mertensSquarePowerEnvelope ε X / 2` times an explicit convergent `p`-series
  constant.  That estimate is unconditional; it uses the `p^2` sparsity of the
  wall and nothing else.

The record-conditioned absorption envelope `g_ε` collects what survives, and
`mertensEnergyBounded_of_postRootRecordAbsorptionSummable` shows that a summable
`g_ε` reaches the protected Mertens energy criterion.  The record indicator in
`g_ε` is not cosmetic.  Dropping it leaves the pointwise positive part of the
physical row `mu(N+1) M(N)`, whose normalized sum is not expected to converge,
so a majorant that ignores record sparsity cannot close the seam.

Nothing here bounds the record-conditioned outer row.  That object -- the
record-breaking physical new row after inherited high transport has been
removed -- is the whole remaining arithmetic seam.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-! ## The two innovation seats -/

/-- The normalized physical outer row: the new Möbius covariance row minus the
inherited post-root transport, with no absolute value on either factor. -/
def postRootRecordOuterRowSeat (ε : ℝ) (N : ℕ) : ℝ :=
  max 0
    ((realMoebiusStep (N + 1) * realMertensLength (N + 1) -
        postRootPrimeFamilyCovarianceRowTotal N) /
      Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε))

/-- The normalized square-wall departure seat. -/
def postRootRecordDepartureSeat (ε : ℝ) (N : ℕ) : ℝ :=
  max 0
    (postRootPrimeFamilyCovarianceDeparture N /
      Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε))

theorem postRootRecordOuterRowSeat_nonneg (ε : ℝ) (N : ℕ) :
    0 ≤ postRootRecordOuterRowSeat ε N := by
  unfold postRootRecordOuterRowSeat
  exact le_max_left _ _

theorem postRootRecordDepartureSeat_nonneg (ε : ℝ) (N : ℕ) :
    0 ≤ postRootRecordDepartureSeat ε N := by
  unfold postRootRecordDepartureSeat
  exact le_max_left _ _

/-! ## Disjoint support of the two mechanisms -/

/-- Every family leaving the post-root set does so at a prime square, so away
from a prime square the departure is literally zero. -/
theorem postRootPrimeFamilyCovarianceDeparture_eq_zero_of_not_primeSquare
    {W : ℕ} (h : ∀ p : ℕ, p.Prime → p * p ≠ W + 1) :
    postRootPrimeFamilyCovarianceDeparture W = 0 := by
  unfold postRootPrimeFamilyCovarianceDeparture
  apply Finset.sum_eq_zero
  intro q hq
  rcases Finset.mem_sdiff.mp hq with ⟨hqOld, hqNot⟩
  exact absurd (postRootPrimeFamilySet_succ_removed_eq_square hqOld hqNot)
    (h q (mem_postRootPrimeFamilySet.mp hqOld).2.2)

/-- A prime-square endpoint is not squarefree, so the physical new row vanishes
there. -/
theorem realMoebiusStep_eq_zero_of_primeSquare
    {W p : ℕ} (hp : p.Prime) (hsq : p * p = W + 1) :
    realMoebiusStep (W + 1) = 0 := by
  have hnsf : ¬ Squarefree (W + 1) := by
    rw [← hsq]
    intro hsf
    have hunit := Nat.isUnit_iff.mp (hsf p dvd_rfl)
    have h2 := hp.two_le
    omega
  unfold realMoebiusStep
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]
  simp

/-- At a prime-square endpoint the only prime that could carry an inherited row
is the wall prime itself, and that prime has already left the family set.  The
whole active inherited row total therefore vanishes. -/
theorem postRootPrimeFamilyCovarianceRowTotal_eq_zero_of_primeSquare
    {W p : ℕ} (hp : p.Prime) (hsq : p * p = W + 1) :
    postRootPrimeFamilyCovarianceRowTotal W = 0 := by
  unfold postRootPrimeFamilyCovarianceRowTotal
  apply Finset.sum_eq_zero
  intro q hq
  have hqPrime := (mem_postRootPrimeFamilySet.mp hq).2.2
  have hqRoot := (mem_postRootPrimeFamilySet.mp hq).1
  have hnd : ¬ (q ∣ W + 1) := by
    intro hqdvd
    have hqmul : q ∣ p * p := by rw [hsq]; exact hqdvd
    have hqp : q = p := by
      rcases (Nat.Prime.dvd_mul hqPrime).mp hqmul with h | h <;>
        exact (Nat.prime_dvd_prime_iff_eq hqPrime hp).mp h
    rw [hqp, ← hsq, Nat.sqrt_eq] at hqRoot
    exact lt_irrefl _ hqRoot
  rw [postRootLowerCovarianceRow_eq_ite, if_neg hnd]

/-- Splitting a positive part along a summand that is known to vanish costs
nothing.  This is the only place the wall split could have lost sign
information, and it does not. -/
private theorem max_zero_div_add_of_disjoint {A B S : ℝ} (h : A = 0 ∨ B = 0) :
    max 0 ((A + B) / S) = max 0 (A / S) + max 0 (B / S) := by
  rcases h with h | h <;> subst h <;> simp

/-- **Exact wall split.**  The innovation budget is the physical outer row
seat plus the square-wall departure seat, with equality.  No absolute value and
no triangle inequality is used: the two seats have disjoint support. -/
theorem postRootCovariancePowerLocalInnovationBudget_eq_outerRow_add_departure
    (ε : ℝ) (N : ℕ) :
    postRootCovariancePowerLocalInnovationBudget ε N =
      postRootRecordOuterRowSeat ε N + postRootRecordDepartureSeat ε N := by
  have hdisjoint :
      realMoebiusStep (N + 1) * realMertensLength (N + 1) -
            postRootPrimeFamilyCovarianceRowTotal N = 0 ∨
        postRootPrimeFamilyCovarianceDeparture N = 0 := by
    by_cases hsq : ∃ p : ℕ, p.Prime ∧ p * p = N + 1
    · obtain ⟨p, hp, hpsq⟩ := hsq
      left
      rw [realMoebiusStep_eq_zero_of_primeSquare hp hpsq,
        postRootPrimeFamilyCovarianceRowTotal_eq_zero_of_primeSquare hp hpsq]
      ring
    · right
      push_neg at hsq
      exact postRootPrimeFamilyCovarianceDeparture_eq_zero_of_not_primeSquare hsq
  unfold postRootCovariancePowerLocalInnovationBudget postRootRecordOuterRowSeat
    postRootRecordDepartureSeat
  rw [postRootCovarianceLocalInnovation_eq_row_sub_inherited_add_departure]
  exact max_zero_div_add_of_disjoint hdisjoint

/-! ## The exact remaining object at a post-root jump -/

/-- At a post-root quotient jump the outer row is exactly the complementary
prefix interaction of the cofactor.  This is the object the record process has
to control: the physical new row *after* the inherited high transport has been
subtracted, still carrying its own Möbius sign. -/
theorem postRootRecordOuterRowNumerator_eq_complementaryPrefix
    {W p : ℕ} (hp : p.Prime) (hmem : p ∈ postRootPrimeFamilySet (W + 1))
    (hdvd : p ∣ W + 1) :
    realMoebiusStep (W + 1) * realMertensLength (W + 1) -
        postRootPrimeFamilyCovarianceRowTotal W =
      -realMoebiusStep ((W + 1) / p) *
        (realMertensLength (W + 1) + realMertensLength ((W + 1) / p)) := by
  have hpRoot := (mem_postRootPrimeFamilySet.mp hmem).1
  have hlt : W + 1 < p * p := (Nat.sqrt_lt).1 hpRoot
  have hc : (W + 1) / p < p := (Nat.div_lt_iff_lt_mul hp.pos).2 hlt
  have hmul : p * ((W + 1) / p) = W + 1 := Nat.mul_div_cancel' hdvd
  have hquot : W / p + 1 = (W + 1) / p := by
    rw [Nat.succ_div, if_pos hdvd]
  have hrow :
      postRootPrimeFamilyCovarianceRowTotal W =
        realMoebiusStep ((W + 1) / p) * realMertensLength ((W + 1) / p) := by
    rw [postRootPrimeFamilyCovarianceRowTotal_eq_single_of_dvd hmem hdvd,
      postRootLowerCovarianceRow_eq_ite, if_pos hdvd, hquot]
  have hfresh := freshPrimePhysicalRow_sub_inherited_eq_complementaryPrefix hp hc
  rw [hmul] at hfresh
  rw [hrow]
  exact hfresh

/-! ## The record threshold -/

private theorem envelope_lt_seat_of_recordExcess_pos
    (ε : ℝ) {N : ℕ} (hrec : 0 < postRootCovariancePowerRecordExcess ε N) :
    postRootCovariancePowerEnvelope ε N <
      postRootCovariancePowerSeat ε (N + 1) := by
  unfold postRootCovariancePowerRecordExcess at hrec
  by_contra hle
  push_neg at hle
  rw [max_eq_left (sub_nonpos.mpr hle)] at hrec
  exact lt_irrefl 0 hrec

private theorem seat_succ_eq_of_recordExcess_pos
    (ε : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε N) :
    postRootCovariancePowerSeat ε (N + 1) =
      postRootCovarianceRemainder (N + 1) /
        Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) := by
  have hgt := envelope_lt_seat_of_recordExcess_pos ε hrec
  have hpos : 0 < postRootCovariancePowerSeat ε (N + 1) :=
    lt_of_le_of_lt (postRootCovariancePowerEnvelope_nonneg ε N) hgt
  unfold postRootCovariancePowerSeat at hpos ⊢
  rw [if_pos (show 2 ≤ N + 1 by omega)] at hpos ⊢
  rcases le_or_gt
      (postRootCovarianceRemainder (N + 1) /
        Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε)) 0 with h | h
  · rw [max_eq_left h] at hpos
    exact absurd hpos (lt_irrefl 0)
  · exact max_eq_right h.le

/-- **Record threshold, raw form.**  A positive record must beat the old
envelope on the *increment* of the endpoint scale, not merely on the scale
itself.  The old remainder is already bounded by the old envelope at the old
scale, so the entire old mass cancels. -/
theorem postRootCovariancePowerEnvelope_mul_scaleGap_lt_localInnovation_of_recordExcess_pos
    (ε : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε N) :
    postRootCovariancePowerEnvelope ε N *
        (Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) - Real.rpow (N : ℝ) (1 + ε)) <
      postRootCovarianceLocalInnovation N := by
  have hN1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < N + 1 by omega)
  have hS : 0 < Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) :=
    Real.rpow_pos_of_pos hN1pos _
  have hgt := envelope_lt_seat_of_recordExcess_pos ε hrec
  rw [seat_succ_eq_of_recordExcess_pos ε hN hrec] at hgt
  have hlt := (lt_div_iff₀ hS).mp hgt
  have hE := postRootCovarianceRemainder_le_powerEnvelope ε hN (le_refl N)
  have hinnov := postRootCovarianceRemainder_succ_sub_eq_localInnovation N
  nlinarith [hlt, hE, hinnov]

/-- One unit of endpoint scale separates consecutive powers. -/
private theorem rpow_scaleGap_ge (ε : ℝ) (hε : 0 ≤ ε) {N : ℕ} (hN : 1 ≤ N) :
    Real.rpow (N : ℝ) ε ≤
      Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) - Real.rpow (N : ℝ) (1 + ε) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < N + 1 by omega)
  have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  have hsplitA :
      Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) =
        ((N + 1 : ℕ) : ℝ) * Real.rpow ((N + 1 : ℕ) : ℝ) ε := by
    calc
      Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) =
          Real.rpow ((N + 1 : ℕ) : ℝ) 1 * Real.rpow ((N + 1 : ℕ) : ℝ) ε :=
        Real.rpow_add hN1pos _ _
      _ = ((N + 1 : ℕ) : ℝ) * Real.rpow ((N + 1 : ℕ) : ℝ) ε :=
        congrArg (fun t : ℝ => t * Real.rpow ((N + 1 : ℕ) : ℝ) ε)
          (Real.rpow_one _)
  have hsplitB :
      Real.rpow (N : ℝ) (1 + ε) = (N : ℝ) * Real.rpow (N : ℝ) ε := by
    calc
      Real.rpow (N : ℝ) (1 + ε) =
          Real.rpow (N : ℝ) 1 * Real.rpow (N : ℝ) ε := Real.rpow_add hNpos _ _
      _ = (N : ℝ) * Real.rpow (N : ℝ) ε :=
        congrArg (fun t : ℝ => t * Real.rpow (N : ℝ) ε) (Real.rpow_one _)
  have hmono : Real.rpow (N : ℝ) ε ≤ Real.rpow ((N + 1 : ℕ) : ℝ) ε := by
    refine Real.rpow_le_rpow hNpos.le ?_ hε
    rw [hcast]
    linarith
  rw [hcast] at hmono
  rw [hsplitA, hsplitB, hcast]
  nlinarith [mul_nonneg hNpos.le (sub_nonneg.mpr hmono), hmono, hNpos]

/-- **Record threshold.**  Every positive record pays a full endpoint power:
the old envelope times `N^ε` is strictly below the new local innovation.  The
naive localization only gives the innovation over `(N+1)^(1+ε)`; the record
hypothesis supplies the extra power without any absolute value. -/
theorem postRootCovariancePowerEnvelope_mul_rpow_lt_localInnovation_of_recordExcess_pos
    (ε : ℝ) (hε : 0 ≤ ε) {N : ℕ} (hN : 2 ≤ N)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε N) :
    postRootCovariancePowerEnvelope ε N * Real.rpow (N : ℝ) ε <
      postRootCovarianceLocalInnovation N := by
  have hraw :=
    postRootCovariancePowerEnvelope_mul_scaleGap_lt_localInnovation_of_recordExcess_pos
      ε hN hrec
  have hgap := rpow_scaleGap_ge ε hε (show 1 ≤ N by omega)
  have henv := postRootCovariancePowerEnvelope_nonneg ε N
  nlinarith [hraw, mul_nonneg henv (sub_nonneg.mpr hgap)]

/-- **Record-to-record absorption.**  After a record the whole envelope is the
last innovation divided by a full `(N+1)^ε`.  Every earlier record has been
absorbed; only the innovation at the current record survives. -/
theorem postRootCovariancePowerEnvelope_succ_mul_rpow_lt_localInnovation_of_recordExcess_pos
    (ε : ℝ) (hε : 0 ≤ ε) {N : ℕ} (hN : 2 ≤ N)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε N) :
    postRootCovariancePowerEnvelope ε (N + 1) *
        Real.rpow ((N + 1 : ℕ) : ℝ) ε <
      postRootCovarianceLocalInnovation N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < N + 1 by omega)
  have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  have hEps : 0 < Real.rpow ((N + 1 : ℕ) : ℝ) ε := Real.rpow_pos_of_pos hN1pos _
  have hsplitA :
      Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) =
        ((N + 1 : ℕ) : ℝ) * Real.rpow ((N + 1 : ℕ) : ℝ) ε := by
    calc
      Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) =
          Real.rpow ((N + 1 : ℕ) : ℝ) 1 * Real.rpow ((N + 1 : ℕ) : ℝ) ε :=
        Real.rpow_add hN1pos _ _
      _ = ((N + 1 : ℕ) : ℝ) * Real.rpow ((N + 1 : ℕ) : ℝ) ε :=
        congrArg (fun t : ℝ => t * Real.rpow ((N + 1 : ℕ) : ℝ) ε)
          (Real.rpow_one _)
  have hsplitB :
      Real.rpow (N : ℝ) (1 + ε) = (N : ℝ) * Real.rpow (N : ℝ) ε := by
    calc
      Real.rpow (N : ℝ) (1 + ε) =
          Real.rpow (N : ℝ) 1 * Real.rpow (N : ℝ) ε := Real.rpow_add hNpos _ _
      _ = (N : ℝ) * Real.rpow (N : ℝ) ε :=
        congrArg (fun t : ℝ => t * Real.rpow (N : ℝ) ε) (Real.rpow_one _)
  have hthr :=
    postRootCovariancePowerEnvelope_mul_rpow_lt_localInnovation_of_recordExcess_pos
      ε hε hN hrec
  have hstep :
      postRootCovariancePowerEnvelope ε N * Real.rpow (N : ℝ) ε * (N : ℝ) <
        postRootCovarianceLocalInnovation N * (N : ℝ) :=
    mul_lt_mul_of_pos_right hthr hNpos
  have hE := postRootCovarianceRemainder_le_powerEnvelope ε hN (le_refl N)
  rw [hsplitB] at hE
  have hinnov := postRootCovarianceRemainder_succ_sub_eq_localInnovation N
  have hEnext :
      postRootCovarianceRemainder (N + 1) <
        postRootCovarianceLocalInnovation N * ((N + 1 : ℕ) : ℝ) := by
    rw [hcast]
    nlinarith [hE, hinnov, hstep]
  have henvsucc :
      postRootCovariancePowerEnvelope ε (N + 1) =
        postRootCovarianceRemainder (N + 1) /
          Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) := by
    rw [postRootCovariancePowerEnvelope,
      max_eq_right (envelope_lt_seat_of_recordExcess_pos ε hrec).le]
    exact seat_succ_eq_of_recordExcess_pos ε hN hrec
  rw [henvsucc, hsplitA, div_mul_eq_mul_div,
    div_lt_iff₀ (mul_pos hN1pos hEps)]
  nlinarith [mul_lt_mul_of_pos_right hEnext hEps]

/-- **Fresh-prime record sign condition.**  At a new prime there is no inherited
row and no departure, so a record forces a deeply negative Mertens prefix. -/
theorem realMertensLength_lt_neg_envelope_mul_rpow_of_recordExcess_pos_of_prime
    (ε : ℝ) (hε : 0 ≤ ε) {N : ℕ} (hN : 2 ≤ N) (hprime : (N + 1).Prime)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε N) :
    realMertensLength (N + 1) <
      -(postRootCovariancePowerEnvelope ε N * Real.rpow (N : ℝ) ε) := by
  have h :=
    postRootCovariancePowerEnvelope_mul_rpow_lt_localInnovation_of_recordExcess_pos
      ε hε hN hrec
  rw [postRootCovarianceLocalInnovation_eq_neg_prefix_of_prime hprime] at h
  linarith

/-! ## An unconditional ceiling from the record threshold -/

private theorem abs_realMoebiusStep_le_one (n : ℕ) : |realMoebiusStep n| ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [realMoebiusStep, h]

/-- The Mertens prefix is bounded by its length, with no cancellation used. -/
theorem abs_realMertensLength_le (K : ℕ) : |realMertensLength K| ≤ (K : ℝ) := by
  unfold realMertensLength
  calc
    |∑ n ∈ Finset.range K, realMoebiusStep n| ≤
        ∑ n ∈ Finset.range K, |realMoebiusStep n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range K, (1 : ℝ) :=
      Finset.sum_le_sum fun n _ => abs_realMoebiusStep_le_one n
    _ = (K : ℝ) := by simp

private theorem row_le_endpoint_of_index {a b : ℕ} (hab : a ≤ b) :
    realMoebiusStep a * realMertensLength a ≤ ((b : ℕ) : ℝ) := by
  have hcast : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  calc
    realMoebiusStep a * realMertensLength a ≤
        |realMoebiusStep a * realMertensLength a| := le_abs_self _
    _ = |realMoebiusStep a| * |realMertensLength a| := abs_mul _ _
    _ ≤ 1 * ((a : ℕ) : ℝ) :=
      mul_le_mul (abs_realMoebiusStep_le_one a) (abs_realMertensLength_le a)
        (abs_nonneg _) zero_le_one
    _ = ((a : ℕ) : ℝ) := one_mul _
    _ ≤ ((b : ℕ) : ℝ) := hcast

private theorem neg_row_le_endpoint_of_index {a b : ℕ} (hab : a ≤ b) :
    -(realMoebiusStep a * realMertensLength a) ≤ ((b : ℕ) : ℝ) := by
  have hcast : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  calc
    -(realMoebiusStep a * realMertensLength a) ≤
        |realMoebiusStep a * realMertensLength a| := neg_le_abs _
    _ = |realMoebiusStep a| * |realMertensLength a| := abs_mul _ _
    _ ≤ 1 * ((a : ℕ) : ℝ) :=
      mul_le_mul (abs_realMoebiusStep_le_one a) (abs_realMertensLength_le a)
        (abs_nonneg _) zero_le_one
    _ = ((a : ℕ) : ℝ) := one_mul _
    _ ≤ ((b : ℕ) : ℝ) := hcast

theorem physicalRow_le_endpoint (N : ℕ) :
    realMoebiusStep (N + 1) * realMertensLength (N + 1) ≤ ((N + 1 : ℕ) : ℝ) :=
  row_le_endpoint_of_index (le_refl (N + 1))

theorem neg_postRootPrimeFamilyCovarianceRowTotal_le_endpoint (N : ℕ) :
    -postRootPrimeFamilyCovarianceRowTotal N ≤ ((N + 1 : ℕ) : ℝ) := by
  by_cases hex : ∃ p ∈ postRootPrimeFamilySet (N + 1), p ∣ N + 1
  · obtain ⟨p, hp, hdvd⟩ := hex
    rw [postRootPrimeFamilyCovarianceRowTotal_eq_single_of_dvd hp hdvd,
      postRootLowerCovarianceRow_eq_ite, if_pos hdvd]
    exact neg_row_le_endpoint_of_index
      (Nat.succ_le_succ (Nat.div_le_self N p))
  · have hzero : postRootPrimeFamilyCovarianceRowTotal N = 0 := by
      unfold postRootPrimeFamilyCovarianceRowTotal
      apply Finset.sum_eq_zero
      intro p hp
      have hnd : ¬ (p ∣ N + 1) := fun hdvd => hex ⟨p, hp, hdvd⟩
      rw [postRootLowerCovarianceRow_eq_ite, if_neg hnd]
    rw [hzero, neg_zero]
    exact Nat.cast_nonneg _

/-! ## Square-wall departure: exact support, exact value, `p^2` sparsity -/

private theorem nat_mul_self_inj {a b : ℕ} (h : a * a = b * b) : a = b := by
  have hs := congrArg Nat.sqrt h
  simpa only [Nat.sqrt_eq] using hs

theorem postRootRecordDepartureSeat_eq_zero_of_not_primeSquare
    (ε : ℝ) {N : ℕ} (h : ∀ p : ℕ, p.Prime → p * p ≠ N + 1) :
    postRootRecordDepartureSeat ε N = 0 := by
  unfold postRootRecordDepartureSeat
  rw [postRootPrimeFamilyCovarianceDeparture_eq_zero_of_not_primeSquare h]
  simp

/-- The wall prime is genuinely present: at `W + 1 = p^2` the departing family
set is exactly `{p}`, and the departure is the complete lower covariance carried
by that one family. -/
theorem postRootPrimeFamilyCovarianceDeparture_eq_lowerPairSum
    {W p : ℕ} (hp : p.Prime) (hsq : p * p = W + 1) :
    postRootPrimeFamilyCovarianceDeparture W =
      realMertensPositiveLagPairSum (W / p + 1) := by
  have hp2 := hp.two_le
  have hsingle :
      postRootPrimeFamilySet W \ postRootPrimeFamilySet (W + 1) = {p} := by
    apply Finset.Subset.antisymm
    · intro q hq
      rcases Finset.mem_sdiff.mp hq with ⟨hqOld, hqNot⟩
      have hqsq := postRootPrimeFamilySet_succ_removed_eq_square hqOld hqNot
      have hqp : q = p := nat_mul_self_inj (by rw [hqsq, hsq])
      simp [hqp]
    · intro q hq
      have hqp : q = p := Finset.mem_singleton.mp hq
      rw [hqp]
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · refine mem_postRootPrimeFamilySet.mpr ⟨?_, ?_, hp⟩
        · exact (Nat.sqrt_lt).2 (by omega)
        · have hmul : p * 2 ≤ p * p := Nat.mul_le_mul_left p hp2
          omega
      · intro hmem
        have hroot := (mem_postRootPrimeFamilySet.mp hmem).1
        rw [← hsq, Nat.sqrt_eq] at hroot
        exact lt_irrefl _ hroot
  unfold postRootPrimeFamilyCovarianceDeparture
  rw [hsingle, Finset.sum_singleton]

/-- The complete lower covariance is at most half the lower Mertens energy,
because the squarefree diagonal it removes is nonnegative. -/
theorem realMertensPositiveLagPairSum_le_half_lengthSq (K : ℕ) :
    realMertensPositiveLagPairSum K ≤ realMertensLength K ^ 2 / 2 := by
  have hid := realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum K
  have hdiag := realMertensDiagonal_nonneg K
  linarith

/-- **Departure at a wall.**  A prime-square wall costs at most the running
Mertens-square envelope over a single power of the wall prime.  The exponent is
`p^(1+ε)`, not `(W+1)^(1+ε)`, and that is exactly the `p^2` sparsity gain. -/
theorem postRootRecordDepartureSeat_le_of_primeSquare
    (ε : ℝ) (hε : 0 < ε) {W p X : ℕ} (hp : p.Prime) (hsq : p * p = W + 1)
    (hWX : W ≤ X) :
    postRootRecordDepartureSeat ε W ≤
      mertensSquarePowerEnvelope ε X / 2 * (Real.rpow (p : ℝ) (1 + ε))⁻¹ := by
  have hA := mertensSquarePowerEnvelope_nonneg ε X
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hP : 0 < Real.rpow (p : ℝ) (1 + ε) := Real.rpow_pos_of_pos hppos _
  have hWlt : W < p * p := by omega
  have hcof : W / p + 1 ≤ p := (Nat.div_lt_iff_lt_mul hp.pos).2 hWlt
  have hbound :
      postRootPrimeFamilyCovarianceDeparture W ≤
        mertensSquarePowerEnvelope ε X * Real.rpow (p : ℝ) (1 + ε) / 2 := by
    have h1 := postRootPrimeFamilyCovarianceDeparture_eq_lowerPairSum hp hsq
    have h2 := realMertensPositiveLagPairSum_le_half_lengthSq (W / p + 1)
    have h3 :=
      realMertensLength_sq_le_powerEnvelope ε
        (show W / p ≤ X from le_trans (Nat.div_le_self W p) hWX)
    have h4 :
        Real.rpow ((W / p + 1 : ℕ) : ℝ) (1 + ε) ≤
          Real.rpow (p : ℝ) (1 + ε) := by
      refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by linarith)
      exact_mod_cast hcof
    have h5 :
        mertensSquarePowerEnvelope ε X *
            Real.rpow ((W / p + 1 : ℕ) : ℝ) (1 + ε) ≤
          mertensSquarePowerEnvelope ε X * Real.rpow (p : ℝ) (1 + ε) :=
      mul_le_mul_of_nonneg_left h4 hA
    rw [h1]
    linarith
  have hcastsq : ((W + 1 : ℕ) : ℝ) = (p : ℝ) * (p : ℝ) := by
    rw [← hsq]; push_cast; ring
  have hsplit :
      Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) =
        Real.rpow (p : ℝ) (1 + ε) * Real.rpow (p : ℝ) (1 + ε) := by
    rw [hcastsq]
    exact Real.mul_rpow hppos.le hppos.le
  unfold postRootRecordDepartureSeat
  rw [hsplit]
  apply max_le
  · exact mul_nonneg (by linarith) (inv_nonneg.mpr hP.le)
  · rw [div_le_iff₀ (mul_pos hP hP)]
    have hPne : Real.rpow (p : ℝ) (1 + ε) ≠ 0 := ne_of_gt hP
    have hrearrange :
        mertensSquarePowerEnvelope ε X / 2 * (Real.rpow (p : ℝ) (1 + ε))⁻¹ *
            (Real.rpow (p : ℝ) (1 + ε) * Real.rpow (p : ℝ) (1 + ε)) =
          mertensSquarePowerEnvelope ε X * Real.rpow (p : ℝ) (1 + ε) / 2 := by
      rw [mul_assoc, ← mul_assoc (Real.rpow (p : ℝ) (1 + ε))⁻¹,
        inv_mul_cancel₀ hPne, one_mul, div_mul_eq_mul_div]
    rw [hrearrange]
    exact hbound

/-! ## An unconditional envelope ceiling -/

theorem postRootPrimeFamilyCovarianceDeparture_le_endpoint (N : ℕ) :
    postRootPrimeFamilyCovarianceDeparture N ≤ ((N + 1 : ℕ) : ℝ) := by
  by_cases hex : ∃ p : ℕ, p.Prime ∧ p * p = N + 1
  · obtain ⟨p, hp, hsq⟩ := hex
    rw [postRootPrimeFamilyCovarianceDeparture_eq_lowerPairSum hp hsq]
    have hhalf := realMertensPositiveLagPairSum_le_half_lengthSq (N / p + 1)
    have habs := abs_realMertensLength_le (N / p + 1)
    have hcof : N / p + 1 ≤ p := (Nat.div_lt_iff_lt_mul hp.pos).2 (by omega)
    have hcast : ((N / p + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hcof
    have hle : |realMertensLength (N / p + 1)| ≤ (p : ℝ) := le_trans habs hcast
    have hsqbound : realMertensLength (N / p + 1) ^ 2 ≤ (p : ℝ) ^ 2 := by
      have hnn := abs_nonneg (realMertensLength (N / p + 1))
      have hid := sq_abs (realMertensLength (N / p + 1))
      nlinarith [hle, hnn, hid]
    have hpN : (p : ℝ) ^ 2 = ((N + 1 : ℕ) : ℝ) := by
      rw [← hsq]; push_cast; ring
    have hnn : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hpN] at hsqbound
    linarith
  · push_neg at hex
    rw [postRootPrimeFamilyCovarianceDeparture_eq_zero_of_not_primeSquare hex]
    exact Nat.cast_nonneg _

/-- **Unconditional innovation ceiling.**  No cancellation is used: the new
physical row, the single active inherited row, and the square-wall departure are
each bounded by one endpoint. -/
theorem postRootCovarianceLocalInnovation_le_three_mul_endpoint (N : ℕ) :
    postRootCovarianceLocalInnovation N ≤ 3 * ((N + 1 : ℕ) : ℝ) := by
  rw [postRootCovarianceLocalInnovation_eq_row_sub_inherited_add_departure]
  have h1 := physicalRow_le_endpoint N
  have h2 := neg_postRootPrimeFamilyCovarianceRowTotal_le_endpoint N
  have h3 := postRootPrimeFamilyCovarianceDeparture_le_endpoint N
  linarith

/-- **Unconditional envelope ceiling.**  Feeding the trivial one-endpoint
innovation ceiling through the record threshold already improves its coarse
`envelope <= N` by a full `N^ε`.  No arithmetic input is used beyond the
absolute-value bounds on the three innovation terms; the gain is entirely the
record structure. -/
theorem postRootCovariancePowerEnvelope_le_subEndpoint
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) {X : ℕ} (hX : 2 ≤ X) :
    postRootCovariancePowerEnvelope ε X ≤
      max (postRootCovariancePowerEnvelope ε 2)
        (3 * Real.rpow (X : ℝ) (1 - ε)) := by
  have key : ∀ N : ℕ, 2 ≤ N → N ≤ X →
      postRootCovariancePowerEnvelope ε N ≤
        max (postRootCovariancePowerEnvelope ε 2)
          (3 * Real.rpow (X : ℝ) (1 - ε)) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
        intro _
        exact le_max_left _ _
    | succ N h2N ih =>
        intro hNX
        by_cases hrec : 0 < postRootCovariancePowerRecordExcess ε N
        · have hN1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
            exact_mod_cast (show 0 < N + 1 by omega)
          have hEps : 0 < Real.rpow ((N + 1 : ℕ) : ℝ) ε :=
            Real.rpow_pos_of_pos hN1pos _
          have hsub :
              Real.rpow ((N + 1 : ℕ) : ℝ) (1 - ε) *
                  Real.rpow ((N + 1 : ℕ) : ℝ) ε = ((N + 1 : ℕ) : ℝ) := by
            calc
              Real.rpow ((N + 1 : ℕ) : ℝ) (1 - ε) *
                    Real.rpow ((N + 1 : ℕ) : ℝ) ε =
                  Real.rpow ((N + 1 : ℕ) : ℝ) (1 - ε + ε) :=
                (Real.rpow_add hN1pos _ _).symm
              _ = Real.rpow ((N + 1 : ℕ) : ℝ) 1 :=
                congrArg (Real.rpow ((N + 1 : ℕ) : ℝ)) (by ring)
              _ = ((N + 1 : ℕ) : ℝ) := Real.rpow_one _
          have hkey :=
            postRootCovariancePowerEnvelope_succ_mul_rpow_lt_localInnovation_of_recordExcess_pos
              ε hε.le h2N hrec
          have hceil := postRootCovarianceLocalInnovation_le_three_mul_endpoint N
          have hmul :
              postRootCovariancePowerEnvelope ε (N + 1) *
                  Real.rpow ((N + 1 : ℕ) : ℝ) ε <
                3 * Real.rpow ((N + 1 : ℕ) : ℝ) (1 - ε) *
                  Real.rpow ((N + 1 : ℕ) : ℝ) ε := by
            nlinarith [hkey, hceil, hsub]
          have hlt :
              postRootCovariancePowerEnvelope ε (N + 1) <
                3 * Real.rpow ((N + 1 : ℕ) : ℝ) (1 - ε) :=
            lt_of_mul_lt_mul_right hmul hEps.le
          have hmono :
              Real.rpow ((N + 1 : ℕ) : ℝ) (1 - ε) ≤
                Real.rpow (X : ℝ) (1 - ε) := by
            refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by linarith)
            exact_mod_cast hNX
          have hfinal :
              postRootCovariancePowerEnvelope ε (N + 1) ≤
                3 * Real.rpow (X : ℝ) (1 - ε) := by linarith
          exact le_trans hfinal (le_max_right _ _)
        · push_neg at hrec
          have hzero : postRootCovariancePowerRecordExcess ε N = 0 :=
            le_antisymm hrec (postRootCovariancePowerRecordExcess_nonneg ε N)
          rw [postRootCovariancePowerEnvelope_succ_eq_add_recordExcess, hzero,
            add_zero]
          exact ih (by omega)
  exact key X hX (le_refl X)

/-- The explicit convergent `p`-series constant that absorbs every prime-square
wall.  It depends only on `ε`. -/
def postRootDepartureSparsityConstant (ε : ℝ) : ℝ :=
  ∑' k : ℕ, (Real.rpow (k : ℝ) (1 + ε))⁻¹

private theorem summable_rpow_inv (ε : ℝ) (hε : 0 < ε) :
    Summable (fun k : ℕ => (Real.rpow (k : ℝ) (1 + ε))⁻¹) :=
  Real.summable_nat_rpow_inv.mpr (by linarith)

theorem postRootDepartureSparsityConstant_nonneg (ε : ℝ) :
    0 ≤ postRootDepartureSparsityConstant ε := by
  unfold postRootDepartureSparsityConstant
  apply tsum_nonneg
  intro k
  exact inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg k) _)

/-- The endpoints below `X` that sit at a prime-square wall. -/
private def departureWallIndices (X : ℕ) : Finset ℕ :=
  (Finset.range X).filter
    (fun N => Nat.Prime (Nat.sqrt (N + 1)) ∧
      Nat.sqrt (N + 1) * Nat.sqrt (N + 1) = N + 1)

/-- The wall primes whose square is at most `X`. -/
private def departureWallPrimes (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun p => Nat.Prime p ∧ p * p ≤ X)

private theorem departureWallIndices_subset (X : ℕ) :
    departureWallIndices X ⊆ Finset.range X :=
  Finset.filter_subset _ _

private theorem departureWallPrimes_subset (X : ℕ) :
    departureWallPrimes X ⊆ Finset.range (X + 1) :=
  Finset.filter_subset _ _

private theorem mem_departureWallIndices {X N : ℕ} :
    N ∈ departureWallIndices X ↔
      N < X ∧ Nat.Prime (Nat.sqrt (N + 1)) ∧
        Nat.sqrt (N + 1) * Nat.sqrt (N + 1) = N + 1 := by
  simp [departureWallIndices, Finset.mem_filter, Finset.mem_range]

private theorem mem_departureWallPrimes {X p : ℕ} :
    p ∈ departureWallPrimes X ↔ p < X + 1 ∧ Nat.Prime p ∧ p * p ≤ X := by
  simp [departureWallPrimes, Finset.mem_filter, Finset.mem_range]

/-- **Square-wall absorption.**  Unconditionally, the total normalized
square-wall departure over any horizon is at most half the running Mertens
square envelope times a fixed convergent constant.  The walls sit at `p^2`, so
the whole family contributes a convergent `p`-series, not an endpoint-sized
mass.  This is the promised explicit absorption of the departure; it assumes
nothing. -/
theorem sum_postRootRecordDepartureSeat_le_sparsity
    (ε : ℝ) (hε : 0 < ε) (X : ℕ) :
    (∑ N ∈ Finset.range X, postRootRecordDepartureSeat ε N) ≤
      mertensSquarePowerEnvelope ε X / 2 *
        postRootDepartureSparsityConstant ε := by
  have hA := mertensSquarePowerEnvelope_nonneg ε X
  have hsupport :
      (∑ N ∈ Finset.range X, postRootRecordDepartureSeat ε N) =
        ∑ N ∈ departureWallIndices X, postRootRecordDepartureSeat ε N := by
    refine (Finset.sum_subset (departureWallIndices_subset X) ?_).symm
    intro N hN hNS
    apply postRootRecordDepartureSeat_eq_zero_of_not_primeSquare
    intro p hp hpsq
    have hs : Nat.sqrt (N + 1) = p := by rw [← hpsq, Nat.sqrt_eq]
    refine hNS (mem_departureWallIndices.mpr ⟨Finset.mem_range.mp hN, ?_, ?_⟩)
    · rw [hs]; exact hp
    · rw [hs]; exact hpsq
  have hsubset :
      departureWallIndices X ⊆
        (departureWallPrimes X).image (fun p => p * p - 1) := by
    intro N hN
    rcases mem_departureWallIndices.mp hN with ⟨hNX, hprime, hsqeq⟩
    have hp2 := hprime.two_le
    refine Finset.mem_image.mpr ⟨Nat.sqrt (N + 1), ?_, ?_⟩
    · refine mem_departureWallPrimes.mpr ⟨?_, hprime, ?_⟩
      · have hle : Nat.sqrt (N + 1) ≤ N + 1 := by
          have h1 : Nat.sqrt (N + 1) ≤ Nat.sqrt (N + 1) * Nat.sqrt (N + 1) :=
            Nat.le_mul_of_pos_left _ (by omega)
          rw [hsqeq] at h1
          exact h1
        omega
      · omega
    · show Nat.sqrt (N + 1) * Nat.sqrt (N + 1) - 1 = N
      simp [hsqeq]
  have hstep1 :
      (∑ N ∈ departureWallIndices X, postRootRecordDepartureSeat ε N) ≤
        ∑ N ∈ (departureWallPrimes X).image (fun p => p * p - 1),
          postRootRecordDepartureSeat ε N :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun N _ _ => postRootRecordDepartureSeat_nonneg ε N)
  have hinj :
      Set.InjOn (fun p => p * p - 1) (↑(departureWallPrimes X) : Set ℕ) := by
    intro a ha b hb hab
    have ha2 := (mem_departureWallPrimes.mp (Finset.mem_coe.mp ha)).2.1.two_le
    have hb2 := (mem_departureWallPrimes.mp (Finset.mem_coe.mp hb)).2.1.two_le
    have haa : 0 < a * a := Nat.mul_pos (by omega) (by omega)
    have hbb : 0 < b * b := Nat.mul_pos (by omega) (by omega)
    have hab' : a * a - 1 = b * b - 1 := hab
    exact nat_mul_self_inj (by omega)
  have hstep2 :
      (∑ N ∈ (departureWallPrimes X).image (fun p => p * p - 1),
          postRootRecordDepartureSeat ε N) =
        ∑ p ∈ departureWallPrimes X,
          postRootRecordDepartureSeat ε (p * p - 1) :=
    Finset.sum_image hinj
  have hstep3 :
      (∑ p ∈ departureWallPrimes X,
          postRootRecordDepartureSeat ε (p * p - 1)) ≤
        ∑ p ∈ departureWallPrimes X, mertensSquarePowerEnvelope ε X / 2 *
          (Real.rpow (p : ℝ) (1 + ε))⁻¹ := by
    refine Finset.sum_le_sum ?_
    intro p hp
    rcases mem_departureWallPrimes.mp hp with ⟨_, hprime, hpX⟩
    have hp2 := hprime.two_le
    have hpp : 0 < p * p := Nat.mul_pos (by omega) (by omega)
    exact postRootRecordDepartureSeat_le_of_primeSquare ε hε hprime
      (by omega) (by omega)
  have hstep4 :
      (∑ p ∈ departureWallPrimes X, mertensSquarePowerEnvelope ε X / 2 *
          (Real.rpow (p : ℝ) (1 + ε))⁻¹) ≤
        ∑ k ∈ Finset.range (X + 1), mertensSquarePowerEnvelope ε X / 2 *
          (Real.rpow (k : ℝ) (1 + ε))⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (departureWallPrimes_subset X) ?_
    intro k _ _
    exact mul_nonneg (by linarith)
      (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg k) _))
  have hstep5 :
      (∑ k ∈ Finset.range (X + 1), mertensSquarePowerEnvelope ε X / 2 *
          (Real.rpow (k : ℝ) (1 + ε))⁻¹) ≤
        mertensSquarePowerEnvelope ε X / 2 *
          postRootDepartureSparsityConstant ε := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact (summable_rpow_inv ε hε).sum_le_tsum (Finset.range (X + 1))
      (fun k _ => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg k) _))
  rw [hsupport]
  linarith

/-! ## The record-conditioned absorption envelope -/

/-- The physical outer row seat, kept only at a record step. -/
def postRootRecordOuterRowRecordSeat (ε : ℝ) (N : ℕ) : ℝ :=
  if postRootCovariancePowerEnvelope ε N <
      postRootCovariancePowerSeat ε (N + 1) then
    postRootRecordOuterRowSeat ε N
  else 0

/-- `g_ε(N)`: the absorption envelope of the record excess.  It is the exact
innovation budget at a record step and zero elsewhere.  The record indicator is
essential: the pointwise positive part of the physical row is not expected to be
summable, so a majorant that ignores record sparsity cannot bound the
envelope. -/
def postRootRecordAbsorptionEnvelope (ε : ℝ) (N : ℕ) : ℝ :=
  if postRootCovariancePowerEnvelope ε N <
      postRootCovariancePowerSeat ε (N + 1) then
    postRootRecordOuterRowSeat ε N + postRootRecordDepartureSeat ε N
  else 0

theorem postRootRecordOuterRowRecordSeat_nonneg (ε : ℝ) (N : ℕ) :
    0 ≤ postRootRecordOuterRowRecordSeat ε N := by
  unfold postRootRecordOuterRowRecordSeat
  split
  · exact postRootRecordOuterRowSeat_nonneg ε N
  · exact le_rfl

theorem postRootRecordAbsorptionEnvelope_nonneg (ε : ℝ) (N : ℕ) :
    0 ≤ postRootRecordAbsorptionEnvelope ε N := by
  unfold postRootRecordAbsorptionEnvelope
  split
  · exact add_nonneg (postRootRecordOuterRowSeat_nonneg ε N)
      (postRootRecordDepartureSeat_nonneg ε N)
  · exact le_rfl

theorem postRootCovariancePowerRecordExcess_eq_zero_of_not_record
    (ε : ℝ) {N : ℕ}
    (h : postRootCovariancePowerSeat ε (N + 1) ≤
      postRootCovariancePowerEnvelope ε N) :
    postRootCovariancePowerRecordExcess ε N = 0 := by
  unfold postRootCovariancePowerRecordExcess
  exact max_eq_left (sub_nonpos.mpr h)

/-- **Record absorption inequality.**  Every record excess is dominated by the
record-conditioned absorption envelope.  At a record the bound is the exact
innovation budget; away from a record both sides are zero. -/
theorem postRootCovariancePowerRecordExcess_le_absorptionEnvelope
    (ε : ℝ) (hε : 0 < ε) {N : ℕ} (hN : 2 ≤ N) :
    postRootCovariancePowerRecordExcess ε N ≤
      postRootRecordAbsorptionEnvelope ε N := by
  by_cases hrec : postRootCovariancePowerEnvelope ε N <
      postRootCovariancePowerSeat ε (N + 1)
  · have hval : postRootRecordAbsorptionEnvelope ε N =
        postRootRecordOuterRowSeat ε N + postRootRecordDepartureSeat ε N :=
      if_pos hrec
    rw [hval, ←
      postRootCovariancePowerLocalInnovationBudget_eq_outerRow_add_departure]
    exact postRootCovariancePowerRecordExcess_le_localInnovationBudget ε hε hN
  · have hval : postRootRecordAbsorptionEnvelope ε N = 0 := if_neg hrec
    rw [hval]
    exact le_of_eq
      (postRootCovariancePowerRecordExcess_eq_zero_of_not_record ε
        (not_lt.mp hrec))

theorem postRootRecordAbsorptionEnvelope_le_recordOuterRow_add_departure
    (ε : ℝ) (N : ℕ) :
    postRootRecordAbsorptionEnvelope ε N ≤
      postRootRecordOuterRowRecordSeat ε N +
        postRootRecordDepartureSeat ε N := by
  by_cases h : postRootCovariancePowerEnvelope ε N <
      postRootCovariancePowerSeat ε (N + 1)
  · have h1 : postRootRecordAbsorptionEnvelope ε N =
        postRootRecordOuterRowSeat ε N + postRootRecordDepartureSeat ε N :=
      if_pos h
    have h2 : postRootRecordOuterRowRecordSeat ε N =
        postRootRecordOuterRowSeat ε N := if_pos h
    exact le_of_eq (by rw [h1, h2])
  · have h1 : postRootRecordAbsorptionEnvelope ε N = 0 := if_neg h
    have h2 : postRootRecordOuterRowRecordSeat ε N = 0 := if_neg h
    rw [h1, h2, zero_add]
    exact postRootRecordDepartureSeat_nonneg ε N

/-- **The absorption sum, unconditionally.**  Over any horizon the whole
absorption envelope is the record-conditioned outer row plus a fixed multiple of
the running Mertens square envelope.  The square-wall departure has been fully
absorbed by its `p^2` sparsity and contributes no growth of its own. -/
theorem sum_postRootRecordAbsorptionEnvelope_le_outerRow_add_sparsity
    (ε : ℝ) (hε : 0 < ε) (X : ℕ) :
    (∑ N ∈ Finset.range X, postRootRecordAbsorptionEnvelope ε N) ≤
      (∑ N ∈ Finset.range X, postRootRecordOuterRowRecordSeat ε N) +
        mertensSquarePowerEnvelope ε X / 2 *
          postRootDepartureSparsityConstant ε := by
  have hsplit :
      (∑ N ∈ Finset.range X, postRootRecordAbsorptionEnvelope ε N) ≤
        (∑ N ∈ Finset.range X, postRootRecordOuterRowRecordSeat ε N) +
          ∑ N ∈ Finset.range X, postRootRecordDepartureSeat ε N := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum
      (fun N _ =>
        postRootRecordAbsorptionEnvelope_le_recordOuterRow_add_departure ε N)
  have hdep := sum_postRootRecordDepartureSeat_le_sparsity ε hε X
  linarith

/-! ## Composition with the terminal bridge -/

/-- Summability of the record-conditioned absorption envelope. -/
def PostRootRecordAbsorptionSummableStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ X : ℕ,
        (∑ N ∈ Finset.range X, postRootRecordAbsorptionEnvelope ε N) ≤ D

/-- Summability of the record-conditioned physical outer row alone.  This is the
whole remaining arithmetic seam. -/
def PostRootRecordOuterRowSummableStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ X : ℕ,
        (∑ N ∈ Finset.range X, postRootRecordOuterRowRecordSeat ε N) ≤ D

/-- Uniform boundedness of the Mertens square envelope. -/
def MertensSquarePowerEnvelopeBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W : ℕ, mertensSquarePowerEnvelope ε W ≤ A

/-- The Mertens square envelope of the row-energy layer is exactly the protected
Mertens energy criterion.  Consequently the departure absorption above is stated
relative to the target itself, and is not an independent arithmetic input. -/
theorem mertensSquarePowerEnvelopeBounded_iff_mertensEnergyBounded :
    MertensSquarePowerEnvelopeBoundedStatement ↔
      MertensEnergyBoundedStatement := by
  constructor
  · intro henv ε hε
    rcases henv ε hε with ⟨A, hA, hbound⟩
    refine ⟨A, hA, ?_⟩
    intro x
    have hlen := realMertensLength_sq_le_powerEnvelope ε (le_refl x)
    have hnorm := norm_mertensSummatory_sq_eq_realMertensLength_sq x
    have hpow : (0 : ℝ) ≤ Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hmul :
        mertensSquarePowerEnvelope ε x *
            Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) ≤
          A * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) :=
      mul_le_mul_of_nonneg_right (hbound x) hpow
    rw [hnorm]
    linarith
  · intro hmert ε hε
    rcases hmert ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro W
    induction W with
    | zero => simpa [mertensSquarePowerEnvelope] using hC
    | succ W ih =>
        rw [mertensSquarePowerEnvelope]
        refine max_le ih ?_
        have hposN : (0 : ℝ) < ((W + 1 + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_pos (W + 1)
        have hpow : (0 : ℝ) < Real.rpow ((W + 1 + 1 : ℕ) : ℝ) (1 + ε) :=
          Real.rpow_pos_of_pos hposN _
        have hnorm := norm_mertensSummatory_sq_eq_realMertensLength_sq (W + 1)
        have hb := hbound (W + 1)
        rw [hnorm] at hb
        exact (div_le_iff₀ hpow).2 hb

/-- **Absorption closes the envelope.**  A summable record-conditioned
absorption envelope bounds the whole running envelope, anchored at the
fixed finite prefix `W <= 2`. -/
theorem postRootCovariancePowerEnvelopeBounded_of_recordAbsorptionSummable
    (habs : PostRootRecordAbsorptionSummableStatement) :
    PostRootCovariancePowerEnvelopeBoundedStatement := by
  intro ε hε
  rcases habs ε hε with ⟨D, hD, hbound⟩
  refine ⟨postRootCovariancePowerEnvelope ε 2 + D, ?_, ?_⟩
  · have := postRootCovariancePowerEnvelope_nonneg ε 2
    linarith
  · intro N
    by_cases hN : N ≤ 2
    · have hmono := postRootCovariancePowerEnvelope_mono ε hN
      linarith
    · push_neg at hN
      have h2N : 2 ≤ N := le_of_lt hN
      rw [postRootCovariancePowerEnvelope_eq_anchor_add_tailRecordExcess ε h2N]
      have htail :
          (∑ j ∈ Finset.Ico 2 N, postRootCovariancePowerRecordExcess ε j) ≤
            ∑ j ∈ Finset.Ico 2 N, postRootRecordAbsorptionEnvelope ε j :=
        Finset.sum_le_sum fun j hj =>
          postRootCovariancePowerRecordExcess_le_absorptionEnvelope ε hε
            (Finset.mem_Ico.mp hj).1
      have hIco :
          (∑ j ∈ Finset.Ico 2 N, postRootRecordAbsorptionEnvelope ε j) ≤
            ∑ j ∈ Finset.range N, postRootRecordAbsorptionEnvelope ε j := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro x hx
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
        · exact fun j _ _ => postRootRecordAbsorptionEnvelope_nonneg ε j
      have hb := hbound N
      linarith

/-- **The sharpest form of the seam.**  A pointwise `W^ε` bound on the local
innovation, required only at record steps, already bounds the whole envelope.
Compare the unconditional statement being replaced, which asks for `W^(1+ε)` at
every endpoint: the record process has absorbed one full endpoint power. -/
def PostRootRecordInnovationPowerBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ N : ℕ, 2 ≤ N → 0 < postRootCovariancePowerRecordExcess ε N →
        postRootCovarianceLocalInnovation N ≤
          D * Real.rpow ((N + 1 : ℕ) : ℝ) ε

/-- **Record innovation closes the envelope.**  Between records the envelope is
constant, and at a record the record-to-record absorption theorem replaces it by
the current innovation over `(N+1)^ε`.  So a single pointwise power bound at
record steps propagates to a uniform bound. -/
theorem postRootCovariancePowerEnvelopeBounded_of_recordInnovationPowerBounded
    (hinnovBound : PostRootRecordInnovationPowerBoundedStatement) :
    PostRootCovariancePowerEnvelopeBoundedStatement := by
  intro ε hε
  rcases hinnovBound ε hε with ⟨D, hD, hbound⟩
  have key : ∀ N : ℕ, 2 ≤ N →
      postRootCovariancePowerEnvelope ε N ≤
        max (postRootCovariancePowerEnvelope ε 2) D := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact le_max_left _ _
    | succ N h2N ih =>
        by_cases hrec : 0 < postRootCovariancePowerRecordExcess ε N
        · have hN1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
            exact_mod_cast (show 0 < N + 1 by omega)
          have hpos : (0 : ℝ) < Real.rpow ((N + 1 : ℕ) : ℝ) ε :=
            Real.rpow_pos_of_pos hN1pos _
          have hkey :=
            postRootCovariancePowerEnvelope_succ_mul_rpow_lt_localInnovation_of_recordExcess_pos
              ε hε.le h2N hrec
          have hmul :
              postRootCovariancePowerEnvelope ε (N + 1) *
                  Real.rpow ((N + 1 : ℕ) : ℝ) ε <
                D * Real.rpow ((N + 1 : ℕ) : ℝ) ε :=
            lt_of_lt_of_le hkey (hbound N h2N hrec)
          exact le_trans (lt_of_mul_lt_mul_right hmul hpos.le).le (le_max_right _ _)
        · push_neg at hrec
          have hzero : postRootCovariancePowerRecordExcess ε N = 0 :=
            le_antisymm hrec (postRootCovariancePowerRecordExcess_nonneg ε N)
          rw [postRootCovariancePowerEnvelope_succ_eq_add_recordExcess, hzero,
            add_zero]
          exact ih
  refine ⟨max (postRootCovariancePowerEnvelope ε 2) D, ?_, ?_⟩
  · exact le_trans (postRootCovariancePowerEnvelope_nonneg ε 2) (le_max_left _ _)
  · intro N
    by_cases hN : 2 ≤ N
    · exact key N hN
    · push_neg at hN
      exact le_trans (postRootCovariancePowerEnvelope_mono ε (le_of_lt hN))
        (le_max_left _ _)

/-- The record-step innovation power bound reaches the protected Mertens energy
criterion. -/
theorem mertensEnergyBounded_of_postRootRecordInnovationPowerBounded
    (hinnovBound : PostRootRecordInnovationPowerBoundedStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_postRootCovariancePowerEnvelopeBounded
    (postRootCovariancePowerEnvelopeBounded_of_recordInnovationPowerBounded
      hinnovBound)

/-- The record absorption seam reaches the protected Mertens energy criterion
through the bootstrap. -/
theorem mertensEnergyBounded_of_postRootRecordAbsorptionSummable
    (habs : PostRootRecordAbsorptionSummableStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_postRootCovariancePowerEnvelopeBounded
    (postRootCovariancePowerEnvelopeBounded_of_recordAbsorptionSummable habs)

/-- **Where the seam now sits.**  This is a decomposition, not a proof: by the
equivalence above the Mertens square hypothesis *is* the terminal target.  Read
the other way it says the square-wall departures cannot obstruct the record
process -- under the target itself they contribute one fixed constant -- so any
failure of record absorption must come from the record-conditioned physical
outer row. -/
theorem postRootRecordAbsorptionSummable_of_outerRow_of_mertensSquareEnvelopeBounded
    (houter : PostRootRecordOuterRowSummableStatement)
    (hsq : MertensSquarePowerEnvelopeBoundedStatement) :
    PostRootRecordAbsorptionSummableStatement := by
  intro ε hε
  rcases houter ε hε with ⟨D, hD, hDbound⟩
  rcases hsq ε hε with ⟨A, hA, hAbound⟩
  have hZ := postRootDepartureSparsityConstant_nonneg ε
  refine ⟨D + A / 2 * postRootDepartureSparsityConstant ε, ?_, ?_⟩
  · have hnn : 0 ≤ A / 2 * postRootDepartureSparsityConstant ε :=
      mul_nonneg (by linarith) hZ
    linarith
  · intro X
    have h1 := sum_postRootRecordAbsorptionEnvelope_le_outerRow_add_sparsity ε hε X
    have h2 :
        mertensSquarePowerEnvelope ε X / 2 *
            postRootDepartureSparsityConstant ε ≤
          A / 2 * postRootDepartureSparsityConstant ε :=
      mul_le_mul_of_nonneg_right (by linarith [hAbound X]) hZ
    have h3 := hDbound X
    linarith

end RHLean.Proof
