import RHLean.Proof.PostRootCovarianceRecordAbsorption

/-!
# Per-Mobius square-energy charge at post-root records

The record-step reduction leaves one physical outer covariance row after the
inherited high-prime row has been subtracted.  This file moves that object one
level deeper, to the individual Mobius square-energy increment.

At an active post-root divisor `p | W+1`, with cofactor `c = (W+1)/p`, fresh
prime transport gives `mu(W+1) = -mu(c)`.  The diagonal squares therefore
cancel exactly, and twice the surviving outer covariance row is the difference
of the two discrete Mertens-square increments:

`2 * outerRow = DeltaM2(W+1) - DeltaM2(c)`.

At a positive record the already-proved square-energy record threshold says the
new cumulative Mertens square strictly dominates every transported lower square.
Because both Mertens values are integer-valued, the gap between the physical
and lower cumulative prefixes then has magnitude at least one.  This converts
the exact row identity into the one-sided per-Mobius charge

`outerRow <= M_new^2 - M_lower^2`,

and hence bounds the record excess by that same cumulative square gap at the
physical endpoint normalization.

The final section also records the sharp unconditional finite-horizon ceiling
coming directly from the already-proved `E(W) <= W^2`: for `eps <= 1`,
`envelope_eps(X) <= X^(1-eps)`.  This corrects the weaker constant-three
ceiling inherited from the source branch; it does not claim a subquadratic
remainder bound.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Discrete cumulative Mertens square-energy row belonging to the Mobius atom
at index `c`. -/
def realMertensSquareStep (c : ℕ) : ℝ :=
  realMertensLength (c + 1) ^ 2 - realMertensLength c ^ 2

/-- The square-energy row is its diagonal unit plus twice its covariance row. -/
theorem realMertensSquareStep_eq_diagonal_add_two_mul_row (c : ℕ) :
    realMertensSquareStep c =
      realMoebiusStep c ^ 2 + 2 * realMoebiusStep c * realMertensLength c := by
  unfold realMertensSquareStep
  exact realMertensLength_sq_succ_sub_eq_diagonal_add_two_mul_row c

/-- **Per-Mobius high-transport identity.**  On an active post-root divisor,
the physical row after subtracting its inherited lower row is exactly half the
difference of the corresponding cumulative square-energy rows.  The two
Mobius diagonals cancel because the fresh prime reverses the atom sign. -/
theorem two_mul_postRootRecordOuterRowNumerator_eq_squareStep_sub_lower
    {W p : ℕ} (hp : p.Prime)
    (hmem : p ∈ postRootPrimeFamilySet (W + 1))
    (hdvd : p ∣ W + 1) :
    2 * (realMoebiusStep (W + 1) * realMertensLength (W + 1) -
      postRootPrimeFamilyCovarianceRowTotal W) =
      realMertensSquareStep (W + 1) -
        realMertensSquareStep ((W + 1) / p) := by
  have hpRoot := (mem_postRootPrimeFamilySet.mp hmem).1
  have hlt : W + 1 < p * p := (Nat.sqrt_lt).1 hpRoot
  have hc : (W + 1) / p < p :=
    (Nat.div_lt_iff_lt_mul hp.pos).2 hlt
  have hmul : p * ((W + 1) / p) = W + 1 := Nat.mul_div_cancel' hdvd
  have hquot : W / p + 1 = (W + 1) / p := by
    rw [Nat.succ_div, if_pos hdvd]
  have hrow :
      postRootPrimeFamilyCovarianceRowTotal W =
        realMoebiusStep ((W + 1) / p) *
          realMertensLength ((W + 1) / p) := by
    rw [postRootPrimeFamilyCovarianceRowTotal_eq_single_of_dvd hmem hdvd,
      postRootLowerCovarianceRow_eq_ite, if_pos hdvd, hquot]
  have hmuMul :
      realMoebiusStep (p * ((W + 1) / p)) =
        -realMoebiusStep ((W + 1) / p) :=
    realMoebiusStep_prime_mul_of_lt hp hc
  rw [hmul] at hmuMul
  have hmu :
      realMoebiusStep (W + 1) = -realMoebiusStep ((W + 1) / p) := hmuMul
  rw [hrow, realMertensSquareStep_eq_diagonal_add_two_mul_row,
    realMertensSquareStep_eq_diagonal_add_two_mul_row, hmu]
  ring

/-- An active post-root divisor rules out a simultaneous prime-square wall, so
the local innovation is exactly the physical outer row. -/
theorem postRootCovarianceLocalInnovation_eq_outerRow_of_activePostRootDivisor
    {W p : ℕ} (hp : p.Prime)
    (hmem : p ∈ postRootPrimeFamilySet (W + 1))
    (hdvd : p ∣ W + 1) :
    postRootCovarianceLocalInnovation W =
      realMoebiusStep (W + 1) * realMertensLength (W + 1) -
        postRootPrimeFamilyCovarianceRowTotal W := by
  have hdepart : postRootPrimeFamilyCovarianceDeparture W = 0 := by
    apply postRootPrimeFamilyCovarianceDeparture_eq_zero_of_not_primeSquare
    intro q hq hsq
    have hpdvd : p ∣ q * q := by
      rw [hsq]
      exact hdvd
    have hpq : p = q := by
      rcases (Nat.Prime.dvd_mul hp).mp hpdvd with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hp hq).mp h
      · exact (Nat.prime_dvd_prime_iff_eq hp hq).mp h
    have hroot := (mem_postRootPrimeFamilySet.mp hmem).1
    rw [hpq, ← hsq, Nat.sqrt_eq] at hroot
    exact lt_irrefl _ hroot
  rw [postRootCovarianceLocalInnovation_eq_row_sub_inherited_add_departure,
    hdepart, add_zero]

/-- **Record-row square charge.**  At a positive record carried by an active
post-root divisor, the whole new envelope times one endpoint power is strictly
below half the difference of the physical and inherited cumulative square rows.
This is the per-Mobius-to-cumulative bridge, before any family aggregation. -/
theorem two_mul_envelope_succ_mul_rpow_lt_squareStep_sub_lower_of_record
    (ε : ℝ) (hε : 0 ≤ ε) {W p : ℕ} (hW : 2 ≤ W)
    (hp : p.Prime) (hmem : p ∈ postRootPrimeFamilySet (W + 1))
    (hdvd : p ∣ W + 1)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W) :
    2 * postRootCovariancePowerEnvelope ε (W + 1) *
        Real.rpow ((W + 1 : ℕ) : ℝ) ε <
      realMertensSquareStep (W + 1) -
        realMertensSquareStep ((W + 1) / p) := by
  have hthr :=
    postRootCovariancePowerEnvelope_succ_mul_rpow_lt_localInnovation_of_recordExcess_pos
      ε hε hW hrec
  have hlocal :=
    postRootCovarianceLocalInnovation_eq_outerRow_of_activePostRootDivisor hp hmem hdvd
  have hcharge :=
    two_mul_postRootRecordOuterRowNumerator_eq_squareStep_sub_lower hp hmem hdvd
  rw [hlocal] at hthr
  nlinarith

/-- At a fresh prime the lower square row is the unit row at `1`, hence the
physical square increment is exactly `1 + 2 * innovation`. -/
theorem realMertensSquareStep_eq_one_add_two_mul_localInnovation_of_prime
    {W : ℕ} (hprime : (W + 1).Prime) :
    realMertensSquareStep (W + 1) =
      1 + 2 * postRootCovarianceLocalInnovation W := by
  rw [realMertensSquareStep_eq_diagonal_add_two_mul_row,
    postRootCovarianceLocalInnovation_eq_neg_prefix_of_prime hprime]
  simp [realMoebiusStep, ArithmeticFunction.moebius_apply_prime hprime]
  ring

/-- Fresh-prime records are therefore paid directly by the positive square
energy created by that single prime step. -/
theorem two_mul_envelope_succ_mul_rpow_lt_squareStep_sub_one_of_prime_record
    (ε : ℝ) (hε : 0 ≤ ε) {W : ℕ} (hW : 2 ≤ W)
    (hprime : (W + 1).Prime)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W) :
    2 * postRootCovariancePowerEnvelope ε (W + 1) *
        Real.rpow ((W + 1 : ℕ) : ℝ) ε <
      realMertensSquareStep (W + 1) - 1 := by
  have hthr :=
    postRootCovariancePowerEnvelope_succ_mul_rpow_lt_localInnovation_of_recordExcess_pos
      ε hε hW hrec
  have hs := realMertensSquareStep_eq_one_add_two_mul_localInnovation_of_prime hprime
  nlinarith

/-! ## From one Mobius row to its cumulative square share -/

/-- Two distinct integer-valued Mertens prefixes differ in absolute value by at
least one.  The strict square inequality is a convenient way to certify their
distinctness in the record argument below. -/
private theorem one_le_abs_realMertensLength_sub_of_sq_lt
    {A B : ℕ}
    (h : realMertensLength B ^ 2 < realMertensLength A ^ 2) :
    1 ≤ |realMertensLength A - realMertensLength B| := by
  let a : ℤ := ∑ n ∈ Finset.range A, μ n
  let b : ℤ := ∑ n ∈ Finset.range B, μ n
  have ha : (a : ℝ) = realMertensLength A := by
    simp [a, realMertensLength, realMoebiusStep]
  have hb : (b : ℝ) = realMertensLength B := by
    simp [b, realMertensLength, realMoebiusStep]
  have hab : a ≠ b := by
    intro heq
    have hre : realMertensLength A = realMertensLength B := by
      rw [← ha, ← hb, heq]
    rw [hre] at h
    exact (lt_irrefl _) h
  have hsplit : a - b ≤ -1 ∨ 1 ≤ a - b := by omega
  rcases hsplit with hneg | hpos
  · have hr : realMertensLength A - realMertensLength B ≤ (-1 : ℝ) := by
      have hz : ((a - b : ℤ) : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hneg
      rw [Int.cast_sub, ha, hb] at hz
      exact hz
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hr : (1 : ℝ) ≤ realMertensLength A - realMertensLength B := by
      have hz : (1 : ℝ) ≤ ((a - b : ℤ) : ℝ) := by exact_mod_cast hpos
      rw [Int.cast_sub, ha, hb] at hz
      exact hz
    rw [abs_of_nonneg (by linarith)]
    exact hr

/-- If a unit-signed linear row points in the same direction as a positive
integer square gap, the row is no larger than that cumulative square gap. -/
private theorem signed_sum_le_square_gap
    {u x y : ℝ}
    (hu : |u| = 1)
    (hrow : 0 < -u * (x + y))
    (hgap : y ^ 2 < x ^ 2)
    (hdiff : 1 ≤ |x - y|) :
    -u * (x + y) ≤ x ^ 2 - y ^ 2 := by
  have hrowAbs : -u * (x + y) = |x + y| := by
    calc
      -u * (x + y) = |-u * (x + y)| := (abs_of_pos hrow).symm
      _ = |-u| * |x + y| := abs_mul _ _
      _ = |x + y| := by rw [abs_neg, hu, one_mul]
  have hgapPos : 0 < x ^ 2 - y ^ 2 := sub_pos.mpr hgap
  calc
    -u * (x + y) = |x + y| := hrowAbs
    _ = 1 * |x + y| := by ring
    _ ≤ |x - y| * |x + y| :=
      mul_le_mul_of_nonneg_right hdiff (abs_nonneg _)
    _ = |(x - y) * (x + y)| := (abs_mul _ _).symm
    _ = |x ^ 2 - y ^ 2| := by
      congr 1
      ring
    _ = x ^ 2 - y ^ 2 := abs_of_pos hgapPos

/-- **Per-Mobius cumulative charge bound.**  At a positive record with an
active post-root divisor `p`, the dangerous outer row is no larger than the
literal cumulative Mertens square gap between the new physical prefix and the
transported lower prefix.  No family norm or cancellation hypothesis appears. -/
theorem postRootRecordOuterRowNumerator_le_currentSquare_sub_lowerSquare
    (ε : ℝ) (hε : 0 ≤ ε) {W p : ℕ} (hW : 2 ≤ W)
    (hp : p.Prime) (hmem : p ∈ postRootPrimeFamilySet (W + 1))
    (hdvd : p ∣ W + 1)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W) :
    realMoebiusStep (W + 1) * realMertensLength (W + 1) -
        postRootPrimeFamilyCovarianceRowTotal W ≤
      realMertensLength (W + 2) ^ 2 -
        realMertensLength ((W + 1) / p + 1) ^ 2 := by
  let c := (W + 1) / p
  have hpRoot := (mem_postRootPrimeFamilySet.mp hmem).1
  have hlt : W + 1 < p * p := (Nat.sqrt_lt).1 hpRoot
  have hc : c < p := by
    dsimp [c]
    exact (Nat.div_lt_iff_lt_mul hp.pos).2 hlt
  have hmul : p * c = W + 1 := by
    dsimp [c]
    exact Nat.mul_div_cancel' hdvd
  have hmu : realMoebiusStep (W + 1) = -realMoebiusStep c := by
    rw [← hmul, realMoebiusStep_prime_mul_of_lt hp hc]
  have hphys := realMertensLength_succ (W + 1)
  have hlow := realMertensLength_succ c
  have hW2 : W + 1 + 1 = W + 2 := by omega
  rw [hW2] at hphys
  have hsum :
      realMertensLength (W + 1) + realMertensLength c =
        realMertensLength (W + 2) + realMertensLength (c + 1) := by
    rw [hphys, hlow, hmu]
    ring
  have houterEq :
      realMoebiusStep (W + 1) * realMertensLength (W + 1) -
          postRootPrimeFamilyCovarianceRowTotal W =
        -realMoebiusStep c *
          (realMertensLength (W + 2) + realMertensLength (c + 1)) := by
    have h := postRootRecordOuterRowNumerator_eq_complementaryPrefix hp hmem hdvd
    dsimp [c] at h ⊢
    rw [hsum] at h
    exact h
  have hlocal :=
    postRootCovarianceLocalInnovation_eq_outerRow_of_activePostRootDivisor hp hmem hdvd
  have hthr :=
    postRootCovariancePowerEnvelope_succ_mul_rpow_lt_localInnovation_of_recordExcess_pos
      ε hε hW hrec
  rw [hlocal] at hthr
  have hleft :
      0 ≤ postRootCovariancePowerEnvelope ε (W + 1) *
        Real.rpow ((W + 1 : ℕ) : ℝ) ε :=
    mul_nonneg (postRootCovariancePowerEnvelope_nonneg ε (W + 1))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have houterPos :
      0 < realMoebiusStep (W + 1) * realMertensLength (W + 1) -
        postRootPrimeFamilyCovarianceRowTotal W :=
    lt_of_le_of_lt hleft hthr
  have hmunz : realMoebiusStep c ≠ 0 := by
    intro hz
    rw [houterEq, hz] at houterPos
    norm_num at houterPos
  have hmuabs : |realMoebiusStep c| = 1 := by
    rcases ArithmeticFunction.moebius_eq_or c with h | h | h
    · simp [realMoebiusStep, h] at hmunz
    · simp [realMoebiusStep, h]
    · simp [realMoebiusStep, h]
  have hfamilyTerm :
      realMertensLength (c + 1) ^ 2 ≤ postRootFamilyMertensSquareEnergy (W + 1) := by
    rw [postRootFamilyMertensSquareEnergy_eq_sum_realMertensLength_sq]
    dsimp [c]
    exact Finset.single_le_sum
      (fun q _ => sq_nonneg (realMertensLength ((W + 1) / q + 1))) hmem
  have hrecordSq :=
    postRootFamilySquareEnergy_add_recordThreshold_lt_outerSquare_of_recordExcess_pos
      ε (show 1 ≤ W by omega) hrec
  have hthreshold :
      0 ≤ 2 * Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) *
        postRootCovariancePowerEnvelope ε W :=
    mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (postRootCovariancePowerEnvelope_nonneg ε W)
  have hgap :
      realMertensLength (c + 1) ^ 2 < realMertensLength (W + 2) ^ 2 := by
    have hW2' : W + 1 + 1 = W + 2 := by omega
    rw [hW2'] at hrecordSq
    nlinarith
  have hdiff :
      1 ≤ |realMertensLength (W + 2) - realMertensLength (c + 1)| :=
    one_le_abs_realMertensLength_sub_of_sq_lt hgap
  have houterPos' :
      0 < -realMoebiusStep c *
        (realMertensLength (W + 2) + realMertensLength (c + 1)) := by
    rw [← houterEq]
    exact houterPos
  rw [houterEq]
  exact signed_sum_le_square_gap hmuabs houterPos' hgap hdiff

/-- **Normalized record-excess bound.**  On an active high-prime record, the
new record excess is bounded by its literal cumulative Mertens-square gap,
normalized only once at the physical endpoint. -/
theorem postRootCovariancePowerRecordExcess_le_currentSquareGap
    (ε : ℝ) (hε : 0 < ε) {W p : ℕ} (hW : 2 ≤ W)
    (hp : p.Prime) (hmem : p ∈ postRootPrimeFamilySet (W + 1))
    (hdvd : p ∣ W + 1)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W) :
    postRootCovariancePowerRecordExcess ε W ≤
      (realMertensLength (W + 2) ^ 2 -
        realMertensLength ((W + 1) / p + 1) ^ 2) /
          Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) := by
  have hlocal :=
    postRootCovarianceLocalInnovation_eq_outerRow_of_activePostRootDivisor hp hmem hdvd
  have houter :=
    postRootRecordOuterRowNumerator_le_currentSquare_sub_lowerSquare
      ε hε.le hW hp hmem hdvd hrec
  have hthr :=
    postRootCovariancePowerEnvelope_succ_mul_rpow_lt_localInnovation_of_recordExcess_pos
      ε hε.le hW hrec
  rw [hlocal] at hthr
  have hleft :
      0 ≤ postRootCovariancePowerEnvelope ε (W + 1) *
        Real.rpow ((W + 1 : ℕ) : ℝ) ε :=
    mul_nonneg (postRootCovariancePowerEnvelope_nonneg ε (W + 1))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have houterPos :
      0 < realMoebiusStep (W + 1) * realMertensLength (W + 1) -
        postRootPrimeFamilyCovarianceRowTotal W :=
    lt_of_le_of_lt hleft hthr
  have hscale : 0 < Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hbudget := postRootCovariancePowerRecordExcess_le_localInnovationBudget
    ε hε hW
  unfold postRootCovariancePowerLocalInnovationBudget at hbudget
  rw [hlocal, max_eq_right (div_nonneg houterPos.le hscale.le)] at hbudget
  exact hbudget.trans (div_le_div_of_nonneg_right houter hscale.le)

/-! ## Sharp unconditional finite-horizon ceiling -/

private theorem endpoint_sq_div_postRootPower_eq_rpow_one_sub
    (ε : ℝ) {W : ℕ} (hW : 0 < W) :
    (W : ℝ) ^ 2 / Real.rpow (W : ℝ) (1 + ε) =
      Real.rpow (W : ℝ) (1 - ε) := by
  have hpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have htwo : Real.rpow (W : ℝ) (2 : ℝ) = (W : ℝ) ^ (2 : ℕ) :=
    Real.rpow_natCast (W : ℝ) 2
  calc
    (W : ℝ) ^ 2 / Real.rpow (W : ℝ) (1 + ε) =
        Real.rpow (W : ℝ) (2 : ℝ) / Real.rpow (W : ℝ) (1 + ε) := by
          rw [htwo]
    _ = Real.rpow (W : ℝ) ((2 : ℝ) - (1 + ε)) :=
      (Real.rpow_sub hpos (2 : ℝ) (1 + ε)).symm
    _ = Real.rpow (W : ℝ) (1 - ε) := by
      congr 1
      ring

/-- The quadratic physical carrier bound already gives the exact normalized
ceiling `W^(1-eps)` at one seat. -/
theorem postRootCovariancePowerSeat_le_rpow_one_sub
    (ε : ℝ) {W : ℕ} (hW : 2 ≤ W) :
    postRootCovariancePowerSeat ε W ≤ Real.rpow (W : ℝ) (1 - ε) := by
  have hWpos : 0 < W := by omega
  have hpowpos : 0 < Real.rpow (W : ℝ) (1 + ε) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hWpos) _
  unfold postRootCovariancePowerSeat
  rw [if_pos hW]
  apply max_le
  · exact Real.rpow_nonneg (Nat.cast_nonneg W) _
  · calc
      postRootCovarianceRemainder W /
          Real.rpow (W : ℝ) (1 + ε) ≤
        (W : ℝ) ^ 2 / Real.rpow (W : ℝ) (1 + ε) :=
          div_le_div_of_nonneg_right (postRootCovarianceRemainder_le_endpoint_sq W)
            hpowpos.le
      _ = Real.rpow (W : ℝ) (1 - ε) :=
        endpoint_sq_div_postRootPower_eq_rpow_one_sub ε hWpos

/-- **Sharp unconditional envelope ceiling.**  For `eps <= 1`, the running
envelope is at most `X^(1-eps)`.  This is stronger than the inherited
constant-three record ceiling, but it is only a repackaging of `E(W) <= W^2`:
multiplying back by `W^(1+eps)` still gives the quadratic remainder bound. -/
theorem postRootCovariancePowerEnvelope_le_rpow_one_sub
    (ε : ℝ) (hε1 : ε ≤ 1) {X : ℕ} (hX : 2 ≤ X) :
    postRootCovariancePowerEnvelope ε X ≤ Real.rpow (X : ℝ) (1 - ε) := by
  have hexp : 0 ≤ 1 - ε := by linarith
  induction X, hX using Nat.le_induction with
  | base =>
      have hprev : postRootCovariancePowerEnvelope ε 1 = 0 := by
        simp [postRootCovariancePowerEnvelope, postRootCovariancePowerSeat]
      rw [show (2 : ℕ) = 1 + 1 by norm_num,
        postRootCovariancePowerEnvelope, hprev]
      rw [max_eq_right (postRootCovariancePowerSeat_nonneg ε 2)]
      exact postRootCovariancePowerSeat_le_rpow_one_sub ε (by norm_num)
  | succ N h2N ih =>
      rw [postRootCovariancePowerEnvelope]
      apply max_le
      · have hmono :
            Real.rpow (N : ℝ) (1 - ε) ≤
              Real.rpow ((N + 1 : ℕ) : ℝ) (1 - ε) := by
          refine Real.rpow_le_rpow (Nat.cast_nonneg N) ?_ hexp
          exact_mod_cast Nat.le_succ N
        exact ih.trans hmono
      · exact postRootCovariancePowerSeat_le_rpow_one_sub ε (by omega)

end RHLean.Proof
