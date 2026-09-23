import RHLean.Proof.PostRootMertensSquareFiniteDifference

/-!
# Individual post-root covariance rows and their lower-prefix energy

The squared row `mu(c) M(c-1)` is bounded by the preceding Mertens square.
At a post-root quotient jump this gives the exact half-power gain against a
finite envelope of preceding Mertens energies.  There is at most one nonzero
active inherited row at a unit step.

The full innovation also contains the new physical row and departures at the
prime-square wall.  Both are retained below.  Inside a transported family the
atom and prefix both reverse signs, so their covariance row is preserved; its
minus sign in the remainder comes from the family subtraction.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Exact square-energy contribution of one physical Möbius atom. -/
theorem realMertensLength_sq_succ_sub_eq_diagonal_add_two_mul_row (c : ℕ) :
    realMertensLength (c + 1) ^ 2 - realMertensLength c ^ 2 =
      realMoebiusStep c ^ 2 + 2 * realMoebiusStep c * realMertensLength c := by
  rw [realMertensLength_succ]
  ring

/-- An individual covariance row is owned by its preceding cumulative prefix. -/
theorem realMoebiusCovarianceRow_sq_le_lowerMertensEnergy (c : ℕ) :
    (realMoebiusStep c * realMertensLength c) ^ 2 ≤ realMertensLength c ^ 2 := by
  have h := mul_le_mul_of_nonneg_right (realMoebiusStep_sq_le_one c)
    (sq_nonneg (realMertensLength c))
  simpa only [mul_pow, one_mul] using h

/-- The inherited covariance increment on one fixed quotient coordinate. -/
def postRootLowerCovarianceRow (W p : ℕ) : ℝ :=
  realMertensPositiveLagPairSum ((W + 1) / p + 1) -
    realMertensPositiveLagPairSum (W / p + 1)

theorem postRootLowerCovarianceRow_eq_ite (W p : ℕ) :
    postRootLowerCovarianceRow W p =
      if p ∣ W + 1 then
        realMoebiusStep (W / p + 1) * realMertensLength (W / p + 1)
      else 0 :=
  postRootLowerCovariance_succQuotient_sub W p

/-- The requested per-row inequality holds for every `W,p`, including `p=0`
and non-jump steps.  No primality or cancellation hypothesis is needed. -/
theorem postRootLowerCovarianceRow_sq_le_lowerMertensEnergy (W p : ℕ) :
    (realMertensPositiveLagPairSum ((W + 1) / p + 1) -
      realMertensPositiveLagPairSum (W / p + 1)) ^ 2 ≤
      realMertensLength (W / p + 1) ^ 2 := by
  rw [postRootLowerCovariance_succQuotient_sub]
  by_cases hdvd : p ∣ W + 1
  · rw [if_pos hdvd]
    exact realMoebiusCovarianceRow_sq_le_lowerMertensEnergy _
  · rw [if_neg hdvd, zero_pow (by norm_num : 2 ≠ 0)]
    exact sq_nonneg _

/-! ## A finite envelope of cumulative Mertens energy -/

/-- `max_{0 <= d <= W} M(d)^2 / (d+1)^(1+epsilon)`.  The zero seat is zero.
This is a Mertens-energy envelope, distinct from its remainder envelope. -/
def mertensSquarePowerEnvelope (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | N + 1 => max (mertensSquarePowerEnvelope ε N)
      (realMertensLength (N + 1 + 1) ^ 2 /
        Real.rpow ((N + 1 + 1 : ℕ) : ℝ) (1 + ε))

theorem mertensSquarePowerEnvelope_nonneg (ε : ℝ) (W : ℕ) :
    0 ≤ mertensSquarePowerEnvelope ε W := by
  induction W with
  | zero => simp [mertensSquarePowerEnvelope]
  | succ W ih =>
      rw [mertensSquarePowerEnvelope]
      exact ih.trans (le_max_left _ _)

theorem mertensSquarePowerEnvelope_mono (ε : ℝ) {N W : ℕ} (hNW : N ≤ W) :
    mertensSquarePowerEnvelope ε N ≤ mertensSquarePowerEnvelope ε W := by
  induction W, hNW using Nat.le_induction with
  | base => exact le_rfl
  | succ W _hNW ih =>
      rw [mertensSquarePowerEnvelope]
      exact ih.trans (le_max_left _ _)

theorem realMertensSquarePowerSeat_le_selfEnvelope (ε : ℝ) (d : ℕ) :
    realMertensLength (d + 1) ^ 2 /
        Real.rpow ((d + 1 : ℕ) : ℝ) (1 + ε) ≤
      mertensSquarePowerEnvelope ε d := by
  cases d with
  | zero => simp [mertensSquarePowerEnvelope, realMertensLength, realMoebiusStep]
  | succ d =>
      rw [mertensSquarePowerEnvelope]
      exact le_max_right _ _

theorem realMertensLength_sq_le_powerEnvelope (ε : ℝ) {d W : ℕ} (hd : d ≤ W) :
    realMertensLength (d + 1) ^ 2 ≤
      mertensSquarePowerEnvelope ε W * Real.rpow ((d + 1 : ℕ) : ℝ) (1 + ε) := by
  have hratio := (realMertensSquarePowerSeat_le_selfEnvelope ε d).trans
    (mertensSquarePowerEnvelope_mono ε hd)
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).1 hratio

private theorem rpow_le_halfPower_of_sq_le
    {c N : ℕ} {α : ℝ} (hα : 0 ≤ α) (hc : c ^ 2 ≤ N) :
    Real.rpow (c : ℝ) α ≤ Real.rpow (N : ℝ) (α / 2) := by
  have hreal : (c : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hc
  have hpowTwo : Real.rpow (c : ℝ) (2 : ℝ) = (c : ℝ) ^ (2 : ℕ) :=
    Real.rpow_natCast (c : ℝ) 2
  calc
    Real.rpow (c : ℝ) α = Real.rpow (c : ℝ) (2 * (α / 2)) := by
      congr 1
      ring
    _ = Real.rpow (Real.rpow (c : ℝ) (2 : ℝ)) (α / 2) :=
      Real.rpow_mul (Nat.cast_nonneg c) _ _
    _ = Real.rpow ((c : ℝ) ^ 2) (α / 2) := by rw [hpowTwo]
    _ ≤ Real.rpow (N : ℝ) (α / 2) :=
      Real.rpow_le_rpow (sq_nonneg _) hreal (by linarith)

/-- On a jumping post-root coordinate, the new cofactor `c=W/p+1` has square
at most `W+1`.  Non-jump rows are zero and require no cofactor-scale estimate. -/
theorem postRootLowerCovarianceRow_sq_le_powerEnvelope_halfPower
    (ε : ℝ) (hε : 0 ≤ ε) (W p : ℕ) (hpRoot : Nat.sqrt (W + 1) < p) :
    postRootLowerCovarianceRow W p ^ 2 ≤
      mertensSquarePowerEnvelope ε W *
        Real.rpow ((W + 1 : ℕ) : ℝ) ((1 + ε) / 2) := by
  have henv := mertensSquarePowerEnvelope_nonneg ε W
  by_cases hdvd : p ∣ W + 1
  · have hpPos : 0 < p := (Nat.zero_le _).trans_lt hpRoot
    have hdiv : (W + 1) / p = W / p + 1 := by
      rw [Nat.succ_div, if_pos hdvd]
    have hquot : (W + 1) / p < p :=
      (Nat.div_lt_iff_lt_mul hpPos).2 ((Nat.sqrt_lt).1 hpRoot)
    have hsq : (W / p + 1) ^ 2 ≤ W + 1 := by
      rw [← hdiv, pow_two]
      exact (Nat.mul_le_mul_left _ hquot.le).trans (Nat.div_mul_le_self (W + 1) p)
    have hprefix := realMertensLength_sq_le_powerEnvelope ε (Nat.div_le_self W p)
    have hpower := rpow_le_halfPower_of_sq_le (by linarith : 0 ≤ 1 + ε) hsq
    calc
      postRootLowerCovarianceRow W p ^ 2 ≤ realMertensLength (W / p + 1) ^ 2 :=
        postRootLowerCovarianceRow_sq_le_lowerMertensEnergy W p
      _ ≤ mertensSquarePowerEnvelope ε W *
          Real.rpow ((W / p + 1 : ℕ) : ℝ) (1 + ε) := hprefix
      _ ≤ _ := mul_le_mul_of_nonneg_left hpower henv
  · rw [postRootLowerCovarianceRow_eq_ite, if_neg hdvd]
    have hpow := Real.rpow_nonneg (show (0 : ℝ) ≤ ((W + 1 : ℕ) : ℝ) by positivity)
      ((1 + ε) / 2)
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using mul_nonneg henv hpow

private theorem normalized_le_inverse_halfPower
    {r A x ε : ℝ} (hx : 0 < x)
    (h : r ≤ A * Real.rpow x ((1 + ε) / 2)) :
    r / Real.rpow x (1 + ε) ≤ A / Real.rpow x ((1 + ε) / 2) := by
  have hs : 0 < Real.rpow x ((1 + ε) / 2) := Real.rpow_pos_of_pos hx _
  have hsplit : Real.rpow x (1 + ε) =
      Real.rpow x ((1 + ε) / 2) * Real.rpow x ((1 + ε) / 2) := by
    have he : 1 + ε = (1 + ε) / 2 + (1 + ε) / 2 := by ring
    calc
      Real.rpow x (1 + ε) = Real.rpow x ((1 + ε) / 2 + (1 + ε) / 2) :=
        congrArg (Real.rpow x) he
      _ = _ := Real.rpow_add hx _ _
  rw [hsplit]
  apply (div_le_div_iff₀ (mul_pos hs hs) hs).2
  have hmul := mul_le_mul_of_nonneg_right h hs.le
  nlinarith

/-- The exact requested normalized contraction for an individual inherited
row.  It holds at every step, so also at any new Mertens-energy record. -/
theorem postRootLowerCovarianceRow_sq_div_power_le_envelope_div_halfPower
    (ε : ℝ) (hε : 0 ≤ ε) (W p : ℕ) (hpRoot : Nat.sqrt (W + 1) < p) :
    postRootLowerCovarianceRow W p ^ 2 /
        Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) ≤
      mertensSquarePowerEnvelope ε W /
        Real.rpow ((W + 1 : ℕ) : ℝ) ((1 + ε) / 2) :=
  normalized_le_inverse_halfPower (by positivity)
    (postRootLowerCovarianceRow_sq_le_powerEnvelope_halfPower ε hε W p hpRoot)

/-! ## One active inherited row, with all family departures retained -/

def postRootPrimeFamilyCovarianceRowTotal (W : ℕ) : ℝ :=
  ∑ p ∈ postRootPrimeFamilySet (W + 1), postRootLowerCovarianceRow W p

/-- The covariance removed when a prime family leaves at the square-root wall.
Its support is exactly the old family set minus the new family set. -/
def postRootPrimeFamilyCovarianceDeparture (W : ℕ) : ℝ :=
  ∑ p ∈ postRootPrimeFamilySet W \ postRootPrimeFamilySet (W + 1),
    realMertensPositiveLagPairSum (W / p + 1)

theorem postRootPrimeFamilyCovarianceRowTotal_eq_single_of_dvd
    {W p : ℕ} (hp : p ∈ postRootPrimeFamilySet (W + 1)) (hdvd : p ∣ W + 1) :
    postRootPrimeFamilyCovarianceRowTotal W = postRootLowerCovarianceRow W p := by
  unfold postRootPrimeFamilyCovarianceRowTotal
  apply Finset.sum_eq_single p
  · intro q hq hqp
    rw [postRootLowerCovarianceRow_eq_ite, if_neg]
    intro hqdvd
    exact hqp (postRootPrimeFamily_divisor_unique hq hp hqdvd hdvd)
  · intro hnot
    exact (hnot hp).elim

/-- Uniqueness allows the entire active inherited row total to keep the
individual half-power estimate, without a prime-count multiplicity loss. -/
theorem postRootPrimeFamilyCovarianceRowTotal_sq_le_powerEnvelope_halfPower
    (ε : ℝ) (hε : 0 ≤ ε) (W : ℕ) :
    postRootPrimeFamilyCovarianceRowTotal W ^ 2 ≤
      mertensSquarePowerEnvelope ε W *
        Real.rpow ((W + 1 : ℕ) : ℝ) ((1 + ε) / 2) := by
  by_cases hex : ∃ p ∈ postRootPrimeFamilySet (W + 1), p ∣ W + 1
  · obtain ⟨p, hp, hdvd⟩ := hex
    rw [postRootPrimeFamilyCovarianceRowTotal_eq_single_of_dvd hp hdvd]
    exact postRootLowerCovarianceRow_sq_le_powerEnvelope_halfPower ε hε W p
      (mem_postRootPrimeFamilySet.mp hp).1
  · have hzero : postRootPrimeFamilyCovarianceRowTotal W = 0 := by
      unfold postRootPrimeFamilyCovarianceRowTotal
      apply Finset.sum_eq_zero
      intro p hp
      rw [postRootLowerCovarianceRow_eq_ite, if_neg]
      intro hdvd
      exact hex ⟨p, hp, hdvd⟩
    rw [hzero]
    have henv := mertensSquarePowerEnvelope_nonneg ε W
    have hpow := Real.rpow_nonneg (show (0 : ℝ) ≤ ((W + 1 : ℕ) : ℝ) by positivity)
      ((1 + ε) / 2)
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using mul_nonneg henv hpow

theorem postRootPrimeFamilyCovarianceRowTotal_sq_div_power_le_envelope_div_halfPower
    (ε : ℝ) (hε : 0 ≤ ε) (W : ℕ) :
    postRootPrimeFamilyCovarianceRowTotal W ^ 2 /
        Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) ≤
      mertensSquarePowerEnvelope ε W /
        Real.rpow ((W + 1 : ℕ) : ℝ) ((1 + ε) / 2) :=
  normalized_le_inverse_halfPower (by positivity)
    (postRootPrimeFamilyCovarianceRowTotal_sq_le_powerEnvelope_halfPower ε hε W)

/-- The full inherited increment is the at-most-one active row minus the
departing family covariance.  New prime coordinates have zero old covariance. -/
theorem postRootPrimeFamilyCovarianceIncrement_eq_rowTotal_sub_departure (W : ℕ) :
    postRootPrimeFamilyCovarianceIncrement W =
      postRootPrimeFamilyCovarianceRowTotal W - postRootPrimeFamilyCovarianceDeparture W := by
  let S := postRootPrimeFamilySet W
  let T := postRootPrimeFamilySet (W + 1)
  let f := fun p : ℕ => realMertensPositiveLagPairSum (W / p + 1)
  have hnew : ∀ p ∈ T, p ∉ S → f p = 0 := by
    intro p hpT hpS
    have heq := postRootPrimeFamilySet_succ_new_eq_endpoint hpT hpS
    subst p
    dsimp [f]
    rw [Nat.div_eq_of_lt (Nat.lt_succ_self W)]
    simp [realMertensPositiveLagPairSum, realMertensLength, realMoebiusStep]
  have hT : (∑ p ∈ T ∩ S, f p) = ∑ p ∈ T, f p := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro p hpT hpNot
    apply hnew p hpT
    intro hpS
    exact hpNot (Finset.mem_inter.mpr ⟨hpT, hpS⟩)
  have hdiff : S \ (S ∩ T) = S \ T := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsplit := Finset.sum_sdiff
    (show S ∩ T ⊆ S from Finset.inter_subset_left) (f := f)
  rw [hdiff, Finset.inter_comm S T, hT] at hsplit
  unfold postRootPrimeFamilyCovarianceIncrement postRootPrimeFamilyCovarianceTotal
    postRootPrimeFamilyCovarianceRowTotal postRootPrimeFamilyCovarianceDeparture
    postRootLowerCovarianceRow
  rw [Finset.sum_sub_distrib]
  dsimp [S, T, f] at hsplit
  linarith

/-- The exact innovation after moving inside the individual inherited row.
The global new row and the prime-square departure are still present. -/
theorem postRootCovarianceLocalInnovation_eq_row_sub_inherited_add_departure (W : ℕ) :
    postRootCovarianceLocalInnovation W =
      realMoebiusStep (W + 1) * realMertensLength (W + 1) -
        postRootPrimeFamilyCovarianceRowTotal W +
        postRootPrimeFamilyCovarianceDeparture W := by
  unfold postRootCovarianceLocalInnovation
  rw [postRootPrimeFamilyCovarianceIncrement_eq_rowTotal_sub_departure]
  ring

/-- Feed this exact row decomposition into the existing record bound. -/
theorem postRootCovariancePowerRecordExcess_le_fullRowBudget
    (ε : ℝ) (hε : 0 < ε) {W : ℕ} (hW : 2 ≤ W) :
    postRootCovariancePowerRecordExcess ε W ≤
      max 0 ((realMoebiusStep (W + 1) * realMertensLength (W + 1) -
        postRootPrimeFamilyCovarianceRowTotal W +
        postRootPrimeFamilyCovarianceDeparture W) /
          Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε)) := by
  have h := postRootCovariancePowerRecordExcess_le_localInnovationBudget ε hε hW
  unfold postRootCovariancePowerLocalInnovationBudget at h
  rw [postRootCovarianceLocalInnovation_eq_row_sub_inherited_add_departure] at h
  exact h

/-! ## Audit which covariance row reverses sign -/

/-- Reversing only the atom against an unchanged prefix reverses the product. -/
theorem freshPrimeAtom_mul_unchangedPrefix_eq_neg_row
    {p c : ℕ} (hp : p.Prime) (hc : c < p) :
    realMoebiusStep (p * c) * realMertensLength c =
      -(realMoebiusStep c * realMertensLength c) := by
  rw [realMoebiusStep_prime_mul_of_lt hp hc]
  ring

/-- On the actual transported family both factors reverse.  Consequently its
internal cumulative covariance row is preserved, not negated. -/
theorem freshPrimeFamily_covarianceRow_eq_lowerRow
    {p c : ℕ} (hp : p.Prime) (hc : c < p) :
    realMoebiusStep (p * c) * largePrimeFamilyPrefix p c =
      realMoebiusStep c * realMertensLength c := by
  rw [realMoebiusStep_prime_mul_of_lt hp hc, largePrimeFamilyPrefix_eq_neg hp hc.le]
  ring

/-- Subtracting the inherited family row leaves the full complementary-prefix
interaction.  Replacing the physical prefix by the lower one would lose it. -/
theorem freshPrimePhysicalRow_sub_inherited_eq_complementaryPrefix
    {p c : ℕ} (hp : p.Prime) (hc : c < p) :
    realMoebiusStep (p * c) * realMertensLength (p * c) -
        realMoebiusStep c * realMertensLength c =
      -realMoebiusStep c * (realMertensLength (p * c) + realMertensLength c) := by
  rw [realMoebiusStep_prime_mul_of_lt hp hc]
  ring

/-- A top-half family has no inherited covariance jump. -/
theorem postRootLowerCovarianceRow_eq_zero_of_upperHalf
    {W p : ℕ} (hp : (W + 1) / 2 < p) : postRootLowerCovarianceRow W p = 0 := by
  have hpPos : 0 < p := (Nat.zero_le _).trans_lt hp
  by_cases hdvd : p ∣ W + 1
  · have hdiv : (W + 1) / p = W / p + 1 := by
      rw [Nat.succ_div, if_pos hdvd]
    have hsmall : (W + 1) / p < 2 := by
      apply (Nat.div_lt_iff_lt_mul hpPos).2
      have h := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).1 hp
      simpa [Nat.mul_comm] using h
    rw [hdiv] at hsmall
    have hzero : W / p = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      have hone : 1 ≤ W / p := hpos
      have htwo : 2 ≤ W / p + 1 := Nat.succ_le_succ hone
      exact (Nat.not_le_of_gt hsmall) htwo
    rw [postRootLowerCovarianceRow_eq_ite, if_pos hdvd, hzero]
    simp [realMertensLength, realMoebiusStep]
  · rw [postRootLowerCovarianceRow_eq_ite, if_neg hdvd]

/-- At a new prime, inherited rows and square-wall departures vanish, but the
global covariance row is still `-M(W)`.  Its effect is not only a diagonal unit. -/
theorem postRootCovarianceLocalInnovation_eq_neg_prefix_of_prime
    {W : ℕ} (hprime : (W + 1).Prime) :
    postRootCovarianceLocalInnovation W = -realMertensLength (W + 1) := by
  have hrows : postRootPrimeFamilyCovarianceRowTotal W = 0 := by
    unfold postRootPrimeFamilyCovarianceRowTotal
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hdvd : p ∣ W + 1
    · have heq := (Nat.prime_dvd_prime_iff_eq
        (mem_postRootPrimeFamilySet.mp hp).2.2 hprime).mp hdvd
      subst p
      apply postRootLowerCovarianceRow_eq_zero_of_upperHalf
      exact Nat.div_lt_self (Nat.succ_pos W) (by norm_num : 1 < 2)
    · rw [postRootLowerCovarianceRow_eq_ite, if_neg hdvd]
  have hdepart : postRootPrimeFamilyCovarianceDeparture W = 0 := by
    unfold postRootPrimeFamilyCovarianceDeparture
    apply Finset.sum_eq_zero
    intro p hp
    rcases Finset.mem_sdiff.mp hp with ⟨hpOld, hpNot⟩
    have hsquare := postRootPrimeFamilySet_succ_removed_eq_square hpOld hpNot
    have hdvd : p ∣ W + 1 := by
      rw [← hsquare]
      exact dvd_mul_right p p
    have hpData := mem_postRootPrimeFamilySet.mp hpOld
    have heq := (Nat.prime_dvd_prime_iff_eq hpData.2.2 hprime).mp hdvd
    have hpW := hpData.2.1
    omega
  rw [postRootCovarianceLocalInnovation_eq_row_sub_inherited_add_departure, hrows, hdepart]
  simp [realMoebiusStep, ArithmeticFunction.moebius_apply_prime hprime]

end RHLean.Proof