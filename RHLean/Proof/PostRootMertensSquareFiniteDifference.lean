import RHLean.Proof.PostRootCovariancePowerEnvelope

/-!
# Square energy with signed post-root transport

Restore the linear coordinate of the LCM falling energy while retaining the
existing post-root family energy and the record process.  All prefixes use
the physical convention `M(W) = realMertensLength (W + 1)`.

The fresh-prime family has mass `-M(W/p)` and square energy `M(W/p)^2`.
Subtracting these family energies has a fixed favorable sign.  This is a
same-endpoint decomposition; it does not assert monotonicity in `W` or prove
the still-open positive-power bound on the difference.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The existing transported family energy in the real-prefix convention. -/
theorem postRootFamilyMertensSquareEnergy_eq_sum_realMertensLength_sq (W : ℕ) :
    postRootFamilyMertensSquareEnergy W =
      ∑ p ∈ postRootPrimeFamilySet W, realMertensLength (W / p + 1) ^ 2 := by
  unfold postRootFamilyMertensSquareEnergy
  simp_rw [norm_mertensSummatory_sq_eq_realMertensLength_sq]

/-- The pure square-energy finite difference, using the already-defined high
transport rather than introducing a second family carrier. -/
def postRootMertensSquareFiniteDifference (W : ℕ) : ℝ :=
  realMertensLength (W + 1) ^ 2 - postRootFamilyMertensSquareEnergy W

/-- The linear coordinate removed by passage to the LCM falling energy. -/
def postRootMertensLinearFiniteDifference (W : ℕ) : ℝ :=
  realMertensLength (W + 1) -
    ∑ p ∈ postRootPrimeFamilySet W, realMertensLength (W / p + 1)

/-- Exact restoration of the linear coordinate: no estimate or sign loss. -/
theorem postRootFallingEnergyFiniteDifference_eq_square_sub_linear (W : ℕ) :
    postRootFallingEnergyFiniteDifference W =
      postRootMertensSquareFiniteDifference W -
        postRootMertensLinearFiniteDifference W := by
  unfold postRootFallingEnergyFiniteDifference
    postRootMertensSquareFiniteDifference postRootMertensLinearFiniteDifference
  rw [postRootFamilyMertensSquareEnergy_eq_sum_realMertensLength_sq,
    Finset.sum_sub_distrib]
  ring

private theorem abs_realMertensLength_endpoint_le (W : ℕ) :
    |realMertensLength (W + 1)| ≤ (W : ℝ) := by
  have h := norm_mertensSummatory_sub_le 0 W (Nat.zero_le W)
  rw [mertensSummatory_zero, sub_zero, Nat.sub_zero,
    ← realMertensLength_cast_eq_mertensSummatory,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- Quotient packing pays for the entire linear correction at cost `2W`.
Absolute values are used only on this correction, after the energy split. -/
theorem abs_postRootMertensLinearFiniteDifference_le_two_mul_endpoint (W : ℕ) :
    |postRootMertensLinearFiniteDifference W| ≤ 2 * (W : ℝ) := by
  have hpack :
      (∑ p ∈ postRootPrimeFamilySet W, ((W / p : ℕ) : ℝ)) ≤ (W : ℝ) := by
    exact_mod_cast sum_postRootPrimeFamily_quotients_le_endpoint W
  have hsum :
      |∑ p ∈ postRootPrimeFamilySet W, realMertensLength (W / p + 1)| ≤
        (W : ℝ) := by
    calc
      |∑ p ∈ postRootPrimeFamilySet W, realMertensLength (W / p + 1)| ≤
          ∑ p ∈ postRootPrimeFamilySet W, |realMertensLength (W / p + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ postRootPrimeFamilySet W, ((W / p : ℕ) : ℝ) :=
        Finset.sum_le_sum fun p _hp => abs_realMertensLength_endpoint_le (W / p)
      _ ≤ (W : ℝ) := hpack
  unfold postRootMertensLinearFiniteDifference
  calc
    |realMertensLength (W + 1) -
        ∑ p ∈ postRootPrimeFamilySet W, realMertensLength (W / p + 1)| ≤
      |realMertensLength (W + 1)| +
        |∑ p ∈ postRootPrimeFamilySet W, realMertensLength (W / p + 1)| :=
      abs_sub _ _
    _ ≤ 2 * (W : ℝ) := by
      have h := abs_realMertensLength_endpoint_le W
      linarith

/-- Squaring the actual sign-reversed prime-comb family yields exactly the
transported lower square, including the unit cofactor. -/
theorem primeCombLargePrimeFamilyMass_norm_sq_eq_lower_square
    {W p : ℕ} (hp : p ∈ postRootPrimeFamilySet W) :
    ‖primeCombLargePrimeFamilyMass W p‖ ^ 2 =
      realMertensLength (W / p + 1) ^ 2 := by
  rcases mem_postRootPrimeFamilySet.mp hp with ⟨hpRoot, _hpW, hpPrime⟩
  rw [primeCombLargePrimeFamilyMass_eq_neg_mertens hpPrime hpRoot, norm_neg,
    norm_mertensSummatory_sq_eq_realMertensLength_sq]

theorem postRootFamilyMertensSquareEnergy_nonneg (W : ℕ) :
    0 ≤ postRootFamilyMertensSquareEnergy W := by
  unfold postRootFamilyMertensSquareEnergy
  exact Finset.sum_nonneg fun p _hp => sq_nonneg _

/-- Every transported square has its favorable sign at this fixed endpoint. -/
theorem neg_postRootFamilyMertensSquareEnergy_nonpos (W : ℕ) :
    -postRootFamilyMertensSquareEnergy W ≤ 0 :=
  neg_nonpos.mpr (postRootFamilyMertensSquareEnergy_nonneg W)

/-! ## The existing Bessel diagonal on its literal complementary carrier -/

/-- Diagonal energy of one family is the squared Möbius mass on the existing
seat-product image used by quotient packing. -/
theorem sum_signedFirstJumpPrimeSeatProductSet_sq_eq_lowerDiagonal
    {W p : ℕ} (hp : p ∈ postRootPrimeFamilySet W) :
    (∑ n ∈ signedFirstJumpPrimeSeatProductSet W p, realMoebiusStep n ^ 2) =
      realMertensDiagonal (W / p + 1) := by
  rcases mem_postRootPrimeFamilySet.mp hp with ⟨hpRoot, _hpW, hpPrime⟩
  unfold signedFirstJumpPrimeSeatProductSet
  rw [Finset.sum_image]
  · rw [← sum_Icc_realMoebiusStep_sq_eq_realMertensDiagonal]
    apply Finset.sum_congr rfl
    intro c hc
    have hcLt := signedFirstJumpPrimeSeat_lt_prime hpPrime hpRoot hc
    rw [Nat.mul_comm c p, realMoebiusStep_prime_mul_of_lt hpPrime hcLt, neg_sq]
  · intro a _ha b _hb hab
    exact Nat.eq_of_mul_eq_mul_right hpPrime.pos hab

/-- The transported diagonal is a sum on the disjoint union already used for
product packing.  Fresh-prime sign reversal preserves each squared weight. -/
theorem postRootFamilyDiagonalEnergy_eq_seatProductUnion (W : ℕ) :
    postRootFamilyDiagonalEnergy W =
      ∑ n ∈ (signedFirstJumpPostRootPrimeSet W).biUnion
          (signedFirstJumpPrimeSeatProductSet W), realMoebiusStep n ^ 2 := by
  rw [Finset.sum_biUnion (signedFirstJumpPrimeSeatProductSet_pairwiseDisjoint W)]
  unfold postRootFamilyDiagonalEnergy
  rw [← postRootPrimeFamilySet_eq_signedFirstJumpPostRootPrimeSet]
  apply Finset.sum_congr rfl
  intro p hp
  exact (sum_signedFirstJumpPrimeSeatProductSet_sq_eq_lowerDiagonal hp).symm

/-- The Bessel correction is literally the unassigned squarefree diagonal. -/
theorem postRootComplementDiagonalResidual_eq_complement_sum (W : ℕ) :
    postRootComplementDiagonalResidual W =
      ∑ n ∈ Finset.Icc 1 W \
          (signedFirstJumpPostRootPrimeSet W).biUnion
            (signedFirstJumpPrimeSeatProductSet W), realMoebiusStep n ^ 2 := by
  have hsplit := Finset.sum_sdiff
    (signedFirstJumpPrimeSeatProductUnion_subset_Icc W)
    (f := fun n : ℕ => realMoebiusStep n ^ 2)
  rw [sum_Icc_realMoebiusStep_sq_eq_realMertensDiagonal,
    ← postRootFamilyDiagonalEnergy_eq_seatProductUnion] at hsplit
  unfold postRootComplementDiagonalResidual
  linarith

theorem postRootComplementDiagonalResidual_nonneg (W : ℕ) :
    0 ≤ postRootComplementDiagonalResidual W := by
  rw [postRootComplementDiagonalResidual_eq_complement_sum]
  exact Finset.sum_nonneg fun n _hn => sq_nonneg _

theorem postRootComplementDiagonalResidual_le_endpoint (W : ℕ) :
    postRootComplementDiagonalResidual W ≤ (W : ℝ) := by
  have hfamily : 0 ≤ postRootFamilyDiagonalEnergy W := by
    unfold postRootFamilyDiagonalEnergy
    exact Finset.sum_nonneg fun p _hp => realMertensDiagonal_nonneg _
  have hdiag : realMertensDiagonal (W + 1) ≤ (W : ℝ) := by
    rw [← sum_Icc_realMoebiusStep_sq_eq_realMertensDiagonal]
    calc
      (∑ n ∈ Finset.Icc 1 W, realMoebiusStep n ^ 2) ≤
          ∑ _n ∈ Finset.Icc 1 W, (1 : ℝ) :=
        Finset.sum_le_sum fun n _hn => realMoebiusStep_sq_le_one n
      _ = (W : ℝ) := by simp
  unfold postRootComplementDiagonalResidual
  linarith

/-- The requested square difference is the existing Bessel defect with its
nonnegative complementary diagonal restored. -/
theorem postRootMertensSquareFiniteDifference_eq_two_mul_remainder_add_diagonal
    (W : ℕ) :
    postRootMertensSquareFiniteDifference W =
      2 * postRootCovarianceRemainder W + postRootComplementDiagonalResidual W := by
  have h := two_mul_postRootCovarianceRemainder_eq_besselDefect W
  rw [norm_mertensSummatory_sq_eq_realMertensLength_sq] at h
  unfold postRootMertensSquareFiniteDifference
  linarith

theorem two_mul_postRootCovarianceRemainder_le_squareFiniteDifference (W : ℕ) :
    2 * postRootCovarianceRemainder W ≤ postRootMertensSquareFiniteDifference W := by
  rw [postRootMertensSquareFiniteDifference_eq_two_mul_remainder_add_diagonal]
  have h := postRootComplementDiagonalResidual_nonneg W
  linarith

/-! ## The same positive-power seam and terminal bootstrap -/

/-- One-sided square-energy finite-difference target.  This proposition remains
an arithmetic input; the identities below do not supply its bound. -/
def PostRootMertensSquareFiniteDifferencePowerStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ W : ℕ, 2 ≤ W →
        postRootMertensSquareFiniteDifference W ≤
          D * Real.rpow (W : ℝ) (1 + ε)

/-- Restoring the linear coordinate costs at most two units of power scale. -/
theorem postRootMertensSquareFiniteDifferencePower_iff_fallingEnergyPower :
    PostRootMertensSquareFiniteDifferencePowerStatement ↔
      PostRootFallingEnergyFiniteDifferencePowerStatement := by
  constructor
  · intro hsquare ε hε
    rcases hsquare ε hε with ⟨D, hD, hbound⟩
    refine ⟨D + 2, by positivity, ?_⟩
    intro W hW
    have hb := hbound W hW
    have hl := abs_le.mp
      (abs_postRootMertensLinearFiniteDifference_le_two_mul_endpoint W)
    have hs := endpoint_le_postRootPowerScale hε hW
    rw [postRootFallingEnergyFiniteDifference_eq_square_sub_linear]
    nlinarith [hl.1]
  · intro hfall ε hε
    rcases hfall ε hε with ⟨D, hD, hbound⟩
    refine ⟨D + 2, by positivity, ?_⟩
    intro W hW
    have hb := hbound W hW
    have hl := abs_le.mp
      (abs_postRootMertensLinearFiniteDifference_le_two_mul_endpoint W)
    have hs := endpoint_le_postRootPowerScale hε hW
    rw [postRootFallingEnergyFiniteDifference_eq_square_sub_linear] at hb
    nlinarith [hl.2]

/-- A sharper direct equivalence uses the literal complementary diagonal:
`0 <= Delta_sq - 2E <= W`. -/
theorem postRootMertensSquareFiniteDifferencePower_iff_powerRemainder :
    PostRootMertensSquareFiniteDifferencePowerStatement ↔
      PostRootCovariancePowerRemainderStatement := by
  constructor
  · intro hsquare ε hε
    rcases hsquare ε hε with ⟨D, hD, hbound⟩
    refine ⟨D / 2, by positivity, ?_⟩
    intro W hW
    have hb := hbound W hW
    have hle := two_mul_postRootCovarianceRemainder_le_squareFiniteDifference W
    nlinarith
  · intro hrem ε hε
    rcases hrem ε hε with ⟨D, hD, hbound⟩
    refine ⟨2 * D + 1, by positivity, ?_⟩
    intro W hW
    have hb := hbound W hW
    have hd := postRootComplementDiagonalResidual_le_endpoint W
    have hs := endpoint_le_postRootPowerScale hε hW
    rw [postRootMertensSquareFiniteDifference_eq_two_mul_remainder_add_diagonal]
    nlinarith

theorem postRootCovariancePowerEnvelopeBounded_iff_squareFiniteDifferencePower :
    PostRootCovariancePowerEnvelopeBoundedStatement ↔
      PostRootMertensSquareFiniteDifferencePowerStatement := by
  rw [postRootCovariancePowerEnvelopeBounded_iff_powerRemainder,
    postRootMertensSquareFiniteDifferencePower_iff_powerRemainder]

theorem postRootCovariancePowerRecordExcessBounded_iff_squareFiniteDifferencePower :
    PostRootCovariancePowerRecordExcessBoundedStatement ↔
      PostRootMertensSquareFiniteDifferencePowerStatement := by
  rw [postRootCovariancePowerRecordExcessBounded_iff_powerRemainder,
    postRootMertensSquareFiniteDifferencePower_iff_powerRemainder]

theorem mertensEnergyBounded_of_postRootMertensSquareFiniteDifferencePower
    (hsquare : PostRootMertensSquareFiniteDifferencePowerStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_postRootCovariancePowerRemainder
    (postRootMertensSquareFiniteDifferencePower_iff_powerRemainder.mp hsquare)

/-! ## Exact reciprocal bands, including the top-half unit transport -/

/-- The old prime-comb band is precisely a quotient fibre of the same post-root
prime set used by covariance and square energy. -/
theorem primeCombPostRootReciprocalBand_eq_quotient_filter
    (W z : ℕ) (hz : 0 < z) :
    primeCombPostRootReciprocalBand W z =
      (postRootPrimeFamilySet W).filter (fun p => W / p = z) := by
  ext p
  constructor
  · intro hp
    rcases mem_primeCombPostRootReciprocalBand.mp hp with ⟨hpBand, hpRoot⟩
    exact Finset.mem_filter.mpr
      ⟨mem_postRootPrimeFamilySet.mpr
        ⟨hpRoot, primeCombReciprocalBand_le_endpoint hpBand,
          primeCombReciprocalBand_prime hpBand⟩,
        primeCombReciprocalBand_div_eq hz hpBand⟩
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpSet, hquot⟩
    rcases mem_postRootPrimeFamilySet.mp hpSet with ⟨hpRoot, _hpW, hpPrime⟩
    apply mem_primeCombPostRootReciprocalBand.mpr
    refine ⟨mem_primeCombReciprocalBand.mpr ⟨?_, ?_, hpPrime⟩, hpRoot⟩
    · apply (Nat.div_lt_iff_lt_mul (by omega : 0 < z + 1)).2
      have h := (Nat.div_lt_iff_lt_mul hpPrime.pos).1
        (show W / p < z + 1 by omega)
      simpa [Nat.mul_comm] using h
    · apply (Nat.le_div_iff_mul_le hz).2
      have h := Nat.div_mul_le_self W p
      rw [hquot] at h
      simpa [Nat.mul_comm] using h

theorem sum_postRootReciprocalBand_lower_square_eq_card_mul
    (W z : ℕ) (hz : 0 < z) :
    (∑ p ∈ primeCombPostRootReciprocalBand W z,
      realMertensLength (W / p + 1) ^ 2) =
      ((primeCombPostRootReciprocalBand W z).card : ℝ) *
        realMertensLength (z + 1) ^ 2 := by
  calc
    (∑ p ∈ primeCombPostRootReciprocalBand W z,
        realMertensLength (W / p + 1) ^ 2) =
        ∑ _p ∈ primeCombPostRootReciprocalBand W z,
          realMertensLength (z + 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [primeCombReciprocalBand_div_eq hz
        (mem_primeCombPostRootReciprocalBand.mp hp).1]
    _ = _ := by simp

/-- Grouping all high transport by its reciprocal quotient retains the entire
signed-energy subtraction; every lower endpoint is at most the square root. -/
theorem postRootFamilyMertensSquareEnergy_eq_reciprocalBands (W : ℕ) :
    postRootFamilyMertensSquareEnergy W =
      ∑ z ∈ Finset.Icc 1 (Nat.sqrt W),
        ((primeCombPostRootReciprocalBand W z).card : ℝ) *
          realMertensLength (z + 1) ^ 2 := by
  rw [postRootFamilyMertensSquareEnergy_eq_sum_realMertensLength_sq]
  symm
  calc
    (∑ z ∈ Finset.Icc 1 (Nat.sqrt W),
        ((primeCombPostRootReciprocalBand W z).card : ℝ) *
          realMertensLength (z + 1) ^ 2) =
      ∑ z ∈ Finset.Icc 1 (Nat.sqrt W),
        ∑ p ∈ (postRootPrimeFamilySet W).filter (fun p => W / p = z),
          realMertensLength (W / p + 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro z hz
      have hzpos : 0 < z := (Finset.mem_Icc.mp hz).1
      rw [← sum_postRootReciprocalBand_lower_square_eq_card_mul W z hzpos,
        primeCombPostRootReciprocalBand_eq_quotient_filter W z hzpos]
    _ = ∑ p ∈ postRootPrimeFamilySet W,
        ∑ z ∈ Finset.Icc 1 (Nat.sqrt W),
          if W / p = z then realMertensLength (W / p + 1) ^ 2 else 0 := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ p ∈ postRootPrimeFamilySet W,
        realMertensLength (W / p + 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpData := mem_postRootPrimeFamilySet.mp hp
      have hqpos : 0 < W / p := Nat.div_pos hpData.2.1 hpData.2.2.pos
      have hqroot : W / p ≤ Nat.sqrt W := by
        apply (Nat.le_sqrt).2
        simpa [pow_two] using postRootPrimeFamily_quotient_sq_le hp
      have hqmem : W / p ∈ Finset.Icc 1 (Nat.sqrt W) :=
        Finset.mem_Icc.mpr ⟨hqpos, hqroot⟩
      simp [hqmem]

theorem postRootMertensSquareFiniteDifference_eq_reciprocalBands (W : ℕ) :
    postRootMertensSquareFiniteDifference W =
      realMertensLength (W + 1) ^ 2 -
        ∑ z ∈ Finset.Icc 1 (Nat.sqrt W),
          ((primeCombPostRootReciprocalBand W z).card : ℝ) *
            realMertensLength (z + 1) ^ 2 := by
  unfold postRootMertensSquareFiniteDifference
  rw [postRootFamilyMertensSquareEnergy_eq_reciprocalBands]

theorem primeCombPostRootReciprocalBand_one_eq_upperHalf (W : ℕ) :
    primeCombPostRootReciprocalBand W 1 =
      (Finset.Ioc (W / 2) W).filter Nat.Prime := by
  have hband : primeCombReciprocalBand W 1 =
      (Finset.Ioc (W / 2) W).filter Nat.Prime := by
    simp [primeCombReciprocalBand]
  unfold primeCombPostRootReciprocalBand
  rw [hband]
  apply Finset.filter_eq_self.mpr
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpRange, hpPrime⟩
  have hWlt : W < p * 2 :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).1 (Finset.mem_Ioc.mp hpRange).1
  apply (Nat.sqrt_lt).2
  have hp2 := hpPrime.two_le
  nlinarith

/-- Each top-half prime transports exactly one square-energy unit. -/
theorem realMertensLength_quotient_sq_eq_one_of_upperHalf
    {W p : ℕ} (hp : p ∈ (Finset.Ioc (W / 2) W).filter Nat.Prime) :
    realMertensLength (W / p + 1) ^ 2 = 1 := by
  have hpBand : p ∈ primeCombReciprocalBand W 1 := by
    simpa [primeCombReciprocalBand] using hp
  rw [primeCombReciprocalBand_div_eq (by norm_num : 0 < 1) hpBand]
  norm_num [realMertensLength, realMoebiusStep, Finset.sum_range_succ]

/-- Exact prime-count gain, valid even at the small endpoints.  The casts are
separate so subtraction is in the signed real coordinate. -/
theorem sum_upperHalf_lower_square_eq_primeCounting_sub (W : ℕ) :
    (∑ p ∈ (Finset.Ioc (W / 2) W).filter Nat.Prime,
      realMertensLength (W / p + 1) ^ 2) =
      (Nat.primeCounting W : ℝ) - (Nat.primeCounting (W / 2) : ℝ) := by
  have hcount := primeCard_Ioc_add_primeCounting_eq (Nat.div_le_self W 2)
  have hcountReal :
      (((Finset.Ioc (W / 2) W).filter Nat.Prime).card : ℝ) +
        (Nat.primeCounting (W / 2) : ℝ) = (Nat.primeCounting W : ℝ) := by
    exact_mod_cast hcount
  calc
    (∑ p ∈ (Finset.Ioc (W / 2) W).filter Nat.Prime,
        realMertensLength (W / p + 1) ^ 2) =
      ∑ _p ∈ (Finset.Ioc (W / 2) W).filter Nat.Prime, (1 : ℝ) :=
        Finset.sum_congr rfl fun p hp => realMertensLength_quotient_sq_eq_one_of_upperHalf hp
    _ = (((Finset.Ioc (W / 2) W).filter Nat.Prime).card : ℝ) := by simp
    _ = _ := by linarith

/-- Expose the exact negative unit for every top-half prime inside the whole
square difference, retaining all other high-prime squares with their sign. -/
theorem postRootMertensSquareFiniteDifference_eq_sub_upperHalf_sub_remaining
    (W : ℕ) :
    postRootMertensSquareFiniteDifference W =
      realMertensLength (W + 1) ^ 2 -
        ((Nat.primeCounting W : ℝ) - (Nat.primeCounting (W / 2) : ℝ)) -
        ∑ p ∈ postRootPrimeFamilySet W \
            (Finset.Ioc (W / 2) W).filter Nat.Prime,
          realMertensLength (W / p + 1) ^ 2 := by
  have hsub : (Finset.Ioc (W / 2) W).filter Nat.Prime ⊆
      postRootPrimeFamilySet W := by
    rw [← primeCombPostRootReciprocalBand_one_eq_upperHalf,
      primeCombPostRootReciprocalBand_eq_quotient_filter W 1 (by norm_num)]
    exact Finset.filter_subset _ _
  have hsplit := Finset.sum_sdiff hsub
    (f := fun p : ℕ => realMertensLength (W / p + 1) ^ 2)
  rw [sum_upperHalf_lower_square_eq_primeCounting_sub,
    ← postRootFamilyMertensSquareEnergy_eq_sum_realMertensLength_sq] at hsplit
  unfold postRootMertensSquareFiniteDifference
  linarith

/-! ## Feed the existing record event into square energy -/

/-- Record budget with all high transported squares still subtracted.
The nonnegative complementary diagonal allows an upper bound with no allowance. -/
def postRootCovariancePowerSquareRecordBudget (ε : ℝ) (N : ℕ) : ℝ :=
  max 0 (postRootMertensSquareFiniteDifference (N + 1) /
      (2 * Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε)) -
    postRootCovariancePowerEnvelope ε N)

private theorem max_zero_sub_max_zero_eq {a b : ℝ} (hb : 0 ≤ b) :
    max 0 (max 0 a - b) = max 0 (a - b) := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_right ha]
  · have ha0 : a ≤ 0 := le_of_not_ge ha
    rw [max_eq_left ha0, max_eq_left (by linarith : 0 - b ≤ 0),
      max_eq_left (by linarith : a - b ≤ 0)]

theorem postRootCovariancePowerRecordExcess_le_squareRecordBudget
    (ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    postRootCovariancePowerRecordExcess ε N ≤
      postRootCovariancePowerSquareRecordBudget ε N := by
  have hW : 2 ≤ N + 1 := by omega
  have hscale : 0 < Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hratio :
      postRootCovarianceRemainder (N + 1) /
          Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) ≤
        postRootMertensSquareFiniteDifference (N + 1) /
          (2 * Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε)) := by
    apply (div_le_div_iff₀ hscale (mul_pos (by norm_num) hscale)).2
    have h := two_mul_postRootCovarianceRemainder_le_squareFiniteDifference (N + 1)
    nlinarith
  unfold postRootCovariancePowerRecordExcess postRootCovariancePowerSeat
    postRootCovariancePowerSquareRecordBudget
  rw [if_pos hW,
    max_zero_sub_max_zero_eq (postRootCovariancePowerEnvelope_nonneg ε N)]
  exact max_le_max le_rfl (sub_le_sub_right hratio _)

/-- A genuine record must clear the old envelope in the square-energy
coordinate itself.  The complete high transport has not been discarded. -/
theorem postRootCovariancePowerEnvelope_lt_squareNormalized_of_recordExcess_pos
    (ε : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (hrecord : 0 < postRootCovariancePowerRecordExcess ε N) :
    postRootCovariancePowerEnvelope ε N <
      postRootMertensSquareFiniteDifference (N + 1) /
        (2 * Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε)) := by
  have hbudget := lt_of_lt_of_le hrecord
    (postRootCovariancePowerRecordExcess_le_squareRecordBudget ε hN)
  unfold postRootCovariancePowerSquareRecordBudget at hbudget
  by_contra hnot
  rw [max_eq_left (sub_nonpos.mpr (le_of_not_gt hnot))] at hbudget
  exact (lt_irrefl 0) hbudget

/-- In low/high form, a new record requires the outer square to pay both the
entire inherited high square energy and the old normalized record threshold. -/
theorem postRootFamilySquareEnergy_add_recordThreshold_lt_outerSquare_of_recordExcess_pos
    (ε : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (hrecord : 0 < postRootCovariancePowerRecordExcess ε N) :
    postRootFamilyMertensSquareEnergy (N + 1) +
      2 * Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) *
        postRootCovariancePowerEnvelope ε N < realMertensLength (N + 1 + 1) ^ 2 := by
  have h := postRootCovariancePowerEnvelope_lt_squareNormalized_of_recordExcess_pos
    ε hN hrecord
  have hscale : 0 < 2 * Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) := by
    apply mul_pos (by norm_num)
    exact Real.rpow_pos_of_pos (by positivity) _
  have hmul := (lt_div_iff₀ hscale).1 h
  unfold postRootMertensSquareFiniteDifference at hmul
  nlinarith

end RHLean.Proof
