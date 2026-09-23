import RHLean.Proof.PostRootCovarianceRecordSquareChargeClosure

/-!
# The global exponent is exactly twice the Mertens exponent

Every reduction in this chain runs in one direction: the terminal Mertens
energy criterion is *implied* by control of the signed post-root remainder.
This module supplies the missing return path and closes the loop.

The whole return path is one inequality.  In the Bessel identity

```text
2 * E(W) = M(W)^2 - complementDiagonalResidual(W) - familyMertensSquareEnergy(W)
```

both subtracted terms are nonnegative, so

```text
E(W) <= M(W)^2 / 2
```

unconditionally, with no cancellation, no record hypothesis and no sieve.  That
single line turns every compiled reduction into an equivalence:

```text
PostRootCovariancePowerRemainderStatement
  <-> PostRootCovariancePowerEnvelopeBoundedStatement
  <-> PostRootCovariancePowerRecordExcessBoundedStatement
  <-> PostRootFallingEnergyFiniteDifferencePowerStatement
  <-> MertensSquarePowerEnvelopeBoundedStatement
  <-> MertensEnergyBoundedStatement.
```

Read quantitatively rather than as a bi-implication, the same inequality is a
transfer with an exact exchange rate: a Mertens bound of exponent `theta`
gives the remainder exponent `2*theta`, and the compiled bootstrap gives the
converse.  So the arrow carries a string: any unconditional improvement of the
Mertens exponent moves the global remainder exponent immediately and by
exactly a factor two, and nothing in the post-root/record machinery can move it
without one.  That is a genuine no-go for the current carrier, and it is stated
here so it is not rediscovered.

The unconditional exponent therefore cannot be improved here, but the
unconditional *constant* can.  `|M| <= squarefree count`, and one quarter of
every block of four is a multiple of four and so not squarefree, giving

```text
E(W) <= 9 * (W + 4)^2 / 32,
```

which improves the compiled `E(W) <= W^2` for every `W >= 5`.

Finally the record threshold is restated in its sharpest closed form: at a
record the entire accumulated remainder is below one endpoint times one local
innovation, and on an active post-root divisor below one endpoint times the
cumulative square gap.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-! ## The return path: half the physical square pays for the remainder -/

/-- **The missing half of the reduction.**  Both terms removed from the physical
Mertens square by the Bessel identity -- the complementary squarefree diagonal
and every transported post-root family square -- are nonnegative.  So the signed
post-root remainder never exceeds half the physical square, unconditionally. -/
theorem postRootCovarianceRemainder_le_half_mertensSquare (W : ℕ) :
    postRootCovarianceRemainder W ≤ realMertensLength (W + 1) ^ 2 / 2 := by
  have h := two_mul_postRootCovarianceRemainder_le_squareFiniteDifference W
  have hfam := postRootFamilyMertensSquareEnergy_nonneg W
  unfold postRootMertensSquareFiniteDifference at h
  linarith

/-- The same bound in the terminal criterion's own coordinate. -/
theorem postRootCovarianceRemainder_le_half_mertensEnergy (W : ℕ) :
    postRootCovarianceRemainder W ≤ ‖mertensSummatory W‖ ^ 2 / 2 := by
  rw [norm_mertensSummatory_sq_eq_realMertensLength_sq]
  exact postRootCovarianceRemainder_le_half_mertensSquare W

/-! ## The loop closes: every seam is equivalent to the terminal criterion -/

/-- **Return path.**  The protected Mertens energy criterion bounds the signed
post-root remainder, losing only the fixed factor `2^ε` from the endpoint
convention.  This is the converse of the bootstrap. -/
theorem postRootCovariancePowerRemainder_of_mertensEnergyBounded
    (hM : MertensEnergyBoundedStatement) :
    PostRootCovariancePowerRemainderStatement := by
  intro ε hε
  rcases hM ε hε with ⟨C, hC, hbound⟩
  refine ⟨C * Real.rpow (2 : ℝ) ε,
    mul_nonneg hC (Real.rpow_nonneg (by norm_num) _), ?_⟩
  intro W hW
  have hWpos : (0 : ℝ) < (W : ℝ) := by
    exact_mod_cast (show 0 < W by omega)
  have hWone : (1 : ℝ) ≤ (W : ℝ) := by
    exact_mod_cast (show 1 ≤ W by omega)
  have hcast : ((W + 1 : ℕ) : ℝ) ≤ 2 * (W : ℝ) := by
    push_cast
    linarith
  have hmono :
      Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) ≤
        Real.rpow (2 * (W : ℝ)) (1 + ε) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hcast (by linarith)
  have hsplit :
      Real.rpow (2 * (W : ℝ)) (1 + ε) =
        Real.rpow (2 : ℝ) (1 + ε) * Real.rpow (W : ℝ) (1 + ε) :=
    Real.mul_rpow (by norm_num) hWpos.le
  have htwo :
      Real.rpow (2 : ℝ) (1 + ε) = 2 * Real.rpow (2 : ℝ) ε := by
    calc
      Real.rpow (2 : ℝ) (1 + ε) =
          Real.rpow (2 : ℝ) 1 * Real.rpow (2 : ℝ) ε :=
        Real.rpow_add (by norm_num) _ _
      _ = 2 * Real.rpow (2 : ℝ) ε :=
        congrArg (fun t : ℝ => t * Real.rpow (2 : ℝ) ε) (Real.rpow_one _)
  rw [hsplit, htwo] at hmono
  have hCA :
      C * Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) ≤
        C * (2 * Real.rpow (2 : ℝ) ε * Real.rpow (W : ℝ) (1 + ε)) :=
    mul_le_mul_of_nonneg_left hmono hC
  have hhalf := postRootCovarianceRemainder_le_half_mertensEnergy W
  have hb := hbound W
  linarith

/-- **Exact tether.**  The signed post-root power remainder and the protected
Mertens energy criterion are the same proposition.  Neither direction loses an
exponent. -/
theorem postRootCovariancePowerRemainder_iff_mertensEnergyBounded :
    PostRootCovariancePowerRemainderStatement ↔ MertensEnergyBoundedStatement :=
  ⟨mertensEnergyBounded_of_postRootCovariancePowerRemainder,
    postRootCovariancePowerRemainder_of_mertensEnergyBounded⟩

theorem postRootCovariancePowerEnvelopeBounded_iff_mertensEnergyBounded :
    PostRootCovariancePowerEnvelopeBoundedStatement ↔
      MertensEnergyBoundedStatement := by
  rw [postRootCovariancePowerEnvelopeBounded_iff_powerRemainder,
    postRootCovariancePowerRemainder_iff_mertensEnergyBounded]

theorem postRootCovariancePowerRecordExcessBounded_iff_mertensEnergyBounded :
    PostRootCovariancePowerRecordExcessBoundedStatement ↔
      MertensEnergyBoundedStatement := by
  rw [postRootCovariancePowerRecordExcessBounded_iff_powerRemainder,
    postRootCovariancePowerRemainder_iff_mertensEnergyBounded]

theorem postRootFallingEnergyFiniteDifferencePower_iff_mertensEnergyBounded :
    PostRootFallingEnergyFiniteDifferencePowerStatement ↔
      MertensEnergyBoundedStatement := by
  rw [postRootFallingEnergyFiniteDifferencePower_iff_powerRemainder,
    postRootCovariancePowerRemainder_iff_mertensEnergyBounded]

/-- **The whole tower is one proposition.**  The Mertens square envelope
and the post-root power remainder are equivalent, so no reduction in the
chain has cost or gained anything. -/
theorem mertensSquarePowerEnvelopeBounded_iff_postRootCovariancePowerRemainder :
    MertensSquarePowerEnvelopeBoundedStatement ↔
      PostRootCovariancePowerRemainderStatement := by
  rw [mertensSquarePowerEnvelopeBounded_iff_mertensEnergyBounded,
    ← postRootCovariancePowerRemainder_iff_mertensEnergyBounded]

/-! ## The exchange rate: exponent `theta` in, exponent `2*theta` out -/

/-- **Exponent transfer.**  A Mertens bound with exponent `theta` at one
endpoint transfers to the signed post-root remainder with exponent exactly
`2*theta`.  This is the string on the arrow: it is unconditional, it is
pointwise in `W`, and by the equivalence above the exchange rate is exact, so
no post-root or record reduction can improve the global exponent without an
improvement of the Mertens exponent itself. -/
theorem postRootCovarianceRemainder_le_of_mertensPowerBound
    {B θ : ℝ} {W : ℕ} (hW : 1 ≤ W)
    (hM : |realMertensLength (W + 1)| ≤ B * Real.rpow (W : ℝ) θ) :
    postRootCovarianceRemainder W ≤
      B ^ 2 / 2 * Real.rpow (W : ℝ) (2 * θ) := by
  have hWpos : (0 : ℝ) < (W : ℝ) := by
    exact_mod_cast (show 0 < W by omega)
  have hpow : (0 : ℝ) ≤ Real.rpow (W : ℝ) θ :=
    Real.rpow_nonneg hWpos.le _
  have hdouble :
      Real.rpow (W : ℝ) (2 * θ) =
        Real.rpow (W : ℝ) θ * Real.rpow (W : ℝ) θ := by
    calc
      Real.rpow (W : ℝ) (2 * θ) = Real.rpow (W : ℝ) (θ + θ) :=
        congrArg (Real.rpow (W : ℝ)) (by ring)
      _ = Real.rpow (W : ℝ) θ * Real.rpow (W : ℝ) θ :=
        Real.rpow_add hWpos _ _
  have hnn := abs_nonneg (realMertensLength (W + 1))
  have habs := sq_abs (realMertensLength (W + 1))
  have hsq := mul_self_le_mul_self hnn hM
  have hhalf := postRootCovarianceRemainder_le_half_mertensSquare W
  rw [hdouble]
  nlinarith [hhalf, habs, hsq]

/-! ## The unconditional constant: one quarter of every block is not squarefree -/

private theorem abs_realMoebiusStep_eq_sq (n : ℕ) :
    |realMoebiusStep n| = realMoebiusStep n ^ 2 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    norm_num [realMoebiusStep, h]

/-- The Mertens prefix is bounded by the squarefree count, not merely by the
length: the `mu = 0` population is removed with no cancellation used. -/
theorem abs_realMertensLength_le_diagonal (K : ℕ) :
    |realMertensLength K| ≤ realMertensDiagonal K := by
  unfold realMertensLength realMertensDiagonal
  calc
    |∑ n ∈ Finset.range K, realMoebiusStep n| ≤
        ∑ n ∈ Finset.range K, |realMoebiusStep n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ Finset.range K, realMoebiusStep n ^ 2 :=
      Finset.sum_congr rfl fun n _hn => abs_realMoebiusStep_eq_sq n

theorem realMertensDiagonal_mono {K L : ℕ} (h : K ≤ L) :
    realMertensDiagonal K ≤ realMertensDiagonal L := by
  unfold realMertensDiagonal
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    fun n _hn _hnot => sq_nonneg _

private theorem realMoebiusStep_four_mul_eq_zero (m : ℕ) :
    realMoebiusStep (4 * m) = 0 := by
  have hnsf : ¬ Squarefree (4 * m) := by
    intro hsf
    have hdvd : 2 * 2 ∣ 4 * m := ⟨m, by ring⟩
    have hunit := Nat.isUnit_iff.mp (hsf 2 hdvd)
    omega
  unfold realMoebiusStep
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]
  simp

/-- **Elementary squarefree sieve.**  One residue in every block of four is a
multiple of four, hence not squarefree, so the squarefree count is at most three
quarters of the length. -/
theorem realMertensDiagonal_four_mul_le (m : ℕ) :
    realMertensDiagonal (4 * m) ≤ 3 * (m : ℝ) := by
  induction m with
  | zero => simp [realMertensDiagonal]
  | succ m ih =>
      have hstep : 4 * (m + 1) = 4 * m + 1 + 1 + 1 + 1 := by ring
      rw [hstep, realMertensDiagonal_succ, realMertensDiagonal_succ,
        realMertensDiagonal_succ, realMertensDiagonal_succ]
      have h0 : realMoebiusStep (4 * m) ^ 2 = 0 := by
        rw [realMoebiusStep_four_mul_eq_zero]
        ring
      have h1 := realMoebiusStep_sq_le_one (4 * m + 1)
      have h2 := realMoebiusStep_sq_le_one (4 * m + 1 + 1)
      have h3 := realMoebiusStep_sq_le_one (4 * m + 1 + 1 + 1)
      push_cast
      linarith

theorem abs_realMertensLength_le_threeQuarters (K : ℕ) :
    |realMertensLength K| ≤ 3 * ((K : ℝ) + 3) / 4 := by
  have hle : K ≤ 4 * ((K + 3) / 4) := by omega
  have hblock : 4 * ((K + 3) / 4) ≤ K + 3 := by omega
  have hcast : 4 * (((K + 3) / 4 : ℕ) : ℝ) ≤ (K : ℝ) + 3 := by
    exact_mod_cast hblock
  have hchain :=
    (abs_realMertensLength_le_diagonal K).trans (realMertensDiagonal_mono hle)
  have hsieve := realMertensDiagonal_four_mul_le ((K + 3) / 4)
  linarith

/-- **Unconditional global bound.**  Half the physical square, sieved by the
squarefree density of a single prime square, improves the compiled
`E(W) <= W^2` by a factor `32/9` for every `W >= 5`.  The exponent is
unchanged, and by the transfer above it cannot be changed here. -/
theorem postRootCovarianceRemainder_le_sieveSquare (W : ℕ) :
    postRootCovarianceRemainder W ≤ 9 * ((W : ℝ) + 4) ^ 2 / 32 := by
  have hhalf := postRootCovarianceRemainder_le_half_mertensSquare W
  have hsieve := abs_realMertensLength_le_threeQuarters (W + 1)
  have hcast : ((W + 1 : ℕ) : ℝ) = (W : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hsieve
  have hnn := abs_nonneg (realMertensLength (W + 1))
  have habs := sq_abs (realMertensLength (W + 1))
  have hsq := mul_self_le_mul_self hnn hsieve
  nlinarith [hhalf, habs, hsq]

/-! ## The seam in its most familiar form -/

/-- A power saving for the Mertens function: for every positive loss there is a
constant with `|M(x)| <= C * x^((1+ε)/2)`.  This is the classical
`M(x) << x^(1/2+delta)`. -/
def MertensPowerSavingStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℕ, |realMertensLength (x + 1)| ≤
        C * Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2)

private theorem rpow_half_mul_self (ε : ℝ) (x : ℕ) :
    Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2) *
        Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2) =
      Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
  have hpos : (0 : ℝ) < ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos x
  calc
    Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2) *
        Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2) =
        Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2 + (1 + ε) / 2) :=
      (Real.rpow_add hpos _ _).symm
    _ = Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) :=
      congrArg (Real.rpow ((x + 1 : ℕ) : ℝ)) (by ring)

theorem mertensEnergyBounded_of_mertensPowerSaving
    (h : MertensPowerSavingStatement) : MertensEnergyBoundedStatement := by
  intro ε hε
  rcases h ε hε with ⟨C, hC, hb⟩
  refine ⟨C ^ 2, sq_nonneg _, ?_⟩
  intro x
  have hnn := abs_nonneg (realMertensLength (x + 1))
  have habs := sq_abs (realMertensLength (x + 1))
  have hsq := mul_self_le_mul_self hnn (hb x)
  have hkey :
      (C * Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2)) *
          (C * Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2)) =
        C ^ 2 * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
    rw [← rpow_half_mul_self ε x]
    ring
  rw [hkey] at hsq
  rw [norm_mertensSummatory_sq_eq_realMertensLength_sq]
  nlinarith [hsq, habs]

theorem mertensPowerSaving_of_mertensEnergyBounded
    (h : MertensEnergyBoundedStatement) : MertensPowerSavingStatement := by
  intro ε hε
  rcases h ε hε with ⟨C, hC, hb⟩
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro x
  have hpos : (0 : ℝ) < ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos x
  have hR : (0 : ℝ) ≤ Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2) :=
    Real.rpow_nonneg hpos.le _
  have hrhs : (0 : ℝ) ≤ Real.sqrt C * Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) hR
  have hsqrtC : Real.sqrt C * Real.sqrt C = C := Real.mul_self_sqrt hC
  have hprod :
      (Real.sqrt C * Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2)) *
          (Real.sqrt C * Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2)) =
        C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
    calc
      (Real.sqrt C * Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2)) *
          (Real.sqrt C * Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2)) =
          (Real.sqrt C * Real.sqrt C) *
            (Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2) *
              Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2)) := by ring
      _ = C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
        rw [hsqrtC, rpow_half_mul_self ε x]
  have hb' := hb x
  rw [norm_mertensSummatory_sq_eq_realMertensLength_sq] at hb'
  refine abs_le_of_sq_le_sq ?_ hrhs
  have hpow :
      (Real.sqrt C * Real.rpow ((x + 1 : ℕ) : ℝ) ((1 + ε) / 2)) ^ 2 =
        C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
    rw [sq]
    exact hprod
  rw [hpow]
  exact hb'

/-- **The seam, named once and for all.**  Every compiled reduction in the
post-root/record tower is equivalent to a classical Mertens power saving.  There
is no remaining structural slack: the arrow is tied to the string at both
ends. -/
theorem mertensPowerSaving_iff_postRootCovariancePowerRemainder :
    MertensPowerSavingStatement ↔ PostRootCovariancePowerRemainderStatement := by
  rw [postRootCovariancePowerRemainder_iff_mertensEnergyBounded]
  exact ⟨mertensEnergyBounded_of_mertensPowerSaving,
    mertensPowerSaving_of_mertensEnergyBounded⟩

/-! ## The record threshold in closed form -/

/-- **At a record the whole accumulated remainder is one endpoint times one
step.**  Combining the record threshold with the seat bound removes every
normalization: no `ε` power survives on either side. -/
theorem postRootCovarianceRemainder_succ_lt_endpoint_mul_localInnovation
    (ε : ℝ) (hε : 0 ≤ ε) {W : ℕ} (hW : 2 ≤ W)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W) :
    postRootCovarianceRemainder (W + 1) <
      postRootCovarianceLocalInnovation W * ((W + 1 : ℕ) : ℝ) := by
  have hN1pos : (0 : ℝ) < ((W + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < W + 1 by omega)
  have hsplit :
      Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) =
        ((W + 1 : ℕ) : ℝ) * Real.rpow ((W + 1 : ℕ) : ℝ) ε := by
    calc
      Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) =
          Real.rpow ((W + 1 : ℕ) : ℝ) 1 * Real.rpow ((W + 1 : ℕ) : ℝ) ε :=
        Real.rpow_add hN1pos _ _
      _ = ((W + 1 : ℕ) : ℝ) * Real.rpow ((W + 1 : ℕ) : ℝ) ε :=
        congrArg (fun t : ℝ => t * Real.rpow ((W + 1 : ℕ) : ℝ) ε)
          (Real.rpow_one _)
  have hE := postRootCovarianceRemainder_le_powerEnvelope ε
    (show 2 ≤ W + 1 by omega) (le_refl (W + 1))
  rw [hsplit] at hE
  have hthr :=
    postRootCovariancePowerEnvelope_succ_mul_rpow_lt_localInnovation_of_recordExcess_pos
      ε hε hW hrec
  have hscaled := mul_lt_mul_of_pos_left hthr hN1pos
  nlinarith [hE, hscaled]

/-- On an active post-root divisor the same statement is closed in the Mertens
square alone, via its cumulative square-gap charge. -/
theorem postRootCovarianceRemainder_succ_lt_endpoint_mul_squareGap
    (ε : ℝ) (hε : 0 ≤ ε) {W p : ℕ} (hW : 2 ≤ W)
    (hp : p.Prime) (hmem : p ∈ postRootPrimeFamilySet (W + 1))
    (hdvd : p ∣ W + 1)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W) :
    postRootCovarianceRemainder (W + 1) <
      (realMertensLength (W + 2) ^ 2 -
        realMertensLength ((W + 1) / p + 1) ^ 2) * ((W + 1 : ℕ) : ℝ) := by
  have h1 :=
    postRootCovarianceRemainder_succ_lt_endpoint_mul_localInnovation ε hε hW hrec
  rw [postRootCovarianceLocalInnovation_eq_outerRow_of_activePostRootDivisor
    hp hmem hdvd] at h1
  have h2 := postRootRecordOuterRowNumerator_le_currentSquare_sub_lowerSquare
    ε hε hW hp hmem hdvd hrec
  have hn : (0 : ℝ) ≤ ((W + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3 := mul_le_mul_of_nonneg_right h2 hn
  linarith

/-- **The record equation.**  Eliminating the covariance coordinate entirely:
at a record, the physical Mertens square minus its transported post-root family
squares is below twice one endpoint times one local innovation, plus one
endpoint.  This is the constraint that a Mertens-exponent attack on the record
carrier has to contradict, stated with no covariance object left in it. -/
theorem mertensSquare_sub_familyEnergy_lt_endpoint_charge
    (ε : ℝ) (hε : 0 ≤ ε) {W : ℕ} (hW : 2 ≤ W)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W) :
    realMertensLength (W + 2) ^ 2 -
        postRootFamilyMertensSquareEnergy (W + 1) <
      2 * (postRootCovarianceLocalInnovation W * ((W + 1 : ℕ) : ℝ)) +
        ((W + 1 : ℕ) : ℝ) := by
  have hid :=
    postRootMertensSquareFiniteDifference_eq_two_mul_remainder_add_diagonal (W + 1)
  have hres := postRootComplementDiagonalResidual_le_endpoint (W + 1)
  have hrem :=
    postRootCovarianceRemainder_succ_lt_endpoint_mul_localInnovation ε hε hW hrec
  unfold postRootMertensSquareFiniteDifference at hid
  have hcast : W + 1 + 1 = W + 2 := by omega
  rw [hcast] at hid
  linarith

end RHLean.Proof
