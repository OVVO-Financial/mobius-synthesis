import RHLean.Proof.PhysicalQ2TerminalSynthesis
import RHLean.Proof.PhysicalQ2FourFrameTerminalSynthesis
import RHLean.Proof.SignedTransportAmplificationAudit
import RHLean.Proof.FinalCompensatedParentReduction
import RHLean.Analysis.MertensEnergyRHForward

/-!
# Exceptional-owner terminal synthesis

The maximal blocker geometry leaves only the complete least-square owners
`3,5,7`.  If the fully compensated physical parent can be reconstructed from
those three whole signed q^2 daughters plus a linear energy error, no selected-11
spectral transfer is needed for closure.

The universal three-vector inequality costs a factor `3`.  Because earlier layers
identify the whole signed daughters with the raw Mertens cutoffs

`M(4*K/9), M(4*K/25), M(4*K/49)`,

the only extra bookkeeping is the at-most-three-site transfer from each raw
cutoff to its nearest complete four-cell endpoint.  Using

`E(Y) <= (5/4) E(4*floor(Y/4)) + 45`,

the effective recursive coefficient is

`3 * (5/4) * (1/9 + 1/25 + 1/49) = 1891/2940 < 1`.

Thus the factor-three exceptional recurrence alone implies RH.  This module is
conditional only on that parent recurrence; it does not assert that the physical
parent decomposition has already been proved.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The exact complete-cell recurrence that a signed exceptional-parent
reconstruction would provide after the universal three-daughter Cauchy step. -/
def PhysicalCompleteCellExceptionalQ2EnergyStep (C : ℚ) : Prop :=
  ∀ K : ℕ,
    mertensEnergy (4 * K) ≤ C * (K : ℚ) +
      3 * (mertensEnergy ((4 * K) / 9) +
        mertensEnergy ((4 * K) / 25) +
        mertensEnergy ((4 * K) / 49))

private theorem natCast_div_le_rat
    (X d : ℕ) (hd : 0 < d) :
    ((X / d : ℕ) : ℚ) ≤ (X : ℚ) / (d : ℚ) := by
  apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℚ) < (d : ℚ))).2
  exact_mod_cast Nat.div_mul_le_self X d

/-- The complete-cell index beneath a raw `4*K/d` child is at most the exact
rational scale `K/d`. -/
private theorem rawDaughter_completeCellIndex_le_scale
    (K d : ℕ) (hd : 0 < d) :
    (((4 * K / d) / 4 : ℕ) : ℚ) ≤ (K : ℚ) / (d : ℚ) := by
  have h4 :
      (((4 * K / d) / 4 : ℕ) : ℚ) ≤
        (((4 * K / d : ℕ) : ℚ)) / 4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 4)).2
    exact_mod_cast Nat.div_mul_le_self (4 * K / d) 4
  have hdv := natCast_div_le_rat (4 * K) d hd
  calc
    (((4 * K / d) / 4 : ℕ) : ℚ) ≤
        (((4 * K / d : ℕ) : ℚ)) / 4 := h4
    _ ≤ (((4 * K : ℕ) : ℚ) / (d : ℚ)) / 4 := by
      nlinarith
    _ = (K : ℚ) / (d : ℚ) := by
      push_cast
      ring

/-- Exact reciprocal-square scale for the three exceptional complete-cell child
indices, with floors retained on the left. -/
private theorem exceptional_rawDaughter_completeCellIndices_scale (K : ℕ) :
    ((((4 * K / 9) / 4 : ℕ) : ℚ) +
      (((4 * K / 25) / 4 : ℕ) : ℚ) +
      (((4 * K / 49) / 4 : ℕ) : ℚ)) ≤
        (1891 : ℚ) / 11025 * (K : ℚ) := by
  have h9 := rawDaughter_completeCellIndex_le_scale K 9 (by norm_num)
  have h25 := rawDaughter_completeCellIndex_le_scale K 25 (by norm_num)
  have h49 := rawDaughter_completeCellIndex_le_scale K 49 (by norm_num)
  calc
    ((((4 * K / 9) / 4 : ℕ) : ℚ) +
      (((4 * K / 25) / 4 : ℕ) : ℚ) +
      (((4 * K / 49) / 4 : ℕ) : ℚ)) ≤
        (K : ℚ) / 9 + (K : ℚ) / 25 + (K : ℚ) / 49 := by
          linarith
    _ = (1891 : ℚ) / 11025 * (K : ℚ) := by ring

private theorem rawDaughter_completeCellIndex_lt
    {K d : ℕ} (hK : 0 < K) (hd : 0 < d) (hd4 : 4 < d) :
    (4 * K / d) / 4 < K := by
  have hY : 4 * K / d < K := by
    apply (Nat.div_lt_iff_lt_mul hd).2
    nlinarith
  exact (Nat.div_le_self (4 * K / d) 4).trans_lt hY

/-- **Factor-three exceptional induction.**  No prime-11 contraction appears:
the restricted `3,5,7` square scales already make the universal synthesis
subcritical after the exact endpoint transfer. -/
theorem physicalCompleteCell_exceptionalFactorThreeStep_implies_linear
    {C : ℚ} (hC : 0 ≤ C)
    (hstep : PhysicalCompleteCellExceptionalQ2EnergyStep C) :
    ∀ K : ℕ,
      mertensEnergy (4 * K) ≤ (3 * (C + 405)) * (K : ℚ) := by
  let A : ℚ := 3 * (C + 405)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hfixed :
      C + 405 + (1891 : ℚ) / 2940 * A ≤ A := by
    dsimp [A]
    nlinarith
  intro K
  induction K using Nat.strong_induction_on with
  | h K ih =>
      by_cases hK0 : K = 0
      · subst K
        simp [mertensEnergy, mertensSummatoryInt]
      · have hKpos : 0 < K := Nat.pos_of_ne_zero hK0
        have child_bound (d : ℕ) (hd : 0 < d) (hd4 : 4 < d) :
            mertensEnergy (4 * K / d) ≤
              (5 : ℚ) / 4 * A * ((((4 * K / d) / 4 : ℕ) : ℚ)) + 45 := by
          let Y : ℕ := 4 * K / d
          let J : ℕ := Y / 4
          have hJlt : J < K := by
            dsimp [J, Y]
            exact rawDaughter_completeCellIndex_lt hKpos hd hd4
          have hcomplete := ih J hJlt
          have hend := mertensEnergy_le_five_fourths_completeCell_add_fortyFive Y
          change mertensEnergy Y ≤
            (5 : ℚ) / 4 * A * (J : ℚ) + 45
          calc
            mertensEnergy Y ≤
                (5 : ℚ) / 4 * mertensEnergy (4 * J) + 45 := by
                  simpa [J] using hend
            _ ≤ (5 : ℚ) / 4 * (A * (J : ℚ)) + 45 := by
                  gcongr
            _ = (5 : ℚ) / 4 * A * (J : ℚ) + 45 := by ring
        have h9 := child_bound 9 (by norm_num) (by norm_num)
        have h25 := child_bound 25 (by norm_num) (by norm_num)
        have h49 := child_bound 49 (by norm_num) (by norm_num)
        have hscale := exceptional_rawDaughter_completeCellIndices_scale K
        have hKone : (1 : ℚ) ≤ (K : ℚ) := by exact_mod_cast hKpos
        have hchildren :
            mertensEnergy (4 * K / 9) +
              mertensEnergy (4 * K / 25) +
              mertensEnergy (4 * K / 49) ≤
                (((5 : ℚ) / 4 * (1891 : ℚ) / 11025 * A) + 135) *
                  (K : ℚ) := by
          have hcoef : 0 ≤ (5 : ℚ) / 4 * A := by positivity
          calc
            mertensEnergy (4 * K / 9) +
                mertensEnergy (4 * K / 25) +
                mertensEnergy (4 * K / 49) ≤
              (5 : ℚ) / 4 * A * ((((4 * K / 9) / 4 : ℕ) : ℚ)) + 45 +
                ((5 : ℚ) / 4 * A * ((((4 * K / 25) / 4 : ℕ) : ℚ)) + 45) +
                ((5 : ℚ) / 4 * A * ((((4 * K / 49) / 4 : ℕ) : ℚ)) + 45) := by
                  linarith
            _ = (5 : ℚ) / 4 * A *
                  (((((4 * K / 9) / 4 : ℕ) : ℚ)) +
                    ((((4 * K / 25) / 4 : ℕ) : ℚ)) +
                    ((((4 * K / 49) / 4 : ℕ) : ℚ))) + 135 := by ring
            _ ≤ (5 : ℚ) / 4 * A *
                  ((1891 : ℚ) / 11025 * (K : ℚ)) + 135 := by
                    exact add_le_add_right
                      (mul_le_mul_of_nonneg_left hscale hcoef) 135
            _ ≤ (5 : ℚ) / 4 * A *
                  ((1891 : ℚ) / 11025 * (K : ℚ)) +
                    135 * (K : ℚ) := by
                      linarith
            _ = (((5 : ℚ) / 4 * (1891 : ℚ) / 11025 * A) + 135) *
                  (K : ℚ) := by ring
        have hs := hstep K
        have hweighted := mul_le_mul_of_nonneg_left hchildren (by norm_num : (0 : ℚ) ≤ 3)
        calc
          mertensEnergy (4 * K) ≤
              C * (K : ℚ) +
                3 * (mertensEnergy (4 * K / 9) +
                  mertensEnergy (4 * K / 25) +
                  mertensEnergy (4 * K / 49)) := hs
          _ ≤ C * (K : ℚ) +
                3 * ((((5 : ℚ) / 4 * (1891 : ℚ) / 11025 * A) + 135) *
                  (K : ℚ)) := add_le_add_left hweighted _
          _ = (C + 405 + (1891 : ℚ) / 2940 * A) * (K : ℚ) := by ring
          _ ≤ A * (K : ℚ) :=
                mul_le_mul_of_nonneg_right hfixed (by positivity)

/-- **Exceptional-owner single-hypothesis RH theorem.**  If the compensated
physical parent supplies the universal factor-three recurrence on its exact
three whole signed daughters, all remaining arithmetic and analytic wiring is
already closed. -/
theorem riemannHypothesis_of_physicalCompleteCell_exceptionalFactorThreeStep
    {C : ℚ} (hC : 0 ≤ C)
    (hstep : PhysicalCompleteCellExceptionalQ2EnergyStep C) :
    RiemannHypothesis := by
  let A : ℚ := 3 * (C + 405)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hlinear : ∀ K : ℕ, mertensEnergy (4 * K) ≤ A * (K : ℚ) := by
    simpa [A] using
      physicalCompleteCell_exceptionalFactorThreeStep_implies_linear hC hstep
  exact riemannHypothesis_of_threeSlotDegreeOneEnergy
    (threeSlotDegreeOneEnergy_of_completeCellMertensLinear hA hlinear)

/-! ## Literal q² endpoint recurrence and amplification equivalence -/

/-- Literal odd-owner q² recurrence before square-endpoint shell interpolation. -/
def SquareEndpointRawOddQ2EnergyStep (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    2 ≤ R →
    LowerMertensCriticalEnvelope R K →
    squareEndpointMertensEnergyReal R ≤
      C * (R : ℝ) ^ 2 * K +
        4 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          rawQ2ChildEnergyReal R q

/-- The same literal recurrence with an explicit daughter coefficient. -/
def SquareEndpointRawOddQ2EnergyStepWith (a C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    2 ≤ R →
    LowerMertensCriticalEnvelope R K →
    squareEndpointMertensEnergyReal R ≤
      C * (R : ℝ) ^ 2 * K +
        a * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          rawQ2ChildEnergyReal R q

private theorem rawOddQ2Owner_card_le_root (R : ℕ) :
    ((primesUpTo (R - 1)).erase 2).card ≤ R := by
  let S : Finset ℕ := (primesUpTo (R - 1)).erase 2
  have hsub : S ⊆ Finset.range R := by
    intro q hq
    have hq' : q ∈ primesUpTo (R - 1) := (Finset.mem_erase.mp hq).2
    have hqPrime := (mem_primesUpTo.mp hq').1
    have hqle := (mem_primesUpTo.mp hq').2
    have hq2 : 2 ≤ q := hqPrime.two_le
    exact Finset.mem_range.mpr (by omega)
  simpa [S] using Finset.card_le_card hsub

/-- The total deterministic shell width has root-energy scale. -/
theorem sum_roundedQ2ChildRoot_succ_sq_le_two_root_sq
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ q ∈ (primesUpTo (R - 1)).erase 2,
      (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2) ≤
        2 * (R : ℝ) ^ 2 := by
  let S := (primesUpTo (R - 1)).erase 2
  have hpoint : ∀ q ∈ S,
      (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2 ≤
        2 * ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 + 2 := by
    intro q hq
    nlinarith [sq_nonneg (((roundedQ2ChildRoot R q : ℕ) : ℝ) - 1)]
  have hsum :
      (∑ q ∈ S, (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2) ≤
        ∑ q ∈ S, (2 * ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 + 2) := by
    apply Finset.sum_le_sum
    intro q hq
    exact hpoint q hq
  have hsumId :
      (∑ q ∈ S, (2 * ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 + 2)) =
        2 * (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2) +
          2 * (S.card : ℝ) := by
    rw [Finset.sum_add_distrib]
    simp [Finset.mul_sum]
    ring
  have hscale := sum_roundedQ2ChildRoot_sq_le_seventeen_over_seventy_two R
  change (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2) ≤
    (17 : ℝ) / 72 * (R : ℝ) ^ 2 at hscale
  have hcardNat : S.card ≤ R := by
    simpa [S] using rawOddQ2Owner_card_le_root R
  have hcard : (S.card : ℝ) ≤ (R : ℝ) := by exact_mod_cast hcardNat
  calc
    (∑ q ∈ S, (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2) ≤
        ∑ q ∈ S, (2 * ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 + 2) := hsum
    _ = 2 * (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2) +
          2 * (S.card : ℝ) := hsumId
    _ ≤ 2 * ((17 : ℝ) / 72 * (R : ℝ) ^ 2) + 2 * (R : ℝ) := by
      nlinarith
    _ ≤ 2 * (R : ℝ) ^ 2 := by
      have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
      nlinarith [sq_nonneg ((R : ℝ) - 2)]

private theorem rawRoundedQ2ChildRoot_lt_parent
    {R q : ℕ} (hR : 1 ≤ R) :
    roundedQ2ChildRoot R q < R := by
  unfold roundedQ2ChildRoot
  apply (Nat.sqrt_lt').2
  have hle : squareRootEndpoint R / (q * q) ≤ squareRootEndpoint R :=
    Nat.div_le_self _ _
  have hsqPos : 0 < R ^ 2 := by positivity
  have hend : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    exact Nat.sub_lt hsqPos (by norm_num)
  exact hle.trans_lt hend

private theorem rawLowerEnvelope_mono_root
    {R S : ℕ} {K : ℝ}
    (hSR : S < R)
    (hK : LowerMertensCriticalEnvelope R K) :
    LowerMertensCriticalEnvelope S K := by
  refine ⟨hK.1, ?_⟩
  intro y hy
  exact hK.2 y (hy.trans hSR)

private theorem rawSquareEndpointEnergy_eq_zero_of_lt_two
    {R : ℕ} (hR : R < 2) :
    squareEndpointMertensEnergyReal R = 0 := by
  interval_cases R <;>
    simp [squareEndpointMertensEnergyReal, squareRootEndpoint,
      mertensSummatoryInt]

/-- Every subcritical literal coefficient closes by strong induction.  The
rounded shell contributes `296*a*R^2` additively.  Its only multiplicative
cost is the explicit `37/36`, already present in `hcontract`. -/
theorem squareEndpointRawOddQ2EnergyStepWith_implies_unshifted_amplification
    {a C : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hcontract : a * ((37 : ℝ) / 36) * ((17 : ℝ) / 72) < 1)
    (hstep : SquareEndpointRawOddQ2EnergyStepWith a C) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ R : ℕ, ∀ K : ℝ,
        2 ≤ R →
        LowerMertensCriticalEnvelope R K →
        squareEndpointMertensEnergyReal R ≤ A * (R : ℝ) ^ 2 * K := by
  have hden : 0 < 1 - a * ((37 : ℝ) / 36) * ((17 : ℝ) / 72) :=
    sub_pos.mpr hcontract
  let A : ℝ := (C + 296 * a) /
    (1 - a * ((37 : ℝ) / 36) * ((17 : ℝ) / 72))
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro R
  induction R using Nat.strong_induction_on with
  | h R ih =>
      intro K hR hK
      let S : Finset ℕ := (primesUpTo (R - 1)).erase 2
      have hK0 : 0 ≤ K := hK.1
      have hK1 : 1 ≤ K := by
        have h0 := hK.2 0 (by omega)
        have hm0 : mertensSummatoryInt 0 = 0 := by
          simp [mertensSummatoryInt]
        rw [hm0] at h0
        norm_num at h0
        exact h0
      have hchild : ∀ q ∈ S,
          squareEndpointMertensEnergyReal (roundedQ2ChildRoot R q) ≤
            A * ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 * K := by
        intro q hq
        have hsR : roundedQ2ChildRoot R q < R :=
          rawRoundedQ2ChildRoot_lt_parent (by omega)
        by_cases hs2 : 2 ≤ roundedQ2ChildRoot R q
        · exact ih (roundedQ2ChildRoot R q) hsR K hs2
            (rawLowerEnvelope_mono_root hsR hK)
        · have hslt : roundedQ2ChildRoot R q < 2 := by omega
          rw [rawSquareEndpointEnergy_eq_zero_of_lt_two hslt]
          positivity
      have hrawTerms : ∀ q ∈ S,
          rawQ2ChildEnergyReal R q ≤
            ((37 : ℝ) / 36 * A * K) *
                ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 +
              148 * (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2 := by
        intro q hq
        have hshell :=
          rawQ2ChildEnergyReal_le_thirtySeven_thirtySix_rounded_add_shell R q
        have hc := hchild q hq
        calc
          rawQ2ChildEnergyReal R q ≤
              (37 : ℝ) / 36 *
                  squareEndpointMertensEnergyReal (roundedQ2ChildRoot R q) +
                148 * (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2 := hshell
          _ ≤ (37 : ℝ) / 36 *
                  (A * ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 * K) +
                148 * (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2 := by
              gcongr
          _ = ((37 : ℝ) / 36 * A * K) *
                  ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 +
                148 * (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2 := by ring
      have hrawSum :
          (∑ q ∈ S, rawQ2ChildEnergyReal R q) ≤
            ((37 : ℝ) / 36 * A * K) *
                (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2) +
              148 * (∑ q ∈ S,
                (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2) := by
        calc
          (∑ q ∈ S, rawQ2ChildEnergyReal R q) ≤
              ∑ q ∈ S,
                (((37 : ℝ) / 36 * A * K) *
                    ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 +
                  148 * (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2) := by
                    apply Finset.sum_le_sum
                    intro q hq
                    exact hrawTerms q hq
          _ = ((37 : ℝ) / 36 * A * K) *
                (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2) +
              148 * (∑ q ∈ S,
                (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2) := by
                  rw [Finset.sum_add_distrib]
                  rw [← Finset.mul_sum, ← Finset.mul_sum]
      have hscale := sum_roundedQ2ChildRoot_sq_le_seventeen_over_seventy_two R
      change (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2) ≤
        (17 : ℝ) / 72 * (R : ℝ) ^ 2 at hscale
      have hshellSum := sum_roundedQ2ChildRoot_succ_sq_le_two_root_sq R hR
      change (∑ q ∈ S,
        (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2) ≤
          2 * (R : ℝ) ^ 2 at hshellSum
      have hcoef : 0 ≤ (37 : ℝ) / 36 * A * K := by
        exact mul_nonneg (mul_nonneg (by norm_num) hA) hK0
      have hrawSum' :
          (∑ q ∈ S, rawQ2ChildEnergyReal R q) ≤
            ((37 : ℝ) / 36 * A * K) *
                ((17 : ℝ) / 72 * (R : ℝ) ^ 2) +
              148 * (2 * (R : ℝ) ^ 2) := by
        exact hrawSum.trans (add_le_add
          (mul_le_mul_of_nonneg_left hscale hcoef)
          (mul_le_mul_of_nonneg_left hshellSum (by norm_num)))
      have hs := hstep R K hR hK
      change squareEndpointMertensEnergyReal R ≤
        C * (R : ℝ) ^ 2 * K +
          a * ∑ q ∈ S, rawQ2ChildEnergyReal R q at hs
      have hweighted := mul_le_mul_of_nonneg_left hrawSum'
        ha
      have hfixed :
          C + 296 * a + (a * ((37 : ℝ) / 36) * ((17 : ℝ) / 72)) * A = A := by
        have hmul : A * (1 - a * ((37 : ℝ) / 36) * ((17 : ℝ) / 72)) =
            C + 296 * a := by
          dsimp [A]
          exact div_mul_cancel₀ _ (ne_of_gt hden)
        nlinarith
      calc
        squareEndpointMertensEnergyReal R ≤
            C * (R : ℝ) ^ 2 * K +
              a * ∑ q ∈ S, rawQ2ChildEnergyReal R q := hs
        _ ≤ C * (R : ℝ) ^ 2 * K +
              a * (((37 : ℝ) / 36 * A * K) *
                  ((17 : ℝ) / 72 * (R : ℝ) ^ 2) +
                148 * (2 * (R : ℝ) ^ 2)) := add_le_add_left hweighted _
        _ = (C + (a * ((37 : ℝ) / 36) * ((17 : ℝ) / 72)) * A) * ((R : ℝ) ^ 2 * K) +
              296 * a * (R : ℝ) ^ 2 := by ring
        _ ≤ (C + 296 * a + (a * ((37 : ℝ) / 36) * ((17 : ℝ) / 72)) * A) *
              ((R : ℝ) ^ 2 * K) := by
                have hrem : 296 * a * (R : ℝ) ^ 2 ≤
                    296 * a * (R : ℝ) ^ 2 * K := by
                  have hnonneg : 0 ≤ 296 * a * (R : ℝ) ^ 2 := by positivity
                  simpa only [mul_one] using
                    mul_le_mul_of_nonneg_left hK1 hnonneg
                nlinarith
        _ = A * (R : ℝ) ^ 2 * K := by rw [hfixed]; ring

/-- The original factor-four interface is preserved as a specialization. -/
theorem squareEndpointRawOddQ2EnergyStep_implies_unshifted_amplification
    {C : ℝ} (hC : 0 ≤ C)
    (hstep : SquareEndpointRawOddQ2EnergyStep C) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ R : ℕ, ∀ K : ℝ,
        2 ≤ R →
        LowerMertensCriticalEnvelope R K →
        squareEndpointMertensEnergyReal R ≤ A * (R : ℝ) ^ 2 * K := by
  exact squareEndpointRawOddQ2EnergyStepWith_implies_unshifted_amplification
    (a := 4) hC (by norm_num) (by norm_num) hstep

/-- The literal q² recurrence therefore supplies exactly the endpoint
amplification interface consumed by the unconditional Mertens closure. -/
theorem squareEndpointRawOddQ2EnergyStepWith_implies_endpointAmplification
    {a C : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hcontract : a * ((37 : ℝ) / 36) * ((17 : ℝ) / 72) < 1)
    (hstep : SquareEndpointRawOddQ2EnergyStepWith a C) :
    SquareRootMertensEndpointAmplificationStatement := by
  rcases squareEndpointRawOddQ2EnergyStepWith_implies_unshifted_amplification
      hC ha hcontract hstep with ⟨A, hA, hbound⟩
  refine ⟨2 * A + 1, by positivity, ?_⟩
  intro R K hR hK
  have hM := hbound R K hR hK
  have hK1 : 1 ≤ K := by
    have h0 := hK.2 0 (by omega)
    have hm0 : mertensSummatoryInt 0 = 0 := by
      simp [mertensSummatoryInt]
    rw [hm0] at h0
    norm_num at h0
    exact h0
  let m : ℝ := ((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ)
  have hM' : m ^ 2 ≤ A * (R : ℝ) ^ 2 * K := by
    simpa [m, squareEndpointMertensEnergyReal] using hM
  have hshift : (m - 1) ^ 2 ≤ 2 * m ^ 2 + 2 := by
    nlinarith [sq_nonneg (m + 1)]
  have hmshift :
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ)) = m - 1 := by
    dsimp [m]
    push_cast
    ring
  rw [hmshift]
  calc
    (m - 1) ^ 2 ≤ 2 * m ^ 2 + 2 := hshift
    _ ≤ 2 * (A * (R : ℝ) ^ 2 * K) + 2 := by nlinarith [hM']
    _ ≤ (2 * A + 1) * (R : ℝ) ^ 2 * K := by
      have hK1' : 1 ≤ K := hK1
      have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
      nlinarith

/-- Backwards-compatible factor-four terminal interface. -/
theorem squareEndpointRawOddQ2EnergyStep_implies_endpointAmplification
    {C : ℝ} (hC : 0 ≤ C)
    (hstep : SquareEndpointRawOddQ2EnergyStep C) :
    SquareRootMertensEndpointAmplificationStatement := by
  exact squareEndpointRawOddQ2EnergyStepWith_implies_endpointAmplification
    (a := 4) hC (by norm_num) (by norm_num) hstep

/-- The exact FAR-4 terminal budget, including shell rounding. -/
theorem rawOddQ2FortyOneTen_budget :
    ((41 : ℝ) / 10) * ((37 : ℝ) / 36) * ((17 : ℝ) / 72) =
      (25789 : ℝ) / 25920 ∧
    (25789 : ℝ) / 25920 < 1 := by
  norm_num

/-- The shell has a finite fixed point at coefficient `41/10`. -/
theorem rawOddQ2FortyOneTen_fixedPoint (C : ℝ) :
    (C + 296 * ((41 : ℝ) / 10)) /
        (1 - ((41 : ℝ) / 10) * ((37 : ℝ) / 36) * ((17 : ℝ) / 72)) =
      ((25920 : ℝ) / 131) * (C + (6068 : ℝ) / 5) := by
  ring

/-- Fixed endpoint amplification already implies the existence of a raw q²
recurrence constant. -/
theorem squareRootEndpointAmplification_implies_exists_rawOddQ2EnergyStep
    (hamp : SquareRootMertensEndpointAmplificationStatement) :
    ∃ C : ℝ, 0 ≤ C ∧ SquareEndpointRawOddQ2EnergyStep C := by
  rcases hamp with ⟨A, hA, hbound⟩
  refine ⟨2 * A + 1, by positivity, ?_⟩
  intro R K hR hK
  have hK1 : 1 ≤ K := by
    have h0 := hK.2 0 (by omega)
    have hm0 : mertensSummatoryInt 0 = 0 := by
      simp [mertensSummatoryInt]
    rw [hm0] at h0
    norm_num at h0
    exact h0
  let m : ℝ := ((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ)
  have hmshift :
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ)) = m - 1 := by
    dsimp [m]
    push_cast
    ring
  have hshifted := hbound R K hR hK
  rw [hmshift] at hshifted
  have hm : m ^ 2 ≤ 2 * (m - 1) ^ 2 + 2 := by
    nlinarith [sq_nonneg (m - 2)]
  have hmBound : m ^ 2 ≤ (2 * A + 1) * (R : ℝ) ^ 2 * K := by
    calc
      m ^ 2 ≤ 2 * (m - 1) ^ 2 + 2 := hm
      _ ≤ 2 * (A * (R : ℝ) ^ 2 * K) + 2 := by nlinarith [hshifted]
      _ ≤ (2 * A + 1) * (R : ℝ) ^ 2 * K := by
        have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
        nlinarith
  have hparent :
      squareEndpointMertensEnergyReal R ≤
        (2 * A + 1) * (R : ℝ) ^ 2 * K := by
    simpa [m, squareEndpointMertensEnergyReal] using hmBound
  have hchildren0 :
      0 ≤ ∑ q ∈ (primesUpTo (R - 1)).erase 2,
        rawQ2ChildEnergyReal R q := by
    apply Finset.sum_nonneg
    intro q hq
    unfold rawQ2ChildEnergyReal
    positivity
  exact hparent.trans (by nlinarith)

/-- Existence of a nonnegative literal factor-four q² recurrence constant is
**equivalent** to fixed square-root endpoint amplification. -/
theorem exists_nonneg_squareEndpointRawOddQ2EnergyStep_iff_endpointAmplification :
    (∃ C : ℝ, 0 ≤ C ∧ SquareEndpointRawOddQ2EnergyStep C) ↔
      SquareRootMertensEndpointAmplificationStatement := by
  constructor
  · rintro ⟨C, hC, hstep⟩
    exact squareEndpointRawOddQ2EnergyStep_implies_endpointAmplification hC hstep
  · intro hamp
    exact squareRootEndpointAmplification_implies_exists_rawOddQ2EnergyStep hamp

/-- Consequently the literal signed factor-four recurrence is already an RH
criterion; no further square-shell or endpoint theorem remains after it. -/
theorem riemannHypothesis_of_squareEndpointRawOddQ2EnergyStep
    {C : ℝ} (hC : 0 ≤ C)
    (hstep : SquareEndpointRawOddQ2EnergyStep C) :
    RiemannHypothesis := by
  apply RHLean.Analysis.riemannHypothesis_of_mertensEnergy
  exact mertensEnergyBounded_of_squareRootEndpointAmplification
    (squareEndpointRawOddQ2EnergyStep_implies_endpointAmplification hC hstep)

/-! ## Frozen/top/far endpoint energy bridges -/

/-- The three far populations exposed after the corrected signed subtraction
are exactly the negative frozen/top/far residual. -/
theorem farPopulations_eq_neg_frozenTopFar
    (R : ℕ) (hR : 56 ≤ R) :
    squareEndpointQ2ChildFarSliceColumn R + stableFarRenewalColumn R +
        stableFarTerminalProductColumn R =
      -lowWheelFrozenTopFarResidual R := by
  have hfar := squarePrefixMertens_eq_farPopulations_add_rootBoundary R hR
  have hfrozen := squarePrefixMertens_eq_rootBoundary_sub_frozenTopFar R hR
  linear_combination hfrozen - hfar

/-- FAR-3 in its exact current form: the frozen/top/far packet is controlled by
three times the genuine odd-owner q² daughter energy plus an RH-scale root
boundary. -/
def FrozenTopFarThreeEnergyStatement : Prop :=
  ∃ CF : ℝ, 0 ≤ CF ∧
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖lowWheelFrozenTopFarResidual R‖ ^ 2 ≤
        3 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          rawQ2ChildEnergyReal R q +
        CF * (R : ℝ) ^ 2 * K

private theorem one_le_lowerMertensCriticalEnvelope
    {R : ℕ} {K : ℝ} (hR : 1 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    1 ≤ K := by
  have h0 := hK.2 0 (by omega)
  have hm0 : mertensSummatoryInt 0 = 0 := by
    simp [mertensSummatoryInt]
  rw [hm0] at h0
  norm_num at h0
  exact h0

private theorem norm_mertensSummatory_sq_eq_realInt_sq_local (x : ℕ) :
    ‖RHLean.Analysis.mertensSummatory x‖ ^ 2 =
      ((mertensSummatoryInt x : ℤ) : ℝ) ^ 2 := by
  rw [← mertensSummatoryInt_cast x, Complex.norm_intCast]
  exact sq_abs (((mertensSummatoryInt x : ℤ) : ℝ))

private theorem squareEndpointMertensEnergyReal_eq_squarePrefix_norm_sq
    {R : ℕ} (hR : 1 ≤ R) :
    squareEndpointMertensEnergyReal R =
      ‖squarePrefixMertens (R - 1)‖ ^ 2 := by
  unfold squareEndpointMertensEnergyReal squarePrefixMertens
  rw [squarePrefixEndpoint_pred_eq_squareRootEndpoint R hR]
  symm
  exact norm_mertensSummatory_sq_eq_realInt_sq_local (squareRootEndpoint R)

private theorem squarePrefix_shifted_norm_sq_eq_realInt_sq
    {R : ℕ} (hR : 1 ≤ R) :
    ‖squarePrefixMertens (R - 1) - 1‖ ^ 2 =
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) := by
  unfold squarePrefixMertens
  rw [squarePrefixEndpoint_pred_eq_squareRootEndpoint R hR]
  simpa [shiftedMertensEnergy] using
    shiftedMertensEnergy_eq_intSquare (squareRootEndpoint R)

private theorem norm_sub_sq_le_two (u v : ℂ) :
    ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hnorm := norm_sub_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u - v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

private theorem norm_sub_sq_le_four_fourThirds (u v : ℂ) :
    ‖u - v‖ ^ 2 ≤ 4 * ‖u‖ ^ 2 + (4 : ℝ) / 3 * ‖v‖ ^ 2 := by
  have hnorm := norm_sub_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u - v‖ := norm_nonneg _
  nlinarith [sq_nonneg (3 * ‖u‖ - ‖v‖)]

private theorem squareEndpointMertensEnergyReal_le_root_fourth (R : ℕ) :
    squareEndpointMertensEnergyReal R ≤ (R : ℝ) ^ 4 := by
  let X : ℕ := squareRootEndpoint R
  have hnorm0 := norm_mertensSummatory_sub_le 0 X (Nat.zero_le X)
  have hnorm : ‖RHLean.Analysis.mertensSummatory X‖ ≤ (X : ℝ) := by
    simpa using hnorm0
  have hX0 : 0 ≤ (X : ℝ) := by positivity
  have hnorm0' : 0 ≤ ‖RHLean.Analysis.mertensSummatory X‖ := norm_nonneg _
  have hsq :
      ‖RHLean.Analysis.mertensSummatory X‖ ^ 2 ≤ (X : ℝ) ^ 2 := by
    nlinarith
  have hXNat : X ≤ R ^ 2 := by
    dsimp [X, squareRootEndpoint]
    exact Nat.sub_le _ _
  have hX : (X : ℝ) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast hXNat
  have hR2 : 0 ≤ (R : ℝ) ^ 2 := sq_nonneg _
  have hXsq : (X : ℝ) ^ 2 ≤ (R : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((R : ℝ) ^ 2 - (X : ℝ))]
  have henergy :
      squareEndpointMertensEnergyReal R =
        ‖RHLean.Analysis.mertensSummatory X‖ ^ 2 := by
    dsimp [X, squareEndpointMertensEnergyReal]
    symm
    exact norm_mertensSummatory_sq_eq_realInt_sq_local (squareRootEndpoint R)
  rw [henergy]
  exact hsq.trans hXsq

private theorem smallRoot_squareEndpointMertensEnergyReal_le
    {R : ℕ} {K : ℝ}
    (hR : 2 ≤ R) (hsmall : R < 56)
    (hK : LowerMertensCriticalEnvelope R K) :
    squareEndpointMertensEnergyReal R ≤
      3136 * (R : ℝ) ^ 2 * K := by
  have hbase := squareEndpointMertensEnergyReal_le_root_fourth R
  have hK1 : 1 ≤ K := one_le_lowerMertensCriticalEnvelope (by omega) hK
  have hRleNat : R ≤ 56 := by omega
  have hRle : (R : ℝ) ≤ 56 := by exact_mod_cast hRleNat
  have hR0 : 0 ≤ (R : ℝ) := by positivity
  have hR2 : (R : ℝ) ^ 2 ≤ 3136 := by nlinarith
  have hfour : (R : ℝ) ^ 4 ≤ 3136 * (R : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((R : ℝ) ^ 2)]
  have hscale :
      3136 * (R : ℝ) ^ 2 ≤ 3136 * (R : ℝ) ^ 2 * K := by
    have hnonneg : 0 ≤ 3136 * (R : ℝ) ^ 2 := by positivity
    nlinarith
  exact hbase.trans (hfour.trans hscale)

private theorem rawQ2ChildEnergy_sum_nonneg (R : ℕ) :
    0 ≤ ∑ q ∈ (primesUpTo (R - 1)).erase 2,
      rawQ2ChildEnergyReal R q := by
  apply Finset.sum_nonneg
  intro q hq
  unfold rawQ2ChildEnergyReal
  positivity

/-- The factor-three frozen/top/far estimate is exactly the square-root endpoint
amplification seam.  The forward direction uses the existing literal factor-four
q² recurrence equivalence; the reverse direction uses the shifted endpoint
numerator and the `10 R` root boundary. -/
theorem frozenTopFarThreeEnergy_iff_endpointAmplification :
    FrozenTopFarThreeEnergyStatement ↔
      SquareRootMertensEndpointAmplificationStatement := by
  constructor
  · rintro ⟨CF, hCF, hfar⟩
    apply exists_nonneg_squareEndpointRawOddQ2EnergyStep_iff_endpointAmplification.mp
    let C : ℝ := (4 : ℝ) / 3 * CF + 3536
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    refine ⟨C, hC, ?_⟩
    intro R K hR hK
    let Q : ℝ := ∑ q ∈ (primesUpTo (R - 1)).erase 2,
      rawQ2ChildEnergyReal R q
    have hQ : 0 ≤ Q := by
      dsimp [Q]
      exact rawQ2ChildEnergy_sum_nonneg R
    have hK1 : 1 ≤ K := one_le_lowerMertensCriticalEnvelope (by omega) hK
    by_cases hlarge : 56 ≤ R
    · have hF := hfar R K hlarge hK
      change ‖lowWheelFrozenTopFarResidual R‖ ^ 2 ≤
        3 * Q + CF * (R : ℝ) ^ 2 * K at hF
      have hB := norm_finalCompensatedRootBoundary_le_ten_root R hlarge
      have hBsq :
          ‖finalCompensatedRootBoundary R‖ ^ 2 ≤ 100 * (R : ℝ) ^ 2 := by
        have hbn : 0 ≤ ‖finalCompensatedRootBoundary R‖ := norm_nonneg _
        have hR0 : 0 ≤ (R : ℝ) := by positivity
        nlinarith
      have hsplit := norm_sub_sq_le_four_fourThirds
        (finalCompensatedRootBoundary R) (lowWheelFrozenTopFarResidual R)
      rw [← squarePrefixMertens_eq_rootBoundary_sub_frozenTopFar R hlarge] at hsplit
      have henergy := squareEndpointMertensEnergyReal_eq_squarePrefix_norm_sq
        (R := R) (by omega)
      rw [← henergy] at hsplit
      change squareEndpointMertensEnergyReal R ≤
        C * (R : ℝ) ^ 2 * K + 4 * Q
      dsimp [C]
      nlinarith [sq_nonneg (R : ℝ)]
    · have hsmall : R < 56 := by omega
      have hsmallBound :=
        smallRoot_squareEndpointMertensEnergyReal_le hR hsmall hK
      change squareEndpointMertensEnergyReal R ≤
        C * (R : ℝ) ^ 2 * K + 4 * Q
      dsimp [C]
      have hscale : 0 ≤ (R : ℝ) ^ 2 * K := by
        have hK0 : 0 ≤ K := hK.1
        positivity
      nlinarith
  · rintro ⟨A, hA, hamp⟩
    let CF : ℝ := 242 + 2 * A
    have hCF : 0 ≤ CF := by
      dsimp [CF]
      positivity
    refine ⟨CF, hCF, ?_⟩
    intro R K hR hK
    have hK1 : 1 ≤ K := one_le_lowerMertensCriticalEnvelope (by omega) hK
    have hAmp := hamp R K (by omega) hK
    have hMshift :
        ‖squarePrefixMertens (R - 1) - 1‖ ^ 2 ≤
          A * (R : ℝ) ^ 2 * K := by
      rw [squarePrefix_shifted_norm_sq_eq_realInt_sq (R := R) (by omega)]
      exact hAmp
    have hB := norm_finalCompensatedRootBoundary_le_ten_root R hR
    have hBshiftNorm :
        ‖finalCompensatedRootBoundary R - 1‖ ≤ 11 * (R : ℝ) := by
      have hsub := norm_sub_le (finalCompensatedRootBoundary R) (1 : ℂ)
      have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
      norm_num at hsub
      nlinarith
    have hBshiftSq :
        ‖finalCompensatedRootBoundary R - 1‖ ^ 2 ≤
          121 * (R : ℝ) ^ 2 := by
      have hn : 0 ≤ ‖finalCompensatedRootBoundary R - 1‖ := norm_nonneg _
      have hR0 : 0 ≤ (R : ℝ) := by positivity
      nlinarith
    have hendpoint := squarePrefixMertens_eq_rootBoundary_sub_frozenTopFar R hR
    have hrewrite :
        lowWheelFrozenTopFarResidual R =
          (finalCompensatedRootBoundary R - 1) -
            (squarePrefixMertens (R - 1) - 1) := by
      linear_combination hendpoint
    have htwo := norm_sub_sq_le_two
      (finalCompensatedRootBoundary R - 1)
      (squarePrefixMertens (R - 1) - 1)
    rw [← hrewrite] at htwo
    have hcore :
        ‖lowWheelFrozenTopFarResidual R‖ ^ 2 ≤
          CF * (R : ℝ) ^ 2 * K := by
      dsimp [CF]
      nlinarith [sq_nonneg (R : ℝ)]
    have hQ := rawQ2ChildEnergy_sum_nonneg R
    exact hcore.trans (by
      have hthreeQ :
          0 ≤ 3 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
            rawQ2ChildEnergyReal R q := by positivity
      linarith)

/-- FAR-4 retains each complete signed Mertens daughter before squaring. -/
def FrozenTopFarFourEnergyStatement : Prop :=
  ∃ CF : ℝ, 0 ≤ CF ∧
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖lowWheelFrozenTopFarResidual R‖ ^ 2 ≤
        4 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          rawQ2ChildEnergyReal R q +
        CF * (R : ℝ) ^ 2 * K

private theorem norm_sub_sq_le_fortyOne_fortyOneFortieths (u v : ℂ) :
    ‖u - v‖ ^ 2 ≤ 41 * ‖u‖ ^ 2 + (41 : ℝ) / 40 * ‖v‖ ^ 2 := by
  have hnorm := norm_sub_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u - v‖ := norm_nonneg _
  nlinarith [sq_nonneg (40 * ‖u‖ - ‖v‖)]

/-- FAR-4 supplies a literal `41/10` recurrence, including every small root.
The `10 R` root boundary and `37/36` daughter shell have separate additive
allowances; no rounding error is omitted from the terminal induction. -/
theorem frozenTopFarFourEnergy_implies_rawFortyOneTen
    (hfar : FrozenTopFarFourEnergyStatement) :
    ∃ C : ℝ, 0 ≤ C ∧ SquareEndpointRawOddQ2EnergyStepWith ((41 : ℝ) / 10) C := by
  rcases hfar with ⟨CF, hCF, hfar⟩
  let C : ℝ := 4100 + (41 : ℝ) / 40 * CF
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R K hR hK
  let Q : ℝ := ∑ q ∈ (primesUpTo (R - 1)).erase 2,
    rawQ2ChildEnergyReal R q
  have hQ : 0 ≤ Q := rawQ2ChildEnergy_sum_nonneg R
  have hK1 : 1 ≤ K := one_le_lowerMertensCriticalEnvelope (by omega) hK
  by_cases hlarge : 56 ≤ R
  · have hF := hfar R K hlarge hK
    change ‖lowWheelFrozenTopFarResidual R‖ ^ 2 ≤
      4 * Q + CF * (R : ℝ) ^ 2 * K at hF
    have hB := norm_finalCompensatedRootBoundary_le_ten_root R hlarge
    have hBsq :
        ‖finalCompensatedRootBoundary R‖ ^ 2 ≤ 100 * (R : ℝ) ^ 2 := by
      have hbn : 0 ≤ ‖finalCompensatedRootBoundary R‖ := norm_nonneg _
      have hR0 : 0 ≤ (R : ℝ) := by positivity
      nlinarith
    have hsplit := norm_sub_sq_le_fortyOne_fortyOneFortieths
      (finalCompensatedRootBoundary R) (lowWheelFrozenTopFarResidual R)
    rw [← squarePrefixMertens_eq_rootBoundary_sub_frozenTopFar R hlarge] at hsplit
    have henergy := squareEndpointMertensEnergyReal_eq_squarePrefix_norm_sq
      (R := R) (by omega)
    rw [← henergy] at hsplit
    change squareEndpointMertensEnergyReal R ≤
      C * (R : ℝ) ^ 2 * K + (41 : ℝ) / 10 * Q
    dsimp [C]
    nlinarith [sq_nonneg (R : ℝ)]
  · have hsmall := smallRoot_squareEndpointMertensEnergyReal_le hR
      (show R < 56 by omega) hK
    change squareEndpointMertensEnergyReal R ≤
      C * (R : ℝ) ^ 2 * K + (41 : ℝ) / 10 * Q
    dsimp [C]
    have hscale : 0 ≤ (R : ℝ) ^ 2 * K := by
      have hK0 := hK.1
      positivity
    nlinarith [mul_nonneg hCF hscale]

/-- FAR-4 closes through the exact subcritical terminal engine.  The signed
FAR-4 estimate itself is an explicit hypothesis, not an established Gram bound. -/
theorem frozenTopFarFourEnergy_iff_endpointAmplification :
    FrozenTopFarFourEnergyStatement ↔
      SquareRootMertensEndpointAmplificationStatement := by
  constructor
  · intro hfar
    rcases frozenTopFarFourEnergy_implies_rawFortyOneTen hfar with ⟨C, hC, hstep⟩
    exact squareEndpointRawOddQ2EnergyStepWith_implies_endpointAmplification
      hC (by norm_num) (by norm_num) hstep
  · intro hamp
    rcases frozenTopFarThreeEnergy_iff_endpointAmplification.mpr hamp with
      ⟨CF, hCF, hfar⟩
    refine ⟨CF, hCF, ?_⟩
    intro R K hR hK
    have hF := hfar R K hR hK
    have hQ := rawQ2ChildEnergy_sum_nonneg R
    linarith

/-- Conditional FAR-4 terminal theorem.  No proof of FAR-4 is asserted. -/
theorem riemannHypothesis_of_frozenTopFarFourEnergy
    (hfar : FrozenTopFarFourEnergyStatement) : RiemannHypothesis := by
  apply RHLean.Analysis.riemannHypothesis_of_mertensEnergy
  exact mertensEnergyBounded_of_squareRootEndpointAmplification
    (frozenTopFarFourEnergy_iff_endpointAmplification.mp hfar)

end RHLean.Proof
