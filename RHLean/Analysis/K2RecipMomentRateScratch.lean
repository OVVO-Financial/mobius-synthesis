import RHLean.Analysis.K2CenteredClassicalInterface
import RHLean.Analysis.K2RecipMomentAbelIdentificationScratch

noncomputable section

open Filter Finset Set Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

local notation "gammaE" => Real.eulerMascheroniConstant

/-- The order-two Abel increments remain absolutely summable after one extra
logarithm.  This is the quantitative tail input needed for
`k2r N * log N -> 0`. -/
theorem k2MertensAbelTerm_two_mul_log_summable :
    Summable (fun N : ℕ =>
      Real.log (N : ℝ) * k2MertensAbelTerm 2 N) := by
  obtain ⟨c, C, hc, _hC, hM⟩ := strongNativeMertensSubexp
  let g : ℕ → ℝ := fun N =>
    8 * C * (1 / ((N : ℝ) * (Real.log (N : ℝ)) ^ 2))
  have hbase : Summable (fun N : ℕ =>
      1 / ((N : ℝ) * (Real.log (N : ℝ)) ^ 2)) := by
    rw [← summable_nat_add_iff 3 (G := ℝ)]
    exact (k2LogHarmonicTail_summable (p := 2) (by norm_num)).congr fun n => by
      simp [k2LogHarmonicTail, one_div, mul_inv_rev]
  have hg : Summable g := hbase.mul_left (8 * C)
  have hpowNat :
      ∀ᶠ N : ℕ in atTop,
        strongMertensScale (N : ℝ) ^ 50 ≤
          Real.exp (c * strongMertensScale (N : ℝ)) :=
    tendsto_natCast_atTop_atTop.eventually
      (strongMertens_scale_pow_le_exp_eventually 50 hc)
  apply Summable.of_norm_bounded_eventually_nat hg
  filter_upwards [eventually_ge_atTop 3, hpowNat] with N hN hpow
  have hNposNat : 0 < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNposNat
  have hL : 1 < Real.log (N : ℝ) := logt_gt_one (by exact_mod_cast hN : (3 : ℝ) ≤ N)
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  let r := strongMertensScale (N : ℝ)
  have hr50 : (Real.log (N : ℝ)) ^ 5 = r ^ 50 := by
    have hs := strongMertensScale_pow_ten (X := (N : ℝ)) hN1
    dsimp [r]
    rw [← hs]
    ring
  have hdecay5 :
      Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 5 ≤ 1 := by
    rw [hr50]
    calc
      Real.exp (-c * r) * r ^ 50
          ≤ Real.exp (-c * r) * Real.exp (c * r) :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
  have hdecay3 :
      Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 3 ≤
        1 / (Real.log (N : ℝ)) ^ 2 := by
    rw [le_div_iff₀ (pow_pos hLpos 2)]
    calc
      Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 3 *
          (Real.log (N : ℝ)) ^ 2
          = Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 5 := by ring
      _ ≤ 1 := hdecay5
  have hweight := k2LogRecipWeight_two_diff_abs_le N hN
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.log_nonneg hN1),
    k2MertensAbelTerm, abs_mul]
  calc
    Real.log (N : ℝ) *
        (|nativeMertensSummatory N| *
          |k2LogRecipWeight 2 N - k2LogRecipWeight 2 (N + 1)|)
      ≤ Real.log (N : ℝ) *
          ((C * (N : ℝ) * Real.exp (-c * r)) *
            |k2LogRecipWeight 2 N - k2LogRecipWeight 2 (N + 1)|) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_right
          · simpa [r, strongMertensScale, one_div] using hM N hN
          · exact abs_nonneg _
        · exact Real.log_nonneg hN1
    _ ≤ Real.log (N : ℝ) *
          ((C * (N : ℝ) * Real.exp (-c * r)) *
            (8 * (Real.log (N : ℝ)) ^ 2 / (N : ℝ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left hweight
          positivity
        · exact Real.log_nonneg hN1
    _ = (8 * C / (N : ℝ)) *
          (Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 3) := by
        field_simp [ne_of_gt hNpos]
    _ ≤ (8 * C / (N : ℝ)) *
          (1 / (Real.log (N : ℝ)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left hdecay3
        positivity
    _ = g N := by
        dsimp [g]
        field_simp [ne_of_gt hNpos]

/-- The Abel tail of the order-two moment is `o(1 / log N)`. -/
theorem k2MertensAbelTerm_two_tail_mul_log_tendsto_zero :
    Tendsto
      (fun N : ℕ =>
        Real.log (N : ℝ) *
          (∑' i : ℕ, k2MertensAbelTerm 2 (i + N)))
      atTop (𝓝 0) := by
  have hweightedNorm : Summable (fun n : ℕ =>
      ‖Real.log (n : ℝ) * k2MertensAbelTerm 2 n‖) :=
    k2MertensAbelTerm_two_mul_log_summable.norm
  have htailNorm :
      Tendsto
        (fun N : ℕ =>
          ∑' i : ℕ,
            ‖Real.log ((i + N : ℕ) : ℝ) *
              k2MertensAbelTerm 2 (i + N)‖)
        atTop (𝓝 0) := by
    simpa [Nat.add_comm] using
      (tendsto_sum_nat_add
        (fun n : ℕ => ‖Real.log (n : ℝ) * k2MertensAbelTerm 2 n‖))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ htailNorm
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hshift : Summable (fun i : ℕ => k2MertensAbelTerm 2 (i + N)) :=
    (summable_nat_add_iff N).2 k2MertensAbelTerm_two_summable
  have hleft : Summable (fun i : ℕ =>
      Real.log (N : ℝ) * ‖k2MertensAbelTerm 2 (i + N)‖) :=
    hshift.norm.mul_left (Real.log (N : ℝ))
  have hright : Summable (fun i : ℕ =>
      ‖Real.log ((i + N : ℕ) : ℝ) * k2MertensAbelTerm 2 (i + N)‖) :=
    (summable_nat_add_iff N).2 hweightedNorm
  calc
    ‖Real.log (N : ℝ) *
        (∑' i : ℕ, k2MertensAbelTerm 2 (i + N))‖
      = Real.log (N : ℝ) *
          ‖∑' i : ℕ, k2MertensAbelTerm 2 (i + N)‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hlogN]
    _ ≤ Real.log (N : ℝ) *
          (∑' i : ℕ, ‖k2MertensAbelTerm 2 (i + N)‖) := by
        exact mul_le_mul_of_nonneg_left
          (norm_tsum_le_tsum_norm hshift.norm) hlogN
    _ = ∑' i : ℕ,
          Real.log (N : ℝ) * ‖k2MertensAbelTerm 2 (i + N)‖ := by
        rw [tsum_mul_left]
    _ ≤ ∑' i : ℕ,
          ‖Real.log ((i + N : ℕ) : ℝ) *
            k2MertensAbelTerm 2 (i + N)‖ := by
        exact hleft.tsum_le_tsum (fun i => by
          have hNi : N ≤ i + N := by omega
          have hcast : (N : ℝ) ≤ ((i + N : ℕ) : ℝ) := by exact_mod_cast hNi
          have hNi1 : (1 : ℝ) ≤ ((i + N : ℕ) : ℝ) := by
            exact hcast.trans' (by exact_mod_cast hN)
          have hlogle := Real.log_le_log hNpos hcast
          have hlogNi : 0 ≤ Real.log ((i + N : ℕ) : ℝ) := Real.log_nonneg hNi1
          rw [norm_mul, Real.norm_of_nonneg hlogNi]
          exact mul_le_mul_of_nonneg_right hlogle (norm_nonneg _)) hright

/-- The centered order-two reciprocal moment has the stronger rate required by
the classical K2 hyperbola closure. -/
theorem k2r_mul_log_tendsto_zero_from_strongMertens :
    Tendsto
      (fun N : ℕ => k2r N * Real.log (N : ℝ))
      atTop (𝓝 0) := by
  have hend3 := k2StrongMertens_logRecip_endpoint_tendsto_zero 3
  have htail := k2MertensAbelTerm_two_tail_mul_log_tendsto_zero
  have hcombined :
      Tendsto
        (fun N : ℕ =>
          nativeMertensSummatory N * k2LogRecipWeight 3 N -
            Real.log (N : ℝ) *
              (∑' i : ℕ, k2MertensAbelTerm 2 (i + N)))
        atTop (𝓝 0) := by
    simpa using hend3.sub htail
  refine hcombined.congr fun N => ?_
  have hsum := k2MertensAbelTerm_two_summable.sum_add_tsum_nat_add N
  have hmom := k2MobiusLogMoment_abel 2 N
  rw [k2MertensAbelTerm_sum_Ico_eq_range] at hmom
  have htsum := k2MertensAbelTerm_two_tsum_eq_neg_two_gamma
  have htailEq :
      (∑' i : ℕ, k2MertensAbelTerm 2 (i + N)) =
        -2 * gammaE - ∑ n ∈ Finset.range N, k2MertensAbelTerm 2 n := by
    rw [htsum] at hsum
    linarith
  unfold k2r
  rw [k2A2_eq_moment, hmom]
  have hweight3 :
      nativeMertensSummatory N * k2LogRecipWeight 3 N =
        (nativeMertensSummatory N * k2LogRecipWeight 2 N) *
          Real.log (N : ℝ) := by
    unfold k2LogRecipWeight
    ring
  rw [hweight3, htailEq]
  ring

/-- All analytic inputs required by the finite classical K2 closure now follow
from the Strong Mertens theorem. -/
theorem k2ClassicalMomentInput_from_strongMertens : K2ClassicalMomentInput where
  r_tendsto_zero := k2r_tendsto_zero_from_strongMertens
  r_mul_log_tendsto_zero := k2r_mul_log_tendsto_zero_from_strongMertens
  c3_tendsto := k2C3_tendsto_from_strongMertens

end RHLean.Analysis
