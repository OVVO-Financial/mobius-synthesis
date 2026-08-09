import Mathlib
import RHLean.Proof.VanishingTransitionRelevance
import RHLean.Proof.RealSquareBlockIncrements
import RHLean.Analysis.SquarePrefixMertensBridge

/-!
# Prime-number-theorem closure from vanishing mutable relevance

This module closes the PNT-scale consequence of the mutable-support architecture.
The complete seed-to-current telescope is retained throughout.

If the settled complement has zero Möbius mass and the mutable support in block
`n` has cardinality `o(n)`, then the exact block discrepancy is `o(n)`.
Summing from the common seed gives an `o(N^2)` square-prefix Mertens bound.
The standard gap estimate between consecutive square endpoints then gives the
full `M(x) = o(x)` statement.

No Gram, correlation, or RH-scale premise is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators Topology
open Filter

namespace RHLean.Proof

open RHLean.Arithmetic

def SquarePrefixPNTStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop,
      ‖RHLean.Analysis.squarePrefixMertens N‖ ≤
        ε * (((N + 1 : ℕ) : ℝ) ^ 2)

def MertensPNTStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ x : ℕ in atTop,
      ‖RHLean.Analysis.mertensSummatory x‖ ≤ ε * ((x + 1 : ℕ) : ℝ)

private theorem realIncrement_eq_squareBlockMoebius (n : ℕ) :
    realCanonicalTotalIncrement n = (squareBlockMoebius n : ℝ) := by
  unfold realCanonicalTotalIncrement realCanonicalMoebiusWeight
    canonicalSquareBlock squareBlockMoebius squareBlockInterval
  norm_cast

theorem realCanonicalTotalPrefix_eq_sum_squareBlockMoebius (N : ℕ) :
    realCanonicalTotalPrefix N =
      ∑ n ∈ Finset.range (N + 1), (squareBlockMoebius n : ℝ) := by
  unfold realCanonicalTotalPrefix
  apply Finset.sum_congr rfl
  intro n hn
  exact realIncrement_eq_squareBlockMoebius n

theorem squarePrefixPNT_of_squareBlockDiscrepancyVanishes
    (hΔ : SquareBlockDiscrepancyVanishes) :
    SquarePrefixPNTStatement := by
  intro ε hε
  have htail := hΔ (ε / 4) (by linarith)
  rcases (eventually_atTop.1 htail) with ⟨K0, hK0⟩
  let K := max K0 1
  let A : ℝ := ∑ n ∈ Finset.range K, |(squareBlockMoebius n : ℝ)|
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  obtain ⟨T : ℕ, hT⟩ := exists_nat_gt (4 * A / ε)
  filter_upwards [eventually_ge_atTop (max K T)] with N hN
  have hKN : K ≤ N := le_trans (le_max_left K T) hN
  have hTN : T ≤ N := le_trans (le_max_right K T) hN
  have hK0K : K0 ≤ K := by
    dsimp [K]
    exact le_max_left _ _
  have hKpos : 0 < K := by
    dsimp [K]
    omega
  have hprefixSplit :
      realCanonicalTotalPrefix N =
        (∑ n ∈ Finset.range K, (squareBlockMoebius n : ℝ)) +
        ∑ n ∈ Finset.Ico K (N + 1), (squareBlockMoebius n : ℝ) := by
    rw [realCanonicalTotalPrefix_eq_sum_squareBlockMoebius]
    exact (Finset.sum_range_add_sum_Ico (fun n : ℕ => (squareBlockMoebius n : ℝ))
      (Nat.le_succ_of_le hKN)).symm
  have hhead :
      |∑ n ∈ Finset.range K, (squareBlockMoebius n : ℝ)| ≤ A := by
    dsimp [A]
    simpa only [Real.norm_eq_abs] using
      (norm_sum_le (Finset.range K) (fun n : ℕ => (squareBlockMoebius n : ℝ)))
  have htailPoint : ∀ n ∈ Finset.Ico K (N + 1),
      |(squareBlockMoebius n : ℝ)| ≤ (ε / 4) * (n : ℝ) := by
    intro n hn
    have hnK : K ≤ n := (Finset.mem_Ico.mp hn).1
    have hK0n : K0 ≤ n := le_trans hK0K hnK
    have hnpos : 0 < n := lt_of_lt_of_le hKpos hnK
    have hnorm := hK0 n hK0n
    unfold normalizedSquareBlockDiscrepancy at hnorm
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
    exact (div_le_iff₀ hnreal).mp hnorm
  have htailAbs :
      |∑ n ∈ Finset.Ico K (N + 1), (squareBlockMoebius n : ℝ)| ≤
        (ε / 4) * (((N + 1 : ℕ) : ℝ) ^ 2) := by
    calc
      |∑ n ∈ Finset.Ico K (N + 1), (squareBlockMoebius n : ℝ)| ≤
          ∑ n ∈ Finset.Ico K (N + 1), |(squareBlockMoebius n : ℝ)| := by
            simpa only [Real.norm_eq_abs] using
              (norm_sum_le (Finset.Ico K (N + 1))
                (fun n : ℕ => (squareBlockMoebius n : ℝ)))
      _ ≤ ∑ _n ∈ Finset.Ico K (N + 1),
          (ε / 4) * ((N + 1 : ℕ) : ℝ) := by
            apply Finset.sum_le_sum
            intro n hn
            have hnle : n ≤ N :=
              Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hn).2
            exact (htailPoint n hn).trans
              (mul_le_mul_of_nonneg_left
                (by exact_mod_cast (Nat.le_succ_of_le hnle)) (by linarith))
      _ = ((Finset.Ico K (N + 1)).card : ℝ) *
          ((ε / 4) * ((N + 1 : ℕ) : ℝ)) := by simp [mul_comm]
      _ ≤ ((N + 1 : ℕ) : ℝ) *
          ((ε / 4) * ((N + 1 : ℕ) : ℝ)) := by
            gcongr
            have hcardNat : (Finset.Ico K (N + 1)).card ≤ N + 1 := by
              rw [Nat.card_Ico]
              omega
            exact_mod_cast hcardNat
      _ = (ε / 4) * (((N + 1 : ℕ) : ℝ) ^ 2) := by ring
  have hheadSmall : A ≤ (ε / 4) * (((N + 1 : ℕ) : ℝ) ^ 2) := by
    have hTreal : 4 * A / ε < (T : ℝ) := by exact_mod_cast hT
    have hTle : (T : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (le_trans hTN (Nat.le_succ N))
    have hOne : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le N))
    have hsquare : ((N + 1 : ℕ) : ℝ) ≤ (((N + 1 : ℕ) : ℝ) ^ 2) := by
      nlinarith
    have hquot : 4 * A / ε < (((N + 1 : ℕ) : ℝ) ^ 2) :=
      lt_of_lt_of_le hTreal (le_trans hTle hsquare)
    have hmul : 4 * A < (((N + 1 : ℕ) : ℝ) ^ 2) * ε :=
      (div_lt_iff₀ hε).mp hquot
    have hmul' : 4 * A < ε * (((N + 1 : ℕ) : ℝ) ^ 2) := by
      simpa [mul_comm] using hmul
    linarith
  have hprefAbs :
      |realCanonicalTotalPrefix N| ≤
        (ε / 2) * (((N + 1 : ℕ) : ℝ) ^ 2) := by
    rw [hprefixSplit]
    calc
      |(∑ n ∈ Finset.range K, (squareBlockMoebius n : ℝ)) +
          ∑ n ∈ Finset.Ico K (N + 1), (squareBlockMoebius n : ℝ)| ≤
          |∑ n ∈ Finset.range K, (squareBlockMoebius n : ℝ)| +
          |∑ n ∈ Finset.Ico K (N + 1), (squareBlockMoebius n : ℝ)| :=
        abs_add_le _ _
      _ ≤ A + (ε / 4) * (((N + 1 : ℕ) : ℝ) ^ 2) :=
        add_le_add hhead htailAbs
      _ ≤ (ε / 2) * (((N + 1 : ℕ) : ℝ) ^ 2) := by linarith
  have hcast := realCanonicalTotalPrefix_cast_eq_squarePrefixMertens N
  have hnormeq :
      ‖RHLean.Analysis.squarePrefixMertens N‖ = |realCanonicalTotalPrefix N| := by
    rw [← hcast]
    simp
  rw [hnormeq]
  exact hprefAbs.trans (by
    have hsquareNonneg : 0 ≤ (((N + 1 : ℕ) : ℝ) ^ 2) := sq_nonneg _
    nlinarith)

theorem squarePrefixPNT_of_transitionRelevanceVanishes
    (U : ℕ → Finset ℕ)
    (hU : ∀ n, U n ⊆ squareBlockInterval n)
    (hinterior : ∀ n, ∑ m ∈ squareBlockInterval n \ U n, μ m = 0)
    (hvanish : TransitionRelevanceVanishes U) :
    SquarePrefixPNTStatement :=
  squarePrefixPNT_of_squareBlockDiscrepancyVanishes
    (squareBlockDiscrepancyVanishes_of_transitionRelevanceVanishes
      U hU hinterior hvanish)

/-- Arithmetic core of the square-root interpolation step.

Stated for opaque reals on purpose.  In the main proof the corresponding terms
contain `Nat.sqrt x` under a local definition, and letting the nonlinear
arithmetic tactics see through that definition forces repeated `whnf` on the
`Nat.sqrt` recursion, which exhausts the heartbeat budget. -/
private theorem four_mul_le_of_sq_le_of_lt
    {a X ε : ℝ} (hε : 0 < ε) (hX : 0 < X)
    (hsq : a ^ 2 ≤ 4 * X) (hbig : 64 < ε ^ 2 * X) :
    4 * a ≤ ε * X := by
  have hεX : 0 ≤ ε * X := mul_nonneg hε.le hX.le
  have hstep : (4 * a) ^ 2 < (ε * X) ^ 2 := by
    nlinarith [hsq, mul_lt_mul_of_pos_right hbig hX]
  by_contra hcon
  push_neg at hcon
  have hlt : (ε * X) * (ε * X) < (4 * a) * (4 * a) :=
    mul_self_lt_mul_self hεX hcon
  nlinarith [hstep, hlt]

set_option maxHeartbeats 400000 in
theorem mertensPNT_of_squarePrefixPNT
    (hS : SquarePrefixPNTStatement) :
    MertensPNTStatement := by
  intro ε hε
  have hsample := hS (ε / 2) (by linarith)
  rcases (eventually_atTop.1 hsample) with ⟨N0, hN0⟩
  obtain ⟨X0 : ℕ, hX0⟩ := exists_nat_gt (64 / ε ^ 2)
  filter_upwards [eventually_ge_atTop (max ((N0 + 1) ^ 2) X0)] with x hx
  let r := Nat.sqrt x
  let n := r - 1
  have hxpos : 0 < x := by
    have hbasePos : 0 < (N0 + 1) ^ 2 := by positivity
    have hbase : (N0 + 1) ^ 2 ≤ x := le_trans (le_max_left _ _) hx
    exact lt_of_lt_of_le hbasePos hbase
  have hr : 1 ≤ r := by
    dsimp [r]
    exact Nat.sqrt_pos.mpr hxpos
  have hn1 : n + 1 = r := by dsimp [n]; omega
  have hr_sq_le : r ^ 2 ≤ x := by
    dsimp [r]
    exact Nat.sqrt_le' x
  have hr_le_x : r ≤ x := by
    dsimp [r]
    exact Nat.sqrt_le_self x
  have hn0 : N0 ≤ n := by
    have hN0sq : (N0 + 1) ^ 2 ≤ x := le_trans (le_max_left _ _) hx
    have hN0r : N0 + 1 ≤ r := by
      exact (Nat.le_sqrt).2 (by simpa [pow_two] using hN0sq)
    omega
  have hendpoint : RHLean.Analysis.squarePrefixEndpoint n = r ^ 2 - 1 := by
    unfold RHLean.Analysis.squarePrefixEndpoint
    rw [hn1]
  have hendpoint_le : RHLean.Analysis.squarePrefixEndpoint n ≤ x := by
    rw [hendpoint]
    exact le_trans (Nat.sub_le _ _) hr_sq_le
  have hx_lt : x < (r + 1) ^ 2 := by
    dsimp [r]
    exact Nat.lt_succ_sqrt' x
  have hgapNat : x - RHLean.Analysis.squarePrefixEndpoint n ≤ 2 * (r + 1) := by
    rw [hendpoint]
    have hsquare : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
    rw [hsquare] at hx_lt
    omega
  have hgap := RHLean.Analysis.norm_mertensSummatory_sub_le
    (RHLean.Analysis.squarePrefixEndpoint n) x hendpoint_le
  have hgapR :
      ‖RHLean.Analysis.mertensSummatory x - RHLean.Analysis.squarePrefixMertens n‖ ≤
        2 * (r + 1 : ℝ) := by
    exact hgap.trans (by exact_mod_cast hgapNat)
  have hsampleN := hN0 n hn0
  have hsampleR :
      ‖RHLean.Analysis.squarePrefixMertens n‖ ≤
        (ε / 2) * (r : ℝ) ^ 2 := by
    simpa only [hn1] using hsampleN
  have hrSqR : (r : ℝ) ^ 2 ≤ ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast (hr_sq_le.trans (Nat.le_succ x))
  have hsampleFinal :
      ‖RHLean.Analysis.squarePrefixMertens n‖ ≤
        (ε / 2) * ((x + 1 : ℕ) : ℝ) :=
    hsampleR.trans (mul_le_mul_of_nonneg_left hrSqR (by linarith))
  have hX0le : X0 ≤ x := le_trans (le_max_right _ _) hx
  have hX0real : 64 / ε ^ 2 < (x : ℝ) := by
    exact lt_of_lt_of_le (by exact_mod_cast hX0) (by exact_mod_cast hX0le)
  have hsqrtSmall : 2 * (r + 1 : ℝ) ≤ (ε / 2) * ((x + 1 : ℕ) : ℝ) := by
    have haSq : ((r : ℝ) + 1) ^ 2 ≤ 4 * ((x + 1 : ℕ) : ℝ) := by
      have hnat : (r + 1) ^ 2 ≤ 4 * (x + 1) := by
        have hsquare : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
        rw [hsquare]
        omega
      exact_mod_cast hnat
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hxlargeRaw : 64 < (x : ℝ) * ε ^ 2 :=
      (div_lt_iff₀ hεsq).mp hX0real
    have hxcast : (x : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_succ x)
    have hXpos : (0 : ℝ) < ((x + 1 : ℕ) : ℝ) := by
      have hpos : 0 < x + 1 := Nat.succ_pos x
      exact_mod_cast hpos
    have hxlarge : 64 < ε ^ 2 * ((x + 1 : ℕ) : ℝ) := by
      have hmono : (x : ℝ) * ε ^ 2 ≤ ((x + 1 : ℕ) : ℝ) * ε ^ 2 :=
        mul_le_mul_of_nonneg_right hxcast (sq_nonneg ε)
      have hchain : 64 < ((x + 1 : ℕ) : ℝ) * ε ^ 2 :=
        lt_of_lt_of_le hxlargeRaw hmono
      simpa [mul_comm] using hchain
    have hlinear := four_mul_le_of_sq_le_of_lt hε hXpos haSq hxlarge
    linarith
  calc
    ‖RHLean.Analysis.mertensSummatory x‖ =
        ‖RHLean.Analysis.squarePrefixMertens n +
          (RHLean.Analysis.mertensSummatory x -
            RHLean.Analysis.squarePrefixMertens n)‖ := by
              congr 1
              ring
    _ ≤ ‖RHLean.Analysis.squarePrefixMertens n‖ +
        ‖RHLean.Analysis.mertensSummatory x -
          RHLean.Analysis.squarePrefixMertens n‖ := norm_add_le _ _
    _ ≤ (ε / 2) * ((x + 1 : ℕ) : ℝ) +
        (ε / 2) * ((x + 1 : ℕ) : ℝ) :=
      add_le_add hsampleFinal (hgapR.trans hsqrtSmall)
    _ = ε * ((x + 1 : ℕ) : ℝ) := by ring

theorem mertensPNT_of_transitionRelevanceVanishes
    (U : ℕ → Finset ℕ)
    (hU : ∀ n, U n ⊆ squareBlockInterval n)
    (hinterior : ∀ n, ∑ m ∈ squareBlockInterval n \ U n, μ m = 0)
    (hvanish : TransitionRelevanceVanishes U) :
    MertensPNTStatement :=
  mertensPNT_of_squarePrefixPNT
    (squarePrefixPNT_of_transitionRelevanceVanishes
      U hU hinterior hvanish)

end RHLean.Proof
