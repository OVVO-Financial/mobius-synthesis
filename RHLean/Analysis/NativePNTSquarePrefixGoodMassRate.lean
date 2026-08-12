import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixGoodMass

/-!
# Explicit quadratic good-mass rate from square-prefix shells

This module completes the good-fibre-density replacement.  It first converts
the eventual complete-square PNT1/PNT2 supply into a separated power-shell
selector whose selected points all came from square-prefix search spans.  It
then reruns the reciprocal-quotient packing with those bounds.

The old `nativePNT_exists_good_power_shell_selector` and
`nativeLambdaTwoGoodRecipMass_eventually_quadratic_with_rate` are not used.
The resulting coefficient is explicit:

`eps^2 / 6600000`.

The small numerical change from `6500000` is only the cost of expressing shell
width in the doubled square-prefix exponent clock.  The dependence remains
quadratic and completely effective.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace RHLean.Analysis

/-! ## Square-prefix shell selector -/

private theorem nativePNTSquarePrefix_pow_sq (e : ℕ) :
    (2 ^ e) ^ 2 = 2 ^ (2 * e) := by
  rw [← pow_mul]
  congr 1
  omega

/-- A separated family of good intervals selected only from complete-square
search spans.  `S` is the spacing in the physical binary exponent and `W` is
the width of one selected square-prefix search shell. -/
theorem nativePNT_exists_good_squarePrefix_power_shell_selector
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ S W E : ℕ, ∃ t : ℕ → ℕ,
      0 < S ∧ W + 2 ≤ S ∧
      ((S : ℝ) ≤ 200 / eps) ∧
      (∀ j : ℕ, 2 ^ (E + j * S) ≤ t j) ∧
      (∀ j : ℕ, t j ≤ 2 ^ (E + j * S + W)) ∧
      (∀ j : ℕ,
        ∀ q ∈ Finset.Icc (t j)
          (t j + nativePNTGoodForwardRadius (t j) eps),
          |nativePNTError q| ≤ eps * (q : ℝ)) := by
  classical
  rcases nativePNT_exists_squarePrefix_depth_quantitative eps heps heps1 with
    ⟨K, hdepth, hKupper⟩
  have hshell :=
    nativePNT_exists_good_radius_squarePrefix_eventually
      K eps heps heps1 hdepth
  rcases eventually_atTop.1 hshell with ⟨A0, hA0⟩
  let L : ℕ := K + 2
  let E0 : ℕ := A0 + 1
  let S : ℕ := 2 * L
  let W : ℕ := 2 * K
  let E : ℕ := 2 * E0
  let base : ℕ → ℕ := fun j => 2 ^ (E0 + j * L) - 1
  have hE0pow : E0 ≤ 2 ^ E0 := by
    exact (Nat.lt_pow_self Nat.one_lt_two).le
  have hbaseA0 : ∀ j : ℕ, A0 ≤ base j := by
    intro j
    have hexp : E0 ≤ E0 + j * L := by omega
    have hp : 2 ^ E0 ≤ 2 ^ (E0 + j * L) :=
      (Nat.pow_le_pow_iff_right Nat.one_lt_two).2 hexp
    have hA01 : A0 + 1 ≤ 2 ^ (E0 + j * L) := by
      simpa [E0] using hE0pow.trans hp
    dsimp [base]
    omega
  have hExists : ∀ j : ℕ,
      ∃ u ∈ Finset.Icc (nativePNTSquarePrefixSearchLower (base j))
          (nativePNTSquarePrefixSearchUpper (base j) K),
        |nativePNTError u| ≤ eps * (u : ℝ) / 4 ∧
          ∀ q ∈ Finset.Icc u (u + nativePNTGoodForwardRadius u eps),
            |nativePNTError q| ≤ eps * (q : ℝ) := by
    intro j
    exact hA0 (base j) (hbaseA0 j)
  let t : ℕ → ℕ := fun j => Classical.choose (hExists j)
  have hspec : ∀ j : ℕ,
      t j ∈ Finset.Icc (nativePNTSquarePrefixSearchLower (base j))
          (nativePNTSquarePrefixSearchUpper (base j) K) ∧
        |nativePNTError (t j)| ≤ eps * (t j : ℝ) / 4 ∧
          ∀ q ∈ Finset.Icc (t j)
            (t j + nativePNTGoodForwardRadius (t j) eps),
            |nativePNTError q| ≤ eps * (q : ℝ) := by
    intro j
    exact Classical.choose_spec (hExists j)
  have hSpos : 0 < S := by
    dsimp [S, L]
    omega
  have hgap : W + 2 ≤ S := by
    dsimp [W, S, L]
    omega
  have hSupper : (S : ℝ) ≤ 200 / eps := by
    dsimp [S, L]
    push_cast
    exact hKupper
  have hbaseOne : ∀ j : ℕ, base j + 1 = 2 ^ (E0 + j * L) := by
    intro j
    dsimp [base]
    have hp : 0 < 2 ^ (E0 + j * L) := by positivity
    omega
  have htLower : ∀ j : ℕ, 2 ^ (E + j * S) ≤ t j := by
    intro j
    have hm := (Finset.mem_Icc.mp (hspec j).1).1
    have hExp : E + j * S = 2 * (E0 + j * L) := by
      dsimp [E, S]
      ring
    have hSearch :
        nativePNTSquarePrefixSearchLower (base j) =
          2 ^ (E + j * S) := by
      rw [nativePNTSquarePrefixSearchLower_eq, hbaseOne j]
      rw [nativePNTSquarePrefix_pow_sq]
      rw [hExp]
    rw [hSearch] at hm
    exact hm
  have htUpper : ∀ j : ℕ, t j ≤ 2 ^ (E + j * S + W) := by
    intro j
    have hm := (Finset.mem_Icc.mp (hspec j).1).2
    have hu := nativePNTSquarePrefixSearchUpper_add_one (base j) K
    have hUle :
        t j ≤ nativePNTSquarePrefixSearchUpper (base j) K + 1 :=
      hm.trans (Nat.le_succ _)
    have hExp : E + j * S + W = 2 * (E0 + j * L + K) := by
      dsimp [E, S, W]
      ring
    have hRight :
        ((base j + 1) * 2 ^ K) ^ 2 = 2 ^ (E + j * S + W) := by
      rw [hbaseOne j, ← pow_add]
      rw [nativePNTSquarePrefix_pow_sq]
      rw [hExp]
    rw [hu, hRight] at hUle
    exact hUle
  refine ⟨S, W, E, t, hSpos, hgap, hSupper, htLower, htUpper, ?_⟩
  intro j q hq
  exact (hspec j).2.2 q hq

/-! ## Generic packing arithmetic -/

private lemma nativePNTSquarePrefix_shell_step_lt
    (E S W i : ℕ) (hgap : W + 2 ≤ S) :
    E + i * S + W + 1 < E + (i + 1) * S := by
  have hstep : W + 1 < S := by omega
  nlinarith [Nat.zero_le i]

private lemma nativePNTSquarePrefix_four_mul_sum_le
    {a b q : ℕ} (ha : 8 * a ≤ q) (hb : 8 * b ≤ q) :
    4 * (a + b) ≤ q := by
  omega

private lemma nativePNTSquarePrefix_quarter_cast_lower
    (q : ℕ) (hq : 8 ≤ q) :
    (q : ℝ) / 8 ≤ ((q / 4 : ℕ) : ℝ) := by
  have hdec4 : 4 * (q / 4) + q % 4 = q := Nat.div_add_mod q 4
  have hmod4 : q % 4 < 4 := Nat.mod_lt q (by norm_num)
  have hnat : q ≤ 8 * (q / 4) := by omega
  have hcast : (q : ℝ) ≤ 8 * ((q / 4 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  nlinarith

private lemma nativePNTSquarePrefix_quadratic_product_lower
    (eps logTwo L q J q4 : ℝ)
    (heps : 0 ≤ eps) (hlogTwo : 0 ≤ logTwo)
    (hL : 0 < L) (hq : 0 ≤ q) (hJnonneg : 0 ≤ J)
    (hJ : q / (16 * L) ≤ J) (hq4 : q / 8 ≤ q4) :
    eps * logTwo / (4096 * L) * q ^ 2 ≤
      J * ((eps / 32) * (q4 * logTwo)) := by
  have heps32 : 0 ≤ eps / 32 := div_nonneg heps (by norm_num)
  have hq8 : 0 ≤ q / 8 := div_nonneg hq (by norm_num)
  have hterm0 : 0 ≤ (eps / 32) * ((q / 8) * logTwo) :=
    mul_nonneg heps32 (mul_nonneg hq8 hlogTwo)
  have hterm :
      (eps / 32) * ((q / 8) * logTwo) ≤
        (eps / 32) * (q4 * logTwo) := by
    have hmul : (q / 8) * logTwo ≤ q4 * logTwo :=
      mul_le_mul_of_nonneg_right hq4 hlogTwo
    exact mul_le_mul_of_nonneg_left hmul heps32
  have hleft :
      (q / (16 * L)) * ((eps / 32) * ((q / 8) * logTwo)) ≤
        J * ((eps / 32) * ((q / 8) * logTwo)) :=
    mul_le_mul_of_nonneg_right hJ hterm0
  have hright :
      J * ((eps / 32) * ((q / 8) * logTwo)) ≤
        J * ((eps / 32) * (q4 * logTwo)) :=
    mul_le_mul_of_nonneg_left hterm hJnonneg
  have hprod := hleft.trans hright
  have halg :
      eps * logTwo / (4096 * L) * q ^ 2 =
        (q / (16 * L)) * ((eps / 32) * ((q / 8) * logTwo)) := by
    field_simp [ne_of_gt hL]
    ring
  rw [halg]
  exact hprod

private lemma nativePNTSquarePrefix_log_upper_from_binary
    {N q : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hNpow : N < 2 ^ (q + 1))
    (hlog2le : Real.log (2 : ℝ) ≤ 1) :
    Real.log (N : ℝ) ≤ 2 * (q : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hcast : (N : ℝ) ≤ ((2 ^ (q + 1) : ℕ) : ℝ) := by
    exact_mod_cast hNpow.le
  have hlogle := Real.log_le_log hNpos hcast
  have hlogpow : Real.log ((2 ^ (q + 1) : ℕ) : ℝ) =
      ((q + 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hlogpow] at hlogle
  have hqreal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hmul :
      ((q + 1 : ℕ) : ℝ) * Real.log 2 ≤ ((q + 1 : ℕ) : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left hlog2le (by positivity)
  have hqsum : ((q + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by
    push_cast
    linarith
  calc
    Real.log (N : ℝ) ≤ ((q + 1 : ℕ) : ℝ) * Real.log 2 := hlogle
    _ ≤ ((q + 1 : ℕ) : ℝ) * 1 := hmul
    _ = ((q + 1 : ℕ) : ℝ) := by ring
    _ ≤ 2 * (q : ℝ) := hqsum

/-! ## Quadratic density from the square-prefix selector -/

/-- Generic packing theorem for any separated selector with the calibrated
square-prefix exponent spacing. -/
theorem nativeLambdaTwoGoodRecipMass_eventually_quadratic_of_squarePrefix_selector
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (S W E : ℕ) (t : ℕ → ℕ)
    (hSpos : 0 < S) (hgap : W + 2 ≤ S)
    (hSupper : (S : ℝ) ≤ 200 / eps)
    (htLower : ∀ j : ℕ, 2 ^ (E + j * S) ≤ t j)
    (htUpper : ∀ j : ℕ, t j ≤ 2 ^ (E + j * S + W))
    (htGood : ∀ j : ℕ,
      ∀ q ∈ Finset.Icc (t j)
        (t j + nativePNTGoodForwardRadius (t j) eps),
        |nativePNTError q| ≤ eps * (q : ℝ)) :
    ∃ c : ℝ, eps ^ 2 / 6600000 ≤ c ∧ c ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop,
        c * (Real.log (N : ℝ)) ^ 2 ≤
          nativeLambdaTwoGoodRecipMass N eps := by
  classical
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  let C : ℝ := 2 * (Real.log 4 + 2) + 172
  obtain ⟨M_B : ℕ, hM_Bnat⟩ := exists_nat_gt (32 / eps)
  have hM_B : 32 / eps < (M_B : ℝ) := by exact_mod_cast hM_Bnat
  obtain ⟨M_log : ℕ, hM_lognat⟩ :=
    exists_nat_gt (64 * C / (eps * Real.log 2))
  have hM_log : 64 * C / (eps * Real.log 2) < (M_log : ℝ) := by
    exact_mod_cast hM_lognat
  let c : ℝ := eps * Real.log 2 / (16384 * (S : ℝ))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hden1 : (1 : ℝ) ≤ 16384 * (S : ℝ) := by
    have hS1 : (1 : ℝ) ≤ (S : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.2 hSpos.ne')
    nlinarith
  have hnum1 : eps * Real.log 2 ≤ 1 := by
    have hnonneg : 0 ≤ Real.log (2 : ℝ) := hlog2pos.le
    have h := mul_le_mul heps1 hlog2le hnonneg
      (show (0 : ℝ) ≤ 1 by norm_num)
    simpa using h
  have hc1 : c ≤ 1 := by
    dsimp [c]
    have hdenpos : (0 : ℝ) < 16384 * (S : ℝ) :=
      lt_of_lt_of_le (by norm_num) hden1
    rw [div_le_one hdenpos]
    exact hnum1.trans hden1
  have hepsS : eps * (S : ℝ) ≤ 200 := by
    have h := (le_div_iff₀ heps).mp hSupper
    simpa [mul_comm] using h
  have hepsSqS : eps ^ 2 * (S : ℝ) ≤ 200 * eps := by
    have h := mul_le_mul_of_nonneg_left hepsS heps.le
    nlinarith
  have hlogscaled : eps / 2 ≤ eps * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_left
      nativePNTSquarePrefix_log_two_ge_half heps.le
    nlinarith
  have hconst : (16384 : ℝ) * 200 ≤ 6600000 / 2 := by norm_num
  have hleft :
      16384 * (eps ^ 2 * (S : ℝ)) ≤ 16384 * (200 * eps) :=
    mul_le_mul_of_nonneg_left hepsSqS (by norm_num)
  have hmid : 16384 * (200 * eps) ≤ 6600000 * (eps / 2) := by
    have h := mul_le_mul_of_nonneg_right hconst heps.le
    nlinarith
  have hright : 6600000 * (eps / 2) ≤ 6600000 * (eps * Real.log 2) :=
    mul_le_mul_of_nonneg_left hlogscaled (by norm_num)
  have hcross :
      16384 * (eps ^ 2 * (S : ℝ)) ≤
        6600000 * (eps * Real.log 2) :=
    hleft.trans (hmid.trans hright)
  have hcrate : eps ^ 2 / 6600000 ≤ c := by
    dsimp [c]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 6600000)
      (by positivity : (0 : ℝ) < 16384 * (S : ℝ))]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcross
  refine ⟨c, hcrate, hc1, ?_⟩
  have hqTop : Tendsto (fun N : ℕ => Nat.log 2 N) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop (2 ^ b)] with N hN
    exact Nat.le_log_of_pow_le Nat.one_lt_two hN
  let Q : ℕ := max
    (8 * (E + W + 2))
    (max (16 * S) (max 8 (max (4 * M_B) (4 * M_log))))
  have hqLarge : ∀ᶠ N : ℕ in atTop, Q ≤ Nat.log 2 N :=
    hqTop.eventually_ge_atTop Q
  filter_upwards [eventually_ge_atTop 1, hqLarge] with N hN1 hqQ
  let q : ℕ := Nat.log 2 N
  let J : ℕ := q / (8 * S)
  let M : ℕ := 2 ^ (q / 4)
  have hNne : N ≠ 0 := by omega
  have hqE : 8 * (E + W + 2) ≤ q := by
    dsimp [Q, q] at hqQ ⊢
    exact le_trans (le_max_left _ _) hqQ
  have hqJS : 16 * S ≤ q := by
    dsimp [Q, q] at hqQ ⊢
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hqQ)
  have hq8 : 8 ≤ q := by
    dsimp [Q, q] at hqQ ⊢
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) hqQ))
  have hqMB : 4 * M_B ≤ q := by
    dsimp [Q, q] at hqQ ⊢
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hqQ)))
  have hqMlog : 4 * M_log ≤ q := by
    dsimp [Q, q] at hqQ ⊢
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hqQ)))
  have hq4two : 2 ≤ q / 4 := by omega
  have hMBq : M_B ≤ q / 4 := by
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
      (by simpa [Nat.mul_comm] using hqMB)
  have hMlogq : M_log ≤ q / 4 := by
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
      (by simpa [Nat.mul_comm] using hqMlog)
  have hMfour : 4 ≤ M := by
    dsimp [M]
    have h := (Nat.pow_le_pow_iff_right Nat.one_lt_two).2 hq4two
    norm_num at h ⊢
    exact h
  have hpowq : 2 ^ q ≤ N := by
    dsimp [q]
    exact Nat.pow_log_le_self 2 hNne
  have htOne : ∀ j < J, 1 ≤ t j := by
    intro j _hj
    have hpowpos : 0 < 2 ^ (E + j * S) := by positivity
    have hlow := htLower j
    omega
  have hsep : ∀ i j, i < j → j < J →
      t i + nativePNTGoodForwardRadius (t i) eps < t j := by
    intro i j hij _hjJ
    have hrad := nativePNTGoodForwardRadius_le_self (t i) eps heps.le heps1
    have hui := htUpper i
    have hlj := htLower j
    have hexp : E + i * S + W + 1 < E + j * S := by
      have hji : i + 1 ≤ j := by omega
      have hmul : (i + 1) * S ≤ j * S := Nat.mul_le_mul_right S hji
      have hstep : E + i * S + W + 1 < E + (i + 1) * S :=
        nativePNTSquarePrefix_shell_step_lt E S W i hgap
      exact hstep.trans_le (Nat.add_le_add_left hmul E)
    have hp : 2 ^ (E + i * S + W + 1) < 2 ^ (E + j * S) :=
      Nat.pow_lt_pow_right Nat.one_lt_two hexp
    have htwo : 2 * t i ≤ 2 ^ (E + i * S + W + 1) := by
      calc
        2 * t i ≤ 2 * 2 ^ (E + i * S + W) := Nat.mul_le_mul_left 2 hui
        _ = 2 ^ (E + i * S + W + 1) := by rw [pow_succ]; ring
    have hsum : t i + nativePNTGoodForwardRadius (t i) eps ≤ 2 * t i := by omega
    exact hsum.trans_lt (htwo.trans_lt (hp.trans_le hlj))
  have hJmul : J * (8 * S) ≤ q := by
    dsimp [J]
    exact Nat.div_mul_le_self q (8 * S)
  have hLocalQuot : ∀ j < J,
      M ≤ N / (t j + nativePNTGoodForwardRadius (t j) eps + 1) := by
    intro j hjJ
    have hjstep : (j + 1) * (8 * S) ≤ q := by
      have hj1 : j + 1 ≤ J := by omega
      exact (Nat.mul_le_mul_right (8 * S) hj1).trans hJmul
    have hexpQ : E + j * S + W + 2 ≤ q / 4 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
      have hEpart : 8 * (E + W + 2) ≤ q := hqE
      have hjpart : 8 * (j * S) ≤ q := by
        calc
          8 * (j * S) ≤ 8 * ((j + 1) * S) :=
            Nat.mul_le_mul_left 8 (Nat.mul_le_mul_right S (Nat.le_succ j))
          _ = (j + 1) * (8 * S) := by ring
          _ ≤ q := hjstep
      have hsum0 : 4 * ((E + W + 2) + j * S) ≤ q :=
        nativePNTSquarePrefix_four_mul_sum_le hEpart hjpart
      have hsum : (E + j * S + W + 2) * 4 ≤ q := by
        have hnorm :
            (E + j * S + W + 2) * 4 = 4 * ((E + W + 2) + j * S) := by ring
        rw [hnorm]
        exact hsum0
      exact hsum
    have hrad := nativePNTGoodForwardRadius_le_self (t j) eps heps.le heps1
    have htj1 : 1 ≤ t j := htOne j hjJ
    have hud : t j + nativePNTGoodForwardRadius (t j) eps + 1 ≤ 4 * t j := by
      omega
    have hut := htUpper j
    have hdPow :
        t j + nativePNTGoodForwardRadius (t j) eps + 1 ≤
          2 ^ (E + j * S + W + 2) := by
      calc
        t j + nativePNTGoodForwardRadius (t j) eps + 1 ≤ 4 * t j := hud
        _ ≤ 4 * 2 ^ (E + j * S + W) := Nat.mul_le_mul_left 4 hut
        _ = 2 ^ (E + j * S + W + 2) := by
          calc
            4 * 2 ^ (E + j * S + W) =
                2 ^ 2 * 2 ^ (E + j * S + W) := by norm_num
            _ = 2 ^ (2 + (E + j * S + W)) := by rw [← pow_add]
            _ = 2 ^ (E + j * S + W + 2) := by
              congr 1
              omega
    have hsumExp : E + j * S + W + 2 + q / 4 ≤ q := by
      have hqq : q / 4 + q / 4 ≤ q := by omega
      omega
    have hpowExp :
        2 ^ (E + j * S + W + 2 + q / 4) ≤ 2 ^ q :=
      (Nat.pow_le_pow_iff_right Nat.one_lt_two).2 hsumExp
    have hdM :
        (t j + nativePNTGoodForwardRadius (t j) eps + 1) * M ≤ N := by
      calc
        (t j + nativePNTGoodForwardRadius (t j) eps + 1) * M ≤
            2 ^ (E + j * S + W + 2) * 2 ^ (q / 4) :=
          Nat.mul_le_mul hdPow le_rfl
        _ = 2 ^ (E + j * S + W + 2 + q / 4) := by rw [← pow_add]
        _ ≤ 2 ^ q := hpowExp
        _ ≤ N := hpowq
    have hdpos : 0 < t j + nativePNTGoodForwardRadius (t j) eps + 1 := by omega
    exact (Nat.le_div_iff_mul_le hdpos).2 (by
      simpa [Nat.mul_comm] using hdM)
  have hLocalB : ∀ j < J, M ≤ N / t j := by
    intro j hjJ
    have hd := hLocalQuot j hjJ
    have hden : t j ≤ t j + nativePNTGoodForwardRadius (t j) eps + 1 := by omega
    have htj0 : t j ≠ 0 := Nat.one_le_iff_ne_zero.mp (htOne j hjJ)
    have htjpos : 0 < t j := Nat.pos_of_ne_zero htj0
    exact hd.trans (Nat.div_le_div_left hden htjpos)
  have hA : ∀ j < J,
      3 ≤ N / (t j + nativePNTGoodForwardRadius (t j) eps + 1) := by
    intro j hj
    exact (show 3 ≤ 4 by norm_num).trans (hMfour.trans (hLocalQuot j hj))
  have hMBpow : M_B ≤ M := by
    have hself : M_B ≤ 2 ^ M_B := (Nat.lt_pow_self Nat.one_lt_two).le
    have hp : 2 ^ M_B ≤ 2 ^ (q / 4) :=
      (Nat.pow_le_pow_iff_right Nat.one_lt_two).2 hMBq
    exact hself.trans hp
  have hBbase : 32 ≤ eps * (M : ℝ) := by
    have hMBreal : (M_B : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMBpow
    have h32MB : 32 < eps * (M_B : ℝ) := by
      have h := (div_lt_iff₀ heps).mp hM_B
      simpa [mul_comm] using h
    have hmul := mul_le_mul_of_nonneg_left hMBreal heps.le
    linarith
  have hB : ∀ j < J, 32 ≤ eps * ((N / t j : ℕ) : ℝ) := by
    intro j hj
    have hcast : (M : ℝ) ≤ ((N / t j : ℕ) : ℝ) := by
      exact_mod_cast hLocalB j hj
    exact hBbase.trans (mul_le_mul_of_nonneg_left hcast heps.le)
  have hMlogpow : M_log ≤ q / 4 := hMlogq
  have hlogM :
      ((q / 4 : ℕ) : ℝ) * Real.log 2 = Real.log (M : ℝ) := by
    dsimp [M]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hlogBase : 64 * C ≤ eps * Real.log (M : ℝ) := by
    have hdenpos : 0 < eps * Real.log 2 := mul_pos heps hlog2pos
    have hCML : 64 * C < (M_log : ℝ) * (eps * Real.log 2) := by
      have h := (div_lt_iff₀ hdenpos).mp hM_log
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hMLq : (M_log : ℝ) ≤ ((q / 4 : ℕ) : ℝ) := by exact_mod_cast hMlogpow
    have hmul := mul_le_mul_of_nonneg_right hMLq hdenpos.le
    rw [← hlogM]
    nlinarith
  have hlog : ∀ j < J,
      64 * (2 * (Real.log 4 + 2) + 172) ≤
        eps * Real.log ((N / t j : ℕ) : ℝ) := by
    intro j hj
    have hBpos : 0 < M := by positivity
    have hcast := hLocalB j hj
    have hlogle : Real.log (M : ℝ) ≤ Real.log ((N / t j : ℕ) : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast hBpos
      · exact_mod_cast hcast
    have hmul := mul_le_mul_of_nonneg_left hlogle heps.le
    dsimp [C] at hlogBase ⊢
    exact hlogBase.trans hmul
  have hpacked := nativeLambdaTwoGoodRecipMass_packed_good_radii_lower
    N J eps t heps heps1 htOne (fun j _hj => htGood j) hsep hA hB hlog
  have hterm : ∀ j < J,
      (eps / 32) * (((q / 4 : ℕ) : ℝ) * Real.log 2) ≤
        (eps / 32) * Real.log ((N / t j : ℕ) : ℝ) := by
    intro j hj
    have hlogle : Real.log (M : ℝ) ≤ Real.log ((N / t j : ℕ) : ℝ) := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast hLocalB j hj
    rw [hlogM]
    exact mul_le_mul_of_nonneg_left hlogle (by positivity)
  have hsumTerm :
      ((J : ℕ) : ℝ) *
          ((eps / 32) * (((q / 4 : ℕ) : ℝ) * Real.log 2)) ≤
        ∑ j ∈ Finset.range J,
          (eps / 32) * Real.log ((N / t j : ℕ) : ℝ) := by
    have hcard := Finset.card_nsmul_le_sum (Finset.range J)
      (fun j => (eps / 32) * Real.log ((N / t j : ℕ) : ℝ))
      ((eps / 32) * (((q / 4 : ℕ) : ℝ) * Real.log 2))
      (by
        intro j hj
        exact hterm j (Finset.mem_range.mp hj))
    rw [Finset.card_range, nsmul_eq_mul] at hcard
    exact hcard
  have hdpos : 0 < 8 * S := by positivity
  have hqDecomp : 8 * S * J + q % (8 * S) = q := by
    dsimp [J]
    exact Nat.div_add_mod q (8 * S)
  have hmod : q % (8 * S) < 8 * S := Nat.mod_lt q hdpos
  have hJtwo : 2 ≤ J := by
    dsimp [J]
    apply (Nat.le_div_iff_mul_le hdpos).2
    have hnorm : 2 * (8 * S) = 16 * S := by ring
    rw [hnorm]
    exact hqJS
  have hJone : 1 ≤ J := by omega
  have hdJ : 8 * S ≤ (8 * S) * J := by
    simpa using Nat.mul_le_mul_left (8 * S) hJone
  have hremJ : q % (8 * S) ≤ (8 * S) * J :=
    (Nat.le_of_lt hmod).trans hdJ
  have hJlowerNat : q ≤ 16 * S * J := by
    calc
      q = (8 * S) * J + q % (8 * S) := hqDecomp.symm
      _ ≤ (8 * S) * J + (8 * S) * J := Nat.add_le_add_left hremJ _
      _ = 16 * S * J := by ring
  have hJlower : (q : ℝ) ≤ 16 * (S : ℝ) * (J : ℝ) := by
    exact_mod_cast hJlowerNat
  have hqdiv4 : (q : ℝ) / 8 ≤ ((q / 4 : ℕ) : ℝ) :=
    nativePNTSquarePrefix_quarter_cast_lower q hq8
  have hmassQ :
      eps * Real.log 2 / (4096 * (S : ℝ)) * (q : ℝ) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N eps := by
    have hJreal : (q : ℝ) / (16 * (S : ℝ)) ≤ (J : ℝ) := by
      have hden : (0 : ℝ) < 16 * (S : ℝ) := by positivity
      apply (div_le_iff₀ hden).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using hJlower
    have hprod :
        eps * Real.log 2 / (4096 * (S : ℝ)) * (q : ℝ) ^ 2 ≤
          ((J : ℕ) : ℝ) *
            ((eps / 32) * (((q / 4 : ℕ) : ℝ) * Real.log 2)) := by
      exact nativePNTSquarePrefix_quadratic_product_lower
        eps (Real.log 2) (S : ℝ) (q : ℝ) (J : ℝ) ((q / 4 : ℕ) : ℝ)
        heps.le hlog2pos.le (by exact_mod_cast hSpos) (by positivity)
        (by positivity) hJreal hqdiv4
    calc
      eps * Real.log 2 / (4096 * (S : ℝ)) * (q : ℝ) ^ 2 ≤
          ((J : ℕ) : ℝ) *
            ((eps / 32) * (((q / 4 : ℕ) : ℝ) * Real.log 2)) := hprod
      _ ≤ ∑ j ∈ Finset.range J,
          (eps / 32) * Real.log ((N / t j : ℕ) : ℝ) := hsumTerm
      _ ≤ nativeLambdaTwoGoodRecipMass N eps := hpacked
  have hNpow : N < 2 ^ (q + 1) := by
    dsimp [q]
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self Nat.one_lt_two N
  have hlogNnonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN1)
  have hq1nat : 1 ≤ q := by omega
  have hlogNupper : Real.log (N : ℝ) ≤ 2 * (q : ℝ) :=
    nativePNTSquarePrefix_log_upper_from_binary hN1 hq1nat hNpow hlog2le
  have hsq : (Real.log (N : ℝ)) ^ 2 ≤ 4 * (q : ℝ) ^ 2 := by
    nlinarith only [hlogNnonneg, hlogNupper,
      sq_nonneg (Real.log (N : ℝ) - 2 * (q : ℝ))]
  have hcSq : c * (Real.log (N : ℝ)) ^ 2 ≤
      eps * Real.log 2 / (4096 * (S : ℝ)) * (q : ℝ) ^ 2 := by
    dsimp [c]
    have hcoef : 0 ≤ eps * Real.log 2 / (16384 * (S : ℝ)) := hc.le
    calc
      eps * Real.log 2 / (16384 * (S : ℝ)) * (Real.log (N : ℝ)) ^ 2 ≤
          eps * Real.log 2 / (16384 * (S : ℝ)) * (4 * (q : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hcoef
      _ = eps * Real.log 2 / (4096 * (S : ℝ)) * (q : ℝ) ^ 2 := by ring
  exact hcSq.trans hmassQ

/-- **Square-prefix-native quadratic good-mass density.** -/
theorem nativeLambdaTwoGoodRecipMass_eventually_quadratic_squarePrefix_with_rate
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ c : ℝ, eps ^ 2 / 6600000 ≤ c ∧ c ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop,
        c * (Real.log (N : ℝ)) ^ 2 ≤
          nativeLambdaTwoGoodRecipMass N eps := by
  rcases nativePNT_exists_good_squarePrefix_power_shell_selector
      eps heps heps1 with
    ⟨S, W, E, t, hSpos, hgap, hSupper, htLower, htUpper, htGood⟩
  exact nativeLambdaTwoGoodRecipMass_eventually_quadratic_of_squarePrefix_selector
    eps heps heps1 S W E t hSpos hgap hSupper htLower htUpper htGood

/-- Explicit public rate used by the square-prefix cubic contraction. -/
theorem nativeLambdaTwoGoodRecipMass_eventually_quadratic_squarePrefix_rate
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      (eps ^ 2 / 6600000) * (Real.log (N : ℝ)) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N eps := by
  rcases nativeLambdaTwoGoodRecipMass_eventually_quadratic_squarePrefix_with_rate
      eps heps heps1 with ⟨c, hcrate, _hc1, hgood⟩
  filter_upwards [hgood] with N hN
  exact (mul_le_mul_of_nonneg_right hcrate (sq_nonneg _)).trans hN

/-! ## Square-prefix cubic contraction and explicit iteration budget -/

/-- Cubic constant supplied by the square-prefix good-mass coefficient. -/
def nativePNTSquarePrefixCubicConstant : ℝ := 1 / 1140480000

/-- One affine-envelope contraction step using only the square-prefix density
proved above. -/
theorem nativePNTSquarePrefixHasAffineEnvelope_cubic_step
    (alpha : ℝ) (halpha : 0 < alpha) (halpha6 : alpha ≤ 6)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
      (alpha - nativePNTSquarePrefixCubicConstant * alpha ^ 3) := by
  let beta : ℝ := alpha / 6
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hbeta0 : 0 ≤ beta := hbeta.le
  have hbeta1 : beta ≤ 1 := by dsimp [beta]; linarith
  have hba : beta < alpha := by dsimp [beta]; nlinarith
  let c : ℝ := beta ^ 2 / 6600000
  have hc : 0 < c := by dsimp [c]; positivity
  have hsq : beta ^ 2 ≤ 1 := by
    have hprod : 0 ≤ beta * (1 - beta) :=
      mul_nonneg hbeta0 (sub_nonneg.mpr hbeta1)
    nlinarith
  have hc1 : c ≤ 1 := by dsimp [c]; nlinarith
  have hgood : ∀ᶠ N : ℕ in atTop,
      c * (Real.log (N : ℝ)) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N beta := by
    simpa [c] using
      nativeLambdaTwoGoodRecipMass_eventually_quadratic_squarePrefix_rate
        beta hbeta hbeta1
  have himp := nativePNTHasAffineEnvelope_improve_of_goodMass
    alpha beta c halpha hbeta0 hba hc hc1 hgood henv
  have hcoef :
      alpha - (alpha - beta) * c / 4 =
        alpha - nativePNTSquarePrefixCubicConstant * alpha ^ 3 := by
    dsimp [beta, c, nativePNTSquarePrefixCubicConstant]
    ring
  rw [hcoef] at himp
  exact himp

private theorem nativePNTSquarePrefix_cubic_step_pos
    (alpha : ℝ) (halpha : 0 < alpha) (halpha6 : alpha ≤ 6) :
    0 < alpha - nativePNTSquarePrefixCubicConstant * alpha ^ 3 := by
  have hsq : alpha ^ 2 ≤ (6 : ℝ) ^ 2 :=
    pow_le_pow_left₀ halpha.le halpha6 2
  have hC0 : 0 ≤ nativePNTSquarePrefixCubicConstant := by
    norm_num [nativePNTSquarePrefixCubicConstant]
  have hmul :
      nativePNTSquarePrefixCubicConstant * alpha ^ 2 ≤
        nativePNTSquarePrefixCubicConstant * (6 : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hC0
  have hC36 : nativePNTSquarePrefixCubicConstant * (6 : ℝ) ^ 2 < 1 := by
    norm_num [nativePNTSquarePrefixCubicConstant]
  have hfactor : 0 < 1 - nativePNTSquarePrefixCubicConstant * alpha ^ 2 := by
    linarith
  have hrewrite :
      alpha - nativePNTSquarePrefixCubicConstant * alpha ^ 3 =
        alpha * (1 - nativePNTSquarePrefixCubicConstant * alpha ^ 2) := by ring
  rw [hrewrite]
  exact mul_pos halpha hfactor

/-- Slope sequence driven entirely by the square-prefix contraction step. -/
def nativePNTSquarePrefixCubicSlope : ℕ → ℝ
  | 0 => 6
  | Nat.succ n =>
      nativePNTSquarePrefixCubicSlope n -
        nativePNTSquarePrefixCubicConstant *
          (nativePNTSquarePrefixCubicSlope n) ^ 3

@[simp] theorem nativePNTSquarePrefixCubicSlope_zero :
    nativePNTSquarePrefixCubicSlope 0 = 6 := rfl

@[simp] theorem nativePNTSquarePrefixCubicSlope_succ (n : ℕ) :
    nativePNTSquarePrefixCubicSlope (n + 1) =
      nativePNTSquarePrefixCubicSlope n -
        nativePNTSquarePrefixCubicConstant *
          (nativePNTSquarePrefixCubicSlope n) ^ 3 := rfl

/-- Every square-prefix slope is positive, at most six, and realized by an
affine error envelope. -/
theorem nativePNTSquarePrefixCubicSlope_spec :
    ∀ n : ℕ,
      0 < nativePNTSquarePrefixCubicSlope n ∧
      nativePNTSquarePrefixCubicSlope n ≤ 6 ∧
      nativePNTHasAffineEnvelope (nativePNTSquarePrefixCubicSlope n) := by
  intro n
  induction n with
  | zero => exact ⟨by norm_num, le_rfl, nativePNTHasAffineEnvelope_six⟩
  | succ n ih =>
      rcases ih with ⟨hpos, hle6, henv⟩
      have hnextpos := nativePNTSquarePrefix_cubic_step_pos
        (nativePNTSquarePrefixCubicSlope n) hpos hle6
      have hnextenv := nativePNTSquarePrefixHasAffineEnvelope_cubic_step
        (nativePNTSquarePrefixCubicSlope n) hpos hle6 henv
      have hdrop :
          0 ≤ nativePNTSquarePrefixCubicConstant *
            (nativePNTSquarePrefixCubicSlope n) ^ 3 :=
        mul_nonneg (by norm_num [nativePNTSquarePrefixCubicConstant])
          (pow_nonneg hpos.le 3)
      have hnextle :
          nativePNTSquarePrefixCubicSlope (n + 1) ≤
            nativePNTSquarePrefixCubicSlope n := by
        rw [nativePNTSquarePrefixCubicSlope_succ]
        exact sub_le_self _ hdrop
      exact ⟨by simpa using hnextpos, hnextle.trans hle6,
        by simpa using hnextenv⟩

/-- The square-prefix slope iteration uses the same abstract cubic theorem. -/
theorem nativePNTSquarePrefixCubicSlope_tendsto_zero :
    Tendsto nativePNTSquarePrefixCubicSlope atTop (𝓝 0) := by
  refine tendsto_zero_of_cubic_recurrence
    nativePNTSquarePrefixCubicSlope nativePNTSquarePrefixCubicConstant ?_ ?_ ?_
  · norm_num [nativePNTSquarePrefixCubicConstant]
  · intro n
    exact (nativePNTSquarePrefixCubicSlope_spec n).1.le
  · intro n
    rw [nativePNTSquarePrefixCubicSlope_succ]

/-- Explicit finite-step rate for the square-prefix contraction. -/
theorem nativePNTSquarePrefixCubicSlope_rate (n : ℕ) :
    nativePNTSquarePrefixCubicConstant * (n : ℝ) *
        (nativePNTSquarePrefixCubicSlope n) ^ 3 ≤ 6 := by
  have hC : 0 < nativePNTSquarePrefixCubicConstant := by
    norm_num [nativePNTSquarePrefixCubicConstant]
  have hnonneg : ∀ m, 0 ≤ nativePNTSquarePrefixCubicSlope m :=
    fun m => (nativePNTSquarePrefixCubicSlope_spec m).1.le
  have hrec : ∀ m,
      nativePNTSquarePrefixCubicSlope (m + 1) ≤
        nativePNTSquarePrefixCubicSlope m -
          nativePNTSquarePrefixCubicConstant *
            (nativePNTSquarePrefixCubicSlope m) ^ 3 := by
    intro m
    rw [nativePNTSquarePrefixCubicSlope_succ]
  simpa using
    (cubic_recurrence_rate nativePNTSquarePrefixCubicSlope
      nativePNTSquarePrefixCubicConstant hC hnonneg hrec n)

/-- Concrete iteration budget: any `n` satisfying this inequality realizes an
affine slope at most `eta`. -/
theorem nativePNTSquarePrefixHasAffineEnvelope_of_cubic_budget
    (eta : ℝ) (heta : 0 < eta) (n : ℕ)
    (hbudget :
      6 < nativePNTSquarePrefixCubicConstant * (n : ℝ) * eta ^ 3) :
    nativePNTHasAffineEnvelope eta := by
  have hspec := nativePNTSquarePrefixCubicSlope_spec n
  have hslopeEta : nativePNTSquarePrefixCubicSlope n ≤ eta := by
    by_contra hnot
    have hetaSlope : eta < nativePNTSquarePrefixCubicSlope n := lt_of_not_ge hnot
    have hcube : eta ^ 3 ≤ (nativePNTSquarePrefixCubicSlope n) ^ 3 :=
      pow_le_pow_left₀ heta.le hetaSlope.le 3
    have hcoef0 :
        0 ≤ nativePNTSquarePrefixCubicConstant * (n : ℝ) :=
      mul_nonneg (by norm_num [nativePNTSquarePrefixCubicConstant]) (by positivity)
    have hmul :
        nativePNTSquarePrefixCubicConstant * (n : ℝ) * eta ^ 3 ≤
          nativePNTSquarePrefixCubicConstant * (n : ℝ) *
            (nativePNTSquarePrefixCubicSlope n) ^ 3 :=
      mul_le_mul_of_nonneg_left hcube hcoef0
    have hrate := nativePNTSquarePrefixCubicSlope_rate n
    linarith
  exact nativePNTHasAffineEnvelope_mono hslopeEta hspec.2.2

end RHLean.Analysis
