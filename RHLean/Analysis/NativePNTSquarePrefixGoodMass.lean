import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixMobiusError

/-!
# Square-prefix good-fibre supply for the native PNT contraction

Search intervals are unions of complete square-prefix blocks

`(X_A, X_B]`,  where `X_n = (n+1)^2 - 1`.

The binary coordinate appears only in the index clock.  For positive depth
`K`, multiplying `A+1` by `2^K` before taking the square endpoint gives

`X_A + 1 = (A+1)^2`,

`X_B + 1 = ((A+1) 2^K)^2`.

Thus the reciprocal search depth is `2 K log 2`.  No new analytic estimate is
introduced; the proof uses the already-native finite reciprocal error mass and
the same local PNT2 persistence theorem as the green head.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators Topology

namespace RHLean.Analysis

/-! ## Exact square-prefix search geometry -/

/-- First integer after the `A`th complete square prefix. -/
def nativePNTSquarePrefixSearchLower (A : ℕ) : ℕ :=
  squarePrefixEndpoint A + 1

/-- Last square-prefix index after `K` prime-`2` index-clock extensions. -/
def nativePNTSquarePrefixScaleIndex (A K : ℕ) : ℕ :=
  (A + 1) * 2 ^ K - 1

/-- Right endpoint of the corresponding complete-square search span. -/
def nativePNTSquarePrefixSearchUpper (A K : ℕ) : ℕ :=
  squarePrefixEndpoint (nativePNTSquarePrefixScaleIndex A K)

@[simp] theorem nativePNTSquarePrefixSearchLower_eq (A : ℕ) :
    nativePNTSquarePrefixSearchLower A = (A + 1) ^ 2 := by
  exact squarePrefixEndpoint_add_one A

/-- The right endpoint also lands immediately before an exact square. -/
theorem nativePNTSquarePrefixSearchUpper_add_one
    (A K : ℕ) :
    nativePNTSquarePrefixSearchUpper A K + 1 =
      ((A + 1) * 2 ^ K) ^ 2 := by
  unfold nativePNTSquarePrefixSearchUpper nativePNTSquarePrefixScaleIndex
  rw [squarePrefixEndpoint_add_one]
  have hpos : 0 < (A + 1) * 2 ^ K := by positivity
  have hsub : ((A + 1) * 2 ^ K - 1) + 1 = (A + 1) * 2 ^ K := by omega
  rw [hsub]

/-- Positive index depth makes the complete-square search interval nonempty. -/
theorem nativePNTSquarePrefixSearchLower_le_upper
    (A K : ℕ) (hK : 1 ≤ K) :
    nativePNTSquarePrefixSearchLower A ≤
      nativePNTSquarePrefixSearchUpper A K := by
  rw [nativePNTSquarePrefixSearchLower_eq]
  have hu := nativePNTSquarePrefixSearchUpper_add_one A K
  have hbase : A + 1 < (A + 1) * 2 ^ K := by
    have hp2 : 2 ≤ 2 ^ K := by
      have hp : 2 ^ 1 ≤ 2 ^ K :=
        (Nat.pow_le_pow_iff_right Nat.one_lt_two).2 hK
      simpa using hp
    calc
      A + 1 = (A + 1) * 1 := by omega
      _ < (A + 1) * 2 ^ K :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hpow : (A + 1) ^ 2 < ((A + 1) * 2 ^ K) ^ 2 :=
    Nat.pow_lt_pow_left hbase (by norm_num)
  rw [← hu] at hpow
  omega

/-! ## Finite signed reciprocal mass on a square-prefix span -/

/-- Signed reciprocal error mass on an arbitrary positive integer interval. -/
def nativePNTSquarePrefixWeightedErrorIntervalMass (A B : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc A B,
    nativePNTError n / ((n : ℝ) * (n + 1 : ℝ))

private theorem nativePNTSquarePrefixWeightedErrorIntervalMass_eq_prefix_sub
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    nativePNTSquarePrefixWeightedErrorIntervalMass A B =
      nativePNTWeightedErrorMass B - nativePNTWeightedErrorMass (A - 1) := by
  let f : ℕ → ℝ := fun n =>
    nativePNTError n / ((n : ℝ) * (n + 1 : ℝ))
  have hsets :
      Finset.Icc 1 B = Finset.Icc 1 (A - 1) ∪ Finset.Icc A B := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdis : Disjoint (Finset.Icc 1 (A - 1)) (Finset.Icc A B) := by
    refine Finset.disjoint_left.mpr ?_
    intro n hn1 hn2
    rw [Finset.mem_Icc] at hn1 hn2
    omega
  unfold nativePNTSquarePrefixWeightedErrorIntervalMass nativePNTWeightedErrorMass
  change (∑ n ∈ Finset.Icc A B, f n) =
    (∑ n ∈ Finset.Icc 1 B, f n) - (∑ n ∈ Finset.Icc 1 (A - 1), f n)
  rw [hsets, Finset.sum_union hdis]
  ring

private theorem nativePNTSquarePrefixWeightedErrorIntervalMass_abs_le
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    |nativePNTSquarePrefixWeightedErrorIntervalMass A B| ≤
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) := by
  rw [nativePNTSquarePrefixWeightedErrorIntervalMass_eq_prefix_sub A B hA hAB]
  calc
    |nativePNTWeightedErrorMass B - nativePNTWeightedErrorMass (A - 1)| ≤
        |nativePNTWeightedErrorMass B| +
          |nativePNTWeightedErrorMass (A - 1)| := abs_sub _ _
    _ ≤ (2 * (Real.log 4 + 2) + Real.log 2 + 3) +
          (2 * (Real.log 4 + 2) + Real.log 2 + 3) :=
      add_le_add (nativePNTWeightedErrorMass_abs_le B)
        (nativePNTWeightedErrorMass_abs_le (A - 1))
    _ = 2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) := by ring

private theorem nativePNTSquarePrefixRecipSuccInterval_eq_harmonic_sub
    (A : ℕ) : ∀ B : ℕ, A ≤ B →
    (∑ n ∈ Finset.Icc A B, 1 / (((n + 1 : ℕ) : ℝ))) =
      (harmonic (B + 1) : ℝ) - (harmonic A : ℝ) := by
  intro B hAB
  induction B, hAB using Nat.le_induction with
  | base =>
      rw [Finset.Icc_self, Finset.sum_singleton, harmonic_succ]
      push_cast
      simp [div_eq_mul_inv]
  | succ B hAB ih =>
      rw [Finset.sum_Icc_succ_top (by omega : A ≤ B + 1), ih]
      rw [show B + 2 = (B + 1) + 1 by omega, harmonic_succ (B + 1)]
      push_cast
      ring

private theorem nativePNTSquarePrefixRecipSuccInterval_log_lower
    (A B : ℕ) (_hA : 1 ≤ A) (hAB : A ≤ B) :
    Real.log ((B + 2 : ℕ) : ℝ) - Real.log (A : ℝ) - 1 ≤
      ∑ n ∈ Finset.Icc A B, 1 / (((n + 1 : ℕ) : ℝ)) := by
  rw [nativePNTSquarePrefixRecipSuccInterval_eq_harmonic_sub A B hAB]
  have hlo : Real.log ((B + 2 : ℕ) : ℝ) ≤ (harmonic (B + 1) : ℝ) := by
    simpa [show B + 2 = (B + 1) + 1 by omega] using
      (log_add_one_le_harmonic (B + 1))
  have hup : (harmonic A : ℝ) ≤ 1 + Real.log (A : ℝ) := by
    simpa using (harmonic_le_one_add_log A)
  linarith

/-- A complete-square span has twice the reciprocal logarithmic depth of its
index-clock extension. -/
theorem nativePNTSquarePrefixRecipSuccSearch_lower
    (A K : ℕ) (hK : 1 ≤ K) :
    2 * (K : ℝ) * Real.log 2 - 1 ≤
      ∑ n ∈ Finset.Icc (nativePNTSquarePrefixSearchLower A)
        (nativePNTSquarePrefixSearchUpper A K),
        1 / (((n + 1 : ℕ) : ℝ)) := by
  let L := nativePNTSquarePrefixSearchLower A
  let U := nativePNTSquarePrefixSearchUpper A K
  have hL1 : 1 ≤ L := by
    dsimp [L]
    rw [nativePNTSquarePrefixSearchLower_eq]
    exact one_le_pow₀ (by omega : 1 ≤ A + 1)
  have hLU : L ≤ U := nativePNTSquarePrefixSearchLower_le_upper A K hK
  have hbase := nativePNTSquarePrefixRecipSuccInterval_log_lower L U hL1 hLU
  have hLcast : (L : ℝ) = ((A + 1 : ℕ) : ℝ) ^ 2 := by
    dsimp [L]
    rw [nativePNTSquarePrefixSearchLower_eq]
    norm_cast
  have hUone : U + 1 = ((A + 1) * 2 ^ K) ^ 2 := by
    dsimp [U]
    exact nativePNTSquarePrefixSearchUpper_add_one A K
  have hUonepos : (0 : ℝ) < ((U + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos U
  have hUtwo : U + 1 ≤ U + 2 := by omega
  have hlogmono :
      Real.log ((U + 1 : ℕ) : ℝ) ≤ Real.log ((U + 2 : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact hUonepos
    · exact_mod_cast hUtwo
  have hlogL : Real.log (L : ℝ) = 2 * Real.log ((A + 1 : ℕ) : ℝ) := by
    rw [hLcast, Real.log_pow]
    norm_num
  have hlogUone :
      Real.log ((U + 1 : ℕ) : ℝ) =
        2 * Real.log ((A + 1 : ℕ) : ℝ) +
          2 * (K : ℝ) * Real.log 2 := by
    rw [hUone, Nat.cast_pow, Real.log_pow]
    norm_num
    have hAreal : (0 : ℝ) < (A : ℝ) + 1 := by positivity
    have hpowreal : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
    rw [Real.log_mul (ne_of_gt hAreal) (ne_of_gt hpowreal), Real.log_pow]
    ring
  rw [hlogUone] at hlogmono
  have hdepthLog :
      2 * (K : ℝ) * Real.log 2 - 1 ≤
        Real.log ((U + 2 : ℕ) : ℝ) - Real.log (L : ℝ) - 1 := by
    rw [hlogL]
    linarith
  exact hdepthLog.trans hbase

private theorem nativePNTSquarePrefixWeightedErrorIntervalMass_lower_of_nonneg
    (A B : ℕ) (ε : ℝ) (hA : 1 ≤ A)
    (hsign : ∀ n ∈ Finset.Icc A B, 0 ≤ nativePNTError n)
    (haway : ∀ n ∈ Finset.Icc A B,
      ε * (n : ℝ) ≤ |nativePNTError n|) :
    ε * (∑ n ∈ Finset.Icc A B, 1 / (((n + 1 : ℕ) : ℝ))) ≤
      nativePNTSquarePrefixWeightedErrorIntervalMass A B := by
  unfold nativePNTSquarePrefixWeightedErrorIntervalMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1.trans' hA
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hspos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
  have herr := haway n hn
  rw [abs_of_nonneg (hsign n hn)] at herr
  push_cast at hspos ⊢
  calc
    ε * (1 / ((n : ℝ) + 1)) =
        (ε * (n : ℝ)) / ((n : ℝ) * ((n : ℝ) + 1)) := by
      field_simp [ne_of_gt hnpos]
    _ ≤ nativePNTError n / ((n : ℝ) * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right herr (mul_nonneg hnpos.le hspos.le)

private theorem nativePNTSquarePrefixWeightedErrorIntervalMass_neg_lower_of_nonpos
    (A B : ℕ) (ε : ℝ) (hA : 1 ≤ A)
    (hsign : ∀ n ∈ Finset.Icc A B, nativePNTError n ≤ 0)
    (haway : ∀ n ∈ Finset.Icc A B,
      ε * (n : ℝ) ≤ |nativePNTError n|) :
    ε * (∑ n ∈ Finset.Icc A B, 1 / (((n + 1 : ℕ) : ℝ))) ≤
      -nativePNTSquarePrefixWeightedErrorIntervalMass A B := by
  unfold nativePNTSquarePrefixWeightedErrorIntervalMass
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1.trans' hA
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hspos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
  have herr := haway n hn
  rw [abs_of_nonpos (hsign n hn)] at herr
  push_cast at hspos ⊢
  calc
    ε * (1 / ((n : ℝ) + 1)) =
        (ε * (n : ℝ)) / ((n : ℝ) * ((n : ℝ) + 1)) := by
      field_simp [ne_of_gt hnpos]
    _ ≤ (-nativePNTError n) / ((n : ℝ) * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right herr (mul_nonneg hnpos.le hspos.le)
    _ = -(nativePNTError n / ((n : ℝ) * ((n : ℝ) + 1))) := by ring

/-! ## PNT1 and PNT2 on complete-square search spans -/

/-- **Erdos PNT1 on a genuine square-prefix search span.** -/
theorem nativePNT_exists_small_error_squarePrefix
    (A K : ℕ) (ε : ℝ) (hK : 1 ≤ K)
    (hε : 0 < ε)
    (hdownA :
      1 < ε * (2 * (nativePNTSquarePrefixSearchLower A : ℝ) + 1))
    (hupA :
      Real.log (nativePNTSquarePrefixSearchUpper A K : ℝ) - 1 <
        ε * (2 * (nativePNTSquarePrefixSearchLower A : ℝ) + 1))
    (hdepth :
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
        ε * (2 * (K : ℝ) * Real.log 2 - 1)) :
    ∃ n ∈ Finset.Icc (nativePNTSquarePrefixSearchLower A)
        (nativePNTSquarePrefixSearchUpper A K),
      |nativePNTError n| < ε * (n : ℝ) := by
  let L := nativePNTSquarePrefixSearchLower A
  let U := nativePNTSquarePrefixSearchUpper A K
  have hL1 : 1 ≤ L := by
    dsimp [L]
    rw [nativePNTSquarePrefixSearchLower_eq]
    exact one_le_pow₀ (by omega : 1 ≤ A + 1)
  have hLU : L ≤ U := nativePNTSquarePrefixSearchLower_le_upper A K hK
  by_contra hno
  push_neg at hno
  have haway : ∀ n ∈ Finset.Icc L U,
      ε * (n : ℝ) ≤ |nativePNTError n| := by
    intro n hn
    exact hno n hn
  have hdown : ∀ n, L ≤ n → n < U →
      1 < ε * (2 * (n : ℝ) + 1) := by
    intro n hn _
    have hcast : (L : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [hdownA]
  have hup : ∀ n, L ≤ n → n < U →
      Real.log ((n + 1 : ℕ) : ℝ) - 1 < ε * (2 * (n : ℝ) + 1) := by
    intro n hn hnU
    have hn1U : n + 1 ≤ U := by omega
    have hn1pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hUpos : (0 : ℝ) < (U : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < L) hLU)
    have hlog : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (U : ℝ) := by
      apply Real.log_le_log
      · exact hn1pos
      · exact_mod_cast hn1U
    have hcast : (L : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [hupA]
  have hsign := nativePNTError_sign_constant_of_away
    L U ε hL1 hLU hε hdown hup haway
  have hrecip := nativePNTSquarePrefixRecipSuccSearch_lower A K hK
  have hupper := nativePNTSquarePrefixWeightedErrorIntervalMass_abs_le L U hL1 hLU
  have hscale :
      ε * (2 * (K : ℝ) * Real.log 2 - 1) ≤
        ε * (∑ n ∈ Finset.Icc L U, 1 / (((n + 1 : ℕ) : ℝ))) :=
    mul_le_mul_of_nonneg_left hrecip hε.le
  rcases hsign with hpos | hneg
  · have hlower := nativePNTSquarePrefixWeightedErrorIntervalMass_lower_of_nonneg
      L U ε hL1 hpos haway
    have hmass0 : 0 ≤ nativePNTSquarePrefixWeightedErrorIntervalMass L U := by
      unfold nativePNTSquarePrefixWeightedErrorIntervalMass
      apply Finset.sum_nonneg
      intro n hn
      exact div_nonneg (hpos n hn)
        (mul_nonneg (by positivity) (by positivity))
    rw [abs_of_nonneg hmass0] at hupper
    linarith
  · have hlower := nativePNTSquarePrefixWeightedErrorIntervalMass_neg_lower_of_nonpos
      L U ε hL1 hneg haway
    have hmass0 : nativePNTSquarePrefixWeightedErrorIntervalMass L U ≤ 0 := by
      unfold nativePNTSquarePrefixWeightedErrorIntervalMass
      apply Finset.sum_nonpos
      intro n hn
      exact div_nonpos_of_nonpos_of_nonneg (hneg n hn)
        (mul_nonneg (by positivity) (by positivity))
    rw [abs_of_nonpos hmass0] at hupper
    linarith

/-- PNT1 plus the already-native PNT2 persistence theorem on a complete-square
search span. -/
theorem nativePNT_exists_good_radius_squarePrefix
    (A K : ℕ) (eps : ℝ) (hA : 1 ≤ A) (hK : 1 ≤ K)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hlogA : 1 ≤ Real.log (nativePNTSquarePrefixSearchLower A : ℝ))
    (htailA :
      2200 ≤ eps * Real.log (nativePNTSquarePrefixSearchLower A : ℝ))
    (hdownA :
      1 < (eps / 4) *
        (2 * (nativePNTSquarePrefixSearchLower A : ℝ) + 1))
    (hupA :
      Real.log (nativePNTSquarePrefixSearchUpper A K : ℝ) - 1 <
        (eps / 4) *
          (2 * (nativePNTSquarePrefixSearchLower A : ℝ) + 1))
    (hdepth :
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
        (eps / 4) * (2 * (K : ℝ) * Real.log 2 - 1)) :
    ∃ t ∈ Finset.Icc (nativePNTSquarePrefixSearchLower A)
        (nativePNTSquarePrefixSearchUpper A K),
      |nativePNTError t| ≤ eps * (t : ℝ) / 4 ∧
        ∀ q ∈ Finset.Icc t (t + nativePNTGoodForwardRadius t eps),
          |nativePNTError q| ≤ eps * (q : ℝ) := by
  have hδ : 0 < eps / 4 := by positivity
  rcases nativePNT_exists_small_error_squarePrefix
      A K (eps / 4) hK hδ hdownA hupA hdepth with ⟨t, ht, hsmall⟩
  have htA : nativePNTSquarePrefixSearchLower A ≤ t :=
    (Finset.mem_Icc.mp ht).1
  have hL3 : 3 ≤ nativePNTSquarePrefixSearchLower A := by
    rw [nativePNTSquarePrefixSearchLower_eq]
    calc
      3 ≤ 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ (A + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have ht3 : 3 ≤ t := hL3.trans htA
  have hLpos : (0 : ℝ) < (nativePNTSquarePrefixSearchLower A : ℝ) := by
    exact_mod_cast (show 0 < nativePNTSquarePrefixSearchLower A by
      rw [nativePNTSquarePrefixSearchLower_eq]
      positivity)
  have hlogmono :
      Real.log (nativePNTSquarePrefixSearchLower A : ℝ) ≤ Real.log (t : ℝ) := by
    apply Real.log_le_log
    · exact hLpos
    · exact_mod_cast htA
  have hlogt : 1 ≤ Real.log (t : ℝ) := hlogA.trans hlogmono
  have htailt : 2200 ≤ eps * Real.log (t : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlogmono heps.le
    linarith
  have hsmall' : |nativePNTError t| ≤ eps * (t : ℝ) / 4 := by
    nlinarith [hsmall]
  refine ⟨t, ht, hsmall', ?_⟩
  exact nativePNTError_good_on_forward_radius t eps heps.le
    (fun h hh => nativePNTError_good_forward_interval
      t h eps ht3 heps heps1 hlogt htailt hsmall' hh)

/-! ## Explicit depth and eventual square-prefix selector -/

theorem nativePNTSquarePrefix_log_two_ge_half :
    (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

private lemma nativePNTSquarePrefix_depth_constant_le_24 :
    2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) ≤ (24 : ℝ) := by
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog4eq : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = (2 : ℕ) * Real.log (2 : ℝ) := by rw [Real.log_pow]
      _ = 2 * Real.log (2 : ℝ) := by norm_num
  rw [hlog4eq]
  nlinarith

/-- Calibrated number of square-prefix index-clock extensions, returned in the
exact doubled exponent-clock form consumed by the shell selector. -/
theorem nativePNT_exists_squarePrefix_depth_quantitative
    (eps : ℝ) (heps : 0 < eps) (_heps1 : eps ≤ 1) :
    ∃ K : ℕ,
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
          (eps / 4) * (2 * (K : ℝ) * Real.log 2 - 1) ∧
      2 * ((K : ℝ) + 2) ≤ 200 / eps := by
  let x : ℝ := 96 / eps + 1
  let K : ℕ := ⌊x⌋₊ + 1
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxK : x < (K : ℝ) := by
    dsimp [K]
    push_cast
    simpa using Nat.lt_floor_add_one x
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hKupper0 : (K : ℝ) ≤ x + 1 := by
    dsimp [K]
    push_cast
    linarith
  have hloglow := nativePNTSquarePrefix_log_two_ge_half
  have hKlog : 96 / eps < 2 * (K : ℝ) * Real.log 2 - 1 := by
    have hmul := mul_le_mul_of_nonneg_left hloglow
      (show (0 : ℝ) ≤ 2 * (K : ℝ) by positivity)
    have hKlarge : 96 / eps + 1 < (K : ℝ) := by
      simpa [x] using hxK
    nlinarith
  have hscaled := mul_lt_mul_of_pos_left hKlog
    (show (0 : ℝ) < eps / 4 by positivity)
  have hcancel : (eps / 4) * (96 / eps) = (24 : ℝ) := by
    field_simp [ne_of_gt heps]
    ring
  rw [hcancel] at hscaled
  have hdepth := nativePNTSquarePrefix_depth_constant_le_24.trans_lt hscaled
  have hKupper : (K : ℝ) ≤ 96 / eps + 2 := by
    dsimp [x] at hKupper0
    linarith
  have htail : 96 / eps + 4 ≤ 100 / eps := by
    rw [le_div_iff₀ heps]
    field_simp [ne_of_gt heps]
    nlinarith
  have hK2base : (K : ℝ) + 2 ≤ 100 / eps := by
    nlinarith [hKupper, htail]
  have hK2 : 2 * ((K : ℝ) + 2) ≤ 200 / eps := by
    calc
      2 * ((K : ℝ) + 2) ≤ 2 * (100 / eps) :=
        mul_le_mul_of_nonneg_left hK2base (by norm_num)
      _ = 200 / eps := by ring
  exact ⟨K, hdepth, hK2⟩

private theorem nativePNTSquarePrefixSearchUpper_log_le
    (A K : ℕ) (_hA : 1 ≤ A) (hK : 1 ≤ K) :
    Real.log (nativePNTSquarePrefixSearchUpper A K : ℝ) ≤
      2 * Real.log ((A + 1 : ℕ) : ℝ) + 2 * (K : ℝ) * Real.log 2 := by
  let U := nativePNTSquarePrefixSearchUpper A K
  have hUone := nativePNTSquarePrefixSearchUpper_add_one A K
  have hUpos : 0 < U := by
    dsimp [U]
    have hL := nativePNTSquarePrefixSearchLower_le_upper A K hK
    have hLpos : 0 < nativePNTSquarePrefixSearchLower A := by
      rw [nativePNTSquarePrefixSearchLower_eq]
      positivity
    omega
  have hmono : Real.log (U : ℝ) ≤ Real.log ((U + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hUpos
    · exact_mod_cast (show U ≤ U + 1 by omega)
  have heq :
      Real.log ((U + 1 : ℕ) : ℝ) =
        2 * Real.log ((A + 1 : ℕ) : ℝ) + 2 * (K : ℝ) * Real.log 2 := by
    rw [hUone, Nat.cast_pow, Real.log_pow]
    norm_num
    have hAreal : (0 : ℝ) < (A : ℝ) + 1 := by positivity
    have hpowreal : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
    rw [Real.log_mul (ne_of_gt hAreal) (ne_of_gt hpowreal), Real.log_pow]
    ring
  rw [heq] at hmono
  exact hmono

private theorem nativePNTSquarePrefix_scale_bound
    (a k eps : ℝ)
    (ha : 1 ≤ a) (hk : 1 ≤ k)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hlarge : 16 * (k + 2) < eps * a) :
    2 * (a + 1) + 2 * k < (eps / 2) * (a + 1) ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hepsa : eps * a ≤ a := by
    have h := mul_le_mul_of_nonneg_right heps1 ha0.le
    simpa using h
  have hka : 16 * (k + 2) < a := hlarge.trans_le hepsa
  have hlhs : 2 * (a + 1) + 2 * k < 3 * a := by
    nlinarith
  have hbase : 24 < eps * a := by
    nlinarith
  have hmul : 24 * a < (eps * a) * a :=
    mul_lt_mul_of_pos_right hbase ha0
  have hrhs : 3 * a < (eps / 2) * (a + 1) ^ 2 := by
    nlinarith [hmul]
  exact hlhs.trans hrhs

private theorem nativePNTSquarePrefix_depth_pos
    (K : ℕ) (eps : ℝ) (heps : 0 < eps)
    (hdepth :
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
        (eps / 4) * (2 * (K : ℝ) * Real.log 2 - 1)) :
    1 ≤ K := by
  by_contra hK
  have hK0 : K = 0 := by omega
  subst K
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hC0 :
      0 ≤ 2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) := by
    nlinarith
  simp at hdepth
  nlinarith

/- For fixed square-prefix depth, all PNT1/PNT2 endpoint hypotheses hold on
all sufficiently large square-prefix starting indices. -/
set_option maxHeartbeats 800000 in
theorem nativePNT_exists_good_radius_squarePrefix_eventually
    (K : ℕ) (eps : ℝ)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hdepth :
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
        (eps / 4) * (2 * (K : ℝ) * Real.log 2 - 1)) :
    ∀ᶠ A : ℕ in atTop,
      ∃ t ∈ Finset.Icc (nativePNTSquarePrefixSearchLower A)
          (nativePNTSquarePrefixSearchUpper A K),
        |nativePNTError t| ≤ eps * (t : ℝ) / 4 ∧
          ∀ q ∈ Finset.Icc t (t + nativePNTGoodForwardRadius t eps),
            |nativePNTError q| ≤ eps * (q : ℝ) := by
  have hK : 1 ≤ K := nativePNTSquarePrefix_depth_pos K eps heps hdepth
  have hlogTop :
      Tendsto (fun A : ℕ => Real.log (A : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog1 : ∀ᶠ A : ℕ in atTop, (1 : ℝ) ≤ Real.log (A : ℝ) :=
    hlogTop.eventually_ge_atTop 1
  have htailRaw : ∀ᶠ A : ℕ in atTop,
      2200 / eps ≤ Real.log (A : ℝ) :=
    hlogTop.eventually_ge_atTop (2200 / eps)
  obtain ⟨T : ℕ, hTnat⟩ := exists_nat_gt (16 * ((K : ℝ) + 2) / eps)
  filter_upwards [eventually_ge_atTop (max 1 T), hlog1, htailRaw]
      with A hAT hlogA0 htail0
  have hA1 : 1 ≤ A := (le_max_left 1 T).trans hAT
  have hTA : T ≤ A := (le_max_right 1 T).trans hAT
  have hApos : (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast (show 0 < A by omega)
  have hA1pos : (0 : ℝ) < ((A + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos A
  have hL : nativePNTSquarePrefixSearchLower A = (A + 1) ^ 2 :=
    nativePNTSquarePrefixSearchLower_eq A
  have hlogA1mono : Real.log (A : ℝ) ≤ Real.log ((A + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact hApos
    · exact_mod_cast (show A ≤ A + 1 by omega)
  have hlogL :
      Real.log (nativePNTSquarePrefixSearchLower A : ℝ) =
        2 * Real.log ((A + 1 : ℕ) : ℝ) := by
    rw [hL, Nat.cast_pow, Real.log_pow]
    norm_num
  have hlogStart : 1 ≤ Real.log (nativePNTSquarePrefixSearchLower A : ℝ) := by
    rw [hlogL]
    nlinarith [hlogA0, hlogA1mono]
  have htailStart :
      2200 ≤ eps * Real.log (nativePNTSquarePrefixSearchLower A : ℝ) := by
    have htailA : 2200 ≤ eps * Real.log (A : ℝ) := by
      have h := (div_le_iff₀ heps).mp htail0
      simpa [mul_comm] using h
    rw [hlogL]
    have hmul := mul_le_mul_of_nonneg_left hlogA1mono heps.le
    nlinarith
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlogA1self : Real.log ((A + 1 : ℕ) : ℝ) ≤ ((A + 1 : ℕ) : ℝ) :=
    Real.log_le_self hA1pos.le
  have hTreal : 16 * ((K : ℝ) + 2) / eps < (T : ℝ) := by
    exact_mod_cast hTnat
  have hAre : (T : ℝ) ≤ (A : ℝ) := by exact_mod_cast hTA
  have hlarge : 16 * ((K : ℝ) + 2) < eps * (A : ℝ) := by
    have htmp := lt_of_lt_of_le hTreal hAre
    have hmul := (div_lt_iff₀ heps).mp htmp
    simpa [mul_comm] using hmul
  have hupperLog := nativePNTSquarePrefixSearchUpper_log_le A K hA1 hK
  have hLcast :
      (nativePNTSquarePrefixSearchLower A : ℝ) = ((A + 1 : ℕ) : ℝ) ^ 2 := by
    rw [hL]
    norm_cast
  have hdown :
      1 < (eps / 4) *
        (2 * (nativePNTSquarePrefixSearchLower A : ℝ) + 1) := by
    have hLself :
        Real.log (nativePNTSquarePrefixSearchLower A : ℝ) ≤
          (nativePNTSquarePrefixSearchLower A : ℝ) :=
      Real.log_le_self (by positivity)
    have hepsL : 2200 ≤ eps * (nativePNTSquarePrefixSearchLower A : ℝ) :=
      htailStart.trans (mul_le_mul_of_nonneg_left hLself heps.le)
    nlinarith
  have hup :
      Real.log (nativePNTSquarePrefixSearchUpper A K : ℝ) - 1 <
        (eps / 4) *
          (2 * (nativePNTSquarePrefixSearchLower A : ℝ) + 1) := by
    have hlin :
        2 * Real.log ((A + 1 : ℕ) : ℝ) +
            2 * (K : ℝ) * Real.log 2 ≤
          2 * ((A + 1 : ℕ) : ℝ) + 2 * (K : ℝ) := by
      nlinarith [hlogA1self, hlog2le]
    have hAreal : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA1
    have hKreal : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hscale := nativePNTSquarePrefix_scale_bound
      (A : ℝ) (K : ℝ) eps hAreal hKreal heps heps1 hlarge
    calc
      Real.log (nativePNTSquarePrefixSearchUpper A K : ℝ) - 1 ≤
          (2 * Real.log ((A + 1 : ℕ) : ℝ) +
            2 * (K : ℝ) * Real.log 2) - 1 := sub_le_sub_right hupperLog 1
      _ ≤ 2 * ((A + 1 : ℕ) : ℝ) + 2 * (K : ℝ) := by linarith
      _ < (eps / 2) * (((A + 1 : ℕ) : ℝ) ^ 2) := by
        simpa [Nat.cast_add, Nat.cast_one] using hscale
      _ ≤ (eps / 4) *
          (2 * (nativePNTSquarePrefixSearchLower A : ℝ) + 1) := by
        rw [hLcast]
        nlinarith [heps.le]
  exact nativePNT_exists_good_radius_squarePrefix
    A K eps hA1 hK heps heps1 hlogStart htailStart hdown hup hdepth

end RHLean.Analysis
