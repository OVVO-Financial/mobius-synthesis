import Mathlib
import RHLean.Analysis.NativePNTErdosContraction
import RHLean.Analysis.NativePNTSignedLogSquarePrimeCells
import RHLean.Analysis.PrimeSieveQuotientPNTError

/-!
# Dyadic signed log-square cells

This file keeps the signed second-Selberg attack in one local coordinate.
Odd divisor fibres compress the raw fresh-prime-2 cells to a nonnegative
`Lambda_2` coefficient, same-sign bad endpoints pay an explicit surplus,
opposite-sign endpoints force a good intermediate quotient, and exact
reciprocal fibres carry a quantitative log-square coefficient reservoir.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Complete prime-2 cell sum over the divisors of one product fibre. -/
def nativePNTMobiusLogSquarePrimeTwoDivisorCellFiber (N d : ℕ) : ℝ :=
  ∑ m ∈ d.divisors,
    (nativePNTMobiusLogSquareSignedAtom N m (d / m) +
      nativePNTMobiusLogSquareSignedAtom N (m * 2) (d / m))

/-- On an odd product fibre, Mobius signs recombine exactly to the positive
second Selberg kernel. -/
theorem nativePNTMobiusLogSquarePrimeTwoDivisorCellFiber_eq
    (N d : ℕ) (hd : Odd d) :
    nativePNTMobiusLogSquarePrimeTwoDivisorCellFiber N d =
      nativeLambdaTwo d *
        (nativePNTError (N / d) - nativePNTError (N / (2 * d))) := by
  have htwoD : Nat.Coprime 2 d := hd.coprime_two_left
  unfold nativePNTMobiusLogSquarePrimeTwoDivisorCellFiber
  calc
    (∑ m ∈ d.divisors,
        (nativePNTMobiusLogSquareSignedAtom N m (d / m) +
          nativePNTMobiusLogSquareSignedAtom N (m * 2) (d / m))) =
      ∑ m ∈ d.divisors,
        ((μ : ArithmeticFunction ℝ) m *
          (Real.log ((d / m : ℕ) : ℝ)) ^ 2) *
          (nativePNTError (N / d) - nativePNTError (N / (2 * d))) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmd : m ∣ d := (Nat.mem_divisors.mp hm).1
      have hcopm2 : Nat.Coprime m 2 := (htwoD.of_dvd_right hmd).symm
      have hcell := nativePNTMobiusLogSquareSignedAtom_cross_endpoint
        N m 2 (d / m) Nat.prime_two hcopm2
      have hmul : m * (d / m) = d := Nat.mul_div_cancel' hmd
      have hmul2 : (m * 2) * (d / m) = 2 * d := by
        calc
          (m * 2) * (d / m) = 2 * (m * (d / m)) := by ring
          _ = 2 * d := by rw [hmul]
      rw [hmul, hmul2] at hcell
      simpa [mul_assoc] using hcell
    _ = nativeMobiusLogSquareDivisorFiber d *
        (nativePNTError (N / d) - nativePNTError (N / (2 * d))) := by
      unfold nativeMobiusLogSquareDivisorFiber
      rw [Finset.sum_mul]
    _ = nativeLambdaTwo d *
        (nativePNTError (N / d) - nativePNTError (N / (2 * d))) := by
      rw [nativeMobiusLogSquareDivisorFiber_eq_lambdaTwo]

/-- Positive-kernel dyadic cell. -/
def nativePNTLambdaTwoDyadicSignedCell (N d : ℕ) : ℝ :=
  nativeLambdaTwo d *
    (nativePNTError (N / d) - nativePNTError (N / (2 * d)))

/-- Absolute mass released by pairing its two endpoints. -/
def nativePNTLambdaTwoDyadicAbsSurplus (N d : ℕ) : ℝ :=
  nativeLambdaTwo d *
    (|nativePNTError (N / d)| + |nativePNTError (N / (2 * d))| -
      |nativePNTError (N / d) - nativePNTError (N / (2 * d))|)

private theorem abs_pair_surplus_ge_two_common_lower
    (x y L : ℝ)
    (hx : L ≤ |x|) (hy : L ≤ |y|)
    (hsign : (0 ≤ x ∧ 0 ≤ y) ∨ (x ≤ 0 ∧ y ≤ 0)) :
    2 * L ≤ |x| + |y| - |x - y| := by
  rcases hsign with hpos | hneg
  · rcases hpos with ⟨hx0, hy0⟩
    have hxL : L ≤ x := by simpa [abs_of_nonneg hx0] using hx
    have hyL : L ≤ y := by simpa [abs_of_nonneg hy0] using hy
    rw [abs_of_nonneg hx0, abs_of_nonneg hy0]
    by_cases hxy : x ≤ y
    · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
      linarith
    · have hyx : y ≤ x := le_of_not_ge hxy
      rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
      linarith
  · rcases hneg with ⟨hx0, hy0⟩
    have hxL : L ≤ -x := by simpa [abs_of_nonpos hx0] using hx
    have hyL : L ≤ -y := by simpa [abs_of_nonpos hy0] using hy
    rw [abs_of_nonpos hx0, abs_of_nonpos hy0]
    by_cases hxy : x ≤ y
    · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
      linarith
    · have hyx : y ≤ x := le_of_not_ge hxy
      rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
      linarith

/-- Same-sign beta-bad endpoints pay an explicit positive local charge. -/
theorem nativePNTLambdaTwoDyadicAbsSurplus_ge_of_bad_sameSign
    (N d : ℕ) (beta : ℝ)
    (hd : 1 ≤ d) (hbeta : 0 ≤ beta)
    (hsource : beta * ((N / d : ℕ) : ℝ) ≤ |nativePNTError (N / d)|)
    (hchild : beta * ((N / (2 * d) : ℕ) : ℝ) ≤
      |nativePNTError (N / (2 * d))|)
    (hsign :
      (0 ≤ nativePNTError (N / d) ∧
        0 ≤ nativePNTError (N / (2 * d))) ∨
      (nativePNTError (N / d) ≤ 0 ∧
        nativePNTError (N / (2 * d)) ≤ 0)) :
    2 * beta * ((N / (2 * d) : ℕ) : ℝ) * nativeLambdaTwo d ≤
      nativePNTLambdaTwoDyadicAbsSurplus N d := by
  have hdpos : 0 < d := by omega
  have hqmul : (N / (2 * d)) * d ≤ N := by
    calc
      (N / (2 * d)) * d ≤ (N / (2 * d)) * (2 * d) := by
        exact Nat.mul_le_mul_left (N / (2 * d)) (by omega)
      _ ≤ N := Nat.div_mul_le_self N (2 * d)
  have hqle : N / (2 * d) ≤ N / d :=
    (Nat.le_div_iff_mul_le hdpos).2 hqmul
  have hqleR : ((N / (2 * d) : ℕ) : ℝ) ≤ ((N / d : ℕ) : ℝ) := by
    exact_mod_cast hqle
  have hcommon : beta * ((N / (2 * d) : ℕ) : ℝ) ≤
      |nativePNTError (N / d)| :=
    (mul_le_mul_of_nonneg_left hqleR hbeta).trans hsource
  have hpair := abs_pair_surplus_ge_two_common_lower
    (nativePNTError (N / d)) (nativePNTError (N / (2 * d)))
    (beta * ((N / (2 * d) : ℕ) : ℝ)) hcommon hchild hsign
  have hkernel : 0 ≤ nativeLambdaTwo d := nativeLambdaTwo_nonneg d hd
  have hmul := mul_le_mul_of_nonneg_left hpair hkernel
  unfold nativePNTLambdaTwoDyadicAbsSurplus
  nlinarith

/-- Opposite-sign endpoints force a beta-good point between them once the
native one-step no-crossing inequalities hold. -/
theorem nativePNTError_exists_beta_good_between_of_oppositeSign
    (A B : ℕ) (beta : ℝ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (hbeta : 0 < beta)
    (hdownA : 1 < beta * (2 * (A : ℝ) + 1))
    (hupA : Real.log ((B + 1 : ℕ) : ℝ) - 1 <
      beta * (2 * (A : ℝ) + 1))
    (hopposite :
      (nativePNTError A ≤ 0 ∧ 0 ≤ nativePNTError B) ∨
      (nativePNTError B ≤ 0 ∧ 0 ≤ nativePNTError A)) :
    ∃ n ∈ Finset.Icc A B,
      |nativePNTError n| < beta * (n : ℝ) := by
  by_contra hno
  have haway : ∀ n ∈ Finset.Icc A B,
      beta * (n : ℝ) ≤ |nativePNTError n| := by
    intro n hn
    by_contra hnot
    exact hno ⟨n, hn, lt_of_not_ge hnot⟩
  have hdown : ∀ n, A ≤ n → n < B →
      1 < beta * (2 * (n : ℝ) + 1) := by
    intro n hAn _
    have hAnR : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hAn
    nlinarith [hdownA, hbeta.le]
  have hup : ∀ n, A ≤ n → n < B →
      Real.log ((n + 1 : ℕ) : ℝ) - 1 < beta * (2 * (n : ℝ) + 1) := by
    intro n hAn hnB
    have hlog : Real.log ((n + 1 : ℕ) : ℝ) ≤
        Real.log ((B + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast (show n + 1 ≤ B + 1 by omega)
    have hAnR : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hAn
    nlinarith [hupA, hbeta.le]
  have hsign := nativePNTError_sign_constant_of_away
    A B beta hA hAB hbeta hdown hup haway
  have hAmem : A ∈ Finset.Icc A B := Finset.mem_Icc.mpr ⟨le_rfl, hAB⟩
  have hBmem : B ∈ Finset.Icc A B := Finset.mem_Icc.mpr ⟨hAB, le_rfl⟩
  have hAaway := haway A hAmem
  have hBaway := haway B hBmem
  have hbetaA : 0 < beta * (A : ℝ) :=
    mul_pos hbeta (by exact_mod_cast (show 0 < A by omega))
  have hbetaB : 0 < beta * (B : ℝ) :=
    mul_pos hbeta (by exact_mod_cast (show 0 < B by omega))
  rcases hsign with hallpos | hallneg
  · rcases hopposite with hop | hop
    · have hz : nativePNTError A = 0 := le_antisymm hop.1 (hallpos A hAmem)
      simp [hz] at hAaway
      linarith
    · have hz : nativePNTError B = 0 := le_antisymm hop.1 (hallpos B hBmem)
      simp [hz] at hBaway
      linarith
  · rcases hopposite with hop | hop
    · have hz : nativePNTError B = 0 := le_antisymm (hallneg B hBmem) hop.2
      simp [hz] at hBaway
      linarith
    · have hz : nativePNTError A = 0 := le_antisymm (hallneg A hAmem) hop.2
      simp [hz] at hAaway
      linarith

/-- Every positive quotient below square-root scale is an actual reciprocal
floor endpoint. -/
theorem nativePNT_reciprocal_preimage_of_sq_le
    (N q : ℕ) (hq : 1 ≤ q) (hsq : q ^ 2 ≤ N) :
    ∃ k : ℕ, q ≤ k ∧ k ≤ N ∧ N / k = q := by
  let k := N / q
  have hqpos : 0 < q := by omega
  have hkLower : q ≤ k := by
    dsimp [k]
    apply (Nat.le_div_iff_mul_le hqpos).2
    simpa [pow_two] using hsq
  have hkN : k ≤ N := by dsimp [k]; exact Nat.div_le_self N q
  have hrem : N % q < k := (Nat.mod_lt N hqpos).trans_le hkLower
  have hdecomp : q * k + N % q = N := by
    dsimp [k]
    simpa [Nat.mul_comm] using Nat.div_add_mod N q
  have hlo : q * k ≤ N := by
    dsimp [k]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self N q
  have hhi : N < (q + 1) * k := by
    rw [← hdecomp]
    calc
      q * k + N % q < q * k + k := Nat.add_lt_add_left hrem _
      _ = (q + 1) * k := by ring
  exact ⟨k, hkLower, hkN, Nat.div_eq_of_lt_le hlo hhi⟩

/-! ## Exact quotient fibre mass -/

def nativePNTLogSquareUnitQuotientFiber (N q : ℕ) : Finset ℕ :=
  primeSieveQuotientFiber 0 N q

def nativePNTLogSquareUnitQuotientFiberMass (N q : ℕ) : ℝ :=
  ∑ k ∈ nativePNTLogSquareUnitQuotientFiber N q, (Real.log (k : ℝ)) ^ 2

theorem nativePNT_div_two_mul_of_div_eq
    (N k q : ℕ) (hdiv : N / k = q) :
    N / (2 * k) = q / 2 := by
  calc
    N / (2 * k) = N / (k * 2) := by rw [Nat.mul_comm 2 k]
    _ = (N / k) / 2 := by rw [Nat.div_div_eq_div_mul]
    _ = q / 2 := by rw [hdiv]

theorem nativePNTLogSquareUnitQuotientFiber_card
    (N q : ℕ) (hq : 1 ≤ q) :
    (nativePNTLogSquareUnitQuotientFiber N q).card =
      N / q - N / (q + 1) := by
  unfold nativePNTLogSquareUnitQuotientFiber
  rw [primeSieveQuotientFiber_eq_reciprocalInterval 0 N q (by omega)]
  simp [primeSieveReciprocalInterval, primeSieveReciprocalLower,
    primeSieveReciprocalUpper, Nat.card_Ioc]

private theorem nativePNT_natCast_div_gt_sub_one
    (N d : ℕ) (hd : 1 ≤ d) :
    (N : ℝ) / (d : ℝ) - 1 < ((N / d : ℕ) : ℝ) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hnat : N < d * (N / d + 1) := Nat.lt_mul_div_succ N (by omega)
  have hreal : (N : ℝ) < (d : ℝ) * (((N / d : ℕ) : ℝ) + 1) := by
    exact_mod_cast hnat
  have hquot : (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hdR).2
    simpa [mul_comm] using hreal
  linarith

theorem nativePNTLogSquareUnitQuotientFiber_card_lower
    (N q : ℕ) (hq : 1 ≤ q) (hscale : 2 * q * (q + 1) ≤ N) :
    (N : ℝ) / (2 * (q : ℝ) * ((q + 1 : ℕ) : ℝ)) ≤
      ((nativePNTLogSquareUnitQuotientFiber N q).card : ℝ) := by
  rw [nativePNTLogSquareUnitQuotientFiber_card N q hq]
  have hmono : N / (q + 1) ≤ N / q := Nat.div_le_div_left (by omega) (by omega)
  rw [Nat.cast_sub hmono]
  have hlo := nativePNT_natCast_div_gt_sub_one N q hq
  have hup : ((N / (q + 1) : ℕ) : ℝ) ≤
      (N : ℝ) / ((q + 1 : ℕ) : ℝ) := Nat.cast_div_le
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hq1R : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  have hgap : (N : ℝ) / (q : ℝ) - (N : ℝ) / ((q + 1 : ℕ) : ℝ) =
      (N : ℝ) / ((q : ℝ) * ((q + 1 : ℕ) : ℝ)) := by
    field_simp [ne_of_gt hqR, ne_of_gt hq1R]
    push_cast
    ring
  have hscaleR : 2 * (q : ℝ) * ((q + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hscale
  have hden : 0 < (q : ℝ) * ((q + 1 : ℕ) : ℝ) := mul_pos hqR hq1R
  have hratio2 : 2 ≤ (N : ℝ) / ((q : ℝ) * ((q + 1 : ℕ) : ℝ)) := by
    rw [le_div_iff₀ hden]
    nlinarith [hscaleR]
  have hhalfEq :
      (N : ℝ) / (2 * (q : ℝ) * ((q + 1 : ℕ) : ℝ)) =
        (1 / 2 : ℝ) * ((N : ℝ) / ((q : ℝ) * ((q + 1 : ℕ) : ℝ))) := by
    field_simp [ne_of_gt hqR, ne_of_gt hq1R]
  rw [hhalfEq]
  linarith [hlo, hup, hgap, hratio2]

theorem nativePNTLogSquareUnitQuotientFiber_log_sq_lower
    (N q k : ℕ) (hq : 1 ≤ q) (hscale : 2 * q * (q + 1) ≤ N)
    (hk : k ∈ nativePNTLogSquareUnitQuotientFiber N q) :
    (1 / 4 : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤ (Real.log (k : ℝ)) ^ 2 := by
  have hqpos : 0 < q := by omega
  have hkFiber : k ∈ primeSieveQuotientFiber 0 N q := hk
  rcases mem_primeSieveQuotientFiber.mp hkFiber with ⟨hkpos, _hkN, hdiv⟩
  have hsq : (q + 1) ^ 2 ≤ N := by
    have hq1le2q : q + 1 ≤ 2 * q := by omega
    calc
      (q + 1) ^ 2 = (q + 1) * (q + 1) := by ring
      _ ≤ (2 * q) * (q + 1) := by gcongr
      _ = 2 * q * (q + 1) := by ring
      _ ≤ N := hscale
  have hkRec : k ∈ primeSieveReciprocalInterval 0 N q := by
    rw [← primeSieveQuotientFiber_eq_reciprocalInterval 0 N q hqpos]
    exact hkFiber
  have hdivLower : N / (q + 1) < k := by
    simpa [primeSieveReciprocalLower] using
      (mem_primeSieveReciprocalInterval.mp hkRec).1
  have hqDiv : q + 1 ≤ N / (q + 1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < q + 1)).2
    simpa [pow_two] using hsq
  have hqk : q + 1 < k := hqDiv.trans_lt hdivLower
  have hNlt : N < k * (q + 1) := by
    have h := Nat.lt_mul_div_succ N hkpos
    simpa [hdiv] using h
  have hNkSq : N < k ^ 2 := by
    calc
      N < k * (q + 1) := hNlt
      _ ≤ k * k := Nat.mul_le_mul_left k hqk.le
      _ = k ^ 2 := by ring
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity : 0 < 2 * q * (q + 1)) hscale
  have hN1 : 1 ≤ N := by omega
  have hk1 : 1 ≤ k := by omega
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hlogk0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
  have hlogle : Real.log (N : ℝ) ≤ 2 * Real.log (k : ℝ) := by
    calc
      Real.log (N : ℝ) ≤ Real.log ((k ^ 2 : ℕ) : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast hN1
        · exact_mod_cast (Nat.le_of_lt hNkSq)
      _ = 2 * Real.log (k : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
  have hprod : 0 ≤
      (2 * Real.log (k : ℝ) - Real.log (N : ℝ)) *
      (2 * Real.log (k : ℝ) + Real.log (N : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hlogle)
      (add_nonneg (mul_nonneg (by norm_num) hlogk0) hlogN0)
  nlinarith

theorem nativePNTLogSquareUnitQuotientFiberMass_lower
    (N q : ℕ) (hq : 1 ≤ q) (hscale : 2 * q * (q + 1) ≤ N) :
    ((N : ℝ) / (2 * (q : ℝ) * ((q + 1 : ℕ) : ℝ))) *
        ((1 / 4 : ℝ) * (Real.log (N : ℝ)) ^ 2) ≤
      nativePNTLogSquareUnitQuotientFiberMass N q := by
  have hcard := nativePNTLogSquareUnitQuotientFiber_card_lower N q hq hscale
  have hcoeff : 0 ≤ (1 / 4 : ℝ) * (Real.log (N : ℝ)) ^ 2 := by positivity
  have hcardMul := mul_le_mul_of_nonneg_right hcard hcoeff
  have hpoint : ∀ k ∈ nativePNTLogSquareUnitQuotientFiber N q,
      (1 / 4 : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤ (Real.log (k : ℝ)) ^ 2 := by
    intro k hk
    exact nativePNTLogSquareUnitQuotientFiber_log_sq_lower N q k hq hscale hk
  have hsum :
      ((nativePNTLogSquareUnitQuotientFiber N q).card : ℝ) *
          ((1 / 4 : ℝ) * (Real.log (N : ℝ)) ^ 2) ≤
        nativePNTLogSquareUnitQuotientFiberMass N q := by
    unfold nativePNTLogSquareUnitQuotientFiberMass
    calc
      ((nativePNTLogSquareUnitQuotientFiber N q).card : ℝ) *
          ((1 / 4 : ℝ) * (Real.log (N : ℝ)) ^ 2) =
          ∑ k ∈ nativePNTLogSquareUnitQuotientFiber N q,
            ((1 / 4 : ℝ) * (Real.log (N : ℝ)) ^ 2) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ nativePNTLogSquareUnitQuotientFiber N q,
          (Real.log (k : ℝ)) ^ 2 := Finset.sum_le_sum hpoint
  exact hcardMul.trans hsum

end RHLean.Analysis
