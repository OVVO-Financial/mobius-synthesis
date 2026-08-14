import Mathlib
import RHLean.Analysis.NativePNTSignedLocalSurplus
import RHLean.Analysis.NativePNTSummatorySelberg

/-!
# Signed log-square prime cells

This module opens the second Selberg kernel before taking absolute values.
The exact identity `Lambda_2 = mu * log^2` is reindexed into reciprocal
Möbius fibres, and individual atoms are paired across a fresh-prime extension.

The fixed fresh prime `2` gives a canonical parity family: every cell starts
from an odd Möbius cofactor `m` and uses the two atoms `(m,k)` and `(2m,k)`.
The source supports are odd and the child supports are even, so the family has
multiplicity one.  The cell value is an exact cross-endpoint difference of the
Chebyshev error; no Selberg remainder is estimated in this construction.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-! ## Exact log-square reciprocal transform -/

/-- The log-square divisor fibre whose coefficient is `Lambda_2(d)`. -/
def nativeMobiusLogSquareDivisorFiber (d : ℕ) : ℝ :=
  ∑ m ∈ d.divisors,
    (μ : ArithmeticFunction ℝ) m * (Real.log ((d / m : ℕ) : ℝ)) ^ 2

/-- Coefficientwise form of `mu * log^2 = Lambda_2`. -/
theorem nativeMobiusLogSquareDivisorFiber_eq_lambdaTwo (d : ℕ) :
    nativeMobiusLogSquareDivisorFiber d = nativeLambdaTwo d := by
  unfold nativeMobiusLogSquareDivisorFiber nativeLambdaTwo
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun a b => (μ : ArithmeticFunction ℝ) a * arithmeticLogSquare b)]
  rfl

/-- Reciprocal quotient fibre for the log-square Möbius transform. -/
def nativePNTMobiusLogSquareReciprocalFiber
    (N m : ℕ) (G : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (N / m),
    (Real.log (k : ℝ)) ^ 2 * G (m * k)

/-- Full log-square Möbius reciprocal transform. -/
def nativePNTMobiusLogSquareReciprocalMass
    (N : ℕ) (G : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N,
    (μ : ArithmeticFunction ℝ) m *
      nativePNTMobiusLogSquareReciprocalFiber N m G

/-- Exact finite Fubini identity for the second Selberg kernel. -/
theorem nativeLambdaTwoWeighted_eq_mobiusLogSquareReciprocalMass
    (N : ℕ) (G : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 N, nativeLambdaTwo d * G d) =
      nativePNTMobiusLogSquareReciprocalMass N G := by
  have hmem : ∀ (d m : ℕ),
      d ∈ Finset.Icc 1 N ∧ m ∈ d.divisors ↔
        d ∈ (Finset.Icc 1 N).filter (fun x => m ∣ x) ∧
          m ∈ Finset.Icc 1 N := by
    intro d m
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd1, hdN⟩, hmd, hd0⟩
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hd0 (Nat.eq_zero_of_zero_dvd hmd)
      exact ⟨⟨⟨hd1, hdN⟩, hmd⟩,
        Nat.one_le_iff_ne_zero.mpr hm0,
        (Nat.le_of_dvd (by omega) hmd).trans hdN⟩
    · rintro ⟨⟨⟨hd1, hdN⟩, hmd⟩, _hm1, _hmN⟩
      exact ⟨⟨hd1, hdN⟩, hmd, Nat.ne_of_gt (by omega : 0 < d)⟩
  calc
    (∑ d ∈ Finset.Icc 1 N, nativeLambdaTwo d * G d) =
        ∑ d ∈ Finset.Icc 1 N,
          ∑ m ∈ d.divisors,
            ((μ : ArithmeticFunction ℝ) m *
              (Real.log ((d / m : ℕ) : ℝ)) ^ 2) * G d := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [← nativeMobiusLogSquareDivisorFiber_eq_lambdaTwo d,
        nativeMobiusLogSquareDivisorFiber, Finset.sum_mul]
    _ = ∑ m ∈ Finset.Icc 1 N,
          ∑ d ∈ (Finset.Icc 1 N).filter (fun x => m ∣ x),
            ((μ : ArithmeticFunction ℝ) m *
              (Real.log ((d / m : ℕ) : ℝ)) ^ 2) * G d :=
      Finset.sum_comm' hmem
    _ = ∑ m ∈ Finset.Icc 1 N,
          (μ : ArithmeticFunction ℝ) m *
            (∑ k ∈ Finset.Icc 1 (N / m),
              (Real.log (k : ℝ)) ^ 2 * G (m * k)) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
      have hmap :
          (Finset.Icc 1 N).filter (fun x => m ∣ x) =
            (Finset.Icc 1 (N / m)).image (fun k => m * k) := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hd1, hdN⟩, hmd⟩
          refine ⟨d / m, ?_, Nat.mul_div_cancel' hmd⟩
          have hq1 : 1 ≤ d / m :=
            (Nat.one_le_div_iff hmpos).2
              (Nat.le_of_dvd (by omega) hmd)
          exact ⟨hq1, Nat.div_le_div_right hdN⟩
        · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
          have hmulN' : k * m ≤ N :=
            (Nat.le_div_iff_mul_le hmpos).1 hkN
          have hmulN : m * k ≤ N := by
            simpa [Nat.mul_comm] using hmulN'
          have hkpos : 0 < k := by omega
          exact ⟨⟨Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (Nat.mul_pos hmpos hkpos)), hmulN⟩,
            dvd_mul_right m k⟩
      rw [hmap, Finset.sum_image]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        rw [Nat.mul_div_cancel_left k hmpos]
        ring
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hmpos hab
    _ = nativePNTMobiusLogSquareReciprocalMass N G := by
      rfl

/-- Signed second-Selberg error transform before taking absolute values. -/
def nativePNTMobiusLogSquareReciprocalSignedErrorMass (N : ℕ) : ℝ :=
  nativePNTMobiusLogSquareReciprocalMass N
    (fun d => nativePNTError (N / d))

/-- The signed `Lambda_2` error mass is exactly the log-square Möbius transform. -/
theorem nativeLambdaTwoSignedErrorMass_eq_mobiusLogSquareReciprocal
    (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
      nativeLambdaTwo d * nativePNTError (N / d)) =
      nativePNTMobiusLogSquareReciprocalSignedErrorMass N := by
  simpa [nativePNTMobiusLogSquareReciprocalSignedErrorMass] using
    (nativeLambdaTwoWeighted_eq_mobiusLogSquareReciprocalMass N
      (fun d => nativePNTError (N / d)))

/-! ## Individual two-endpoint log-square cells -/

/-- One signed log-square Möbius atom. -/
def nativePNTMobiusLogSquareSignedAtom (N m k : ℕ) : ℝ :=
  (μ : ArithmeticFunction ℝ) m * (Real.log (k : ℝ)) ^ 2 *
    nativePNTError (N / (m * k))

private theorem nativeMobiusReal_adjoin_prime
    (m p : ℕ) (hp : p.Prime) (hcop : Nat.Coprime m p) :
    (μ : ArithmeticFunction ℝ) (m * p) =
      -(μ : ArithmeticFunction ℝ) m := by
  change (((μ (m * p) : ℤ) : ℝ)) = -(((μ m : ℤ) : ℝ))
  rw [nativeMobius_adjoin_prime m p hp hcop]
  push_cast
  rfl

/-- **Cross-endpoint fresh-prime identity.**  Keeping the inner quotient `k`
fixed and adjoining a fresh prime to the Möbius cofactor produces a genuine
difference of two distinct Chebyshev endpoints. -/
theorem nativePNTMobiusLogSquareSignedAtom_cross_endpoint
    (N m p k : ℕ) (hp : p.Prime) (hcop : Nat.Coprime m p) :
    nativePNTMobiusLogSquareSignedAtom N m k +
        nativePNTMobiusLogSquareSignedAtom N (m * p) k =
      (μ : ArithmeticFunction ℝ) m * (Real.log (k : ℝ)) ^ 2 *
        (nativePNTError (N / (m * k)) -
          nativePNTError (N / ((m * p) * k))) := by
  unfold nativePNTMobiusLogSquareSignedAtom
  rw [nativeMobiusReal_adjoin_prime m p hp hcop]
  ring

/-- Horizontal fresh-prime pairing at the common endpoint.  This records the
part of `log^2(pk)` not canceled by Möbius sign reversal. -/
theorem nativePNTMobiusLogSquareSignedAtom_same_endpoint
    (N m p k : ℕ) (hk : 1 ≤ k)
    (hp : p.Prime) (hcop : Nat.Coprime m p) :
    nativePNTMobiusLogSquareSignedAtom N m (p * k) +
        nativePNTMobiusLogSquareSignedAtom N (m * p) k =
      (μ : ArithmeticFunction ℝ) m *
        ((Real.log (p : ℝ)) ^ 2 +
          2 * Real.log (p : ℝ) * Real.log (k : ℝ)) *
        nativePNTError (N / ((m * p) * k)) := by
  unfold nativePNTMobiusLogSquareSignedAtom
  rw [nativeMobiusReal_adjoin_prime m p hp hcop]
  have hmul : m * (p * k) = (m * p) * k := by ring
  rw [hmul]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (show k ≠ 0 by omega)
  rw [Nat.cast_mul, Real.log_mul hp0 hk0]
  ring

/-- Exact drop in absolute mass produced by one cross-endpoint cell. -/
theorem nativePNTMobiusLogSquareSignedAtom_cross_abs_surplus_eq
    (N m p k : ℕ) (hp : p.Prime) (hcop : Nat.Coprime m p) :
    |nativePNTMobiusLogSquareSignedAtom N m k| +
        |nativePNTMobiusLogSquareSignedAtom N (m * p) k| -
        |nativePNTMobiusLogSquareSignedAtom N m k +
          nativePNTMobiusLogSquareSignedAtom N (m * p) k| =
      |(μ : ArithmeticFunction ℝ) m| * (Real.log (k : ℝ)) ^ 2 *
        (|nativePNTError (N / (m * k))| +
          |nativePNTError (N / ((m * p) * k))| -
          |nativePNTError (N / (m * k)) -
            nativePNTError (N / ((m * p) * k))|) := by
  rw [nativePNTMobiusLogSquareSignedAtom_cross_endpoint N m p k hp hcop]
  unfold nativePNTMobiusLogSquareSignedAtom
  rw [nativeMobiusReal_adjoin_prime m p hp hcop]
  simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.log (k : ℝ)))]
  ring

private theorem abs_pair_surplus_ge_two_lower
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

/-- If both endpoints in one cell have the same sign and each has magnitude at
least `L`, then the cell releases at least twice that common magnitude times
the log-square Möbius coefficient. -/
theorem nativePNTMobiusLogSquareSignedAtom_cross_abs_surplus_ge_of_sameSign
    (N m p k : ℕ) (L : ℝ)
    (hp : p.Prime) (hcop : Nat.Coprime m p)
    (hfirst : L ≤ |nativePNTError (N / (m * k))|)
    (hsecond : L ≤ |nativePNTError (N / ((m * p) * k))|)
    (hsign :
      (0 ≤ nativePNTError (N / (m * k)) ∧
        0 ≤ nativePNTError (N / ((m * p) * k))) ∨
      (nativePNTError (N / (m * k)) ≤ 0 ∧
        nativePNTError (N / ((m * p) * k)) ≤ 0)) :
    2 * |(μ : ArithmeticFunction ℝ) m| *
        (Real.log (k : ℝ)) ^ 2 * L ≤
      |nativePNTMobiusLogSquareSignedAtom N m k| +
        |nativePNTMobiusLogSquareSignedAtom N (m * p) k| -
        |nativePNTMobiusLogSquareSignedAtom N m k +
          nativePNTMobiusLogSquareSignedAtom N (m * p) k| := by
  have hpair := abs_pair_surplus_ge_two_lower
    (nativePNTError (N / (m * k)))
    (nativePNTError (N / ((m * p) * k))) L hfirst hsecond hsign
  have hcoef :
      0 ≤ |(μ : ArithmeticFunction ℝ) m| * (Real.log (k : ℝ)) ^ 2 :=
    mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hpair hcoef
  rw [nativePNTMobiusLogSquareSignedAtom_cross_abs_surplus_eq
    N m p k hp hcop]
  nlinarith

/-! ## Canonical multiplicity-one cells at the prime 2 -/

/-- The fixed-prime-2 cell indexed by an odd cofactor `m` and quotient `k`. -/
def nativePNTLogSquareParityCell (N m k : ℕ) : ℝ :=
  nativePNTMobiusLogSquareSignedAtom N m k +
    nativePNTMobiusLogSquareSignedAtom N (m * 2) k

/-- Prime-2 cells are exact cross-endpoint error differences. -/
theorem nativePNTLogSquareParityCell_eq_cross_endpoint
    (N m k : ℕ) (hm : Odd m) :
    nativePNTLogSquareParityCell N m k =
      (μ : ArithmeticFunction ℝ) m * (Real.log (k : ℝ)) ^ 2 *
        (nativePNTError (N / (m * k)) -
          nativePNTError (N / ((m * 2) * k))) := by
  unfold nativePNTLogSquareParityCell
  exact nativePNTMobiusLogSquareSignedAtom_cross_endpoint
    N m 2 k Nat.prime_two hm.coprime_two_left.symm

/-- Finite family of prime-2 cells whose source atom is in the positive product
prefix. -/
def nativePNTLogSquareParityCellSet (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    (fun c => Odd c.1 ∧ c.1 * c.2 ≤ N)

/-- An atom is used by a parity cell either as its odd source or its even
prime-2 child. -/
def nativePNTLogSquareParityCellUses
    (cell atom : ℕ × ℕ) : Prop :=
  atom = cell ∨ atom = (cell.1 * 2, cell.2)

/-- **Multiplicity one.**  Two cells in the canonical parity family cannot use
the same underlying log-square atom.  Source supports are odd, child supports
are even, and multiplication by two is injective. -/
theorem nativePNTLogSquareParityCellSet_uses_unique
    (N : ℕ) {c₁ c₂ atom : ℕ × ℕ}
    (hc₁ : c₁ ∈ nativePNTLogSquareParityCellSet N)
    (hc₂ : c₂ ∈ nativePNTLogSquareParityCellSet N)
    (h₁ : nativePNTLogSquareParityCellUses c₁ atom)
    (h₂ : nativePNTLogSquareParityCellUses c₂ atom) :
    c₁ = c₂ := by
  rcases c₁ with ⟨m₁, k₁⟩
  rcases c₂ with ⟨m₂, k₂⟩
  simp only [nativePNTLogSquareParityCellSet, Finset.mem_filter] at hc₁ hc₂
  change atom = (m₁, k₁) ∨ atom = (m₁ * 2, k₁) at h₁
  change atom = (m₂, k₂) ∨ atom = (m₂ * 2, k₂) at h₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact h₁.symm.trans h₂
  · have hEq : (m₁, k₁) = (m₂ * 2, k₂) := h₁.symm.trans h₂
    have hmEq : m₁ = m₂ * 2 := congrArg Prod.fst hEq
    rcases hc₁.2.1 with ⟨t, ht⟩
    exfalso
    omega
  · have hEq : (m₁ * 2, k₁) = (m₂, k₂) := h₁.symm.trans h₂
    have hmEq : m₁ * 2 = m₂ := congrArg Prod.fst hEq
    rcases hc₂.2.1 with ⟨t, ht⟩
    exfalso
    omega
  · have hEq : (m₁ * 2, k₁) = (m₂ * 2, k₂) := h₁.symm.trans h₂
    have hmEq : m₁ * 2 = m₂ * 2 := congrArg Prod.fst hEq
    have hkEq : k₁ = k₂ := congrArg Prod.snd hEq
    apply Prod.ext
    · omega
    · exact hkEq

/-! ## Local good-fibre charge in the same raw coordinate -/

/-- On the `m = 1` source row, a beta-good reciprocal quotient releases its
full `alpha - beta` log-square envelope deficit before any scalar aggregation. -/
theorem nativePNTMobiusLogSquareSignedAtom_one_good_deficit
    (N k : ℕ) (alpha beta : ℝ)
    (hgood :
      |nativePNTError (N / k)| ≤
        beta * ((N / k : ℕ) : ℝ)) :
    (alpha - beta) * ((N / k : ℕ) : ℝ) *
        (Real.log (k : ℝ)) ^ 2 ≤
      alpha * ((N / k : ℕ) : ℝ) *
          (Real.log (k : ℝ)) ^ 2 -
        |nativePNTMobiusLogSquareSignedAtom N 1 k| := by
  have hcoef : 0 ≤ (Real.log (k : ℝ)) ^ 2 := sq_nonneg _
  have hmul :
      (Real.log (k : ℝ)) ^ 2 * |nativePNTError (N / k)| ≤
        (Real.log (k : ℝ)) ^ 2 *
          (beta * ((N / k : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hgood hcoef
  have hatom :
      |nativePNTMobiusLogSquareSignedAtom N 1 k| =
        (Real.log (k : ℝ)) ^ 2 * |nativePNTError (N / k)| := by
    simp [nativePNTMobiusLogSquareSignedAtom, abs_mul,
      abs_of_nonneg hcoef]
  rw [hatom]
  calc
    (alpha - beta) * ((N / k : ℕ) : ℝ) *
        (Real.log (k : ℝ)) ^ 2 =
      alpha * ((N / k : ℕ) : ℝ) * (Real.log (k : ℝ)) ^ 2 -
        (Real.log (k : ℝ)) ^ 2 *
          (beta * ((N / k : ℕ) : ℝ)) := by ring
    _ ≤ alpha * ((N / k : ℕ) : ℝ) * (Real.log (k : ℝ)) ^ 2 -
        (Real.log (k : ℝ)) ^ 2 * |nativePNTError (N / k)| := by
      exact sub_le_sub_left hmul _

end RHLean.Analysis
