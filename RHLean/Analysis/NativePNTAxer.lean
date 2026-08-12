import Mathlib
import Mathlib.NumberTheory.Harmonic.Bounds
import RHLean.Analysis.NativePNTErdosContraction

/-!
# Elementary Axer bridge from the native PNT to Mertens cancellation

This module records a finite, quantitative version of the classical
PNT-to-Mertens implication.  The only asymptotic input is the already-proved
native Chebyshev PNT, exposed here through arbitrarily small affine envelopes
for `R(N) = psi(N) - N`.

The proof keeps the useful intermediate calibration.  If
`|R(q)| <= alpha q + D`, then the reciprocal quotient fibres satisfy an Axer
bound of size `alpha N (1 + log N) + D N`.  The exact identity

`sum_{n<=N} mu(n) log n = -1 - sum_{m<=N} mu(m) R(floor(N/m))`

then gives `M(N) = o(N)` after one elementary logarithmic summation estimate.
No zeta-function zero information, Perron formula, or Tauberian theorem is
used.
-/

noncomputable section

open Filter Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators Topology

namespace RHLean.Analysis

/-- Real-valued Mertens summatory function on natural endpoints. -/
def nativeMertensSummatory (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℝ)

/-- Log-weighted real Möbius prefix. -/
def nativeMobiusLogSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (n : ℝ)

/-- Absolute quotient-fibre Chebyshev-error mass used by the Axer bridge. -/
def nativePNTAxerErrorMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, |nativePNTError (N / d)|

private theorem nativeAbsMoebiusReal_le_one (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
  have h := ArithmeticFunction.abs_moebius_le_one (n := n)
  calc
    |((ArithmeticFunction.moebius n : ℤ) : ℝ)| =
        ((|ArithmeticFunction.moebius n| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
    _ ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h
    _ = 1 := by norm_num

/-- The logarithmic derivation of Möbius is the negative Möbius-von-Mangoldt
convolution.  This is the finite coefficient identity behind the Axer formula. -/
theorem arithmeticLogWeight_moebius :
    arithmeticLogWeight (μ : ArithmeticFunction ℝ) =
      -((μ : ArithmeticFunction ℝ) * Λ) := by
  let zetaR : ArithmeticFunction ℝ :=
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
  have hzero :
      arithmeticLogWeight (μ : ArithmeticFunction ℝ) * zetaR +
          (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log = 0 := by
    calc
      arithmeticLogWeight (μ : ArithmeticFunction ℝ) * zetaR +
          (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log =
          arithmeticLogWeight (μ : ArithmeticFunction ℝ) * zetaR +
            (μ : ArithmeticFunction ℝ) * arithmeticLogWeight zetaR := by
              dsimp [zetaR]
              rw [arithmeticLogWeight_zeta]
      _ = arithmeticLogWeight ((μ : ArithmeticFunction ℝ) * zetaR) :=
        (arithmeticLogWeight_mul _ _).symm
      _ = arithmeticLogWeight (1 : ArithmeticFunction ℝ) := by
        dsimp [zetaR]
        rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
      _ = 0 := by
        ext n
        cases n with
        | zero => simp [arithmeticLogWeight]
        | succ n =>
            cases n with
            | zero => simp [arithmeticLogWeight]
            | succ n => simp [arithmeticLogWeight]
  have hDz :
      arithmeticLogWeight (μ : ArithmeticFunction ℝ) * zetaR =
        -((μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) :=
    eq_neg_of_add_eq_zero_left hzero
  calc
    arithmeticLogWeight (μ : ArithmeticFunction ℝ) =
        arithmeticLogWeight (μ : ArithmeticFunction ℝ) * 1 := by simp
    _ = arithmeticLogWeight (μ : ArithmeticFunction ℝ) *
          (zetaR * (μ : ArithmeticFunction ℝ)) := by
        dsimp [zetaR]
        rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]
    _ = (arithmeticLogWeight (μ : ArithmeticFunction ℝ) * zetaR) *
          (μ : ArithmeticFunction ℝ) := by ring
    _ = -((μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) *
          (μ : ArithmeticFunction ℝ) := by rw [hDz]
    _ = -((μ : ArithmeticFunction ℝ) * (zetaR * Λ)) *
          (μ : ArithmeticFunction ℝ) := by
        dsimp [zetaR]
        rw [ArithmeticFunction.zeta_mul_vonMangoldt]
    _ = -(((μ : ArithmeticFunction ℝ) * zetaR) *
          ((μ : ArithmeticFunction ℝ) * Λ)) := by ring
    _ = -((μ : ArithmeticFunction ℝ) * Λ) := by
        dsimp [zetaR]
        rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
        simp

/-- Summatory Möbius-von-Mangoldt convolution reindexed by reciprocal fibres. -/
theorem nativeMobiusLambdaSummatory_eq_reciprocalPsi (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      ((μ : ArithmeticFunction ℝ) * Λ) n) =
      ∑ d ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) d * nativePsi (N / d) := by
  have hmem : ∀ (n d : ℕ),
      n ∈ Finset.Icc 1 N ∧ d ∈ n.divisors ↔
        n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x) ∧
          d ∈ Finset.Icc 1 N := by
    intro n d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, hdvd, hn0⟩
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact hn0 (Nat.eq_zero_of_zero_dvd hdvd)
      exact ⟨⟨⟨hn1, hnN⟩, hdvd⟩,
        Nat.one_le_iff_ne_zero.mpr hd0,
        (Nat.le_of_dvd (by omega) hdvd).trans hnN⟩
    · rintro ⟨⟨⟨hn1, hnN⟩, hdvd⟩, _hd1, _hdN⟩
      exact ⟨⟨hn1, hnN⟩, hdvd, Nat.ne_of_gt (by omega : 0 < n)⟩
  calc
    (∑ n ∈ Finset.Icc 1 N,
      ((μ : ArithmeticFunction ℝ) * Λ) n) =
        ∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ n.divisors,
            (μ : ArithmeticFunction ℝ) d * Λ (n / d) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal
          (fun a b => (μ : ArithmeticFunction ℝ) a * Λ b)]
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x),
            (μ : ArithmeticFunction ℝ) d * Λ (n / d) :=
      Finset.sum_comm' hmem
    _ = ∑ d ∈ Finset.Icc 1 N,
          (μ : ArithmeticFunction ℝ) d *
            ∑ m ∈ Finset.Icc 1 (N / d), Λ m := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hmap :
          (Finset.Icc 1 N).filter (fun x => d ∣ x) =
            (Finset.Icc 1 (N / d)).image (fun m => d * m) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hn1, hnN⟩, hdvd⟩
          refine ⟨n / d, ?_, Nat.mul_div_cancel' hdvd⟩
          have hq1 : 1 ≤ n / d :=
            (Nat.one_le_div_iff hdpos).2
              (Nat.le_of_dvd (by omega) hdvd)
          have hqN : n / d ≤ N / d := Nat.div_le_div_right hnN
          exact ⟨hq1, hqN⟩
        · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
          have hmulN' : m * d ≤ N :=
            (Nat.le_div_iff_mul_le hdpos).1 hmN
          have hmulN : d * m ≤ N := by
            simpa [Nat.mul_comm] using hmulN'
          have hmpos : 0 < m := by omega
          exact ⟨⟨Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (Nat.mul_pos hdpos hmpos)), hmulN⟩,
            dvd_mul_right d m⟩
      rw [hmap, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro m _hm
        rw [Nat.mul_div_cancel_left m hdpos]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hdpos hab
    _ = ∑ d ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) d * nativePsi (N / d) := by rfl

/-- Exact finite Axer identity before subtracting the linear main term. -/
theorem nativeMobiusLogSum_eq_neg_reciprocalPsi (N : ℕ) :
    nativeMobiusLogSum N =
      -∑ d ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) d * nativePsi (N / d) := by
  unfold nativeMobiusLogSum
  calc
    (∑ n ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) n * Real.log (n : ℝ)) =
      ∑ n ∈ Finset.Icc 1 N,
        arithmeticLogWeight (μ : ArithmeticFunction ℝ) n := by rfl
    _ = ∑ n ∈ Finset.Icc 1 N,
        (-((μ : ArithmeticFunction ℝ) * Λ)) n := by
      rw [arithmeticLogWeight_moebius]
    _ = -∑ n ∈ Finset.Icc 1 N,
        ((μ : ArithmeticFunction ℝ) * Λ) n := by
      change (∑ n ∈ Finset.Icc 1 N,
        -(((μ : ArithmeticFunction ℝ) * Λ) n)) =
        -(∑ n ∈ Finset.Icc 1 N,
          ((μ : ArithmeticFunction ℝ) * Λ) n)
      rw [Finset.sum_neg_distrib]
    _ = -∑ d ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) d * nativePsi (N / d) := by
      rw [nativeMobiusLambdaSummatory_eq_reciprocalPsi]

/-- Exact finite Axer identity centered at `psi(q)=q`. -/
theorem nativeMobiusLogSum_eq_neg_one_sub_error
    (N : ℕ) (hN : 1 ≤ N) :
    nativeMobiusLogSum N =
      -1 - ∑ d ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) d * nativePNTError (N / d) := by
  have hfloorZ := nativeSumMoebiusMulFloor N hN
  have hfloorR :
      (∑ d ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) d * ((N / d : ℕ) : ℝ)) = 1 := by
    have hcast := congrArg (fun z : ℤ => (z : ℝ)) hfloorZ
    push_cast at hcast
    simpa using hcast
  rw [nativeMobiusLogSum_eq_neg_reciprocalPsi]
  have hsplit :
      (∑ d ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) d * nativePsi (N / d)) =
        (∑ d ∈ Finset.Icc 1 N,
          (μ : ArithmeticFunction ℝ) d * nativePNTError (N / d)) +
        ∑ d ∈ Finset.Icc 1 N,
          (μ : ArithmeticFunction ℝ) d * ((N / d : ℕ) : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    unfold nativePNTError
    ring
  rw [hsplit, hfloorR]
  ring

/-- The signed Axer correction is controlled by the absolute quotient-error
mass. -/
theorem nativeMobiusPNTErrorSum_abs_le (N : ℕ) :
    |∑ d ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) d * nativePNTError (N / d)| ≤
      nativePNTAxerErrorMass N := by
  unfold nativePNTAxerErrorMass
  calc
    |∑ d ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) d * nativePNTError (N / d)| ≤
        ∑ d ∈ Finset.Icc 1 N,
          |(μ : ArithmeticFunction ℝ) d * nativePNTError (N / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N, |nativePNTError (N / d)| := by
      apply Finset.sum_le_sum
      intro d _hd
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (nativeAbsMoebiusReal_le_one d)

private theorem nativeSumInvIcc_eq_harmonic :
    ∀ N : ℕ,
      (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ)) =
        (harmonic N : ℝ) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih,
        harmonic_succ]
      push_cast
      ring

/-- Quantitative Axer quotient-mass estimate from an affine Chebyshev-error
envelope. -/
theorem nativePNTAxerErrorMass_le_of_affineEnvelope
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (henv : nativePNTHasAffineEnvelope alpha) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ,
      nativePNTAxerErrorMass N ≤
        alpha * (N : ℝ) * (1 + Real.log (N : ℝ)) + D * (N : ℝ) := by
  rcases henv with ⟨D, hD, hpoint⟩
  refine ⟨D, hD, ?_⟩
  intro N
  unfold nativePNTAxerErrorMass
  have hraw :
      (∑ d ∈ Finset.Icc 1 N, |nativePNTError (N / d)|) ≤
        ∑ d ∈ Finset.Icc 1 N,
          (alpha * ((N / d : ℕ) : ℝ) + D) := by
    apply Finset.sum_le_sum
    intro d _hd
    exact hpoint (N / d)
  have hcast :
      (∑ d ∈ Finset.Icc 1 N,
          (alpha * ((N / d : ℕ) : ℝ) + D)) ≤
        ∑ d ∈ Finset.Icc 1 N,
          (alpha * ((N : ℝ) / (d : ℝ)) + D) := by
    apply Finset.sum_le_sum
    intro d hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) :=
      Nat.cast_div_le
    exact add_le_add_right (mul_le_mul_of_nonneg_left hdiv halpha) D
  calc
    (∑ d ∈ Finset.Icc 1 N, |nativePNTError (N / d)|) ≤
        ∑ d ∈ Finset.Icc 1 N,
          (alpha * ((N : ℝ) / (d : ℝ)) + D) := hraw.trans hcast
    _ = alpha * (N : ℝ) * (harmonic N : ℝ) + D * (N : ℝ) := by
      rw [Finset.sum_add_distrib]
      have hfirst :
          (∑ d ∈ Finset.Icc 1 N, alpha * ((N : ℝ) / (d : ℝ))) =
            alpha * (N : ℝ) * (harmonic N : ℝ) := by
        calc
          (∑ d ∈ Finset.Icc 1 N, alpha * ((N : ℝ) / (d : ℝ))) =
              alpha * (N : ℝ) *
                ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d _hd
            ring
          _ = alpha * (N : ℝ) * (harmonic N : ℝ) := by
            rw [nativeSumInvIcc_eq_harmonic]
      rw [hfirst, Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
      have hcard : N + 1 - 1 = N := by omega
      rw [hcard]
      ring
    _ ≤ alpha * (N : ℝ) * (1 + Real.log (N : ℝ)) + D * (N : ℝ) := by
      by_cases hN0 : N = 0
      · subst N
        simp
      · have hharm :
            (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := by
          simpa using harmonic_le_one_add_log N
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hharm
            (mul_nonneg halpha (by positivity))) _

/-- The log-weighted Möbius prefix inherits the calibrated Axer estimate. -/
theorem nativeMobiusLogSum_abs_le_of_affineEnvelope
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (henv : nativePNTHasAffineEnvelope alpha) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 1 ≤ N →
      |nativeMobiusLogSum N| ≤
        1 + alpha * (N : ℝ) * (1 + Real.log (N : ℝ)) + D * (N : ℝ) := by
  rcases nativePNTAxerErrorMass_le_of_affineEnvelope alpha halpha henv with
    ⟨D, hD, hmass⟩
  refine ⟨D, hD, ?_⟩
  intro N hN
  have hid := nativeMobiusLogSum_eq_neg_one_sub_error N hN
  have hsum := nativeMobiusPNTErrorSum_abs_le N
  rw [hid]
  calc
    |-1 - ∑ d ∈ Finset.Icc 1 N,
        (μ : ArithmeticFunction ℝ) d * nativePNTError (N / d)| ≤
        1 + |∑ d ∈ Finset.Icc 1 N,
          (μ : ArithmeticFunction ℝ) d * nativePNTError (N / d)| := by
      have h := abs_add_le (-1 : ℝ)
        (-(∑ d ∈ Finset.Icc 1 N,
          (μ : ArithmeticFunction ℝ) d * nativePNTError (N / d)))
      simpa [abs_neg] using h
    _ ≤ 1 + nativePNTAxerErrorMass N := add_le_add_left hsum 1
    _ ≤ 1 +
        (alpha * (N : ℝ) * (1 + Real.log (N : ℝ)) + D * (N : ℝ)) :=
      add_le_add_left (hmass N) 1
    _ = 1 + alpha * (N : ℝ) * (1 + Real.log (N : ℝ)) + D * (N : ℝ) := by
      ring

/-- Exact decomposition of `M(N) log N` into the logarithmic Möbius prefix and
a harmless positive logarithmic tail. -/
theorem nativeMertens_mul_log_eq (N : ℕ) (hN : 1 ≤ N) :
    nativeMertensSummatory N * Real.log (N : ℝ) =
      nativeMobiusLogSum N +
        ∑ n ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            Real.log ((N : ℝ) / (n : ℝ)) := by
  unfold nativeMertensSummatory nativeMobiusLogSum
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [Real.log_div (ne_of_gt hNpos) (ne_of_gt hnpos)]
  ring

/-- The remaining logarithmic tail in the Mertens decomposition is at most
`N` in absolute value. -/
theorem nativeMertensLogTail_abs_le
    (N : ℕ) (hN : 1 ≤ N) :
    |∑ n ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
          Real.log ((N : ℝ) / (n : ℝ))| ≤ (N : ℝ) := by
  have hsum :
      |∑ n ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            Real.log ((N : ℝ) / (n : ℝ))| ≤
        ∑ n ∈ Finset.Icc 1 N,
          Real.log ((N : ℝ) / (n : ℝ)) := by
    calc
      |∑ n ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            Real.log ((N : ℝ) / (n : ℝ))| ≤
          ∑ n ∈ Finset.Icc 1 N,
            |((ArithmeticFunction.moebius n : ℤ) : ℝ) *
              Real.log ((N : ℝ) / (n : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 N,
          Real.log ((N : ℝ) / (n : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hnNreal : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
        have hratio : (1 : ℝ) ≤ (N : ℝ) / (n : ℝ) := by
          rw [le_div_iff₀ hnpos]
          simpa using hnNreal
        have hlog : 0 ≤ Real.log ((N : ℝ) / (n : ℝ)) :=
          Real.log_nonneg hratio
        rw [abs_mul, abs_of_nonneg hlog]
        exact mul_le_of_le_one_left hlog (nativeAbsMoebiusReal_le_one n)
  have htailEq :
      (∑ n ∈ Finset.Icc 1 N,
          Real.log ((N : ℝ) / (n : ℝ))) =
        (N : ℝ) * Real.log (N : ℝ) -
          Real.log ((Nat.factorial N : ℕ) : ℝ) := by
    have hsumLog :
        (∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ)) =
          Real.log ((Nat.factorial N : ℕ) : ℝ) :=
      (nativeLogFactorial_eq_sum_log N).symm
    have hpoint :
        ∀ n ∈ Finset.Icc 1 N,
          Real.log ((N : ℝ) / (n : ℝ)) =
            Real.log (N : ℝ) - Real.log (n : ℝ) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [Real.log_div]
      · exact_mod_cast (show N ≠ 0 by omega)
      · exact_mod_cast (show n ≠ 0 by omega)
    calc
      (∑ n ∈ Finset.Icc 1 N,
          Real.log ((N : ℝ) / (n : ℝ))) =
          ∑ n ∈ Finset.Icc 1 N,
            (Real.log (N : ℝ) - Real.log (n : ℝ)) :=
        Finset.sum_congr rfl hpoint
      _ = (N : ℝ) * Real.log (N : ℝ) -
          ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
          Nat.card_Icc]
        have hcard : N + 1 - 1 = N := by omega
        rw [hcard]
      _ = (N : ℝ) * Real.log (N : ℝ) -
          Real.log ((Nat.factorial N : ℕ) : ℝ) := by rw [hsumLog]
  have hlower := nativeLogFactorial_lower N hN
  calc
    |∑ n ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
          Real.log ((N : ℝ) / (n : ℝ))| ≤
        ∑ n ∈ Finset.Icc 1 N,
          Real.log ((N : ℝ) / (n : ℝ)) := hsum
    _ = (N : ℝ) * Real.log (N : ℝ) -
        Real.log ((Nat.factorial N : ℕ) : ℝ) := htailEq
    _ ≤ (N : ℝ) - 1 := by linarith
    _ ≤ (N : ℝ) := by linarith

/-- Calibrated Axer bound for the Mertens function from any affine PNT
envelope. -/
theorem nativeMertens_abs_mul_log_le_of_affineEnvelope
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (henv : nativePNTHasAffineEnvelope alpha) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N →
      |nativeMertensSummatory N| * Real.log (N : ℝ) ≤
        alpha * (N : ℝ) * (1 + Real.log (N : ℝ)) +
          (D + 2) * (N : ℝ) := by
  rcases nativeMobiusLogSum_abs_le_of_affineEnvelope alpha halpha henv with
    ⟨D, hD, hlogsum⟩
  refine ⟨D, hD, ?_⟩
  intro N hN
  have hdecomp := nativeMertens_mul_log_eq N (by omega)
  have htail := nativeMertensLogTail_abs_le N (by omega)
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have habsProd :
      |nativeMertensSummatory N| * Real.log (N : ℝ) =
        |nativeMertensSummatory N * Real.log (N : ℝ)| := by
    rw [abs_mul, abs_of_nonneg hlogN]
  rw [habsProd, hdecomp]
  calc
    |nativeMobiusLogSum N +
        ∑ n ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            Real.log ((N : ℝ) / (n : ℝ))| ≤
        |nativeMobiusLogSum N| +
          |∑ n ∈ Finset.Icc 1 N,
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
              Real.log ((N : ℝ) / (n : ℝ))| := abs_add_le _ _
    _ ≤ (1 + alpha * (N : ℝ) * (1 + Real.log (N : ℝ)) +
          D * (N : ℝ)) + (N : ℝ) :=
      add_le_add (hlogsum N (by omega)) htail
    _ ≤ alpha * (N : ℝ) * (1 + Real.log (N : ℝ)) +
          (D + 2) * (N : ℝ) := by
      have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
      nlinarith

/-- **Elementary Axer bridge:** the native Chebyshev PNT implies Mertens
cancellation `M(N)=o(N)`. -/
theorem nativeMertens_div_atTop_zero :
    Tendsto (fun N : ℕ => nativeMertensSummatory N / (N : ℝ))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [] with N
    change a < |nativeMertensSummatory N / (N : ℝ)|
    exact ha.trans_le (abs_nonneg _)
  · intro b hb
    let alpha : ℝ := b / 2
    have halpha : 0 < alpha := by
      dsimp [alpha]
      positivity
    rcases nativePNTHasAffineEnvelope_arbitrarily_small alpha halpha with henv
    rcases nativeMertens_abs_mul_log_le_of_affineEnvelope alpha halpha.le henv with
      ⟨D, hD, hbound⟩
    have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hthreshold :
        ∀ᶠ N : ℕ in atTop,
          (2 * (alpha + D + 2) / b) < Real.log (N : ℝ) :=
      hlogTop.eventually (eventually_gt_atTop (2 * (alpha + D + 2) / b))
    filter_upwards [eventually_ge_atTop 2, hthreshold] with N hN hlogLarge
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hbpos : 0 < b := hb
    have hraw := hbound N hN
    have hrem :
        (alpha + D + 2) / Real.log (N : ℝ) < b / 2 := by
      rw [div_lt_iff₀ hlogpos]
      have hscale := (div_lt_iff₀ hbpos).1 hlogLarge
      nlinarith
    have hnorm :
        |nativeMertensSummatory N| / (N : ℝ) < b := by
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
      have hlogne : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlogpos
      have htarget :
          |nativeMertensSummatory N| / (N : ℝ) ≤
            alpha + (alpha + D + 2) / Real.log (N : ℝ) := by
        field_simp [hNne, hlogne]
        nlinarith [hraw]
      dsimp [alpha] at htarget
      linarith
    change |nativeMertensSummatory N / (N : ℝ)| < b
    rw [abs_div, abs_of_pos hNpos]
    exact hnorm

end RHLean.Analysis
