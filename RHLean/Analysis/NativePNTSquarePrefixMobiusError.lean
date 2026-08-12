import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixContraction

/-!
# Möbius-native Selberg error mass on square prefixes

This file gives the missing full rederivation of the absolute Selberg error
mass in Möbius reciprocal-fibre language.

The route is entirely finite:

1. identify `Lambda = mu * log` as an exact arithmetic-function identity;
2. expand the `Lambda`-weighted error mass coefficientwise;
3. Fubini-reindex `d = m*k`, so the outer variable is the Möbius cofactor and
   the inner variable is its reciprocal quotient fibre;
4. partition the outer cofactor prefix into the native square-prefix blocks;
5. reprove the absolute Selberg recurrence from the signed Selberg
   decomposition using this exact Möbius mass, rather than invoking the old
   `nativePNTError_abs_log_le_weighted` theorem.

No new analytic estimate is introduced.  The only local cancellation identity
used by the new arithmetic layer is adjoining a fresh prime, which reverses the
Möbius sign.  In the logarithmic divisor fibre this gives the exact pair

`mu(m) log(pk) + mu(mp) log(k) = mu(m) log(p)`.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-! ## Exact Möbius-logarithm representation of von Mangoldt -/

/-- Finite arithmetic-function identity `mu * log = Lambda`. -/
theorem nativeMobius_mul_log_eq_vonMangoldt :
    (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log = Λ := by
  let zetaR : ArithmeticFunction ℝ :=
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
  calc
    (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log =
        (μ : ArithmeticFunction ℝ) * (zetaR * Λ) := by
      dsimp [zetaR]
      rw [ArithmeticFunction.zeta_mul_vonMangoldt]
    _ = ((μ : ArithmeticFunction ℝ) * zetaR) * Λ := by ring
    _ = Λ := by
      dsimp [zetaR]
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
      simp

/-- The logarithmic divisor fibre whose exact value is `Lambda(d)`. -/
def nativeMobiusLogDivisorFiber (d : ℕ) : ℝ :=
  ∑ m ∈ d.divisors,
    (μ : ArithmeticFunction ℝ) m * Real.log ((d / m : ℕ) : ℝ)

/-- Coefficientwise form of `mu * log = Lambda`. -/
theorem nativeMobiusLogDivisorFiber_eq_vonMangoldt (d : ℕ) :
    nativeMobiusLogDivisorFiber d = Λ d := by
  rw [← nativeMobius_mul_log_eq_vonMangoldt]
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun a b => (μ : ArithmeticFunction ℝ) a * ArithmeticFunction.log b)]
  rfl

/-- The logarithmic divisor fibre exhibits the same fresh-prime cancellation as
all other native Möbius fibres.  The complementary quotient changes from
`p*k` to `k`, leaving exactly one `log p` contribution. -/
theorem nativeMobiusLogFiber_pair_adjoin_prime
    (m p k : ℕ) (hk : 1 ≤ k)
    (hp : p.Prime) (hcop : Nat.Coprime m p) :
    ((μ m : ℤ) : ℝ) * Real.log ((p * k : ℕ) : ℝ) +
        ((μ (m * p) : ℤ) : ℝ) * Real.log (k : ℝ) =
      ((μ m : ℤ) : ℝ) * Real.log (p : ℝ) := by
  rw [nativeMobius_adjoin_prime m p hp hcop]
  push_cast
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [Real.log_mul hp0 hk0]
  ring

/-! ## Reciprocal-fibre Fubini reindexing -/

/-- The inner reciprocal quotient fibre attached to the Möbius cofactor `m`. -/
def nativePNTMobiusLogReciprocalFiber
    (N m : ℕ) (G : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (N / m),
    Real.log (k : ℝ) * G (m * k)

/-- Full Möbius reciprocal-fibre transform on the positive prefix through `N`. -/
def nativePNTMobiusLogReciprocalMass
    (N : ℕ) (G : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N,
    (μ : ArithmeticFunction ℝ) m *
      nativePNTMobiusLogReciprocalFiber N m G

/-- Exact finite Fubini identity.  A `Lambda`-weighted sum is exactly a Möbius
sum over reciprocal quotient fibres, with no inequality and no discarded sign. -/
theorem nativeLambdaWeighted_eq_mobiusLogReciprocalMass
    (N : ℕ) (G : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 N, Λ d * G d) =
      nativePNTMobiusLogReciprocalMass N G := by
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
    (∑ d ∈ Finset.Icc 1 N, Λ d * G d) =
        ∑ d ∈ Finset.Icc 1 N,
          ∑ m ∈ d.divisors,
            ((μ : ArithmeticFunction ℝ) m *
              Real.log ((d / m : ℕ) : ℝ)) * G d := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [← nativeMobiusLogDivisorFiber_eq_vonMangoldt d,
        nativeMobiusLogDivisorFiber, Finset.sum_mul]
    _ = ∑ m ∈ Finset.Icc 1 N,
          ∑ d ∈ (Finset.Icc 1 N).filter (fun x => m ∣ x),
            ((μ : ArithmeticFunction ℝ) m *
              Real.log ((d / m : ℕ) : ℝ)) * G d :=
      Finset.sum_comm' hmem
    _ = ∑ m ∈ Finset.Icc 1 N,
          (μ : ArithmeticFunction ℝ) m *
            (∑ k ∈ Finset.Icc 1 (N / m),
              Real.log (k : ℝ) * G (m * k)) := by
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
    _ = nativePNTMobiusLogReciprocalMass N G := by
      rfl

/-! ## Signed and absolute Chebyshev-error fibres -/

/-- Signed Selberg error mass after exact Möbius reciprocal-fibre reindexing. -/
def nativePNTMobiusReciprocalSignedErrorMass (N : ℕ) : ℝ :=
  nativePNTMobiusLogReciprocalMass N
    (fun d => nativePNTError (N / d))

/-- Absolute Selberg error mass after exact Möbius reciprocal-fibre reindexing. -/
def nativePNTMobiusReciprocalAbsoluteErrorMass (N : ℕ) : ℝ :=
  nativePNTMobiusLogReciprocalMass N
    (fun d => |nativePNTError (N / d)|)

/-- Exact signed error-mass identity. -/
theorem nativeLambdaSignedErrorMass_eq_mobiusReciprocal
    (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)) =
      nativePNTMobiusReciprocalSignedErrorMass N := by
  simpa [nativePNTMobiusReciprocalSignedErrorMass] using
    (nativeLambdaWeighted_eq_mobiusLogReciprocalMass N
      (fun d => nativePNTError (N / d)))

/-- Exact absolute error-mass identity.  This is the requested replacement of
`sum Lambda(d) |R(floor(N/d))|` by a pure Möbius reciprocal-fibre sum. -/
theorem nativeLambdaAbsoluteErrorMass_eq_mobiusReciprocal
    (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, Λ d * |nativePNTError (N / d)|) =
      nativePNTMobiusReciprocalAbsoluteErrorMass N := by
  simpa [nativePNTMobiusReciprocalAbsoluteErrorMass] using
    (nativeLambdaWeighted_eq_mobiusLogReciprocalMass N
      (fun d => |nativePNTError (N / d)|))

/-- The old coefficientwise triangle step, transported exactly to the Möbius
presentation.  No new majorant is introduced. -/
theorem nativePNTMobiusReciprocalSignedErrorMass_abs_le_absolute
    (N : ℕ) :
    |nativePNTMobiusReciprocalSignedErrorMass N| ≤
      nativePNTMobiusReciprocalAbsoluteErrorMass N := by
  rw [← nativeLambdaSignedErrorMass_eq_mobiusReciprocal,
    ← nativeLambdaAbsoluteErrorMass_eq_mobiusReciprocal]
  calc
    |∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)| ≤
        ∑ d ∈ Finset.Icc 1 N,
          |Λ d * nativePNTError (N / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ Finset.Icc 1 N,
          Λ d * |nativePNTError (N / d)| := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-! ## Full Möbius-native rederivation of the absolute Selberg recurrence -/

/-- **Möbius-native absolute Selberg recurrence.**

This proof starts from the signed Selberg decomposition and redoes the absolute
recurrence with the exact Möbius reciprocal error mass.  It deliberately does
not invoke `nativePNTError_abs_log_le_weighted`.
-/
theorem nativePNTError_abs_log_le_mobiusReciprocal
    (N : ℕ) (hN : 3 ≤ N) :
    |nativePNTError N| * Real.log N ≤
      nativePNTMobiusReciprocalAbsoluteErrorMass N +
        (3 * (Real.log 4 + 2) + 173) * (N : ℝ) := by
  have hsel := nativeSelbergPair_sub_two_mul_log_abs_le N hN
  have hfac := nativeLogFactorial_sub_Nlog_abs_le N (by omega)
  have hmass := nativePNTMobiusReciprocalSignedErrorMass_abs_le_absolute N
  have hdecomp := nativePNTError_selberg_decomposition N
  have hsigned := nativeLambdaSignedErrorMass_eq_mobiusReciprocal N
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hAeq :
      nativePNTError N * Real.log N =
        (nativeSelbergPair N - 2 * (N : ℝ) * Real.log N) -
          nativePNTMobiusReciprocalSignedErrorMass N -
          (Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log N) := by
    linarith [hdecomp, hsigned]
  have htri :
      |nativePNTError N * Real.log N| ≤
        |nativeSelbergPair N - 2 * (N : ℝ) * Real.log N| +
          |nativePNTMobiusReciprocalSignedErrorMass N| +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log N| := by
    rw [hAeq]
    calc
      |(nativeSelbergPair N - 2 * (N : ℝ) * Real.log N) -
          nativePNTMobiusReciprocalSignedErrorMass N -
          (Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log N)| ≤
        |(nativeSelbergPair N - 2 * (N : ℝ) * Real.log N) -
          nativePNTMobiusReciprocalSignedErrorMass N| +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log N| := abs_sub _ _
      _ ≤
        (|nativeSelbergPair N - 2 * (N : ℝ) * Real.log N| +
          |nativePNTMobiusReciprocalSignedErrorMass N|) +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log N| := by
        gcongr
        exact abs_sub _ _
  have hmain :
      |nativePNTError N * Real.log N| ≤
        nativePNTMobiusReciprocalAbsoluteErrorMass N +
          (3 * (Real.log 4 + 2) + 173) * (N : ℝ) := by
    calc
      |nativePNTError N * Real.log N| ≤
        |nativeSelbergPair N - 2 * (N : ℝ) * Real.log N| +
          |nativePNTMobiusReciprocalSignedErrorMass N| +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log N| := htri
      _ ≤
        (3 * (Real.log 4 + 2) + 172) * (N : ℝ) +
          nativePNTMobiusReciprocalAbsoluteErrorMass N +
          (N : ℝ) := by
        gcongr
      _ = nativePNTMobiusReciprocalAbsoluteErrorMass N +
          (3 * (Real.log 4 + 2) + 173) * (N : ℝ) := by ring
  simpa [abs_mul, abs_of_nonneg hlog0] using hmain

/-! ## Native square-prefix block decomposition -/

/-- Every positive square prefix is the disjoint union of the consecutive
native square-prefix blocks. -/
theorem nativePNTSquarePrefix_sum_eq_sum_blocks
    (n : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 (squarePrefixEndpoint n), f m) =
      ∑ j ∈ Finset.range n,
        ∑ m ∈ nativePNTSquarePrefixBlock j, f m := by
  induction n with
  | zero =>
      simp [squarePrefixEndpoint, nativePNTSquarePrefixBlock]
  | succ n ih =>
      have hmono : squarePrefixEndpoint n ≤ squarePrefixEndpoint (n + 1) := by
        have h1 := squarePrefixEndpoint_add_one n
        have h2 := squarePrefixEndpoint_add_one (n + 1)
        have hpow : (n + 1) ^ 2 ≤ (n + 1 + 1) ^ 2 := by
          exact Nat.pow_le_pow_left (by omega) 2
        omega
      have hset :
          Finset.Icc 1 (squarePrefixEndpoint (n + 1)) =
            Finset.Icc 1 (squarePrefixEndpoint n) ∪
              nativePNTSquarePrefixBlock n := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_union,
          nativePNTSquarePrefixBlock, Finset.mem_Ioc]
        omega
      have hdis :
          Disjoint (Finset.Icc 1 (squarePrefixEndpoint n))
            (nativePNTSquarePrefixBlock n) := by
        rw [Finset.disjoint_left]
        intro m hm1 hm2
        rw [Finset.mem_Icc] at hm1
        rw [nativePNTSquarePrefixBlock, Finset.mem_Ioc] at hm2
        omega
      rw [hset, Finset.sum_union hdis, Finset.sum_range_succ, ih]

/-- Möbius absolute error mass at the manuscript's square-prefix endpoint. -/
def nativePNTSquarePrefixMobiusAbsoluteErrorMass (n : ℕ) : ℝ :=
  nativePNTMobiusReciprocalAbsoluteErrorMass (squarePrefixEndpoint n)

/-- One outer Möbius cofactor block in the square-prefix decomposition of the
absolute reciprocal error mass. -/
def nativePNTSquarePrefixMobiusAbsoluteErrorBlockMass
    (n j : ℕ) : ℝ :=
  ∑ m ∈ nativePNTSquarePrefixBlock j,
    (μ : ArithmeticFunction ℝ) m *
      nativePNTMobiusLogReciprocalFiber
        (squarePrefixEndpoint n) m
        (fun d => |nativePNTError (squarePrefixEndpoint n / d)|)

/-- Exact square-prefix block packing of the Möbius reciprocal error mass. -/
theorem nativePNTSquarePrefixMobiusAbsoluteErrorMass_eq_sum_blocks
    (n : ℕ) :
    nativePNTSquarePrefixMobiusAbsoluteErrorMass n =
      ∑ j ∈ Finset.range n,
        nativePNTSquarePrefixMobiusAbsoluteErrorBlockMass n j := by
  unfold nativePNTSquarePrefixMobiusAbsoluteErrorMass
    nativePNTMobiusReciprocalAbsoluteErrorMass
    nativePNTMobiusLogReciprocalMass
    nativePNTSquarePrefixMobiusAbsoluteErrorBlockMass
  exact nativePNTSquarePrefix_sum_eq_sum_blocks n
    (fun m =>
      (μ : ArithmeticFunction ℝ) m *
        nativePNTMobiusLogReciprocalFiber
          (squarePrefixEndpoint n) m
          (fun d => |nativePNTError (squarePrefixEndpoint n / d)|))

/-- Exact bridge from the pre-existing `Lambda` interface to the new Möbius
square-prefix mass.  This is an identity, not an estimate. -/
theorem nativePNTSquarePrefixAbsoluteErrorFiber_eq_mobius
    (n : ℕ) :
    nativePNTSquarePrefixAbsoluteErrorFiber n =
      nativePNTSquarePrefixMobiusAbsoluteErrorMass n := by
  unfold nativePNTSquarePrefixAbsoluteErrorFiber
    nativePNTSquarePrefixMobiusAbsoluteErrorMass
  exact nativeLambdaAbsoluteErrorMass_eq_mobiusReciprocal
    (squarePrefixEndpoint n)

/-- Full square-prefix form of the Möbius-native absolute Selberg recurrence. -/
theorem nativePNTError_abs_log_le_squarePrefixMobiusFiber
    (n : ℕ) (hN : 3 ≤ squarePrefixEndpoint n) :
    |nativePNTError (squarePrefixEndpoint n)| *
        Real.log (squarePrefixEndpoint n : ℝ) ≤
      nativePNTSquarePrefixMobiusAbsoluteErrorMass n +
        (3 * (Real.log 4 + 2) + 173) * (squarePrefixEndpoint n : ℝ) := by
  simpa [nativePNTSquarePrefixMobiusAbsoluteErrorMass] using
    (nativePNTError_abs_log_le_mobiusReciprocal
      (squarePrefixEndpoint n) hN)

/-- Compatibility statement for the old square-prefix `Lambda`-named fibre,
proved through the new Möbius rederivation. -/
theorem nativePNTError_abs_log_le_squarePrefixFiber_mobius_rederived
    (n : ℕ) (hN : 3 ≤ squarePrefixEndpoint n) :
    |nativePNTError (squarePrefixEndpoint n)| *
        Real.log (squarePrefixEndpoint n : ℝ) ≤
      nativePNTSquarePrefixAbsoluteErrorFiber n +
        (3 * (Real.log 4 + 2) + 173) * (squarePrefixEndpoint n : ℝ) := by
  rw [nativePNTSquarePrefixAbsoluteErrorFiber_eq_mobius]
  exact nativePNTError_abs_log_le_squarePrefixMobiusFiber n hN

end RHLean.Analysis
