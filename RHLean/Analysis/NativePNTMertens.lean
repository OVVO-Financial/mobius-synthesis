import Mathlib
import RHLean.Analysis.LogWeightedPrimeExtensionEndpoint

/-!
# Architecture-native Mertens layer for PNT

This module formalizes the two finite floor identities needed by the elementary
Selberg--Erdos route to PNT.

* `nativeVonMangoldtSummatory` reindexes the divisor identity
  `log n = sum_{d|n} Lambda(d)` into reciprocal cofactor fibres.
* `nativeSumMoebiusMulFloor` reindexes `mu * zeta = 1` over the same fibres.
* `nativeMertensRecip_abs_le_one` turns the exact Mobius floor identity into the
  sharp elementary bound `|sum_{d<=N} mu(d)/d| <= 1`.

Every theorem is finite and exact.  No PNT statement, zero-free region, or
asymptotic prime-distribution theorem is imported or assumed.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- `log(N!)` is the finite sum of `log n`, `1 <= n <= N`. -/
theorem nativeLogFactorial_eq_sum_log (N : ℕ) :
    Real.log ((Nat.factorial N : ℕ) : ℝ) =
      ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
  have hprod :
      ∏ n ∈ Finset.Icc 1 N, (n : ℝ) = ((Nat.factorial N : ℕ) : ℝ) := by
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]
      push_cast
      ring
  rw [← hprod, Real.log_prod]
  intro n hn
  rw [Finset.mem_Icc] at hn
  exact Nat.cast_ne_zero.mpr (by omega)

/-- Fundamental reciprocal-fibre von Mangoldt identity:
`sum_{m<=N} Lambda(m) floor(N/m) = log(N!)`. -/
theorem nativeVonMangoldtSummatory (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, Λ m * ((N / m : ℕ) : ℝ) =
      Real.log ((Nat.factorial N : ℕ) : ℝ) := by
  have hset : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hmem : ∀ (n d : ℕ),
      n ∈ Finset.Icc 1 N ∧ d ∈ n.divisors ↔
        n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x) ∧ d ∈ Finset.Icc 1 N := by
    intro n d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, hdvd, hne⟩
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact hne (Nat.eq_zero_of_zero_dvd hdvd)
      exact ⟨⟨⟨h1, h2⟩, hdvd⟩, Nat.one_le_iff_ne_zero.mpr hd0,
        le_trans (Nat.le_of_dvd (by omega) hdvd) h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, hdvd⟩, hd1, _hdN⟩
      exact ⟨⟨h1, h2⟩, hdvd, by omega⟩
  calc
    ∑ m ∈ Finset.Icc 1 N, Λ m * ((N / m : ℕ) : ℝ) =
        ∑ d ∈ Finset.Icc 1 N,
          ∑ _n ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x), Λ d := by
            apply Finset.sum_congr rfl
            intro d _hd
            rw [Finset.sum_const, hset, Nat.Ioc_filter_dvd_card_eq_div N d,
              nsmul_eq_mul]
            exact mul_comm _ _
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, Λ d :=
      (Finset.sum_comm' hmem).symm
    _ = ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact ArithmeticFunction.vonMangoldt_sum
    _ = Real.log ((Nat.factorial N : ℕ) : ℝ) :=
      (nativeLogFactorial_eq_sum_log N).symm

/-- Easy Mertens-first-theorem inequality obtained from
`floor(N/m) <= N/m`. -/
theorem nativeLogFactorial_le (N : ℕ) :
    Real.log ((Nat.factorial N : ℕ) : ℝ) ≤
      (N : ℝ) * ∑ m ∈ Finset.Icc 1 N, Λ m / (m : ℝ) := by
  rw [← nativeVonMangoldtSummatory, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.mem_Icc] at hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (by omega : 0 < m)
  have hΛ : 0 ≤ Λ m := ArithmeticFunction.vonMangoldt_nonneg
  have hcast : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) := Nat.cast_div_le
  calc
    Λ m * ((N / m : ℕ) : ℝ) ≤
        Λ m * ((N : ℝ) / (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hcast hΛ
    _ = (N : ℝ) * (Λ m / (m : ℝ)) := by ring

/-! ## Exact Mobius floor identity and weak reciprocal bound -/

/-- Reciprocal Mobius partial sum `sum_{1<=d<=N} mu(d)/d`. -/
def nativeMertensRecip (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)

@[simp] theorem nativeMertensRecip_zero : nativeMertensRecip 0 = 0 := by
  unfold nativeMertensRecip
  rw [Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1)]
  simp

/-- Number of multiples of `d` in the positive prefix through `N`. -/
theorem nativeCardMultiplesIcc (N d : ℕ) :
    ((Finset.Icc 1 N).filter (fun m => d ∣ m)).card = N / d := by
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]

/-- Mobius divisor indicator `sum_{d|m} mu(d) = [m=1]`. -/
theorem nativeSumMoebiusDivisors (m : ℕ) (_hm : 1 ≤ m) :
    ∑ d ∈ m.divisors, ArithmeticFunction.moebius d =
      if m = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- Exact floor identity `sum_{d<=N} mu(d) floor(N/d) = 1`. -/
theorem nativeSumMoebiusMulFloor (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℤ) * ((N / d : ℕ) : ℤ) = 1 := by
  have key : ∀ d : ℕ,
      (ArithmeticFunction.moebius d : ℤ) * ((N / d : ℕ) : ℤ) =
        ∑ k ∈ Finset.Icc 1 N,
          (if d ∣ k then ArithmeticFunction.moebius d else 0) := by
    intro d
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, nativeCardMultiplesIcc]
    ring
  calc
    ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℤ) * ((N / d : ℕ) : ℤ) =
      ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (if d ∣ k then ArithmeticFunction.moebius d else 0) :=
          Finset.sum_congr rfl (fun d _ => key d)
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
        (if d ∣ k then ArithmeticFunction.moebius d else 0) := Finset.sum_comm
    _ = ∑ k ∈ Finset.Icc 1 N,
        ∑ d ∈ k.divisors, ArithmeticFunction.moebius d := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_Icc] at hk
      rw [← Finset.sum_filter]
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨_, _⟩, hdvd⟩
        exact ⟨hdvd, by omega⟩
      · rintro ⟨hdvd, _⟩
        have hkpos : 0 < k := by omega
        have hd_le : d ≤ k := Nat.le_of_dvd hkpos hdvd
        have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hkpos
        exact ⟨⟨hd_pos, by omega⟩, hdvd⟩
    _ = ∑ k ∈ Finset.Icc 1 N, (if k = 1 then (1 : ℤ) else 0) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_Icc] at hk
      rw [nativeSumMoebiusDivisors k hk.1]
    _ = 1 := by
      simp [Finset.sum_ite_eq', Finset.mem_Icc, hN]

/-- Real floor/fractional-part decomposition of the exact Mobius floor identity. -/
theorem nativeMulMertensRecip_eq (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * nativeMertensRecip N =
      1 + ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) *
          Int.fract ((N : ℝ) / (d : ℝ)) := by
  unfold nativeMertensRecip
  rw [Finset.mul_sum]
  have hsplit : ∀ d ∈ Finset.Icc 1 N,
      (N : ℝ) * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
        (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ) +
          (ArithmeticFunction.moebius d : ℝ) *
            Int.fract ((N : ℝ) / (d : ℝ)) := by
    intro d _
    have hfloorcast :
        (⌊(N : ℝ) / (d : ℝ)⌋ : ℝ) = ((N / d : ℕ) : ℝ) := by
      have hz :
          ⌊(N : ℝ) / (d : ℝ)⌋ = ((N / d : ℕ) : ℤ) := by
        rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]
      rw [hz]
      norm_cast
    have hfract :
        Int.fract ((N : ℝ) / (d : ℝ)) =
          (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) := by
      rw [← Int.self_sub_floor, hfloorcast]
    rw [hfract]
    ring
  have hcast :
      (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ)) =
        (((∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℤ) * ((N / d : ℕ) : ℤ)) : ℤ) : ℝ) := by
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Int.cast_mul, Int.cast_natCast]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hcast,
    nativeSumMoebiusMulFloor N hN, Int.cast_one]

/-- Fractional remainder in the Mobius floor identity is at most `N-1`. -/
theorem nativeMertensFractSum_abs_le (N : ℕ) (hN : 1 ≤ N) :
    |∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) *
          Int.fract ((N : ℝ) / (d : ℝ))| ≤ (N : ℝ) - 1 := by
  set f : ℕ → ℝ := fun d =>
    (ArithmeticFunction.moebius d : ℝ) *
      Int.fract ((N : ℝ) / (d : ℝ)) with hf
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 N :=
    Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hf1 : f 1 = 0 := by
    simp only [hf, Nat.cast_one, div_one, Int.fract_natCast, mul_zero]
  have hsum :
      ∑ d ∈ Finset.Icc 1 N, f d =
        ∑ d ∈ (Finset.Icc 1 N).erase 1, f d := by
    rw [← Finset.add_sum_erase _ f h1mem, hf1, zero_add]
  rw [hsum]
  calc
    |∑ d ∈ (Finset.Icc 1 N).erase 1, f d| ≤
        ∑ d ∈ (Finset.Icc 1 N).erase 1, |f d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (Finset.Icc 1 N).erase 1, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := d)
        calc
          |(ArithmeticFunction.moebius d : ℝ)| =
              ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) := by
            rw [Int.cast_abs]
          _ ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h
          _ = 1 := by norm_num
      have hfr : |Int.fract ((N : ℝ) / (d : ℝ))| ≤ 1 := by
        rw [abs_of_nonneg (Int.fract_nonneg _)]
        exact le_of_lt (Int.fract_lt_one _)
      calc
        |f d| =
            |(ArithmeticFunction.moebius d : ℝ)| *
              |Int.fract ((N : ℝ) / (d : ℝ))| := by
          rw [hf]
          exact abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul hμ hfr (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    _ = (((Finset.Icc 1 N).erase 1).card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (N : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem h1mem, Nat.card_Icc]
      have hns : N + 1 - 1 - 1 = N - 1 := by omega
      rw [hns, Nat.cast_sub hN, Nat.cast_one]

/-- Sharp elementary weak-Mertens reciprocal estimate. -/
theorem nativeMertensRecip_abs_le_one (N : ℕ) :
    |nativeMertensRecip N| ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst N
    rw [nativeMertensRecip_zero]
    norm_num
  · have hN1 : 1 ≤ N := hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have heq := nativeMulMertensRecip_eq N hN1
    have hbound := nativeMertensFractSum_abs_le N hN1
    have hkey : |(N : ℝ) * nativeMertensRecip N| ≤ N := by
      rw [heq, abs_le]
      rw [abs_le] at hbound
      constructor <;> linarith [hbound.1, hbound.2]
    rw [abs_mul, abs_of_pos hNpos] at hkey
    nlinarith [hkey, hNpos, abs_nonneg (nativeMertensRecip N)]

end RHLean.Analysis
