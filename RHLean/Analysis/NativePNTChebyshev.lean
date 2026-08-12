import Mathlib
import RHLean.Analysis.LogWeightedPrimeExtensionEndpoint

/-!
# Architecture-native Chebyshev layer

This module develops only the elementary prime and prime-power bounds needed by
the Selberg--Erdos PNT route.  The starting point is the primorial inequality
already available at the pinned Mathlib revision; no prime number theorem or
prime-density asymptotic is imported.
-/

noncomputable section

open Finset Nat
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- The finite prime-coordinate set through `N`. -/
def nativePrimeSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter Nat.Prime

/-- The first Chebyshev function on an integer endpoint. -/
def nativeTheta (N : ℕ) : ℝ :=
  ∑ p ∈ nativePrimeSet N, Real.log p

/-- The prime layer is nonnegative. -/
theorem nativeTheta_nonneg (N : ℕ) : 0 ≤ nativeTheta N := by
  unfold nativeTheta
  apply Finset.sum_nonneg
  intro p hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
  exact Real.log_nonneg (by exact_mod_cast hpPrime.one_le)

/-- The finite prime layer is exactly the logarithm of the primorial. -/
theorem nativeTheta_eq_log_primorial (N : ℕ) :
    nativeTheta N = Real.log (primorial N) := by
  unfold nativeTheta nativePrimeSet primorial
  have hset :
      (Finset.Icc 1 N).filter Nat.Prime =
        (Finset.range (N + 1)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
      Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨_hp1, hpN⟩, hpPrime⟩
      exact ⟨hpN, hpPrime⟩
    · rintro ⟨hpN, hpPrime⟩
      exact ⟨⟨hpPrime.one_le, hpN⟩, hpPrime⟩
  rw [hset, Nat.cast_prod, Real.log_prod]
  intro p hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
  exact_mod_cast hpPrime.ne_zero

/-- Chebyshev's elementary upper bound on the prime layer, inherited only from
the finite central-binomial proof of `primorial_le_4_pow`. -/
theorem nativeTheta_le_log4_mul (N : ℕ) :
    nativeTheta N ≤ Real.log 4 * (N : ℝ) := by
  rw [nativeTheta_eq_log_primorial]
  calc
    Real.log (primorial N) ≤ Real.log (4 ^ N) := by
      apply Real.log_le_log
      · exact_mod_cast primorial_pos N
      · exact_mod_cast primorial_le_4_pow N
    _ = Real.log 4 * (N : ℝ) := by
      rw [Real.log_pow]
      ring

/-- Exact prime-coordinate decomposition of the second Chebyshev mass:

`psi(N) = sum_{p <= N} floor(log_p N) log p`.

This is the prime-power analogue of the cofactor-first/prime-first reindexings
used throughout the repository. -/
theorem nativePsi_eq_sum_mul_log_prime (N : ℕ) :
    nativePsi N = ∑ p ∈ nativePrimeSet N, p.log N * Real.log p := by
  unfold nativePsi
  calc
    (∑ m ∈ Finset.Icc 1 N, Λ m) =
        ∑ m ∈ ((Finset.Icc 1 N).filter Nat.Prime).biUnion
          (fun p => Finset.image (p ^ ·) (Finset.Icc 1 (p.log N))), Λ m := by
      refine (Finset.sum_subset (fun q hq => ?_) (fun x hx => ?_)).symm
      · simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc,
          Finset.mem_image] at hq ⊢
        obtain ⟨p, ⟨⟨_hp1, hpN⟩, hpPrime⟩, k, ⟨_hk1, hklog⟩, rfl⟩ := hq
        have hpowPos : 0 < p ^ k := pow_pos hpPrime.pos k
        have hN0 : N ≠ 0 := by omega
        exact ⟨Nat.succ_le_iff.mpr hpowPos,
          Nat.pow_le_of_le_log hN0 hklog⟩
      · simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc,
          Finset.mem_image, not_exists, not_and, and_imp,
          ArithmeticFunction.vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
        contrapose!
        rintro ⟨p, k, hp, hk, rfl⟩
        simp only [Finset.mem_Icc] at hx
        have hpowPos : 0 < p ^ k := pow_pos hp.pos k
        have hpn : p ≤ N :=
          (Nat.le_of_dvd hpowPos (dvd_pow_self p hk.ne')).trans hx.2
        exact ⟨p, ⟨hp.one_le, hpn, hp,
          ⟨k, ⟨Nat.succ_le_iff.mpr hk,
            Nat.le_log_of_pow_le hp.one_lt hx.2, rfl⟩⟩⟩⟩
    _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ∑ q ∈ Finset.image (fun k => p ^ k) (Finset.Icc 1 (p.log N)), Λ q := by
      rw [Finset.sum_biUnion]
      intro p hp q hq hpq
      change Disjoint
        (Finset.image (fun k => p ^ k) (Finset.Icc 1 (p.log N)))
        (Finset.image (fun k => q ^ k) (Finset.Icc 1 (q.log N)))
      rw [Finset.disjoint_left]
      intro z hzp hzq
      simp only [Finset.mem_image, Finset.mem_Icc] at hzp hzq
      obtain ⟨a, ha, hpa⟩ := hzp
      obtain ⟨b, hb, hqb⟩ := hzq
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      have hqPrime : q.Prime := (Finset.mem_filter.mp hq).2
      have hpow : p ^ a = q ^ b := hpa.trans hqb.symm
      have hmin := congrArg Nat.minFac hpow
      rw [hpPrime.pow_minFac (by omega), hqPrime.pow_minFac (by omega)] at hmin
      exact hpq hmin
    _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ∑ k ∈ Finset.Icc 1 (p.log N), Λ (p ^ k) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_image]
      intro a _ha b _hb hab
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      exact Nat.pow_right_injective hpPrime.two_le hab
    _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ∑ _k ∈ Finset.Icc 1 (p.log N), Real.log p := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro k hk
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      have hkpos : 0 < k := by
        exact Nat.zero_lt_of_lt (Finset.mem_Icc.mp hk).1
      rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt hkpos),
        ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
    _ = ∑ p ∈ nativePrimeSet N, p.log N * Real.log p := by
      unfold nativePrimeSet
      apply Finset.sum_congr rfl
      intro p _hp
      simp

/-- The second Chebyshev mass is nonnegative. -/
theorem nativePsi_nonneg (N : ℕ) : 0 ≤ nativePsi N := by
  unfold nativePsi
  exact Finset.sum_nonneg fun n _hn => ArithmeticFunction.vonMangoldt_nonneg

/-- One complete prime-power fibre contributes at most `log N`. -/
theorem nativePrimeFiber_le_log
    {N p : ℕ} (hp : p ∈ nativePrimeSet N) :
    (p.log N : ℝ) * Real.log p ≤ Real.log N := by
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpPrime⟩
  rcases Finset.mem_Icc.mp hpIcc with ⟨_hp1, hpN⟩
  have hNpos : 0 < N := hpPrime.pos.trans_le hpN
  have hpow : p ^ p.log N ≤ N :=
    Nat.pow_log_le_self p (Nat.ne_of_gt hNpos)
  have hlog :
      Real.log (((p ^ p.log N : ℕ) : ℝ)) ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (pow_pos hpPrime.pos (p.log N))
    · exact_mod_cast hpow
  rw [Nat.cast_pow, Real.log_pow] at hlog
  exact hlog

/-- Above the natural square-root cutoff a prime can occur only to the first
power below `N`, so its logarithmic multiplicity is exactly one. -/
theorem nativePrime_log_eq_one_of_sqrt_lt
    {N p : ℕ} (hp : p ∈ nativePrimeSet N) (hsqrt : Nat.sqrt N < p) :
    p.log N = 1 := by
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpPrime⟩
  have hpN : p ≤ N := (Finset.mem_Icc.mp hpIcc).2
  apply Nat.log_eq_one_iff'.2
  refine ⟨hpN, ?_⟩
  have hsq : N < p ^ 2 := (Nat.sqrt_lt').1 hsqrt
  simpa [pow_two] using hsq

/-- Pointwise square-root split of a prime-power fibre.  Large primes contribute
only their prime term; all repeated-power mass is confined to primes at most
`sqrt N`. -/
theorem nativePrimeFiber_le_base_add_small
    {N p : ℕ} (hp : p ∈ nativePrimeSet N) :
    (p.log N : ℝ) * Real.log p ≤
      Real.log p + if p ≤ Nat.sqrt N then Real.log N else 0 := by
  by_cases hsmall : p ≤ Nat.sqrt N
  · have hfiber := nativePrimeFiber_le_log hp
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
    have hlogp : 0 ≤ Real.log p :=
      Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
    simp [hsmall]
    linarith
  · have hsqrt : Nat.sqrt N < p := Nat.lt_of_not_ge hsmall
    have hlogEq := nativePrime_log_eq_one_of_sqrt_lt hp hsqrt
    simp [hsmall, hlogEq]

/-- Primes whose bases can support repeated powers below `N`. -/
def nativeSmallPrimeSet (N : ℕ) : Finset ℕ :=
  (nativePrimeSet N).filter fun p => p ≤ Nat.sqrt N

/-- There are at most `sqrt N` prime bases supporting repeated powers. -/
theorem nativeSmallPrimeSet_card_le (N : ℕ) :
    (nativeSmallPrimeSet N).card ≤ Nat.sqrt N := by
  have hsub : nativeSmallPrimeSet N ⊆ Finset.Icc 1 (Nat.sqrt N) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpNative, hpSqrt⟩
    have hp1 : 1 ≤ p :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hpNative).1).1
    exact Finset.mem_Icc.mpr ⟨hp1, hpSqrt⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  omega

/-- Elementary square-root support bound for the complete second Chebyshev
mass. -/
theorem nativePsi_le_theta_add_sqrt_log
    (N : ℕ) (hN : 1 ≤ N) :
    nativePsi N ≤
      nativeTheta N + (Nat.sqrt N : ℝ) * Real.log N := by
  rw [nativePsi_eq_sum_mul_log_prime]
  have hpoint :
      ∀ p ∈ nativePrimeSet N,
        (p.log N : ℝ) * Real.log p ≤
          Real.log p + if p ≤ Nat.sqrt N then Real.log N else 0 := by
    intro p hp
    exact nativePrimeFiber_le_base_add_small hp
  have hsmallSum :
      (∑ p ∈ nativePrimeSet N,
        if p ≤ Nat.sqrt N then Real.log N else 0) =
        ((nativeSmallPrimeSet N).card : ℝ) * Real.log N := by
    calc
      (∑ p ∈ nativePrimeSet N,
          if p ≤ Nat.sqrt N then Real.log N else 0) =
          ∑ p ∈ nativeSmallPrimeSet N, Real.log N := by
            symm
            unfold nativeSmallPrimeSet
            rw [Finset.sum_filter]
      _ = ((nativeSmallPrimeSet N).card : ℝ) * Real.log N := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcard :
      ((nativeSmallPrimeSet N).card : ℝ) ≤ (Nat.sqrt N : ℝ) := by
    exact_mod_cast nativeSmallPrimeSet_card_le N
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  calc
    (∑ p ∈ nativePrimeSet N, (p.log N : ℝ) * Real.log p) ≤
        ∑ p ∈ nativePrimeSet N,
          (Real.log p + if p ≤ Nat.sqrt N then Real.log N else 0) :=
      Finset.sum_le_sum hpoint
    _ = nativeTheta N +
        ∑ p ∈ nativePrimeSet N,
          (if p ≤ Nat.sqrt N then Real.log N else 0) := by
      unfold nativeTheta
      rw [Finset.sum_add_distrib]
    _ = nativeTheta N +
        ((nativeSmallPrimeSet N).card : ℝ) * Real.log N := by
      rw [hsmallSum]
    _ ≤ nativeTheta N + (Nat.sqrt N : ℝ) * Real.log N := by
      exact add_le_add_left (mul_le_mul_of_nonneg_right hcard hlogN) _

/-- The square-root correction is at most `2N`; this uses only the elementary
inequality `log x <= 2 sqrt x`. -/
theorem nativeSqrt_mul_log_le_two_mul
    (N : ℕ) (hN : 1 ≤ N) :
    (Nat.sqrt N : ℝ) * Real.log N ≤ 2 * (N : ℝ) := by
  have hsqrtNat : (Nat.sqrt N) ^ 2 ≤ N := Nat.sqrt_le' N
  have hsqrtSq : ((Nat.sqrt N : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast hsqrtNat
  have hsqrtRealSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrtCast : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hleft : 0 ≤ (Nat.sqrt N : ℝ) := by positivity
    have hright : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    nlinarith
  have hlogRaw :=
    Real.log_natCast_le_rpow_div N (ε := (1 / 2 : ℝ)) (by norm_num)
  have hlog : Real.log (N : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
    rw [← Real.sqrt_eq_rpow] at hlogRaw
    norm_num at hlogRaw ⊢
    nlinarith
  have hsqrtNatNonneg : 0 ≤ (Nat.sqrt N : ℝ) := by positivity
  have htwosqrtNonneg : 0 ≤ 2 * Real.sqrt (N : ℝ) := by positivity
  calc
    (Nat.sqrt N : ℝ) * Real.log N ≤
        (Nat.sqrt N : ℝ) * (2 * Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog hsqrtNatNonneg
    _ ≤ Real.sqrt (N : ℝ) * (2 * Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hsqrtCast htwosqrtNonneg
    _ = 2 * (N : ℝ) := by
      nlinarith [hsqrtRealSq]

/-- Explicit architecture-native Chebyshev bound.  No prime-distribution
asymptotic enters: the prime term is controlled by the primorial, and repeated
prime powers are confined below the square-root cutoff. -/
theorem nativePsi_le_const_mul (N : ℕ) :
    nativePsi N ≤ (Real.log 4 + 2) * (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst N
    simp [nativePsi]
  · have hN1 : 1 ≤ N := hN
    have hpsi := nativePsi_le_theta_add_sqrt_log N hN1
    have htheta := nativeTheta_le_log4_mul N
    have hcorr := nativeSqrt_mul_log_le_two_mul N hN1
    nlinarith

end RHLean.Analysis
