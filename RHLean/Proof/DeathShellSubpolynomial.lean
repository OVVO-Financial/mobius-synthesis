import Mathlib
import RHLean.Proof.DeathShellDivisorFibers
import RHLean.Proof.LifetimeEndpointDecomposition

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-!
# Subpolynomial divisor windows and unconditional death-process control

This module discharges the analytic death-process premise in the lifetime
endpoint decomposition.

The divisor bound is proved internally from the prime-factor product formula.
For a fixed positive integer `k`, only finitely many prime/exponent pairs can
fail the local estimate `(a + 1)^k ≤ p^a`; those exceptional factors are
absorbed into a `k`-dependent constant. This gives `tau(n) = O_eps(n^eps)`.

The existing death-shell divisor-fiber injection then yields a subpolynomial
bound for every death increment, a pointwise `O(n^(1+eps))` bound for the
cumulative death process, and finally the translated local-energy estimate used
by the repository's endpoint criterion.
-/

private def divisorExponentThreshold (k : ℕ) : ℕ :=
  k * max 4 (2 * k)

private def divisorPrimeThreshold (k : ℕ) : ℕ :=
  (divisorExponentThreshold k) ^ k

private def divisorExceptionalConstant (k : ℕ) : ℕ :=
  (divisorExponentThreshold k) ^ divisorPrimeThreshold k

private theorem sq_le_two_pow_of_four_le :
    ∀ q : ℕ, 4 ≤ q → q ^ 2 ≤ 2 ^ q := by
  intro q
  induction q with
  | zero =>
      intro hq
      omega
  | succ q ih =>
      intro hq
      by_cases hq4 : 4 ≤ q
      · have hprev : q ^ 2 ≤ 2 ^ q := ih hq4
        have hstep : (q + 1) ^ 2 ≤ 2 * q ^ 2 := by
          nlinarith
        calc
          (q + 1) ^ 2 ≤ 2 * q ^ 2 := hstep
          _ ≤ 2 * 2 ^ q := Nat.mul_le_mul_left 2 hprev
          _ = 2 ^ (q + 1) := by rw [pow_succ]; ring
      · have hqeq : q = 3 := by omega
        subst q
        norm_num

private theorem factorization_succ_le_two_pow_div
    (k a : ℕ) (hk : 1 ≤ k)
    (ha : divisorExponentThreshold k ≤ a) :
    a + 1 ≤ 2 ^ (a / k) := by
  let q := a / k
  have hkpos : 0 < k := by omega
  have hqThreshold : max 4 (2 * k) ≤ q := by
    apply (Nat.le_div_iff_mul_le hkpos).2
    simpa [divisorExponentThreshold, q, Nat.mul_comm] using ha
  have hq4 : 4 ≤ q := le_trans (le_max_left 4 (2 * k)) hqThreshold
  have htwoK : 2 * k ≤ q :=
    le_trans (le_max_right 4 (2 * k)) hqThreshold
  have ha_lt : a < k * (q + 1) := by
    simpa [q] using Nat.lt_mul_div_succ a hkpos
  have ha_succ : a + 1 ≤ k * (q + 1) := by omega
  have hqOne : 1 ≤ q := by omega
  have hqSucc : q + 1 ≤ 2 * q := by omega
  have hmul : k * (q + 1) ≤ q ^ 2 := by
    calc
      k * (q + 1) ≤ k * (2 * q) := Nat.mul_le_mul_left k hqSucc
      _ = (2 * k) * q := by ring
      _ ≤ q * q := Nat.mul_le_mul_right q htwoK
      _ = q ^ 2 := by ring
  exact ha_succ.trans (hmul.trans (sq_le_two_pow_of_four_le q hq4))

private theorem divisor_factor_pow_le_exception_mul
    (k n p : ℕ) (hk : 1 ≤ k) (hn : n ≠ 0)
    (hp : p ∈ n.primeFactors) :
    (n.factorization p + 1) ^ k ≤
      (if p < divisorPrimeThreshold k ∧
            n.factorization p < divisorExponentThreshold k then
        (divisorExponentThreshold k) ^ k
      else 1) * p ^ n.factorization p := by
  let A := divisorExponentThreshold k
  let P := divisorPrimeThreshold k
  let a := n.factorization p
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have haPos : 0 < a := by
    simpa [a] using hpPrime.factorization_pos_of_dvd hn hpDvd
  by_cases hbad : p < P ∧ a < A
  · rw [if_pos]
    · have hbase : a + 1 ≤ A := by omega
      have hpow : (a + 1) ^ k ≤ A ^ k :=
        Nat.pow_le_pow_left hbase k
      have hpPowOne : 1 ≤ p ^ a := Nat.one_le_pow a p hpPrime.pos
      dsimp [A, P, a] at hpow hpPowOne ⊢
      calc
        (n.factorization p + 1) ^ k ≤ divisorExponentThreshold k ^ k := hpow
        _ = divisorExponentThreshold k ^ k * 1 := by simp
        _ ≤ divisorExponentThreshold k ^ k * p ^ n.factorization p :=
          Nat.mul_le_mul_left _ hpPowOne
    · simpa [A, P, a] using hbad
  · rw [if_neg]
    · by_cases hlargeExponent : A ≤ a
      · have hfactor : a + 1 ≤ 2 ^ (a / k) := by
          apply factorization_succ_le_two_pow_div k a hk
          simpa [A] using hlargeExponent
        have htwoPrime : 2 ^ (a / k) ≤ p ^ (a / k) :=
          Nat.pow_le_pow_left hpPrime.two_le (a / k)
        have hbase : a + 1 ≤ p ^ (a / k) := hfactor.trans htwoPrime
        have hpow : (a + 1) ^ k ≤ (p ^ (a / k)) ^ k :=
          Nat.pow_le_pow_left hbase k
        calc
          (a + 1) ^ k ≤ (p ^ (a / k)) ^ k := hpow
          _ = p ^ ((a / k) * k) := by rw [pow_mul]
          _ ≤ p ^ a :=
            Nat.pow_le_pow_right hpPrime.pos (Nat.div_mul_le_self a k)
          _ = 1 * p ^ a := by simp
      · have haLt : a < A := Nat.lt_of_not_ge hlargeExponent
        have hpLarge : P ≤ p := by
          by_contra hpNot
          have hpLt : p < P := Nat.lt_of_not_ge hpNot
          exact hbad ⟨hpLt, haLt⟩
        have hbase : a + 1 ≤ A := by omega
        have hpow : (a + 1) ^ k ≤ A ^ k :=
          Nat.pow_le_pow_left hbase k
        have hPp : A ^ k ≤ p := by
          simpa [P, divisorPrimeThreshold, A] using hpLarge
        have hpSelf : p ≤ p ^ a :=
          Nat.le_self_pow (Nat.ne_of_gt haPos) p
        calc
          (a + 1) ^ k ≤ A ^ k := hpow
          _ ≤ p := hPp
          _ ≤ p ^ a := hpSelf
          _ = 1 * p ^ a := by simp
    · simpa [A, P, a] using hbad

private theorem badPrimeFactors_card_le
    (k n : ℕ) :
    ((n.primeFactors).filter fun p =>
      p < divisorPrimeThreshold k ∧
        n.factorization p < divisorExponentThreshold k).card ≤
      divisorPrimeThreshold k := by
  have hsubset :
      (n.primeFactors).filter (fun p =>
        p < divisorPrimeThreshold k ∧
          n.factorization p < divisorExponentThreshold k) ⊆
        Finset.range (divisorPrimeThreshold k) := by
    intro p hp
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2.1
  calc
    ((n.primeFactors).filter fun p =>
        p < divisorPrimeThreshold k ∧
          n.factorization p < divisorExponentThreshold k).card ≤
        (Finset.range (divisorPrimeThreshold k)).card :=
      Finset.card_le_card hsubset
    _ = divisorPrimeThreshold k := by simp

private theorem divisor_exception_product_le
    (k n : ℕ) (hk : 1 ≤ k) :
    (∏ p ∈ n.primeFactors,
        if p < divisorPrimeThreshold k ∧
            n.factorization p < divisorExponentThreshold k then
          (divisorExponentThreshold k) ^ k
        else 1) ≤
      (divisorExceptionalConstant k) ^ k := by
  classical
  let A := divisorExponentThreshold k
  let P := divisorPrimeThreshold k
  let C := divisorExceptionalConstant k
  have hcard :
      ((n.primeFactors).filter fun p => p < P ∧ n.factorization p < A).card ≤ P := by
    simpa [A, P] using badPrimeFactors_card_le k n
  have hApos : 0 < A := by
    dsimp [A, divisorExponentThreshold]
    have hmax : 0 < max 4 (2 * k) :=
      lt_of_lt_of_le (by norm_num) (le_max_left 4 (2 * k))
    exact Nat.mul_pos (by omega) hmax
  rw [Finset.prod_ite
    (fun _p => A ^ k) (fun _p => (1 : ℕ))]
  simp only [Finset.prod_const, one_pow, mul_one]
  have hpow :
      (A ^ k) ^ ((n.primeFactors).filter fun p =>
        p < P ∧ n.factorization p < A).card ≤
        (A ^ k) ^ P :=
    Nat.pow_le_pow_right (pow_pos hApos k) hcard
  calc
    (A ^ k) ^ ((n.primeFactors).filter fun p =>
        p < P ∧ n.factorization p < A).card ≤
        (A ^ k) ^ P := hpow
    _ = A ^ (k * P) := by rw [pow_mul]
    _ = A ^ (P * k) := by rw [Nat.mul_comm]
    _ = (A ^ P) ^ k := by rw [pow_mul]
    _ = C ^ k := by rfl

/-- For every positive integer `k`, the `k`th power of the divisor count is at
most a fixed `k`-dependent constant times `n`. -/
theorem card_divisors_pow_le_constant_mul
    (k n : ℕ) (hk : 1 ≤ k) :
    n.divisors.card ^ k ≤
      (divisorExceptionalConstant k) ^ k * n := by
  classical
  by_cases hn : n = 0
  · subst n
    have hk0 : k ≠ 0 := by omega
    simp [hk0]
  · rw [Nat.card_divisors hn]
    rw [← Finset.prod_pow]
    have hterm :
        (∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ k) ≤
          ∏ p ∈ n.primeFactors,
            ((if p < divisorPrimeThreshold k ∧
                  n.factorization p < divisorExponentThreshold k then
                (divisorExponentThreshold k) ^ k
              else 1) * p ^ n.factorization p) := by
      gcongr with p hp
      exact divisor_factor_pow_le_exception_mul k n p hk hn hp
    have hexception := divisor_exception_product_le k n hk
    have hprimeProd :
        (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
      calc
        (∏ p ∈ n.primeFactors, p ^ n.factorization p) =
            n.factorization.prod (fun p a => p ^ a) := by
          rw [Nat.prod_factorization_eq_prod_primeFactors]
        _ = n := Nat.factorization_prod_pow_eq_self hn
    calc
      (∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ k) ≤
          ∏ p ∈ n.primeFactors,
            ((if p < divisorPrimeThreshold k ∧
                  n.factorization p < divisorExponentThreshold k then
                (divisorExponentThreshold k) ^ k
              else 1) * p ^ n.factorization p) := hterm
      _ = (∏ p ∈ n.primeFactors,
            if p < divisorPrimeThreshold k ∧
                n.factorization p < divisorExponentThreshold k then
              (divisorExponentThreshold k) ^ k
            else 1) *
          (∏ p ∈ n.primeFactors, p ^ n.factorization p) := by
            rw [Finset.prod_mul_distrib]
      _ ≤ (divisorExceptionalConstant k) ^ k *
          (∏ p ∈ n.primeFactors, p ^ n.factorization p) :=
            Nat.mul_le_mul_right _ hexception
      _ = (divisorExceptionalConstant k) ^ k * n := by rw [hprimeProd]

/-- Classical subpolynomial divisor bound, proved from the finite-exception
factorization argument above. -/
theorem card_divisors_le_subpolynomial
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, 1 ≤ n →
        (n.divisors.card : ℝ) ≤
          C * Real.rpow (n : ℝ) ε := by
  obtain ⟨k : ℕ, hkLarge⟩ := exists_nat_gt (1 / ε)
  have hkRealPos : 0 < (k : ℝ) := by
    have hInvPos : 0 < 1 / ε := by positivity
    exact lt_trans hInvPos hkLarge
  have hkPos : 0 < k := by
    exact_mod_cast hkRealPos
  have hk : 1 ≤ k := by omega
  have hInvExp : (k : ℝ)⁻¹ ≤ ε := by
    have hmul : 1 < (k : ℝ) * ε := by
      exact (div_lt_iff₀ hε).mp hkLarge
    have hdiv : 1 / (k : ℝ) < ε :=
      (div_lt_iff₀ hkRealPos).2 (by simpa [mul_comm] using hmul)
    simpa [one_div] using hdiv.le
  let Cn := divisorExceptionalConstant k
  refine ⟨(Cn : ℝ), by positivity, ?_⟩
  intro n hn
  have hnPos : 0 < n := by omega
  have hpowNat := card_divisors_pow_le_constant_mul k n hk
  have hroot :
      (n.divisors.card : ℝ) ≤
        Real.rpow (((Cn ^ k) * n : ℕ) : ℝ) (k : ℝ)⁻¹ := by
    apply (Real.le_rpow_inv_iff_of_pos
      (by positivity : 0 ≤ (n.divisors.card : ℝ))
      (by positivity : 0 ≤ (((Cn ^ k) * n : ℕ) : ℝ))
      hkRealPos).2
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_mul] using
      (show ((n.divisors.card ^ k : ℕ) : ℝ) ≤
          (((Cn ^ k) * n : ℕ) : ℝ) by exact_mod_cast hpowNat)
  have hrootEq :
      Real.rpow (((Cn ^ k) * n : ℕ) : ℝ) (k : ℝ)⁻¹ =
        (Cn : ℝ) * Real.rpow (n : ℝ) (k : ℝ)⁻¹ := by
    simp only [Nat.cast_mul, Nat.cast_pow]
    have hCnRoot :
        Real.rpow ((Cn : ℝ) ^ k) (k : ℝ)⁻¹ = (Cn : ℝ) := by
      exact Real.pow_rpow_inv_natCast
        (x := (Cn : ℝ)) (n := k) (by positivity) (Nat.ne_of_gt hkPos)
    calc
      Real.rpow ((Cn : ℝ) ^ k * (n : ℝ)) (k : ℝ)⁻¹ =
          Real.rpow ((Cn : ℝ) ^ k) (k : ℝ)⁻¹ *
            Real.rpow (n : ℝ) (k : ℝ)⁻¹ :=
        Real.mul_rpow (by positivity) (by positivity)
      _ = (Cn : ℝ) * Real.rpow (n : ℝ) (k : ℝ)⁻¹ := by
        rw [hCnRoot]
  have hbase : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexp :
      Real.rpow (n : ℝ) (k : ℝ)⁻¹ ≤ Real.rpow (n : ℝ) ε :=
    Real.rpow_le_rpow_of_exponent_le hbase hInvExp
  calc
    (n.divisors.card : ℝ) ≤
        (Cn : ℝ) * Real.rpow (n : ℝ) (k : ℝ)⁻¹ := by
      rw [← hrootEq]
      exact hroot
    _ ≤ (Cn : ℝ) * Real.rpow (n : ℝ) ε :=
      mul_le_mul_of_nonneg_left hexp (by positivity)

/-- Uniform integer width of a fixed real-width death shell. -/
def deathShellIntegerWindowWidth (Λ : ℝ) : ℕ :=
  Nat.floor (2 * Λ) + 1

/-- The integer-height window crossed in one stage has cardinality bounded by a
constant depending only on `Λ`. -/
theorem card_deathShellIntegerWindow_le_width
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (t : ℕ) :
    (deathShellIntegerWindow Λ t).card ≤ deathShellIntegerWindowWidth Λ := by
  classical
  let a : ℝ := 2 * Λ * (t : ℝ)
  let L : ℕ := deathShellIntegerWindowWidth Λ
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hLReal : 2 * Λ < (L : ℝ) := by
    dsimp [L, deathShellIntegerWindowWidth]
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (2 * Λ)
  have hsubset :
      deathShellIntegerWindow Λ t ⊆
        Finset.Ioc (Nat.floor a) (Nat.floor a + L) := by
    intro m hm
    have hmData := Finset.mem_filter.mp hm
    have hmRange := Finset.mem_range.mp hmData.1
    have hmUpperFloor :
        m ≤ Nat.floor (2 * Λ * ((t + 1 : ℕ) : ℝ)) := by
      omega
    have hUpperNonneg : 0 ≤ 2 * Λ * ((t + 1 : ℕ) : ℝ) := by positivity
    have hmUpperCast :
        (m : ℝ) ≤ (Nat.floor (2 * Λ * ((t + 1 : ℕ) : ℝ)) : ℝ) := by
      exact_mod_cast hmUpperFloor
    have hmUpperReal :
        (m : ℝ) ≤ 2 * Λ * ((t + 1 : ℕ) : ℝ) :=
      hmUpperCast.trans (Nat.floor_le hUpperNonneg)
    have hmLower : Nat.floor a < m := by
      have hmLowerReal : (Nat.floor a : ℝ) < (m : ℝ) := by
        have hmStrict : a < (m : ℝ) := by simpa [a] using hmData.2
        have hFloorLower : (Nat.floor a : ℝ) ≤ a := Nat.floor_le ha0
        exact lt_of_le_of_lt hFloorLower hmStrict
      exact_mod_cast hmLowerReal
    have haFloorSucc : a < (Nat.floor a : ℝ) + 1 := Nat.lt_floor_add_one a
    have hmUpperStrict :
        (m : ℝ) < ((Nat.floor a + L + 1 : ℕ) : ℝ) := by
      have htCast : (((t + 1 : ℕ) : ℝ)) = (t : ℝ) + 1 := by norm_num
      rw [htCast] at hmUpperReal
      push_cast
      dsimp [a] at haFloorSucc
      nlinarith
    have hmUpperNat : m < Nat.floor a + L + 1 := by exact_mod_cast hmUpperStrict
    exact Finset.mem_Ioc.mpr ⟨hmLower, by omega⟩
  calc
    (deathShellIntegerWindow Λ t).card ≤
        (Finset.Ioc (Nat.floor a) (Nat.floor a + L)).card :=
      Finset.card_le_card hsubset
    _ = L := by simp
    _ = deathShellIntegerWindowWidth Λ := rfl

/-- Every integer height in the shell is at most a fixed `Λ`-dependent multiple
of the stage scale. -/
theorem deathShellIntegerWindow_element_le_width_mul
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {t m : ℕ}
    (hm : m ∈ deathShellIntegerWindow Λ t) :
    m ≤ deathShellIntegerWindowWidth Λ * (t + 1) := by
  have hmData := Finset.mem_filter.mp hm
  have hmRange := Finset.mem_range.mp hmData.1
  have hmUpperFloor :
      m ≤ Nat.floor (2 * Λ * ((t + 1 : ℕ) : ℝ)) := by omega
  have hUpperNonneg : 0 ≤ 2 * Λ * ((t + 1 : ℕ) : ℝ) := by positivity
  have hmUpperCast :
      (m : ℝ) ≤ (Nat.floor (2 * Λ * ((t + 1 : ℕ) : ℝ)) : ℝ) := by
    exact_mod_cast hmUpperFloor
  have hmUpperReal :
      (m : ℝ) ≤ 2 * Λ * ((t + 1 : ℕ) : ℝ) :=
    hmUpperCast.trans (Nat.floor_le hUpperNonneg)
  have hWidth :
      2 * Λ < (deathShellIntegerWindowWidth Λ : ℝ) := by
    unfold deathShellIntegerWindowWidth
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (2 * Λ)
  have htPos : 0 < ((t + 1 : ℕ) : ℝ) := by positivity
  have hmLt :
      (m : ℝ) <
        (deathShellIntegerWindowWidth Λ : ℝ) * ((t + 1 : ℕ) : ℝ) :=
    lt_of_le_of_lt hmUpperReal (mul_lt_mul_of_pos_right hWidth htPos)
  have hmLtNat : m < deathShellIntegerWindowWidth Λ * (t + 1) := by
    exact_mod_cast hmLt
  exact Nat.le_of_lt hmLtNat

/-- The exact divisor-window majorant is subpolynomial in the shell stage. -/
theorem deathShellDivisorMajorant_subpolynomial
    {Λ ε : ℝ} (hΛ : 0 < Λ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℕ,
        deathShellDivisorMajorant Λ t ≤
          C * Real.rpow ((t + 1 : ℕ) : ℝ) ε := by
  rcases card_divisors_le_subpolynomial hε with ⟨Cτ, hCτ, hτ⟩
  let L := deathShellIntegerWindowWidth Λ
  let C := (L : ℝ) * Cτ * Real.rpow (L : ℝ) ε
  have hLpos : 0 < L := by
    dsimp [L, deathShellIntegerWindowWidth]
    omega
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by positivity) hCτ)
      (Real.rpow_nonneg (by positivity) ε)
  refine ⟨C, hC, ?_⟩
  intro t
  have hcard := card_deathShellIntegerWindow_le_width hΛ.le t
  have hterm : ∀ m ∈ deathShellIntegerWindow Λ t,
      (m.divisors.card : ℝ) ≤
        Cτ * Real.rpow ((L * (t + 1) : ℕ) : ℝ) ε := by
    intro m hm
    have hmPosReal : 0 < (m : ℝ) := by
      have hLower := (Finset.mem_filter.mp hm).2
      have hnonneg : 0 ≤ 2 * Λ * (t : ℝ) := by positivity
      exact lt_of_le_of_lt hnonneg hLower
    have hmPos : 1 ≤ m := by
      have hmNatPos : 0 < m := by exact_mod_cast hmPosReal
      omega
    have hdiv := hτ m hmPos
    have hmLe := deathShellIntegerWindow_element_le_width_mul hΛ.le hm
    have hmLeReal :
        (m : ℝ) ≤ ((L * (t + 1) : ℕ) : ℝ) := by
      exact_mod_cast hmLe
    have hpow :
        Real.rpow (m : ℝ) ε ≤
          Real.rpow ((L * (t + 1) : ℕ) : ℝ) ε :=
      Real.rpow_le_rpow (by positivity) hmLeReal hε.le
    exact hdiv.trans (mul_le_mul_of_nonneg_left hpow hCτ)
  have hscale :
      Real.rpow ((L * (t + 1) : ℕ) : ℝ) ε =
        Real.rpow (L : ℝ) ε *
          Real.rpow ((t + 1 : ℕ) : ℝ) ε := by
    have hcast :
        (((L * (t + 1) : ℕ) : ℝ)) =
          (L : ℝ) * ((t + 1 : ℕ) : ℝ) := by
      norm_num
    rw [hcast]
    exact Real.mul_rpow (by positivity) (by positivity)
  unfold deathShellDivisorMajorant
  push_cast
  calc
    (∑ m ∈ deathShellIntegerWindow Λ t, (m.divisors.card : ℝ)) ≤
        ∑ _m ∈ deathShellIntegerWindow Λ t,
          Cτ * Real.rpow ((L * (t + 1) : ℕ) : ℝ) ε := by
      exact Finset.sum_le_sum fun m hm => hterm m hm
    _ = ((deathShellIntegerWindow Λ t).card : ℝ) *
        (Cτ * Real.rpow ((L * (t + 1) : ℕ) : ℝ) ε) := by
      simp [mul_comm]
    _ ≤ (L : ℝ) *
        (Cτ * Real.rpow ((L * (t + 1) : ℕ) : ℝ) ε) := by
      have hcardReal :
          ((deathShellIntegerWindow Λ t).card : ℝ) ≤ (L : ℝ) := by
        exact_mod_cast hcard
      have hfactorNonneg :
          0 ≤ Cτ * Real.rpow ((L * (t + 1) : ℕ) : ℝ) ε :=
        mul_nonneg hCτ (Real.rpow_nonneg (by positivity) ε)
      exact mul_le_mul_of_nonneg_right hcardReal hfactorNonneg
    _ = C * Real.rpow ((t : ℝ) + 1) ε := by
      have hsucc : (((t + 1 : ℕ) : ℝ)) = (t : ℝ) + 1 := by norm_num
      rw [hscale, hsucc]
      dsimp [C]
      ring

/-- Every discrete death increment is subpolynomial. -/
theorem norm_lifetimeDeathIncrement_subpolynomial
    {Λ ε : ℝ} (hΛ : 0 < Λ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℕ,
        ‖lifetimeDeathIncrement Λ t‖ ≤
          C * Real.rpow ((t + 1 : ℕ) : ℝ) ε := by
  rcases deathShellDivisorMajorant_subpolynomial hΛ hε with ⟨C, hC, hmajorant⟩
  exact ⟨C, hC, fun t =>
    (norm_lifetimeDeathIncrement_le_divisorMajorant hΛ t).trans (hmajorant t)⟩

/-- Summing the subpolynomial shell increments gives square-root-scale pointwise
control of the cumulative death process on the square-root stage variable. -/
theorem norm_lifetimeDeathMass_le_rpow
    {Λ ε : ℝ} (hΛ : 0 < Λ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ,
        ‖lifetimeDeathMass Λ n‖ ≤
          C * Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε) := by
  rcases deathShellDivisorMajorant_subpolynomial hΛ hε with
    ⟨Cinc, hCinc, hinc⟩
  let D0 := ‖lifetimeDeathMass Λ 0‖
  let C := D0 + Cinc
  refine ⟨C, by dsimp [C, D0]; positivity, ?_⟩
  intro n
  let B : ℝ := ((n + 1 : ℕ) : ℝ)
  have hbase : 1 ≤ B := by
    dsimp [B]
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hbasePos : 0 < B := lt_of_lt_of_le zero_lt_one hbase
  have hsum :
      (∑ t ∈ Finset.range n, deathShellDivisorMajorant Λ t) ≤
        (n : ℝ) * (Cinc * Real.rpow B ε) := by
    calc
      (∑ t ∈ Finset.range n, deathShellDivisorMajorant Λ t) ≤
          ∑ _t ∈ Finset.range n, Cinc * Real.rpow B ε := by
        apply Finset.sum_le_sum
        intro t ht
        have htLe : t + 1 ≤ n + 1 := by
          have htLt : t < n := Finset.mem_range.mp ht
          omega
        have htLeReal : ((t + 1 : ℕ) : ℝ) ≤ B := by
          dsimp [B]
          exact_mod_cast htLe
        have hpow :
            Real.rpow ((t + 1 : ℕ) : ℝ) ε ≤ Real.rpow B ε :=
          Real.rpow_le_rpow (by positivity) htLeReal hε.le
        exact (hinc t).trans (mul_le_mul_of_nonneg_left hpow hCinc)
      _ = (n : ℝ) * (Cinc * Real.rpow B ε) := by simp
  have hraw := norm_lifetimeDeathMass_le_initial_add_sum_divisorMajorant hΛ n
  have hsplit :
      Real.rpow B (1 + ε) = B * Real.rpow B ε := by
    have hB1 : Real.rpow B 1 = B := by
      exact Real.rpow_one B
    calc
      Real.rpow B (1 + ε) =
          Real.rpow B 1 * Real.rpow B ε :=
        Real.rpow_add hbasePos 1 ε
      _ = B * Real.rpow B ε := by
        rw [hB1]
  have htail :
      (n : ℝ) * (Cinc * Real.rpow B ε) ≤
        Cinc * Real.rpow B (1 + ε) := by
    have hn : (n : ℝ) ≤ B := by
      dsimp [B]
      exact_mod_cast Nat.le_succ n
    have hpnonneg : 0 ≤ Real.rpow B ε :=
      Real.rpow_nonneg (le_of_lt hbasePos) ε
    calc
      (n : ℝ) * (Cinc * Real.rpow B ε) =
          Cinc * ((n : ℝ) * Real.rpow B ε) := by ring
      _ ≤ Cinc * (B * Real.rpow B ε) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hn hpnonneg) hCinc
      _ = Cinc * Real.rpow B (1 + ε) := by rw [hsplit]
  have hRone : 1 ≤ Real.rpow B (1 + ε) :=
    Real.one_le_rpow hbase (by linarith)
  calc
    ‖lifetimeDeathMass Λ n‖ ≤ D0 +
        ∑ t ∈ Finset.range n, deathShellDivisorMajorant Λ t := by
      simpa [D0] using hraw
    _ ≤ D0 + (n : ℝ) * (Cinc * Real.rpow B ε) :=
      add_le_add_left hsum D0
    _ ≤ D0 * Real.rpow B (1 + ε) +
        Cinc * Real.rpow B (1 + ε) := by
      have hD0 : D0 ≤ D0 * Real.rpow B (1 + ε) := by
        calc
          D0 = D0 * 1 := by ring
          _ ≤ D0 * Real.rpow B (1 + ε) :=
            mul_le_mul_of_nonneg_left hRone (by dsimp [D0]; positivity)
      exact add_le_add hD0 htail
    _ = C * Real.rpow B (1 + ε) := by
      dsimp [C]
      ring

/-- The death process satisfies the repository's RH-scale translated local
energy statement unconditionally. -/
theorem lifetimeDeathUniformLocalBounded
    {Λ : ℝ} (hΛ : 0 < Λ) :
    LifetimeDeathUniformLocalBoundedStatement Λ := by
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  rcases norm_lifetimeDeathMass_le_rpow hΛ hδ with ⟨C, hC, hpoint⟩
  let K : ℝ := C ^ 2 * Real.rpow 2 (2 + 2 * δ)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (sq_nonneg C)
      (Real.rpow_nonneg (by norm_num) (2 + 2 * δ))
  refine ⟨K, hK, ?_⟩
  intro N H hH hHN
  have hN : 1 ≤ N := le_trans hH hHN
  have hNReal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  unfold RHLean.Analysis.localSequenceEnergy
  calc
    (∑ h ∈ Finset.range H, ‖lifetimeDeathMass Λ (N + h)‖ ^ 2) ≤
        ∑ _h ∈ Finset.range H,
          K * Real.rpow (N : ℝ) (2 + ε) := by
      apply Finset.sum_le_sum
      intro h hh
      have hhLt : h < H := Finset.mem_range.mp hh
      have hstage : N + h + 1 ≤ 2 * N := by omega
      have hpoint' := hpoint (N + h)
      have hstageReal :
          ((N + h + 1 : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
        exact_mod_cast hstage
      have hpowStage :
          Real.rpow ((N + h + 1 : ℕ) : ℝ) (1 + δ) ≤
            Real.rpow ((2 * N : ℕ) : ℝ) (1 + δ) :=
        Real.rpow_le_rpow (by positivity) hstageReal (by linarith)
      have hnorm :
          ‖lifetimeDeathMass Λ (N + h)‖ ≤
            C * Real.rpow ((2 * N : ℕ) : ℝ) (1 + δ) :=
        hpoint'.trans (mul_le_mul_of_nonneg_left hpowStage hC)
      have hupperNonneg :
          0 ≤ C * Real.rpow ((2 * N : ℕ) : ℝ) (1 + δ) :=
        mul_nonneg hC
          (Real.rpow_nonneg (by positivity) (1 + δ))
      have hsquare :
          ‖lifetimeDeathMass Λ (N + h)‖ ^ 2 ≤
            (C * Real.rpow ((2 * N : ℕ) : ℝ) (1 + δ)) ^ 2 := by
        nlinarith [norm_nonneg (lifetimeDeathMass Λ (N + h)), hupperNonneg]
      have hbase0 : 0 ≤ (((2 * N : ℕ) : ℝ)) := by positivity
      have hphase :
          (Real.rpow (((2 * N : ℕ) : ℝ)) (1 + δ)) ^ 2 =
            Real.rpow (((2 * N : ℕ) : ℝ)) (2 + 2 * δ) := by
        let X : ℝ := ((2 * N : ℕ) : ℝ)
        have hX0 : 0 ≤ X := by dsimp [X]; positivity
        calc
          (Real.rpow X (1 + δ)) ^ 2 =
              Real.rpow (Real.rpow X (1 + δ)) (2 : ℝ) := by
            exact (Real.rpow_natCast (Real.rpow X (1 + δ)) 2).symm
          _ = Real.rpow X ((1 + δ) * 2) := by
            exact (Real.rpow_mul hX0 (1 + δ) 2).symm
          _ = Real.rpow X (2 + 2 * δ) := by
            congr 1
            ring
      have htwoN :
          Real.rpow (((2 * N : ℕ) : ℝ)) (2 + 2 * δ) =
            Real.rpow 2 (2 + 2 * δ) *
              Real.rpow (N : ℝ) (2 + 2 * δ) := by
        have hcast : (((2 * N : ℕ) : ℝ)) = 2 * (N : ℝ) := by norm_num
        rw [hcast]
        exact Real.mul_rpow (by norm_num) (by positivity)
      have hexp : 2 + 2 * δ ≤ 2 + ε := by
        dsimp [δ]
        linarith
      have hpowN :
          Real.rpow (N : ℝ) (2 + 2 * δ) ≤
            Real.rpow (N : ℝ) (2 + ε) :=
        Real.rpow_le_rpow_of_exponent_le hNReal hexp
      have htwoNonneg : 0 ≤ Real.rpow 2 (2 + 2 * δ) :=
        Real.rpow_nonneg (by norm_num) (2 + 2 * δ)
      have hinner :
          Real.rpow 2 (2 + 2 * δ) * Real.rpow (N : ℝ) (2 + 2 * δ) ≤
            Real.rpow 2 (2 + 2 * δ) * Real.rpow (N : ℝ) (2 + ε) :=
        mul_le_mul_of_nonneg_left hpowN htwoNonneg
      calc
        ‖lifetimeDeathMass Λ (N + h)‖ ^ 2 ≤
            (C * Real.rpow ((2 * N : ℕ) : ℝ) (1 + δ)) ^ 2 := hsquare
        _ = C ^ 2 * Real.rpow ((2 * N : ℕ) : ℝ) (2 + 2 * δ) := by
          rw [mul_pow, hphase]
        _ = C ^ 2 *
            (Real.rpow 2 (2 + 2 * δ) *
              Real.rpow (N : ℝ) (2 + 2 * δ)) := by
          rw [htwoN]
        _ ≤ C ^ 2 *
            (Real.rpow 2 (2 + 2 * δ) *
              Real.rpow (N : ℝ) (2 + ε)) :=
          mul_le_mul_of_nonneg_left hinner (sq_nonneg C)
        _ = K * Real.rpow (N : ℝ) (2 + ε) := by
          dsimp [K]
          ring
    _ = (H : ℝ) * (K * Real.rpow (N : ℝ) (2 + ε)) := by simp
    _ = K * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) := by ring

/-- The endpoint criterion now has only one open analytic premise: the survivor
birth-minus-death discrepancy. -/
theorem lifetimeEndpointUniformLocalBounded_iff_discrepancy
    {Λ : ℝ} (hΛ : 0 < Λ) :
    LifetimeEndpointUniformLocalBoundedStatement Λ ↔
      LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, lifetimeDeathUniformLocalBounded hΛ⟩

/-- Unconditional death-process control removes that premise from the protected
square-prefix criterion. -/
theorem lifetimeEndpointDiscrepancy_implies_squarePrefixUniformLocal
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hdiscrepancy : LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ) :
    RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement := by
  apply lifetimeEndpointUniformLocalBounded_implies_squarePrefixUniformLocal Λ
  exact (lifetimeEndpointUniformLocalBounded_iff_discrepancy hΛ).2 hdiscrepancy

/-- Terminal consequence: after the unconditional death-process estimate, the
survivor discrepancy is the sole lifetime-flow analytic input to RH. -/
theorem lifetimeEndpointDiscrepancy_implies_riemannHypothesis
    {Λ : ℝ} (hΛ : 0 < Λ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion)
    (hdiscrepancy : LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ) :
    RHLean.Analysis.RiemannHypothesisStatement := by
  apply lifetimeEndpointUniformLocalBounded_implies_riemannHypothesis Λ criterion
  exact (lifetimeEndpointUniformLocalBounded_iff_discrepancy hΛ).2 hdiscrepancy

end RHLean.Proof
