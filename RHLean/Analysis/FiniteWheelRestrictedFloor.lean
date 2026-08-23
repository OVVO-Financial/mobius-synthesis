import Mathlib
import RHLean.Analysis.FiniteWheelReciprocalMertensImprovement
import RHLean.Arithmetic.SignedBuchstabRecursion

/-!
# Restricted finite-wheel Möbius floor identity

This module proves the exact finite convolution behind the rough reciprocal
Möbius sum. A divisor survives precisely when it avoids every wheel prime;
the remaining divisor sum is the indicator that the ambient integer is smooth
with respect to the fixed finite prime set.

It also records the local one-prime mechanism used by the canonical frontier:
convolving the indicator of factors rough at `p` with Möbius restricted to
factors rough strictly above `p` leaves exactly the pure `p`-power channel.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- The convolution of wheel-rough Möbius with `1` is exactly the finite-wheel
smooth indicator. -/
theorem finiteWheelRoughMoebius_mul_zeta_apply
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (n : ℕ) :
    ((finiteWheelRoughMoebius P) * (ζ : ArithmeticFunction ℤ)) n =
      if n = 0 then 0 else if n.primeFactors ⊆ P then 1 else 0 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp [finiteWheelRoughMoebius]
  | prime_pow p k hp hk =>
      rw [ArithmeticFunction.coe_mul_zeta_apply,
        Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ']
      have hk0 : k ≠ 0 := Nat.ne_of_gt hk
      have hpow0 : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
      by_cases hpP : p ∈ P
      · have hpdvd : p ∣ primorialWheelProduct P :=
          (prime_dvd_primorialWheelProduct_iff hp hprime).2 hpP
        have hncp : ¬ Nat.Coprime p (primorialWheelProduct P) := by
          intro hcop
          exact (hp.coprime_iff_not_dvd.mp hcop) hpdvd
        have hsmooth : (p ^ k).primeFactors ⊆ P := by
          rw [Nat.primeFactors_pow p hk0]
          simpa [hp] using hpP
        rw [if_neg hpow0, if_pos hsmooth]
        simp [finiteWheelRoughMoebius, Nat.coprime_pow_left_iff, hncp]
      · have hpndvd : ¬ p ∣ primorialWheelProduct P := by
          exact fun h => hpP ((prime_dvd_primorialWheelProduct_iff hp hprime).1 h)
        have hpcop : Nat.Coprime p (primorialWheelProduct P) :=
          hp.coprime_iff_not_dvd.mpr hpndvd
        have hnSmooth : ¬ (p ^ k).primeFactors ⊆ P := by
          rw [Nat.primeFactors_pow p hk0]
          simpa [hp] using hpP
        rw [if_neg hpow0, if_neg hnSmooth]
        have hpowcop : ∀ j : ℕ, Nat.Coprime (p ^ j) (primorialWheelProduct P) :=
          fun j => hpcop.pow_left j
        simp_rw [finiteWheelRoughMoebius_apply, if_pos (hpowcop _)]
        have hsum :
            (∑ x ∈ Finset.range k, ArithmeticFunction.moebius (p ^ (x + 1))) = (-1 : ℤ) := by
          rw [Finset.sum_eq_single 0]
          · simpa using ArithmeticFunction.moebius_apply_prime hp
          · intro b hb hb0
            have hb1 : b + 1 ≠ 0 := by omega
            rw [ArithmeticFunction.moebius_apply_prime_pow hp hb1]
            simp [hb0]
          · intro hzero
            exact False.elim (hzero (Finset.mem_range.mpr hk))
        rw [hsum]
        norm_num
  | coprime a b ha hb hab haInd hbInd =>
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      have hmul : ArithmeticFunction.IsMultiplicative
          ((finiteWheelRoughMoebius P) * (ζ : ArithmeticFunction ℤ)) :=
        (finiteWheelRoughMoebius_isMultiplicative P).mul
          ArithmeticFunction.isMultiplicative_zeta.natCast
      rw [hmul.map_mul_of_coprime hab, haInd, hbInd]
      rw [Nat.primeFactors_mul ha0 hb0]
      simp only [Finset.union_subset_iff]
      by_cases haS : a.primeFactors ⊆ P <;>
        by_cases hbS : b.primeFactors ⊆ P <;> simp [ha0, hb0, haS, hbS]

/-- Divisor-level form of the local canonical-frontier convolution.  The first
factor is rough at the pivot (`>= p`), while the Möbius-weighted divisor is
rough strictly above the pivot (`> p`). -/
def roughGEMobiusGTConvolution (p n : ℕ) : ℤ :=
  ∑ c ∈ n.divisors,
    if RoughAbove p c ∧ RoughAbove (p - 1) (n / c) then
      ArithmeticFunction.moebius c
    else 0

/-- **Exact local one-prime mechanism.**  For prime `p`,
`1_{rough >= p} * (mu * 1_{rough > p})` leaves exactly the pure `p`-power
channel.  The right-hand side uses `primeFactors ⊆ {p}` as the finite exact
indicator of that channel (with the zero input separated explicitly). -/
theorem roughGE_convolution_roughGT_moebius_eq_primePowers
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    roughGEMobiusGTConvolution p n =
      if n = 0 then 0 else if n.primeFactors ⊆ ({p} : Finset ℕ) then 1 else 0 := by
  classical
  by_cases hn0 : n = 0
  · subst n
    simp [roughGEMobiusGTConvolution]
  by_cases hglobal : RoughAbove (p - 1) n
  · have hsum :
        roughGEMobiusGTConvolution p n =
          ((finiteWheelRoughMoebius ({p} : Finset ℕ)) *
            (ζ : ArithmeticFunction ℤ)) n := by
      unfold roughGEMobiusGTConvolution
      rw [ArithmeticFunction.coe_mul_zeta_apply]
      apply Finset.sum_congr rfl
      intro c hc
      have hcData := Nat.mem_divisors.mp hc
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hcpos : 0 < c := Nat.pos_of_dvd_of_pos hcData.1 hnpos
      have hc0 : c ≠ 0 := Nat.ne_of_gt hcpos
      have hcLe : c ≤ n := Nat.le_of_dvd hnpos hcData.1
      have hquot1 : 1 ≤ n / c := (Nat.one_le_div_iff hcpos).2 hcLe
      have hquot0 : n / c ≠ 0 := by omega
      have hprod : c * (n / c) = n := Nat.mul_div_cancel' hcData.1
      have hpf :
          n.primeFactors = c.primeFactors ∪ (n / c).primeFactors := by
        calc
          n.primeFactors = (c * (n / c)).primeFactors := by rw [hprod]
          _ = c.primeFactors ∪ (n / c).primeFactors :=
            Nat.primeFactors_mul hc0 hquot0
      have hcGE : RoughAbove (p - 1) c := by
        intro q hq
        apply hglobal q
        rw [hpf]
        exact Finset.mem_union_left _ hq
      have hquotGE : RoughAbove (p - 1) (n / c) := by
        intro q hq
        apply hglobal q
        rw [hpf]
        exact Finset.mem_union_right _ hq
      have hgtIff : RoughAbove p c ↔ ¬ p ∣ c := by
        constructor
        · intro hgt
          exact RoughAbove.not_dvd hp (by omega) hgt
        · intro hnd q hq
          have hge := hcGE q hq
          have hqdvd : q ∣ c := Nat.dvd_of_mem_primeFactors hq
          have hne : q ≠ p := by
            intro hqp
            subst q
            exact hnd hqdvd
          omega
      have hcopIff : Nat.Coprime c p ↔ ¬ p ∣ c := by
        simpa [Nat.coprime_comm] using (hp.coprime_iff_not_dvd (n := c))
      have hwheel : primorialWheelProduct ({p} : Finset ℕ) = p := by
        simp [primorialWheelProduct]
      rw [finiteWheelRoughMoebius_apply, hwheel]
      by_cases hgt : RoughAbove p c
      · have hcop : Nat.Coprime c p := hcopIff.2 (hgtIff.1 hgt)
        simp [hgt, hquotGE, hcop]
      · have hnotcop : ¬ Nat.Coprime c p := by
          intro hcop
          exact hgt (hgtIff.2 (hcopIff.1 hcop))
        simp [hgt, hquotGE, hnotcop]
    have hprimeSingleton : ∀ q ∈ ({p} : Finset ℕ), q.Prime := by
      intro q hq
      have hqp : q = p := Finset.mem_singleton.mp hq
      subst q
      exact hp
    rw [hsum, finiteWheelRoughMoebius_mul_zeta_apply
      ({p} : Finset ℕ) hprimeSingleton n]
  · have hzero : roughGEMobiusGTConvolution p n = 0 := by
      unfold roughGEMobiusGTConvolution
      apply Finset.sum_eq_zero
      intro c hc
      have hcData := Nat.mem_divisors.mp hc
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hcpos : 0 < c := Nat.pos_of_dvd_of_pos hcData.1 hnpos
      have hc0 : c ≠ 0 := Nat.ne_of_gt hcpos
      have hcLe : c ≤ n := Nat.le_of_dvd hnpos hcData.1
      have hquot1 : 1 ≤ n / c := (Nat.one_le_div_iff hcpos).2 hcLe
      have hquot0 : n / c ≠ 0 := by omega
      have hprod : c * (n / c) = n := Nat.mul_div_cancel' hcData.1
      have hpf :
          n.primeFactors = c.primeFactors ∪ (n / c).primeFactors := by
        calc
          n.primeFactors = (c * (n / c)).primeFactors := by rw [hprod]
          _ = c.primeFactors ∪ (n / c).primeFactors :=
            Nat.primeFactors_mul hc0 hquot0
      have hcond :
          ¬ (RoughAbove p c ∧ RoughAbove (p - 1) (n / c)) := by
        rintro ⟨hcGT, hquotGE⟩
        apply hglobal
        intro q hq
        rw [hpf] at hq
        rcases Finset.mem_union.mp hq with hqc | hqq
        · have := hcGT q hqc
          omega
        · exact hquotGE q hqq
      simp [hcond]
    have hnotSubset : ¬ n.primeFactors ⊆ ({p} : Finset ℕ) := by
      intro hs
      apply hglobal
      intro q hq
      have hqp : q = p := Finset.mem_singleton.mp (hs hq)
      subst q
      have hp2 := hp.two_le
      omega
    rw [hzero]
    simp [hn0, hnotSubset]

/-- Exact restricted floor identity: summing Möbius only over divisors coprime
to the wheel leaves exactly the number of wheel-smooth integers. -/
theorem finiteWheelRestrictedFloorIdentity
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (X : ℕ) (_hX : 1 ≤ X) :
    ∑ m ∈ finiteWheelCoprimeSet P X,
        (ArithmeticFunction.moebius m : ℤ) * ((X / m : ℕ) : ℤ) =
      (finiteWheelSmoothCount P X : ℤ) := by
  classical
  have hset : Finset.Icc 1 X = Finset.Ioc 0 X := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have key : ∀ d : ℕ,
      finiteWheelRoughMoebius P d * ((X / d : ℕ) : ℤ) =
        ∑ k ∈ Finset.Icc 1 X,
          if d ∣ k then finiteWheelRoughMoebius P d else 0 := by
    intro d
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, hset, Nat.Ioc_filter_dvd_card_eq_div]
    ring
  have hleft :
      (∑ m ∈ finiteWheelCoprimeSet P X,
        (ArithmeticFunction.moebius m : ℤ) * ((X / m : ℕ) : ℤ)) =
      ∑ d ∈ Finset.Icc 1 X,
        finiteWheelRoughMoebius P d * ((X / d : ℕ) : ℤ) := by
    unfold finiteWheelCoprimeSet
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _hd
    by_cases hcop : Nat.Coprime d (primorialWheelProduct P)
    · simp [finiteWheelRoughMoebius]
    · simp [finiteWheelRoughMoebius]
  rw [hleft]
  calc
    ∑ d ∈ Finset.Icc 1 X,
        finiteWheelRoughMoebius P d * ((X / d : ℕ) : ℤ) =
      ∑ d ∈ Finset.Icc 1 X, ∑ k ∈ Finset.Icc 1 X,
        if d ∣ k then finiteWheelRoughMoebius P d else 0 :=
      Finset.sum_congr rfl (fun d _ => key d)
    _ = ∑ k ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 X,
        if d ∣ k then finiteWheelRoughMoebius P d else 0 := Finset.sum_comm
    _ = ∑ k ∈ Finset.Icc 1 X,
        ∑ d ∈ k.divisors, finiteWheelRoughMoebius P d := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hkIcc := Finset.mem_Icc.mp hk
      have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hkIcc.1
      rw [← Finset.sum_filter]
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd1, hdX⟩, hdvd⟩
        exact ⟨hdvd, Nat.ne_of_gt hkpos⟩
      · rintro ⟨hdvd, _hk0⟩
        have hd_le : d ≤ k := Nat.le_of_dvd hkpos hdvd
        have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hkpos
        exact ⟨⟨hd_pos, hd_le.trans hkIcc.2⟩, hdvd⟩
    _ = ∑ k ∈ Finset.Icc 1 X,
        (if k.primeFactors ⊆ P then (1 : ℤ) else 0) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hkIcc := Finset.mem_Icc.mp hk
      have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hkIcc.1
      have hk0 : k ≠ 0 := Nat.ne_of_gt hkpos
      rw [← ArithmeticFunction.coe_mul_zeta_apply,
        finiteWheelRoughMoebius_mul_zeta_apply P hprime k]
      rw [if_neg hk0]
    _ = (finiteWheelSmoothCount P X : ℤ) := by
      unfold finiteWheelSmoothCount finiteWheelSmoothSet
      simp

/-- The restricted floor certificate exists for every genuine finite prime
wheel. -/
def finiteWheelRestrictedFloorCertificate
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    FiniteWheelRestrictedFloorCertificate P where
  floor_identity := finiteWheelRestrictedFloorIdentity P hprime

end RHLean.Analysis
