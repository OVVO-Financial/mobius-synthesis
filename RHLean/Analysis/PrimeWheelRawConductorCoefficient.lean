import Mathlib
import RHLean.Analysis.PrimeWheelRamanujanBoundaryReduction
import RHLean.Analysis.PrimeWheelRawUnitOrbit

/-!
# Eliminate the common raw conductor-shell Fourier coefficient

The Ramanujan boundary reduction leaves one non-arithmetic scalar on each
occupied conductor shell: the common value of the actual periodic raw DFT.
This file eliminates that scalar exactly.

Each local square-sensitive comb has the finite divisor expansion

`u_p(n) = 1 - 2 * 1_(p | n) + 1_(p^2 | n)`.

Expanding the product over the selected primes gives a finite sum indexed by
choices of exponents `0,1,2`.  For one expansion divisor `d`, the complete
additive-character sum over the multiples of `d` in `ZMod N` is `N / d` exactly
when the additive order of the frequency divides `d`, and is zero otherwise.
Therefore the raw DFT coefficient is a finite arithmetic divisor-tail sum.
No CRT dual-frequency choice, Fourier estimate, or norm inequality is needed.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- One exponent `0`, `1`, or `2` for every selected prime coordinate. -/
abbrev PrimeWheelRawExpansionPoint (S : Finset ℕ) :=
  ∀ _p : {p // p ∈ S}, Fin 3

/-- Local coefficient in the three-term divisor expansion of one prime comb. -/
def localPrimeCombExpansionWeight (e : Fin 3) : ℂ :=
  if e.val = 1 then -2 else 1

/-- Divisor selected by one exponent assignment. -/
def primeWheelRawExpansionDivisor
    (S : Finset ℕ) (e : PrimeWheelRawExpansionPoint S) : ℕ :=
  ∏ p : {p // p ∈ S}, p.val ^ (e p).val

/-- Product of the local coefficients selected by one exponent assignment. -/
def primeWheelRawExpansionWeight
    (S : Finset ℕ) (e : PrimeWheelRawExpansionPoint S) : ℂ :=
  ∏ p : {p // p ∈ S}, localPrimeCombExpansionWeight (e p)

/-- Purely arithmetic value of the complete raw DFT on additive conductor `q`.
The only operations are finite products, divisibility tests, and natural
quotients. -/
def primeWheelRawConductorArithmeticCoefficient
    (S : Finset ℕ) (N q : ℕ) : ℂ :=
  -∑ e : PrimeWheelRawExpansionPoint S,
    primeWheelRawExpansionWeight S e *
      (if q ∣ primeWheelRawExpansionDivisor S e then
        (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ))
      else 0)

/-- Primorial specialization of the arithmetic raw conductor coefficient. -/
def primorialRawConductorArithmeticCoefficient (k q : ℕ) : ℂ :=
  primeWheelRawConductorArithmeticCoefficient
    (primorialWheelPrimes k) (primorialMinimalWheelSystem k).modulus q

/-- The three local expansion choices reproduce the local square-sensitive comb
exactly after casting to `ℂ`. -/
private theorem localPrimeComb_cast_eq_expansion (p n : ℕ) :
    (((localPrimeComb p n : ℤ) : ℂ)) =
      ∑ e : Fin 3,
        localPrimeCombExpansionWeight e *
          (if p ^ e.val ∣ n then (1 : ℂ) else 0) := by
  by_cases hsq : p ^ 2 ∣ n
  · have hp : p ∣ n := dvd_trans (dvd_pow_self p (by norm_num)) hsq
    simp [localPrimeComb, localPrimeCombExpansionWeight,
      Fin.sum_univ_succ, hp, hsq]
    norm_num
  · by_cases hp : p ∣ n
    · simp [localPrimeComb, localPrimeCombExpansionWeight,
        Fin.sum_univ_succ, hp, hsq]
      norm_num
    · simp [localPrimeComb, localPrimeCombExpansionWeight,
        Fin.sum_univ_succ, hp, hsq]

/-- Distinct prime-power factors selected by an expansion point are pairwise
relatively prime in the natural-number monoid. -/
private theorem rawExpansionFactors_pairwise_isRelPrime
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (e : PrimeWheelRawExpansionPoint S) :
    Pairwise
      (Function.onFun IsRelPrime
        (fun p : {p // p ∈ S} => p.val ^ (e p).val)) := by
  intro p q hpq
  have hpne : p.val ≠ q.val := by
    intro h
    apply hpq
    exact Subtype.ext h
  exact Nat.coprime_iff_isRelPrime.mp
    (Nat.coprime_pow_primes (e p).val (e q).val
      (hprime p.val p.property) (hprime q.val q.property) hpne)

/-- The product expansion divisor divides `n` iff every selected local prime
power divides `n`. -/
private theorem rawExpansionDivisor_dvd_iff
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (e : PrimeWheelRawExpansionPoint S) (n : ℕ) :
    primeWheelRawExpansionDivisor S e ∣ n ↔
      ∀ p : {p // p ∈ S}, p.val ^ (e p).val ∣ n := by
  constructor
  · intro h p
    apply dvd_trans _ h
    unfold primeWheelRawExpansionDivisor
    exact Finset.dvd_prod_of_mem
      (fun q : {q // q ∈ S} => q.val ^ (e q).val)
      (Finset.mem_univ p)
  · intro h
    unfold primeWheelRawExpansionDivisor
    exact Fintype.prod_dvd_of_isRelPrime
      (rawExpansionFactors_pairwise_isRelPrime S hprime e) h

/-- If every local square period divides an ambient modulus, then every divisor
appearing in the finite prime-comb expansion also divides that modulus. -/
private theorem rawExpansionDivisor_dvd_modulus
    {N : ℕ} (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hperiod : ∀ p ∈ S, p ^ 2 ∣ N)
    (e : PrimeWheelRawExpansionPoint S) :
    primeWheelRawExpansionDivisor S e ∣ N := by
  unfold primeWheelRawExpansionDivisor
  apply Fintype.prod_dvd_of_isRelPrime
    (rawExpansionFactors_pairwise_isRelPrime S hprime e)
  intro p
  have he : (e p).val ≤ 2 := by omega
  have hpow : p.val ^ (e p).val ∣ p.val ^ 2 :=
    (Nat.pow_dvd_pow_iff_le_right (hprime p.val p.property).one_lt).mpr he
  exact dvd_trans hpow (hperiod p.val p.property)

/-- The complete seeded comb is exactly the finite expansion over simultaneous
prime-power divisibility conditions. -/
private theorem seededPrimeComb_cast_eq_rawExpansion
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (n : ℕ) :
    (((seededPrimeComb S n : ℤ) : ℂ)) =
      -∑ e : PrimeWheelRawExpansionPoint S,
        primeWheelRawExpansionWeight S e *
          (if primeWheelRawExpansionDivisor S e ∣ n then (1 : ℂ) else 0) := by
  classical
  unfold seededPrimeComb
  push_cast
  rw [← Finset.prod_coe_sort S
    (fun p : ℕ => (((localPrimeComb p n : ℤ) : ℂ)))]
  apply congrArg Neg.neg
  calc
    (∏ p : {p // p ∈ S}, (((localPrimeComb p.val n : ℤ) : ℂ))) =
      ∏ p : {p // p ∈ S},
        ∑ j : Fin 3,
          localPrimeCombExpansionWeight j *
            (if p.val ^ j.val ∣ n then (1 : ℂ) else 0) := by
              apply Fintype.prod_congr
              intro p
              exact localPrimeComb_cast_eq_expansion p.val n
    _ =
      ∑ e : PrimeWheelRawExpansionPoint S,
        ∏ p : {p // p ∈ S},
          (localPrimeCombExpansionWeight (e p) *
            (if p.val ^ (e p).val ∣ n then (1 : ℂ) else 0)) := by
              simpa using
                (Finset.prod_univ_sum
                  (t := fun _p : {p // p ∈ S} =>
                    (Finset.univ : Finset (Fin 3)))
                  (f := fun p j =>
                    localPrimeCombExpansionWeight j *
                      (if p.val ^ j.val ∣ n then (1 : ℂ) else 0)))
    _ =
      ∑ e : PrimeWheelRawExpansionPoint S,
        primeWheelRawExpansionWeight S e *
          (if primeWheelRawExpansionDivisor S e ∣ n then (1 : ℂ) else 0) := by
            apply Fintype.sum_congr
            intro e
            unfold primeWheelRawExpansionWeight
            rw [Finset.prod_mul_distrib]
            have hiff := rawExpansionDivisor_dvd_iff S hprime e n
            rw [Fintype.prod_boole]
            by_cases hdiv : primeWheelRawExpansionDivisor S e ∣ n
            · have hall :
                  ∀ p : {p // p ∈ S}, p.val ^ (e p).val ∣ n :=
                hiff.mp hdiv
              rw [if_pos hall, if_pos hdiv]
            · have hall :
                  ¬∀ p : {p // p ∈ S}, p.val ^ (e p).val ∣ n :=
                fun h => hdiv (hiff.mpr h)
              rw [if_neg hall, if_neg hdiv]

/-- Canonical least-representative equivalence used to reindex complete
character sums. -/
private def finNatCastEquivZModRawCoefficient
    (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun i := (i.val : ZMod N)
  invFun z := ⟨z.val, ZMod.val_lt z⟩
  left_inv i := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt
  right_inv z := ZMod.natCast_zmod_val z

/-- The multiples of a divisor `d | N` in the canonical range are exactly the
first `N / d` multiples of `d`. -/
private theorem rawMultiplesBelow_eq_image
    {N d : ℕ} (hd : d ∣ N) (hN : 0 < N) :
    (Finset.range N).filter (fun n => d ∣ n) =
      (Finset.range (N / d)).image (fun a => d * a) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hN
  have hprod : d * (N / d) = N := Nat.mul_div_cancel' hd
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hnlt, hdiv⟩
    rcases hdiv with ⟨a, rfl⟩
    have ha : a < N / d := by
      nlinarith
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    constructor
    · nlinarith
    · exact ⟨a, rfl⟩

/-- Exact complete character sum on one physical divisor class. -/
private theorem rawDivisorCharacterSum
    {N d : ℕ} [NeZero N] (hd : d ∣ N) (r : ZMod N) :
    (∑ z : ZMod N,
      (if d ∣ z.val then (1 : ℂ) else 0) *
        ZMod.stdAddChar (-(z * r))) =
      if addOrderOf r ∣ d then (((N / d : ℕ) : ℂ)) else 0 := by
  classical
  have hN : 0 < N := Nat.pos_of_neZero N
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hN
  have hprod : d * (N / d) = N := Nat.mul_div_cancel' hd
  let F : ZMod N → ℂ := fun z =>
    (if d ∣ z.val then (1 : ℂ) else 0) *
      ZMod.stdAddChar (-(z * r))
  calc
    (∑ z : ZMod N,
      (if d ∣ z.val then (1 : ℂ) else 0) *
        ZMod.stdAddChar (-(z * r))) =
      ∑ i : Fin N, F (finNatCastEquivZModRawCoefficient N i) := by
        exact ((finNatCastEquivZModRawCoefficient N).sum_comp F).symm
    _ =
      ∑ i : Fin N,
        (if d ∣ i.val then (1 : ℂ) else 0) *
          ZMod.stdAddChar (-(((i.val : ℕ) : ZMod N) * r)) := by
            apply Finset.sum_congr rfl
            intro i hi
            dsimp [F, finNatCastEquivZModRawCoefficient]
            rw [ZMod.val_natCast_of_lt i.isLt]
    _ =
      ∑ n ∈ Finset.range N,
        (if d ∣ n then (1 : ℂ) else 0) *
          ZMod.stdAddChar (-(((n : ℕ) : ZMod N) * r)) := by
            exact Fin.sum_univ_eq_sum_range
              (fun n : ℕ =>
                (if d ∣ n then (1 : ℂ) else 0) *
                  ZMod.stdAddChar (-(((n : ℕ) : ZMod N) * r))) N
    _ =
      ∑ n ∈ (Finset.range N).filter (fun n => d ∣ n),
        ZMod.stdAddChar (-(((n : ℕ) : ZMod N) * r)) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n hn
          by_cases hdiv : d ∣ n
          · simp only [if_pos hdiv, one_mul]
          · simp only [if_neg hdiv, zero_mul]
    _ =
      ∑ a ∈ Finset.range (N / d),
        ZMod.stdAddChar (-((((d * a : ℕ) : ZMod N)) * r)) := by
          have hinj :
              Set.InjOn (fun a : ℕ => d * a)
                (Finset.range (N / d) : Set ℕ) := by
            intro a ha b hb hab
            exact Nat.eq_of_mul_eq_mul_left hdpos hab
          rw [rawMultiplesBelow_eq_image hd hN, Finset.sum_image hinj]
    _ = if addOrderOf r ∣ d then (((N / d : ℕ) : ℂ)) else 0 := by
      let b : ZMod N := -(((d : ℕ) : ZMod N) * r)
      have hgeom :
          (∑ a ∈ Finset.range (N / d),
            ZMod.stdAddChar (-((((d * a : ℕ) : ZMod N)) * r))) =
          ∑ a ∈ Finset.range (N / d), ZMod.stdAddChar b ^ a := by
        apply Finset.sum_congr rfl
        intro a ha
        have hpow := AddChar.map_nsmul_eq_pow
          (ZMod.stdAddChar : AddChar (ZMod N) ℂ) a b
        rw [← hpow]
        congr 1
        dsimp [b]
        simp [nsmul_eq_mul]
        ring
      rw [hgeom]
      by_cases hcond : addOrderOf r ∣ d
      · have hdr : d • r = 0 :=
          (addOrderOf_dvd_iff_nsmul_eq_zero).mp hcond
        have hb : b = 0 := by
          dsimp [b]
          have hmul : (((d : ℕ) : ZMod N) * r) = 0 := by
            simpa [nsmul_eq_mul] using hdr
          rw [hmul]
          simp
        rw [if_pos hcond]
        simp [hb]
      · have hdr : d • r ≠ 0 := by
          intro h
          exact hcond ((addOrderOf_dvd_iff_nsmul_eq_zero).mpr h)
        have hb : b ≠ 0 := by
          intro hb0
          apply hdr
          dsimp [b] at hb0
          have hmul : (((d : ℕ) : ZMod N) * r) = 0 := by
            exact neg_eq_zero.mp hb0
          simpa [nsmul_eq_mul] using hmul
        have hchar : ZMod.stdAddChar b ≠ 1 := by
          intro h
          have hzero : b = 0 :=
            ZMod.injective_stdAddChar (by simpa using h)
          exact hb hzero
        have hqsmul : (N / d) • b = 0 := by
          dsimp [b]
          simp only [nsmul_eq_mul]
          calc
            (((N / d : ℕ) : ZMod N) *
                (-(((d : ℕ) : ZMod N) * r))) =
              -(((((N / d) * d : ℕ) : ZMod N)) * r) := by
                push_cast
                ring
            _ = -((((N : ℕ) : ZMod N)) * r) := by
              rw [show (N / d) * d = N by simpa [Nat.mul_comm] using hprod]
            _ = 0 := by
              rw [ZMod.natCast_self]
              simp
        have hpow : ZMod.stdAddChar b ^ (N / d) = 1 := by
          calc
            ZMod.stdAddChar b ^ (N / d) =
                ZMod.stdAddChar ((N / d) • b) := by
              symm
              exact AddChar.map_nsmul_eq_pow
                (ZMod.stdAddChar : AddChar (ZMod N) ℂ) (N / d) b
            _ = 1 := by rw [hqsmul]; simp
        rw [if_neg hcond, geom_sum_eq hchar (N / d), hpow]
        simp

/-- On any modulus containing every local `p^2` period, the actual unnormalized
DFT of the seeded prime comb is exactly the arithmetic conductor coefficient. -/
theorem seededPrimeCombDFT_eq_rawConductorArithmeticCoefficient
    {N : ℕ} [NeZero N]
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hperiod : ∀ p ∈ S, p ^ 2 ∣ N)
    (r : ZMod N) :
    ZMod.dft
        (fun z : ZMod N => (((seededPrimeComb S z.val : ℤ) : ℂ))) r =
      primeWheelRawConductorArithmeticCoefficient S N (addOrderOf r) := by
  classical
  unfold primeWheelRawConductorArithmeticCoefficient
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  calc
    (∑ z : ZMod N,
      ZMod.stdAddChar (-(z * r)) *
        (((seededPrimeComb S z.val : ℤ) : ℂ))) =
      ∑ z : ZMod N,
        ZMod.stdAddChar (-(z * r)) *
          (-∑ e : PrimeWheelRawExpansionPoint S,
            primeWheelRawExpansionWeight S e *
              (if primeWheelRawExpansionDivisor S e ∣ z.val then
                (1 : ℂ) else 0)) := by
                  apply Finset.sum_congr rfl
                  intro z hz
                  rw [seededPrimeComb_cast_eq_rawExpansion S hprime z.val]
    _ =
      ∑ z : ZMod N,
        -(∑ e : PrimeWheelRawExpansionPoint S,
          primeWheelRawExpansionWeight S e *
            ((if primeWheelRawExpansionDivisor S e ∣ z.val then
              (1 : ℂ) else 0) * ZMod.stdAddChar (-(z * r)))) := by
                apply Finset.sum_congr rfl
                intro z hz
                calc
                  ZMod.stdAddChar (-(z * r)) *
                      (-∑ e : PrimeWheelRawExpansionPoint S,
                        primeWheelRawExpansionWeight S e *
                          (if primeWheelRawExpansionDivisor S e ∣ z.val then
                            (1 : ℂ) else 0)) =
                    -(ZMod.stdAddChar (-(z * r)) *
                      ∑ e : PrimeWheelRawExpansionPoint S,
                        primeWheelRawExpansionWeight S e *
                          (if primeWheelRawExpansionDivisor S e ∣ z.val then
                            (1 : ℂ) else 0)) := by ring
                  _ =
                    -(∑ e : PrimeWheelRawExpansionPoint S,
                      ZMod.stdAddChar (-(z * r)) *
                        (primeWheelRawExpansionWeight S e *
                          (if primeWheelRawExpansionDivisor S e ∣ z.val then
                            (1 : ℂ) else 0))) := by
                              rw [Finset.mul_sum]
                  _ =
                    -(∑ e : PrimeWheelRawExpansionPoint S,
                      primeWheelRawExpansionWeight S e *
                        ((if primeWheelRawExpansionDivisor S e ∣ z.val then
                          (1 : ℂ) else 0) *
                            ZMod.stdAddChar (-(z * r)))) := by
                              apply congrArg Neg.neg
                              apply Finset.sum_congr rfl
                              intro e he
                              ring
    _ =
      -∑ z : ZMod N,
        ∑ e : PrimeWheelRawExpansionPoint S,
          primeWheelRawExpansionWeight S e *
            ((if primeWheelRawExpansionDivisor S e ∣ z.val then
              (1 : ℂ) else 0) * ZMod.stdAddChar (-(z * r))) := by
                rw [Finset.sum_neg_distrib]
    _ =
      -∑ e : PrimeWheelRawExpansionPoint S,
        ∑ z : ZMod N,
          primeWheelRawExpansionWeight S e *
            ((if primeWheelRawExpansionDivisor S e ∣ z.val then
              (1 : ℂ) else 0) * ZMod.stdAddChar (-(z * r))) := by
                rw [Finset.sum_comm]
    _ =
      -∑ e : PrimeWheelRawExpansionPoint S,
        primeWheelRawExpansionWeight S e *
          (∑ z : ZMod N,
            (if primeWheelRawExpansionDivisor S e ∣ z.val then
              (1 : ℂ) else 0) * ZMod.stdAddChar (-(z * r))) := by
                apply congrArg Neg.neg
                apply Finset.sum_congr rfl
                intro e he
                rw [Finset.mul_sum]
    _ =
      -∑ e : PrimeWheelRawExpansionPoint S,
        primeWheelRawExpansionWeight S e *
          (if addOrderOf r ∣ primeWheelRawExpansionDivisor S e then
            (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ))
          else 0) := by
            apply congrArg Neg.neg
            apply Finset.sum_congr rfl
            intro e he
            rw [rawDivisorCharacterSum
              (rawExpansionDivisor_dvd_modulus S hprime hperiod e) r]

/-- The actual periodic raw spectrum is a conductor-only arithmetic function.
No representative frequency remains on the right-hand side. -/
theorem primorialPeriodicRawSpectrum_eq_rawConductorArithmeticCoefficient
    (k : ℕ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus) :
    primorialPeriodicRawSpectrum k r =
      primorialRawConductorArithmeticCoefficient k
        (reducedAdditiveConductor r) := by
  letI : NeZero (primorialMinimalTorusModulus k) :=
    ⟨Nat.ne_of_gt (primorialMinimalTorusModulus_pos k)⟩
  unfold primorialPeriodicRawSpectrum primorialPeriodicRawTorusField
    primorialRawConductorArithmeticCoefficient
  change
    ZMod.dft
        (fun z : ZMod (primorialMinimalWheelSystem k).modulus =>
          (((seededPrimeComb (primorialWheelPrimes k) z.val : ℤ) : ℂ))) r = _
  have h := seededPrimeCombDFT_eq_rawConductorArithmeticCoefficient
    (N := (primorialMinimalWheelSystem k).modulus)
    (S := primorialWheelPrimes k)
    (fun p hp => prime_of_mem_primesUpTo hp)
    (fun p hp => primorialPrimeSquare_dvd_minimalTorusModulus k p hp) r
  rw [← reducedAdditiveConductor_eq_addOrderOf
    (primorialMinimalWheelSystem k) r] at h
  exact h

/-- Final exact signed packet with the shell coefficient eliminated.  Every term
is now finite arithmetic data: the raw divisor-tail coefficient, Möbius weights,
and explicit divisor-residue boundary defects. -/
theorem primorialPeriodicRawJointConductorResponse_eq_arithmeticDivisorBoundary
    (k x q : ℕ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus)
    (hr : q = reducedAdditiveConductor r)
    (hq : 1 < q)
    (hx : x ≤ (primorialMinimalWheelSystem k).upper) :
    primorialPeriodicRawJointConductorResponse k x q =
      primorialRawConductorArithmeticCoefficient k q *
        (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
          (((∑ d ∈ q.divisors,
            μ (q / d) *
              divisorIntervalBoundary d 0
                (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ)) -
        2 *
          ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
            (((primeWheelSmoothBoundaryPacket
              (primorialMinimalWheelSystem k) x q : ℤ) : ℂ))) := by
  rw [primorialPeriodicRawJointConductorResponse_eq_divisorBoundary
    k x q r hr hq hx]
  rw [primorialPeriodicRawSpectrum_eq_rawConductorArithmeticCoefficient k r]
  rw [← hr]

end RHLean.Analysis