import Mathlib
import RHLean.Analysis.PrimeWheelCompleteSpectrum

/-!
# Explicit local spectrum of one square-sensitive prime comb

The complete CRT spectrum already factors into local `p^2` transforms, but the
local transform was previously left as a finite sum.  This file evaluates that
sum exactly, in the same unnormalized DFT convention used by `ZMod.dft`.

For a prime `p`, the local coefficient is

* `(p - 1)^2` at frequency zero;
* `1 - 2p` at a nonzero frequency divisible by `p`;
* `1` at a frequency not divisible by `p`.

No estimate is used.  The proof is finite additive-character orthogonality plus
an exact reindexing of the multiples of `p` below `p^2`.
-/

open scoped BigOperators
open AddChar

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Public indicator expansion of the local square-sensitive comb. -/
theorem localPrimeComb_eq_indicator_formula (p n : ℕ) :
    localPrimeComb p n =
      1 - 2 * (if p ∣ n then 1 else 0) +
        (if p ^ 2 ∣ n then 1 else 0) := by
  unfold localPrimeComb
  by_cases hsq : p ^ 2 ∣ n
  · have hp : p ∣ n := dvd_trans (dvd_pow_self p (by norm_num)) hsq
    simp [hsq, hp]
  · by_cases hp : p ∣ n
    · simp [hsq, hp]
    · simp [hsq, hp]

/-- The local `p^2` transform with its frequency represented directly in
`ZMod (p^2)`.  This is the same unnormalized transform as
`localPrimeCombCRTSpectrum`, with a more convenient frequency type. -/
def localPrimeCombNaturalSpectrum
    (p : ℕ) (hp : Nat.Prime p) (r : ZMod (p ^ 2)) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ x : Fin (p ^ 2),
    (((localPrimeComb p x.val : ℤ) : ℂ)) *
      ZMod.stdAddChar
        (-(((x.val : ℕ) : ZMod (p ^ 2)) * r))

/-- Canonical least-representative equivalence used to reindex finite character
sums between `Fin N` and `ZMod N`. -/
private def finNatCastEquivZMod (n : ℕ) [NeZero n] : Fin n ≃ ZMod n where
  toFun i := (i.val : ZMod n)
  invFun z := ⟨z.val, ZMod.val_lt z⟩
  left_inv i := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt
  right_inv z := ZMod.natCast_zmod_val z

/-- Complete additive-character sum on the local `p^2` torus, written over
least representatives.  The definition hides the `NeZero (p^2)` instance so
later theorem statements do not depend on typeclass synthesis from primality. -/
private def localFullRangeCharacterSum
    (p : ℕ) (hp : Nat.Prime p) (r : ZMod (p ^ 2)) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ n ∈ Finset.range (p ^ 2),
    ZMod.stdAddChar
      (-(((n : ℕ) : ZMod (p ^ 2)) * r))

/-- Complete additive-character orthogonality on the local `p^2` torus. -/
private theorem localFullRangeCharacterSum_eq
    (p : ℕ) (hp : Nat.Prime p) (r : ZMod (p ^ 2)) :
    localFullRangeCharacterSum p hp r =
      if r = 0 then (((p ^ 2 : ℕ) : ℂ)) else 0 := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let F : ZMod (p ^ 2) → ℂ := fun z =>
    ZMod.stdAddChar (z * (-r))
  have horth :
      (∑ z : ZMod (p ^ 2), F z) =
        if r = 0 then (((p ^ 2 : ℕ) : ℂ)) else 0 := by
    have h := AddChar.sum_mulShift
      (-r) (ZMod.isPrimitive_stdAddChar (p ^ 2))
    simpa [F, ZMod.card] using h
  unfold localFullRangeCharacterSum
  calc
    (∑ n ∈ Finset.range (p ^ 2),
        ZMod.stdAddChar
          (-(((n : ℕ) : ZMod (p ^ 2)) * r))) =
      ∑ x : Fin (p ^ 2),
        ZMod.stdAddChar
          (-(((x.val : ℕ) : ZMod (p ^ 2)) * r)) := by
            symm
            exact Fin.sum_univ_eq_sum_range
              (fun n : ℕ =>
                ZMod.stdAddChar
                  (-(((n : ℕ) : ZMod (p ^ 2)) * r)))
              (p ^ 2)
    _ = ∑ x : Fin (p ^ 2), F (finNatCastEquivZMod (p ^ 2) x) := by
      apply Finset.sum_congr rfl
      intro x hx
      change
        ZMod.stdAddChar
            (-(((x.val : ℕ) : ZMod (p ^ 2)) * r)) =
          ZMod.stdAddChar
            (((x.val : ℕ) : ZMod (p ^ 2)) * (-r))
      congr 1
      ring
    _ = ∑ z : ZMod (p ^ 2), F z :=
      (finNatCastEquivZMod (p ^ 2)).sum_comp F
    _ = if r = 0 then (((p ^ 2 : ℕ) : ℂ)) else 0 := horth

/-- Multiplication by `p` kills a local frequency modulo `p^2` exactly when the
least representative of that frequency is divisible by `p`. -/
private theorem primeMulFrequency_eq_zero_iff
    (p : ℕ) (hp : Nat.Prime p) (r : ZMod (p ^ 2)) :
    (((p : ℕ) : ZMod (p ^ 2)) * r = 0) ↔ p ∣ r.val := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  constructor
  · intro h
    have hcast :
        (((p * r.val : ℕ) : ZMod (p ^ 2))) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      exact h
    have hdvd : p ^ 2 ∣ p * r.val :=
      (ZMod.natCast_eq_zero_iff (p * r.val) (p ^ 2)).mp hcast
    have hmul : p * p ∣ p * r.val := by
      simpa [pow_two] using hdvd
    exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hmul
  · intro hdvd
    have hmul : p * p ∣ p * r.val :=
      (Nat.mul_dvd_mul_iff_left hp.pos).mpr hdvd
    have hsq : p ^ 2 ∣ p * r.val := by
      simpa [pow_two] using hmul
    have hcast :
        (((p * r.val : ℕ) : ZMod (p ^ 2))) = 0 :=
      (ZMod.natCast_eq_zero_iff (p * r.val) (p ^ 2)).mpr hsq
    calc
      (((p : ℕ) : ZMod (p ^ 2)) * r) =
          (((p : ℕ) : ZMod (p ^ 2)) *
            ((r.val : ℕ) : ZMod (p ^ 2))) := by
              rw [ZMod.natCast_zmod_val]
      _ = (((p * r.val : ℕ) : ZMod (p ^ 2))) := by
            rw [Nat.cast_mul]
      _ = 0 := hcast

/-- The natural numbers below `p^2` divisible by `p` are exactly
`0,p,2p,...,(p-1)p`. -/
private theorem multiplesPrimeBelowSquare_eq_image
    (p : ℕ) (hp : Nat.Prime p) :
    (Finset.range (p ^ 2)).filter (fun n => p ∣ n) =
      (Finset.range p).image (fun a => p * a) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hnlt, hdvd⟩
    rcases hdvd with ⟨a, rfl⟩
    have ha : a < p := by
      nlinarith [hp.pos]
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    constructor
    · nlinarith [hp.pos]
    · exact ⟨a, rfl⟩

/-- Character sum over the multiples of `p` in one complete `p^2` period. -/
private def localPrimeMultipleCharacterSum
    (p : ℕ) (hp : Nat.Prime p) (r : ZMod (p ^ 2)) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ n ∈ (Finset.range (p ^ 2)).filter (fun n => p ∣ n),
    ZMod.stdAddChar
      (-(((n : ℕ) : ZMod (p ^ 2)) * r))

/-- Exact orthogonality of the local `p`-multiple slice. -/
private theorem localPrimeMultipleCharacterSum_eq
    (p : ℕ) (hp : Nat.Prime p) (r : ZMod (p ^ 2)) :
    localPrimeMultipleCharacterSum p hp r =
      if p ∣ r.val then (p : ℂ) else 0 := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let b : ZMod (p ^ 2) :=
    -(((p : ℕ) : ZMod (p ^ 2)) * r)
  have hinj : Set.InjOn (fun a : ℕ => p * a) (Finset.range p : Set ℕ) := by
    intro a ha c hc hac
    exact Nat.eq_of_mul_eq_mul_left hp.pos hac
  have hreindex :
      localPrimeMultipleCharacterSum p hp r =
        ∑ a ∈ Finset.range p,
          ZMod.stdAddChar b ^ a := by
    unfold localPrimeMultipleCharacterSum
    rw [multiplesPrimeBelowSquare_eq_image p hp, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro a ha
    have hpow := AddChar.map_nsmul_eq_pow
      (ZMod.stdAddChar : AddChar (ZMod (p ^ 2)) ℂ) a b
    rw [← hpow]
    congr 1
    change
      -((((p * a : ℕ) : ZMod (p ^ 2))) * r) =
        a • b
    dsimp [b]
    simp [nsmul_eq_mul]
    ring
  rw [hreindex]
  by_cases hdiv : p ∣ r.val
  · have hmul : (((p : ℕ) : ZMod (p ^ 2)) * r) = 0 :=
      (primeMulFrequency_eq_zero_iff p hp r).mpr hdiv
    have hb : b = 0 := by
      dsimp [b]
      rw [hmul]
      simp
    rw [if_pos hdiv]
    simp [hb]
  · have hmul : (((p : ℕ) : ZMod (p ^ 2)) * r) ≠ 0 := by
      intro h
      exact hdiv ((primeMulFrequency_eq_zero_iff p hp r).mp h)
    have hb : b ≠ 0 := by
      dsimp [b]
      simpa using hmul
    have hchar : ZMod.stdAddChar b ≠ 1 := by
      intro h
      have hzero : b = 0 :=
        ZMod.injective_stdAddChar (by simpa using h)
      exact hb hzero
    have hbsmul : p • b = 0 := by
      dsimp [b]
      simp only [nsmul_eq_mul]
      calc
        ((p : ℕ) : ZMod (p ^ 2)) *
            (-(((p : ℕ) : ZMod (p ^ 2)) * r)) =
          -((((p ^ 2 : ℕ) : ZMod (p ^ 2))) * r) := by
            push_cast
            ring
        _ = 0 := by
          rw [ZMod.natCast_self]
          simp
    have hpow : ZMod.stdAddChar b ^ p = 1 := by
      calc
        ZMod.stdAddChar b ^ p = ZMod.stdAddChar (p • b) := by
          symm
          exact AddChar.map_nsmul_eq_pow
            (ZMod.stdAddChar : AddChar (ZMod (p ^ 2)) ℂ) p b
        _ = ZMod.stdAddChar 0 := by rw [hbsmul]
        _ = 1 := AddChar.map_zero_eq_one _
    rw [if_neg hdiv, geom_sum_eq hchar p, hpow]
    simp

/-- Within `0 <= n < p^2`, the only multiple of `p^2` is zero. -/
private theorem squareMultiplesBelowSquare_eq_singleton
    (p : ℕ) (hp : Nat.Prime p) :
    (Finset.range (p ^ 2)).filter (fun n => p ^ 2 ∣ n) = {0} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hnlt, hdvd⟩
    by_contra hn0
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
    omega
  · intro hn
    subst n
    exact ⟨pow_pos hp.pos 2, dvd_zero _⟩

/-- The square-multiple indicator character sum. -/
private def localSquareMultipleCharacterSum
    (p : ℕ) (hp : Nat.Prime p) (r : ZMod (p ^ 2)) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ n ∈ Finset.range (p ^ 2),
    if p ^ 2 ∣ n then
      ZMod.stdAddChar
        (-(((n : ℕ) : ZMod (p ^ 2)) * r))
    else 0

/-- The square-multiple indicator contributes exactly the zero residue. -/
private theorem localSquareMultipleCharacterSum_eq_one
    (p : ℕ) (hp : Nat.Prime p) (r : ZMod (p ^ 2)) :
    localSquareMultipleCharacterSum p hp r = 1 := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  unfold localSquareMultipleCharacterSum
  rw [← Finset.sum_filter,
    squareMultiplesBelowSquare_eq_singleton p hp]
  simp

/-- Range-form `p`-multiple character sum, with the additive-character instance
hidden in the definition. -/
private def localPrimeMultipleCharacterIteSum
    (p : ℕ) (hp : Nat.Prime p) (r : ZMod (p ^ 2)) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ n ∈ Finset.range (p ^ 2),
    if p ∣ n then
      ZMod.stdAddChar
        (-(((n : ℕ) : ZMod (p ^ 2)) * r))
    else 0

/-- Range form of the `p`-multiple character orthogonality identity. -/
private theorem localPrimeMultipleCharacterIteSum_eq
    (p : ℕ) (hp : Nat.Prime p) (r : ZMod (p ^ 2)) :
    localPrimeMultipleCharacterIteSum p hp r =
      if p ∣ r.val then (p : ℂ) else 0 := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have h := localPrimeMultipleCharacterSum_eq p hp r
  unfold localPrimeMultipleCharacterSum at h
  unfold localPrimeMultipleCharacterIteSum
  rw [Finset.sum_filter] at h
  exact h

/-- Exact unnormalized local Fourier trichotomy. -/
theorem localPrimeCombNaturalSpectrum_eq_explicit
    (p : ℕ) (hp : Nat.Prime p) (r : ZMod (p ^ 2)) :
    localPrimeCombNaturalSpectrum p hp r =
      if r = 0 then (((p - 1) ^ 2 : ℕ) : ℂ)
      else if p ∣ r.val then 1 - 2 * (p : ℂ)
      else 1 := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let χ : ℕ → ℂ := fun n =>
    ZMod.stdAddChar
      (-(((n : ℕ) : ZMod (p ^ 2)) * r))
  have hfull := localFullRangeCharacterSum_eq p hp r
  have hprime := localPrimeMultipleCharacterIteSum_eq p hp r
  have hsquare := localSquareMultipleCharacterSum_eq_one p hp r
  unfold localPrimeCombNaturalSpectrum
  calc
    (∑ x : Fin (p ^ 2),
        (((localPrimeComb p x.val : ℤ) : ℂ)) *
          ZMod.stdAddChar
            (-(((x.val : ℕ) : ZMod (p ^ 2)) * r))) =
      ∑ n ∈ Finset.range (p ^ 2),
        (((localPrimeComb p n : ℤ) : ℂ)) *
          ZMod.stdAddChar
            (-(((n : ℕ) : ZMod (p ^ 2)) * r)) := by
              exact Fin.sum_univ_eq_sum_range
                (fun n : ℕ =>
                  (((localPrimeComb p n : ℤ) : ℂ)) *
                    ZMod.stdAddChar
                      (-(((n : ℕ) : ZMod (p ^ 2)) * r)))
                (p ^ 2)
    _ =
      ∑ n ∈ Finset.range (p ^ 2),
        (((localPrimeComb p n : ℤ) : ℂ)) * χ n := by
          rfl
    _ =
      ∑ n ∈ Finset.range (p ^ 2),
        (χ n - 2 * (if p ∣ n then χ n else 0) +
          (if p ^ 2 ∣ n then χ n else 0)) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [localPrimeComb_eq_indicator_formula]
            by_cases hpdiv : p ∣ n <;>
              by_cases hsqdiv : p ^ 2 ∣ n <;>
                simp [hpdiv, hsqdiv]
            <;> ring
    _ =
      (∑ n ∈ Finset.range (p ^ 2), χ n) -
        2 * (∑ n ∈ Finset.range (p ^ 2),
          if p ∣ n then χ n else 0) +
        (∑ n ∈ Finset.range (p ^ 2),
          if p ^ 2 ∣ n then χ n else 0) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [← Finset.mul_sum]
    _ =
      localFullRangeCharacterSum p hp r -
        2 * localPrimeMultipleCharacterIteSum p hp r +
        localSquareMultipleCharacterSum p hp r := by
          rfl
    _ =
      (if r = 0 then (((p ^ 2 : ℕ) : ℂ)) else 0) -
        2 * (if p ∣ r.val then (p : ℂ) else 0) + 1 := by
            rw [hfull, hprime, hsquare]
    _ =
      if r = 0 then (((p - 1) ^ 2 : ℕ) : ℂ)
      else if p ∣ r.val then 1 - 2 * (p : ℂ)
      else 1 := by
        by_cases hr : r = 0
        · subst r
          simp
          push_cast [Nat.cast_sub hp.one_le]
          ring
        · by_cases hdiv : p ∣ r.val
          · simp [hr, hdiv]
            ring
          · simp [hr, hdiv]

/-- The existing CRT-local coefficient is exactly the explicit local
trichotomy above. -/
theorem localPrimeCombCRTSpectrum_eq_explicit
    (p : ℕ) (hp : Nat.Prime p) (s : Fin (p ^ 2)) :
    localPrimeCombCRTSpectrum p hp s =
      if s.val = 0 then (((p - 1) ^ 2 : ℕ) : ℂ)
      else if p ∣ s.val then 1 - 2 * (p : ℂ)
      else 1 := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let r : ZMod (p ^ 2) := (s.val : ZMod (p ^ 2))
  have hbridge :
      localPrimeCombNaturalSpectrum p hp r =
        localPrimeCombCRTSpectrum p hp s := by
    unfold localPrimeCombNaturalSpectrum localPrimeCombCRTSpectrum
    rfl
  have hzero : r = 0 ↔ s.val = 0 := by
    dsimp [r]
    have h := (ZMod.val_eq_zero ((s.val : ℕ) : ZMod (p ^ 2))).symm
    simpa [ZMod.val_natCast_of_lt s.isLt] using h
  have hval : r.val = s.val := by
    dsimp [r]
    exact ZMod.val_natCast_of_lt s.isLt
  rw [← hbridge, localPrimeCombNaturalSpectrum_eq_explicit p hp r]
  simp only [hzero, hval]

/-- Local spectral type: zero mode, nonzero frequency divisible by `p`, or a
frequency prime to `p`. -/
def localPrimeSpectrumType
    (p : ℕ) (r : ZMod (p ^ 2)) : ℕ :=
  if r = 0 then 1 else if p ∣ r.val then p else p ^ 2

/-- The explicit local coefficient depends only on the local spectral type. -/
def localPrimeSpectrumCoefficient (p q : ℕ) : ℂ :=
  if q = 1 then (((p - 1) ^ 2 : ℕ) : ℂ)
  else if q = p then 1 - 2 * (p : ℂ)
  else if q = p ^ 2 then 1
  else 0

/-- Repackage the local Fourier trichotomy as dependence only on the local
spectral type. -/
theorem localPrimeCombNaturalSpectrum_eq_typeCoefficient
    (p : ℕ) (hp : Nat.Prime p) (r : ZMod (p ^ 2)) :
    localPrimeCombNaturalSpectrum p hp r =
      localPrimeSpectrumCoefficient p (localPrimeSpectrumType p r) := by
  rw [localPrimeCombNaturalSpectrum_eq_explicit]
  unfold localPrimeSpectrumType localPrimeSpectrumCoefficient
  by_cases hr : r = 0
  · simp [hr]
  · by_cases hdiv : p ∣ r.val
    · simp [hr, hdiv, hp.ne_one]
    · have hpSqNeOne : p ^ 2 ≠ 1 := by
        have hp2le := hp.two_le
        nlinarith
      have hpSqNeP : p ^ 2 ≠ p := by
        have hp2le := hp.two_le
        nlinarith
      simp [hr, hdiv, hpSqNeOne, hpSqNeP]

/-- The complete raw CRT spectrum is an explicit product of the local
three-case coefficients.  No norm has been taken and all local signs remain. -/
theorem primeWheelCRTSpectrum_eq_neg_prod_explicit
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (r : ∀ p : {p // p ∈ S}, Fin (p.val ^ 2)) :
    primeWheelCRTSpectrum S hprime r =
      -∏ p : {p // p ∈ S},
        (if (r p).val = 0 then
          ((((p.val - 1) ^ 2 : ℕ) : ℂ))
        else if p.val ∣ (r p).val then
          1 - 2 * (p.val : ℂ)
        else 1) := by
  rw [primeWheelCRTSpectrum_eq_neg_prod_local]
  apply congrArg Neg.neg
  apply Fintype.prod_congr
  intro p
  exact localPrimeCombCRTSpectrum_eq_explicit
    p.val (hprime p.val p.property) (r p)

end RHLean.Analysis
