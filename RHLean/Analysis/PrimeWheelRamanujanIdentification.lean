import Mathlib
import RHLean.Analysis.RamanujanDivisorBoundary
import RHLean.Analysis.PrimeWheelRawShellConstancy

/-!
# Reduced-conductor kernels are classical Ramanujan sums

The reduced additive conductor is the additive order of a frequency.  Instead of
choosing CRT coordinates for primitive residues, we apply Möbius inversion to
the exact-order condition itself:

`1_(ord r = q) = sum_{d | q} mu(q / d) 1_(ord r | d)`.

The condition `ord r | d` is exactly `d • r = 0`.  For `d | N`, those frequencies
are the `d`-torsion subgroup of `ZMod N`, and their character sum is the elementary
geometric sum

`sum_{d • r = 0} e_N(zr) = d` if `d | z.val`, and `0` otherwise.

Consequently the shell character kernel is exactly

`sum_{d | q, d | z.val} d * mu(q / d)`,

the classical divisor formula for the Ramanujan sum.  No estimate is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Canonical least-representative equivalence used to reindex finite character
sums between `Fin N` and `ZMod N`. -/
private def finNatCastEquivZMod (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun i := (i.val : ZMod N)
  invFun z := ⟨z.val, ZMod.val_lt z⟩
  left_inv i := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt
  right_inv z := ZMod.natCast_zmod_val z

/-- The indicator of one exact additive order is the Möbius inversion of the
indicator that the additive order divides `d`. -/
private theorem exactAddOrderIndicator_eq_moebius
    {N : ℕ} [NeZero N]
    (r : ZMod N) {q : ℕ} (hq : 0 < q) :
    (if addOrderOf r = q then (1 : ℂ) else 0) =
      ∑ d ∈ q.divisors,
        (((μ (q / d) : ℤ) : ℂ)) *
          (if addOrderOf r ∣ d then 1 else 0) := by
  classical
  let f : ℕ → ℂ := fun n => if addOrderOf r = n then 1 else 0
  let g : ℕ → ℂ := fun n => if addOrderOf r ∣ n then 1 else 0
  have hsum :
      ∀ n > 0, ∑ i ∈ n.divisors, f i = g n := by
    intro n hn
    by_cases hdiv : addOrderOf r ∣ n
    · have hmem : addOrderOf r ∈ n.divisors := by
        exact Nat.mem_divisors.mpr ⟨hdiv, Nat.ne_of_gt hn⟩
      dsimp [f, g]
      rw [if_pos hdiv]
      rw [Finset.sum_eq_single (addOrderOf r)]
      · simp
      · intro b hb hne
        simp [Ne.symm hne]
      · intro hnot
        exact (hnot hmem).elim
    · dsimp [f, g]
      rw [if_neg hdiv]
      apply Finset.sum_eq_zero
      intro i hi
      have hidvd : i ∣ n := Nat.dvd_of_mem_divisors hi
      have hne : addOrderOf r ≠ i := by
        intro heq
        apply hdiv
        rw [heq]
        exact hidvd
      simp [hne]
  have hinv :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hsum) q hq
  rw [Nat.sum_divisorsAntidiagonal'
    (fun a b : ℕ => (((μ a : ℤ) : ℂ)) * g b)] at hinv
  simpa [f, g] using hinv.symm

/-- For `d | N`, the equation `d • r = 0` says exactly that the least
representative of `r` is divisible by `N / d`. -/
private theorem nsmul_eq_zero_iff_quotient_dvd_val
    {N d : ℕ} [NeZero N] (hd : d ∣ N) (r : ZMod N) :
    d • r = 0 ↔ N / d ∣ r.val := by
  have hNpos : 0 < N := Nat.pos_of_neZero N
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hNpos
  have hprod : d * (N / d) = N := Nat.mul_div_cancel' hd
  constructor
  · intro h
    have hcast : (((d * r.val : ℕ) : ZMod N)) = 0 := by
      calc
        (((d * r.val : ℕ) : ZMod N)) =
            ((d : ℕ) : ZMod N) * ((r.val : ℕ) : ZMod N) := by
              rw [Nat.cast_mul]
        _ = ((d : ℕ) : ZMod N) * r := by
              rw [ZMod.natCast_zmod_val]
        _ = d • r := by
              simp [nsmul_eq_mul, mul_comm]
        _ = 0 := h
    have hNdiv : N ∣ d * r.val :=
      (ZMod.natCast_eq_zero_iff (d * r.val) N).mp hcast
    have hfactor : d * (N / d) ∣ N := by
      rw [hprod]
    have hmul : d * (N / d) ∣ d * r.val :=
      dvd_trans hfactor hNdiv
    exact (Nat.mul_dvd_mul_iff_left hdpos).mp hmul
  · intro hdiv
    have hmul : d * (N / d) ∣ d * r.val :=
      (Nat.mul_dvd_mul_iff_left hdpos).mpr hdiv
    rw [hprod] at hmul
    have hcast : (((d * r.val : ℕ) : ZMod N)) = 0 :=
      (ZMod.natCast_eq_zero_iff (d * r.val) N).mpr hmul
    calc
      d • r = ((d : ℕ) : ZMod N) * r := by
        simp [nsmul_eq_mul, mul_comm]
      _ = ((d : ℕ) : ZMod N) * ((r.val : ℕ) : ZMod N) := by
        rw [ZMod.natCast_zmod_val]
      _ = (((d * r.val : ℕ) : ZMod N)) := by
        rw [Nat.cast_mul]
      _ = 0 := hcast

/-- Multiplication by the complementary quotient kills `z` exactly when `d`
divides the least representative of `z`. -/
private theorem quotient_mul_eq_zero_iff_dvd_val
    {N d : ℕ} [NeZero N] (hd : d ∣ N) (z : ZMod N) :
    (((N / d : ℕ) : ZMod N) * z = 0) ↔ d ∣ z.val := by
  have hNpos : 0 < N := Nat.pos_of_neZero N
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hNpos
  have hprod : d * (N / d) = N := Nat.mul_div_cancel' hd
  have hqpos : 0 < N / d := by
    nlinarith
  constructor
  · intro h
    have hcast : ((((N / d) * z.val : ℕ) : ZMod N)) = 0 := by
      calc
        ((((N / d) * z.val : ℕ) : ZMod N)) =
            (((N / d : ℕ) : ZMod N) * ((z.val : ℕ) : ZMod N)) := by
              rw [Nat.cast_mul]
        _ = (((N / d : ℕ) : ZMod N) * z) := by
              rw [ZMod.natCast_zmod_val]
        _ = 0 := h
    have hNdiv : N ∣ (N / d) * z.val :=
      (ZMod.natCast_eq_zero_iff ((N / d) * z.val) N).mp hcast
    have hprod' : (N / d) * d = N := by
      simpa [Nat.mul_comm] using hprod
    have hfactor : (N / d) * d ∣ N := by
      rw [hprod']
    have hmul : (N / d) * d ∣ (N / d) * z.val :=
      dvd_trans hfactor hNdiv
    exact (Nat.mul_dvd_mul_iff_left hqpos).mp hmul
  · intro hdiv
    have hmul : (N / d) * d ∣ (N / d) * z.val :=
      (Nat.mul_dvd_mul_iff_left hqpos).mpr hdiv
    have hprod' : (N / d) * d = N := by
      simpa [Nat.mul_comm] using hprod
    rw [hprod'] at hmul
    have hcast : ((((N / d) * z.val : ℕ) : ZMod N)) = 0 :=
      (ZMod.natCast_eq_zero_iff ((N / d) * z.val) N).mpr hmul
    calc
      (((N / d : ℕ) : ZMod N) * z) =
          (((N / d : ℕ) : ZMod N) * ((z.val : ℕ) : ZMod N)) := by
            rw [ZMod.natCast_zmod_val]
      _ = ((((N / d) * z.val : ℕ) : ZMod N)) := by
            rw [Nat.cast_mul]
      _ = 0 := hcast

/-- The multiples of `N / d` below `N` are exactly the first `d` multiples. -/
private theorem quotientMultiplesBelow_eq_image
    {N d : ℕ} (hd : d ∣ N) (hN : 0 < N) :
    (Finset.range N).filter (fun n => N / d ∣ n) =
      (Finset.range d).image (fun a => (N / d) * a) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hN
  have hprod : d * (N / d) = N := Nat.mul_div_cancel' hd
  have hqpos : 0 < N / d := by
    nlinarith
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hnlt, hdiv⟩
    rcases hdiv with ⟨a, rfl⟩
    have ha : a < d := by
      nlinarith
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    constructor
    · nlinarith
    · exact ⟨a, rfl⟩

/-- Exact character sum over the `d`-torsion subgroup of `ZMod N`. -/
private theorem zmod_torsion_character_sum
    {N d : ℕ} [NeZero N] (hd : d ∣ N) (z : ZMod N) :
    (∑ r : ZMod N,
      if d • r = 0 then ZMod.stdAddChar (z * r) else 0) =
      if d ∣ z.val then (d : ℂ) else 0 := by
  classical
  have hN : 0 < N := Nat.pos_of_neZero N
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hN
  have hprod : d * (N / d) = N := Nat.mul_div_cancel' hd
  have hqpos : 0 < N / d := by
    nlinarith
  let F : ZMod N → ℂ := fun r =>
    if d • r = 0 then ZMod.stdAddChar (z * r) else 0
  calc
    (∑ r : ZMod N,
      if d • r = 0 then ZMod.stdAddChar (z * r) else 0) =
        ∑ i : Fin N, F (finNatCastEquivZMod N i) := by
          exact ((finNatCastEquivZMod N).sum_comp F).symm
    _ = ∑ n ∈ Finset.range N,
        if d • ((n : ℕ) : ZMod N) = 0 then
          ZMod.stdAddChar (z * ((n : ℕ) : ZMod N))
        else 0 := by
          change
            (∑ i : Fin N,
              if d • ((i.val : ℕ) : ZMod N) = 0 then
                ZMod.stdAddChar (z * ((i.val : ℕ) : ZMod N))
              else 0) = _
          exact Fin.sum_univ_eq_sum_range
            (fun n : ℕ =>
              if d • ((n : ℕ) : ZMod N) = 0 then
                ZMod.stdAddChar (z * ((n : ℕ) : ZMod N))
              else 0) N
    _ = ∑ n ∈ (Finset.range N).filter (fun n => N / d ∣ n),
        ZMod.stdAddChar (z * ((n : ℕ) : ZMod N)) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n hn
          have hiff :
              d • ((n : ℕ) : ZMod N) = 0 ↔ N / d ∣ n := by
            have h := nsmul_eq_zero_iff_quotient_dvd_val
              hd ((n : ℕ) : ZMod N)
            rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)] at h
            exact h
          by_cases hzero : d • ((n : ℕ) : ZMod N) = 0
          · have hdiv : N / d ∣ n := hiff.mp hzero
            rw [if_pos hzero, if_pos hdiv]
          · have hdiv : ¬ N / d ∣ n := fun h => hzero (hiff.mpr h)
            rw [if_neg hzero, if_neg hdiv]
    _ = ∑ a ∈ Finset.range d,
        ZMod.stdAddChar
          (z * ((((N / d) * a : ℕ) : ZMod N))) := by
          have hinj :
              Set.InjOn (fun a : ℕ => (N / d) * a)
                (Finset.range d : Set ℕ) := by
            intro a ha b hb hab
            exact Nat.eq_of_mul_eq_mul_left hqpos hab
          rw [quotientMultiplesBelow_eq_image hd hN,
            Finset.sum_image hinj]
    _ = if d ∣ z.val then (d : ℂ) else 0 := by
      let b : ZMod N := z * ((N / d : ℕ) : ZMod N)
      have hgeom :
          (∑ a ∈ Finset.range d,
            ZMod.stdAddChar
              (z * ((((N / d) * a : ℕ) : ZMod N)))) =
            ∑ a ∈ Finset.range d, ZMod.stdAddChar b ^ a := by
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
      by_cases hdiv : d ∣ z.val
      · have hb : b = 0 := by
          dsimp [b]
          have hz := (quotient_mul_eq_zero_iff_dvd_val hd z).mpr hdiv
          simpa [mul_comm] using hz
        rw [if_pos hdiv]
        simp [hb]
      · have hb : b ≠ 0 := by
          intro hb0
          apply hdiv
          apply (quotient_mul_eq_zero_iff_dvd_val hd z).mp
          simpa [b, mul_comm] using hb0
        have hchar : ZMod.stdAddChar b ≠ 1 := by
          intro h
          have hzero : b = 0 :=
            ZMod.injective_stdAddChar (by simpa using h)
          exact hb hzero
        have hdb : d • b = 0 := by
          dsimp [b]
          calc
            d • (z * ((N / d : ℕ) : ZMod N)) =
                z * (((d * (N / d) : ℕ) : ZMod N)) := by
                  simp [nsmul_eq_mul]
                  ring
            _ = z * ((N : ℕ) : ZMod N) := by rw [hprod]
            _ = 0 := by simp
        have hpowd : ZMod.stdAddChar b ^ d = 1 := by
          calc
            ZMod.stdAddChar b ^ d = ZMod.stdAddChar (d • b) := by
              symm
              exact AddChar.map_nsmul_eq_pow
                (ZMod.stdAddChar : AddChar (ZMod N) ℂ) d b
            _ = 1 := by rw [hdb]; simp
        rw [if_neg hdiv, geom_sum_eq hchar d, hpowd]
        simp

/-- Möbius inversion turns an exact reduced-conductor shell into a signed sum of
finite torsion-character sums. -/
theorem primeWheelReducedConductorKernel_eq_torsionSums
    (W : PrimeWheelFiniteSystem) {q : ℕ} (hq : 0 < q)
    (z : ZMod W.modulus) :
    primeWheelReducedConductorKernel W q z =
      ∑ d ∈ q.divisors,
        (((μ (q / d) : ℤ) : ℂ)) *
          ∑ r : ZMod W.modulus,
            if d • r = 0 then ZMod.stdAddChar (z * r) else 0 := by
  classical
  unfold primeWheelReducedConductorKernel
  calc
    (∑ r : ZMod W.modulus,
      if q = reducedAdditiveConductor r then
        ZMod.stdAddChar (z * r)
      else 0) =
      ∑ r : ZMod W.modulus,
        (if addOrderOf r = q then (1 : ℂ) else 0) *
          ZMod.stdAddChar (z * r) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [reducedAdditiveConductor_eq_addOrderOf W r]
            by_cases hord : addOrderOf r = q
            · have hrev : q = addOrderOf r := hord.symm
              rw [if_pos hrev, if_pos hord, one_mul]
            · have hrev : q ≠ addOrderOf r := fun h => hord h.symm
              rw [if_neg hrev, if_neg hord, zero_mul]
    _ =
      ∑ r : ZMod W.modulus,
        (∑ d ∈ q.divisors,
          (((μ (q / d) : ℤ) : ℂ)) *
            (if addOrderOf r ∣ d then 1 else 0)) *
          ZMod.stdAddChar (z * r) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [exactAddOrderIndicator_eq_moebius r hq]
    _ =
      ∑ r : ZMod W.modulus,
        ∑ d ∈ q.divisors,
          (((μ (q / d) : ℤ) : ℂ)) *
            (if d • r = 0 then ZMod.stdAddChar (z * r) else 0) := by
              apply Finset.sum_congr rfl
              intro r hr
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro d hd
              have hiff : addOrderOf r ∣ d ↔ d • r = 0 :=
                addOrderOf_dvd_iff_nsmul_eq_zero
              by_cases hzero : d • r = 0
              · have hdiv : addOrderOf r ∣ d := hiff.mpr hzero
                rw [if_pos hdiv, if_pos hzero]
                ring
              · have hdiv : ¬ addOrderOf r ∣ d :=
                  fun h => hzero (hiff.mp h)
                rw [if_neg hdiv, if_neg hzero]
                ring
    _ =
      ∑ d ∈ q.divisors,
        (((μ (q / d) : ℤ) : ℂ)) *
          ∑ r : ZMod W.modulus,
            if d • r = 0 then ZMod.stdAddChar (z * r) else 0 := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro d hd
              rw [Finset.mul_sum]

/-- On a genuine conductor divisor `q | modulus`, the repository's reduced-
conductor character kernel is exactly the classical Ramanujan divisor sum. -/
theorem primeWheelReducedConductorKernel_eq_ramanujanDivisorKernel
    (W : PrimeWheelFiniteSystem) {q : ℕ}
    (hq : 0 < q) (hqmod : q ∣ W.modulus)
    (z : ZMod W.modulus) :
    primeWheelReducedConductorKernel W q z =
      (((ramanujanDivisorKernel q z.val 0 : ℤ) : ℂ)) := by
  classical
  rw [primeWheelReducedConductorKernel_eq_torsionSums W hq z]
  unfold ramanujanDivisorKernel
  push_cast
  apply Finset.sum_congr rfl
  intro d hd
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hdN : d ∣ W.modulus := dvd_trans hdq hqmod
  rw [zmod_torsion_character_sum hdN z]
  by_cases hdiv : d ∣ z.val
  · have hmod : Nat.ModEq d z.val 0 :=
      Nat.modEq_zero_iff_dvd.mpr hdiv
    simp [hdiv, hmod]
    ring
  · have hmod : ¬ Nat.ModEq d z.val 0 := by
      intro h
      exact hdiv (Nat.modEq_zero_iff_dvd.mp h)
    simp [hdiv, hmod]

end RHLean.Analysis