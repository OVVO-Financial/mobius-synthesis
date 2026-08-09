import Mathlib
import RHLean.Analysis.PrimeWheelRamanujanIdentification
import RHLean.Analysis.PrimeWheelArithmeticSpectrum

/-!
# Ramanujan windows and smooth packets as divisor-boundary sums

This file turns the classical Ramanujan identification into the exact arithmetic
form needed for the remaining estimate.  The pinned raw shell becomes an
interval Ramanujan sum, while the smooth correction becomes a Möbius-weighted
sum of shifted interval Ramanujan sums.  For every nontrivial conductor `q > 1`,
both are then replaced by the divisor-residue boundary defects from
`RamanujanDivisorBoundary`.

The signed `raw - 2 * smooth` structure is preserved throughout.  No norm,
triangle inequality, or asymptotic estimate is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

private def finNatCastEquivZModBoundary
    (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun i := (i.val : ZMod N)
  invFun z := ⟨z.val, ZMod.val_lt z⟩
  left_inv i := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt
  right_inv z := ZMod.natCast_zmod_val z

/-- Reducing a displacement modulo a divisor of the ambient torus is equivalent
to comparing the two endpoints in that residue class. -/
private theorem modEq_sub_val_zero_iff
    {N d : ℕ} [NeZero N] (hd : d ∣ N)
    (a b : ZMod N) :
    Nat.ModEq d (b - a).val 0 ↔ Nat.ModEq d b.val a.val := by
  rw [Nat.modEq_zero_iff_dvd]
  rw [← (ZMod.natCast_eq_zero_iff (b - a).val d)]
  rw [← ZMod.cast_eq_val]
  rw [ZMod.cast_sub hd]
  rw [sub_eq_zero]
  rw [ZMod.cast_eq_val, ZMod.cast_eq_val]
  exact ZMod.natCast_eq_natCast_iff b.val a.val d

/-- The divisor-form Ramanujan kernel of a torus displacement is the shifted
classical Ramanujan kernel on the least representatives. -/
theorem ramanujanDivisorKernel_sub_eq_shift
    {N q : ℕ} [NeZero N] (hqmod : q ∣ N)
    (a b : ZMod N) :
    ramanujanDivisorKernel q (b - a).val 0 =
      ramanujanDivisorKernel q b.val a.val := by
  classical
  unfold ramanujanDivisorKernel
  apply Finset.sum_congr rfl
  intro d hd
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hdN : d ∣ N := dvd_trans hdq hqmod
  have hiff := modEq_sub_val_zero_iff hdN a b
  by_cases hmod : Nat.ModEq d (b - a).val 0
  · have hshift : Nat.ModEq d b.val a.val := hiff.mp hmod
    rw [if_pos hmod, if_pos hshift]
  · have hshift : ¬ Nat.ModEq d b.val a.val :=
      fun h => hmod (hiff.mpr h)
    rw [if_neg hmod, if_neg hshift]

/-- Any value-dependent sum over the pinned torus prefix is exactly the
corresponding natural sum over `(lower,x]`. -/
private theorem zmodPrefixValSum_eq_Ioc
    (W : PrimeWheelFiniteSystem) {x : ℕ}
    (hx : x < W.modulus) (f : ℕ → ℂ) :
    (∑ z : ZMod W.modulus,
      W.torusPrefixWindow x z * f z.val) =
      ∑ n ∈ Finset.Ioc W.lower x, f n := by
  classical
  unfold PrimeWheelFiniteSystem.torusPrefixWindow
  calc
    (∑ z : ZMod W.modulus,
      (if W.lower < z.val ∧ z.val ≤ x then 1 else 0) * f z.val) =
      ∑ i : Fin W.modulus,
        (if W.lower <
              (finNatCastEquivZModBoundary W.modulus i).val ∧
            (finNatCastEquivZModBoundary W.modulus i).val ≤ x then 1 else 0) *
          f (finNatCastEquivZModBoundary W.modulus i).val := by
            exact ((finNatCastEquivZModBoundary W.modulus).sum_comp
              (fun z : ZMod W.modulus =>
                (if W.lower < z.val ∧ z.val ≤ x then 1 else 0) *
                  f z.val)).symm
    _ = ∑ i : Fin W.modulus,
        (if W.lower < i.val ∧ i.val ≤ x then 1 else 0) * f i.val := by
          apply Finset.sum_congr rfl
          intro i hi
          have hval :
              (finNatCastEquivZModBoundary W.modulus i).val = i.val := by
            change ((i.val : ZMod W.modulus)).val = i.val
            exact ZMod.val_natCast_of_lt i.isLt
          rw [hval]
    _ = ∑ n ∈ Finset.range W.modulus,
        (if W.lower < n ∧ n ≤ x then 1 else 0) * f n := by
          exact Fin.sum_univ_eq_sum_range
            (fun n : ℕ =>
              (if W.lower < n ∧ n ≤ x then 1 else 0) * f n)
            W.modulus
    _ = ∑ n ∈ Finset.Ioc W.lower x, f n := by
      have hfilter :
          (Finset.range W.modulus).filter
              (fun n => W.lower < n ∧ n ≤ x) =
            Finset.Ioc W.lower x := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
        omega
      rw [← hfilter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hmem : W.lower < n ∧ n ≤ x
      · simp [hmem]
      · simp [hmem]

/-- Any value-dependent pairing with the zero-padded smooth block is exactly the
corresponding natural sum on the arithmetic block. -/
private theorem zmodSmoothBlockValSum_eq_Ioc
    (W : PrimeWheelFiniteSystem) (f : ℕ → ℂ) :
    (∑ z : ZMod W.modulus,
      W.torusSmoothCoreBlockField z * f z.val) =
      ∑ n ∈ Finset.Ioc W.lower W.upper,
        (((W.smoothCoreSite n : ℤ) : ℂ)) * f n := by
  classical
  unfold PrimeWheelFiniteSystem.torusSmoothCoreBlockField
  calc
    (∑ z : ZMod W.modulus,
      (if W.lower < z.val ∧ z.val ≤ W.upper then
          ((W.smoothCoreSite z.val : ℤ) : ℂ)
        else 0) * f z.val) =
      ∑ i : Fin W.modulus,
        (if W.lower <
              (finNatCastEquivZModBoundary W.modulus i).val ∧
            (finNatCastEquivZModBoundary W.modulus i).val ≤ W.upper then
            ((W.smoothCoreSite
              (finNatCastEquivZModBoundary W.modulus i).val : ℤ) : ℂ)
          else 0) *
          f (finNatCastEquivZModBoundary W.modulus i).val := by
            exact ((finNatCastEquivZModBoundary W.modulus).sum_comp
              (fun z : ZMod W.modulus =>
                (if W.lower < z.val ∧ z.val ≤ W.upper then
                    ((W.smoothCoreSite z.val : ℤ) : ℂ)
                  else 0) * f z.val)).symm
    _ = ∑ i : Fin W.modulus,
        (if W.lower < i.val ∧ i.val ≤ W.upper then
            ((W.smoothCoreSite i.val : ℤ) : ℂ)
          else 0) * f i.val := by
            apply Finset.sum_congr rfl
            intro i hi
            have hval :
                (finNatCastEquivZModBoundary W.modulus i).val = i.val := by
              change ((i.val : ZMod W.modulus)).val = i.val
              exact ZMod.val_natCast_of_lt i.isLt
            rw [hval]
    _ = ∑ n ∈ Finset.range W.modulus,
        (if W.lower < n ∧ n ≤ W.upper then
            ((W.smoothCoreSite n : ℤ) : ℂ)
          else 0) * f n := by
            exact Fin.sum_univ_eq_sum_range
              (fun n : ℕ =>
                (if W.lower < n ∧ n ≤ W.upper then
                    ((W.smoothCoreSite n : ℤ) : ℂ)
                  else 0) * f n)
              W.modulus
    _ = ∑ n ∈ Finset.Ioc W.lower W.upper,
        (((W.smoothCoreSite n : ℤ) : ℂ)) * f n := by
      have hfilter :
          (Finset.range W.modulus).filter
              (fun n => W.lower < n ∧ n ≤ W.upper) =
            Finset.Ioc W.lower W.upper := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
        constructor
        · intro hn
          exact hn.2
        · intro hn
          exact ⟨lt_of_le_of_lt hn.2 W.upper_lt_modulus, hn⟩
      rw [← hfilter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hmem : W.lower < n ∧ n ≤ W.upper
      · simp [hmem]
      · simp [hmem]

/-- The normalized reduced-conductor window is literally a pinned interval sum
of the classical divisor-form Ramanujan kernel. -/
theorem primeWheelReducedConductorRamanujanWindow_eq_divisorInterval
    (W : PrimeWheelFiniteSystem) {x q : ℕ}
    (hx : x ≤ W.upper) (hq : 0 < q) (hqmod : q ∣ W.modulus) :
    primeWheelReducedConductorRamanujanWindow W x q =
      ((W.modulus : ℂ)⁻¹) *
        (((ramanujanDivisorInterval q 0 W.lower x : ℤ) : ℂ)) := by
  classical
  unfold primeWheelReducedConductorRamanujanWindow
  congr 1
  calc
    (∑ z : ZMod W.modulus,
      W.torusPrefixWindow x z * primeWheelReducedConductorKernel W q z) =
      ∑ z : ZMod W.modulus,
        W.torusPrefixWindow x z *
          (((ramanujanDivisorKernel q z.val 0 : ℤ) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [primeWheelReducedConductorKernel_eq_ramanujanDivisorKernel
              W hq hqmod z]
    _ = ∑ n ∈ Finset.Ioc W.lower x,
        (((ramanujanDivisorKernel q n 0 : ℤ) : ℂ)) := by
          exact zmodPrefixValSum_eq_Ioc W
            (lt_of_le_of_lt hx W.upper_lt_modulus)
            (fun n => (((ramanujanDivisorKernel q n 0 : ℤ) : ℂ)))
    _ = (((ramanujanDivisorInterval q 0 W.lower x : ℤ) : ℂ)) := by
      unfold ramanujanDivisorInterval ramanujanDivisorSumOn
      push_cast
      rfl

/-- For `q > 1`, the normalized reduced-conductor window contains no bulk term:
it is exactly the Möbius-weighted divisor boundary sum. -/
theorem primeWheelReducedConductorRamanujanWindow_eq_divisorBoundary
    (W : PrimeWheelFiniteSystem) {x q : ℕ}
    (hx : x ≤ W.upper) (hq : 1 < q) (hqmod : q ∣ W.modulus) :
    primeWheelReducedConductorRamanujanWindow W x q =
      ((W.modulus : ℂ)⁻¹) *
        (((∑ d ∈ q.divisors,
          μ (q / d) * divisorIntervalBoundary d 0 W.lower x : ℤ) : ℂ)) := by
  rw [primeWheelReducedConductorRamanujanWindow_eq_divisorInterval
    W hx (Nat.zero_lt_of_lt hq) hqmod]
  rw [ramanujanDivisorInterval_eq_boundary hq]

/-- Generic smooth contribution carried by a reduced additive conductor. -/
def primeWheelSmoothConductorResponse
    (W : PrimeWheelFiniteSystem) (x q : ℕ) : ℂ :=
  ∑ r : ZMod W.modulus,
    if q = reducedAdditiveConductor r then
      (((W.modulus : ℂ)⁻¹) * W.smoothCoreBlockSpectrum r) *
        W.prefixWindowSpectrum x (-r)
    else 0

/-- The primorial smooth conductor response is the generic smooth response on
the minimal primorial wheel. -/
theorem primorialPeriodicSmoothConductorResponse_eq_generic
    (k x q : ℕ) :
    primorialPeriodicSmoothConductorResponse k x q =
      primeWheelSmoothConductorResponse
        (primorialMinimalWheelSystem k) x q := by
  rfl

/-- Exact physical-space formula for one smooth reduced-conductor packet. -/
theorem primeWheelSmoothConductorResponse_eq_kernelPairing
    (W : PrimeWheelFiniteSystem) (x q : ℕ) :
    primeWheelSmoothConductorResponse W x q =
      ((W.modulus : ℂ)⁻¹) *
        ∑ a : ZMod W.modulus,
          ∑ b : ZMod W.modulus,
            W.torusSmoothCoreBlockField a * W.torusPrefixWindow x b *
              primeWheelReducedConductorKernel W q (b - a) := by
  classical
  unfold primeWheelSmoothConductorResponse
  calc
    (∑ r : ZMod W.modulus,
      if q = reducedAdditiveConductor r then
        (((W.modulus : ℂ)⁻¹) * W.smoothCoreBlockSpectrum r) *
          W.prefixWindowSpectrum x (-r)
      else 0) =
      ((W.modulus : ℂ)⁻¹) *
        ∑ r : ZMod W.modulus,
          if q = reducedAdditiveConductor r then
            W.smoothCoreBlockSpectrum r * W.prefixWindowSpectrum x (-r)
          else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r hr
            by_cases hcond : q = reducedAdditiveConductor r
            · simp [hcond, mul_assoc]
            · simp [hcond]
    _ = ((W.modulus : ℂ)⁻¹) *
      ∑ r : ZMod W.modulus,
        ∑ a : ZMod W.modulus,
          ∑ b : ZMod W.modulus,
            if q = reducedAdditiveConductor r then
              (ZMod.stdAddChar (-(a * r)) * W.torusSmoothCoreBlockField a) *
                (ZMod.stdAddChar (-(b * (-r))) * W.torusPrefixWindow x b)
            else 0 := by
              congr 1
              unfold PrimeWheelFiniteSystem.smoothCoreBlockSpectrum
                PrimeWheelFiniteSystem.prefixWindowSpectrum
              simp only [ZMod.dft_apply, smul_eq_mul]
              apply Finset.sum_congr rfl
              intro r hr
              by_cases hcond : q = reducedAdditiveConductor r
              · simp only [hcond, if_true]
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro a ha
                rw [Finset.mul_sum]
              · simp [hcond]
    _ = ((W.modulus : ℂ)⁻¹) *
      ∑ a : ZMod W.modulus,
        ∑ b : ZMod W.modulus,
          ∑ r : ZMod W.modulus,
            if q = reducedAdditiveConductor r then
              (ZMod.stdAddChar (-(a * r)) * W.torusSmoothCoreBlockField a) *
                (ZMod.stdAddChar (-(b * (-r))) * W.torusPrefixWindow x b)
            else 0 := by
              congr 1
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.sum_comm]
    _ = ((W.modulus : ℂ)⁻¹) *
      ∑ a : ZMod W.modulus,
        ∑ b : ZMod W.modulus,
          W.torusSmoothCoreBlockField a * W.torusPrefixWindow x b *
            primeWheelReducedConductorKernel W q (b - a) := by
              congr 1
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro b hb
              unfold primeWheelReducedConductorKernel
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r hr
              by_cases hcond : q = reducedAdditiveConductor r
              · simp only [hcond, if_true]
                have hchar :
                    ZMod.stdAddChar (-(a * r)) *
                        ZMod.stdAddChar (-(b * (-r))) =
                      ZMod.stdAddChar ((b - a) * r) := by
                  rw [← AddChar.map_add_eq_mul]
                  congr 1
                  ring
                calc
                  (ZMod.stdAddChar (-(a * r)) * W.torusSmoothCoreBlockField a) *
                        (ZMod.stdAddChar (-(b * (-r))) * W.torusPrefixWindow x b) =
                      W.torusSmoothCoreBlockField a * W.torusPrefixWindow x b *
                        (ZMod.stdAddChar (-(a * r)) *
                          ZMod.stdAddChar (-(b * (-r)))) := by ring
                  _ = W.torusSmoothCoreBlockField a * W.torusPrefixWindow x b *
                        ZMod.stdAddChar ((b - a) * r) := by rw [hchar]
              · simp [hcond]

/-- On the arithmetic block, a smooth-core site is exactly `-mu(n)` when `n`
is a squarefree divisor of the coordinate product, and zero otherwise. -/
theorem primeWheelSmoothCoreSite_eq_neg_moebius_divisor
    (W : PrimeWheelFiniteSystem) (n : ℕ) :
    W.smoothCoreSite n =
      if n ≤ W.upper ∧ Squarefree n ∧
          n ∣ primeWheelCoordinateProduct W.primeCoordinates then
        -(μ n)
      else 0 := by
  classical
  unfold PrimeWheelFiniteSystem.smoothCoreSite primeWheelSmoothCoreSite
  have hsiff := isPrimeWheelSmooth_iff_squarefree_dvd_coordinateProduct
    W.primeCoordinates n W.primeCoordinates_prime
  by_cases hn : n ≤ W.upper
  · by_cases hs : IsPrimeWheelSmooth W.primeCoordinates n
    · have hcrit := hsiff.mp hs
      have hraw := seededPrimeComb_eq_neg_moebius_of_smooth
        W.primeCoordinates W.primeCoordinates_prime hs
      simp [hn, hs, hcrit, hraw]
    · have hcrit :
          ¬(Squarefree n ∧
            n ∣ primeWheelCoordinateProduct W.primeCoordinates) := by
        exact fun h => hs (hsiff.mpr h)
      simp [hn, hs, hcrit]
  · simp [hn]

/-- The exact finite set of smooth divisor sites in one wheel block. -/
def primeWheelSmoothDivisorSites
    (W : PrimeWheelFiniteSystem) : Finset ℕ :=
  (Finset.Ioc W.lower W.upper).filter fun n =>
    Squarefree n ∧ n ∣ primeWheelCoordinateProduct W.primeCoordinates

/-- Purely arithmetic smooth packet: each smooth divisor shifts the same
Ramanujan interval by its residue. -/
def primeWheelSmoothRamanujanPacket
    (W : PrimeWheelFiniteSystem) (x q : ℕ) : ℤ :=
  ∑ a ∈ primeWheelSmoothDivisorSites W,
    -(μ a) * ramanujanDivisorInterval q a W.lower x

/-- Purely arithmetic boundary form of the smooth packet. -/
def primeWheelSmoothBoundaryPacket
    (W : PrimeWheelFiniteSystem) (x q : ℕ) : ℤ :=
  ∑ a ∈ primeWheelSmoothDivisorSites W,
    -(μ a) *
      ∑ d ∈ q.divisors,
        μ (q / d) * divisorIntervalBoundary d a W.lower x

/-- Bulk cancellation is simultaneous for every shifted smooth Ramanujan
interval. -/
theorem primeWheelSmoothRamanujanPacket_eq_boundary
    (W : PrimeWheelFiniteSystem) (x : ℕ)
    {q : ℕ} (hq : 1 < q) :
    primeWheelSmoothRamanujanPacket W x q =
      primeWheelSmoothBoundaryPacket W x q := by
  classical
  unfold primeWheelSmoothRamanujanPacket primeWheelSmoothBoundaryPacket
  apply Finset.sum_congr rfl
  intro a ha
  rw [ramanujanDivisorInterval_eq_boundary hq]

/-- The smooth Fourier conductor packet is exactly the normalized arithmetic
sum of shifted Ramanujan intervals. -/
theorem primeWheelSmoothConductorResponse_eq_ramanujanPacket
    (W : PrimeWheelFiniteSystem) {x q : ℕ}
    (hx : x ≤ W.upper) (hq : 0 < q) (hqmod : q ∣ W.modulus) :
    primeWheelSmoothConductorResponse W x q =
      ((W.modulus : ℂ)⁻¹) *
        (((primeWheelSmoothRamanujanPacket W x q : ℤ) : ℂ)) := by
  classical
  rw [primeWheelSmoothConductorResponse_eq_kernelPairing]
  congr 1
  calc
    (∑ a : ZMod W.modulus,
      ∑ b : ZMod W.modulus,
        W.torusSmoothCoreBlockField a * W.torusPrefixWindow x b *
          primeWheelReducedConductorKernel W q (b - a)) =
      ∑ a : ZMod W.modulus,
        W.torusSmoothCoreBlockField a *
          (((ramanujanDivisorInterval q a.val W.lower x : ℤ) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro a ha
            have hinner :
                (∑ b : ZMod W.modulus,
                  W.torusPrefixWindow x b *
                    primeWheelReducedConductorKernel W q (b - a)) =
                  (((ramanujanDivisorInterval q a.val W.lower x : ℤ) : ℂ)) := by
              calc
                (∑ b : ZMod W.modulus,
                  W.torusPrefixWindow x b *
                    primeWheelReducedConductorKernel W q (b - a)) =
                  ∑ b : ZMod W.modulus,
                    W.torusPrefixWindow x b *
                      (((ramanujanDivisorKernel q b.val a.val : ℤ) : ℂ)) := by
                        apply Finset.sum_congr rfl
                        intro b hb
                        rw [primeWheelReducedConductorKernel_eq_ramanujanDivisorKernel
                          W hq hqmod (b - a)]
                        rw [ramanujanDivisorKernel_sub_eq_shift hqmod a b]
                _ = ∑ n ∈ Finset.Ioc W.lower x,
                    (((ramanujanDivisorKernel q n a.val : ℤ) : ℂ)) := by
                      exact zmodPrefixValSum_eq_Ioc W
                        (lt_of_le_of_lt hx W.upper_lt_modulus)
                        (fun n => (((ramanujanDivisorKernel q n a.val : ℤ) : ℂ)))
                _ = (((ramanujanDivisorInterval q a.val W.lower x : ℤ) : ℂ)) := by
                      unfold ramanujanDivisorInterval ramanujanDivisorSumOn
                      push_cast
                      rfl
            calc
              (∑ b : ZMod W.modulus,
                W.torusSmoothCoreBlockField a * W.torusPrefixWindow x b *
                  primeWheelReducedConductorKernel W q (b - a)) =
                W.torusSmoothCoreBlockField a *
                  (∑ b : ZMod W.modulus,
                    W.torusPrefixWindow x b *
                      primeWheelReducedConductorKernel W q (b - a)) := by
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro b hb
                        ring
              _ = W.torusSmoothCoreBlockField a *
                  (((ramanujanDivisorInterval q a.val W.lower x : ℤ) : ℂ)) := by
                    rw [hinner]
    _ = (((primeWheelSmoothRamanujanPacket W x q : ℤ) : ℂ)) := by
      rw [zmodSmoothBlockValSum_eq_Ioc W
        (fun n => (((ramanujanDivisorInterval q n W.lower x : ℤ) : ℂ)))]
      unfold primeWheelSmoothRamanujanPacket primeWheelSmoothDivisorSites
      push_cast
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      have hnupper : n ≤ W.upper := (Finset.mem_Ioc.mp hn).2
      rw [primeWheelSmoothCoreSite_eq_neg_moebius_divisor W n]
      simp only [hnupper, true_and]
      by_cases hcrit : Squarefree n ∧
          n ∣ primeWheelCoordinateProduct W.primeCoordinates
      · simp [hcrit]
      · simp [hcrit]

/-- For a nontrivial conductor, the smooth Fourier packet is already a purely
arithmetic divisor-boundary packet. -/
theorem primeWheelSmoothConductorResponse_eq_boundaryPacket
    (W : PrimeWheelFiniteSystem) {x q : ℕ}
    (hx : x ≤ W.upper) (hq : 1 < q) (hqmod : q ∣ W.modulus) :
    primeWheelSmoothConductorResponse W x q =
      ((W.modulus : ℂ)⁻¹) *
        (((primeWheelSmoothBoundaryPacket W x q : ℤ) : ℂ)) := by
  rw [primeWheelSmoothConductorResponse_eq_ramanujanPacket
    W hx (Nat.zero_lt_of_lt hq) hqmod]
  rw [primeWheelSmoothRamanujanPacket_eq_boundary W x hq]

/-- Any actually occupied conductor shell divides the ambient modulus. -/
theorem reducedConductor_dvd_modulus
    (W : PrimeWheelFiniteSystem)
    (r : ZMod W.modulus) :
    reducedAdditiveConductor r ∣ W.modulus := by
  rw [reducedAdditiveConductor_eq_addOrderOf W r]
  simpa using (addOrderOf_dvd_card (x := r))

/-- Final exact signed arithmetic packet.  For every occupied nontrivial shell,
the only remaining objects are the actual common raw shell coefficient and
explicit finite divisor-boundary sums. -/
theorem primorialPeriodicRawJointConductorResponse_eq_divisorBoundary
    (k x q : ℕ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus)
    (hr : q = reducedAdditiveConductor r)
    (hq : 1 < q)
    (hx : x ≤ (primorialMinimalWheelSystem k).upper) :
    primorialPeriodicRawJointConductorResponse k x q =
      primorialPeriodicRawSpectrum k r *
        (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
          (((∑ d ∈ q.divisors,
            μ (q / d) *
              divisorIntervalBoundary d 0
                (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ)) -
        2 *
          ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
            (((primeWheelSmoothBoundaryPacket
              (primorialMinimalWheelSystem k) x q : ℤ) : ℂ))) := by
  have hqmod : q ∣ (primorialMinimalWheelSystem k).modulus := by
    rw [hr]
    exact reducedConductor_dvd_modulus
      (primorialMinimalWheelSystem k) r
  rw [primorialPeriodicRawJointConductorResponse_eq_frequencyRamanujan_sub_two_smooth
    k x q r hr]
  unfold primorialReducedConductorRamanujanWindow
  rw [primeWheelReducedConductorRamanujanWindow_eq_divisorBoundary
    (primorialMinimalWheelSystem k) hx hq hqmod]
  rw [primorialPeriodicSmoothConductorResponse_eq_generic]
  rw [primeWheelSmoothConductorResponse_eq_boundaryPacket
    (primorialMinimalWheelSystem k) hx hq hqmod]
  ring

end RHLean.Analysis