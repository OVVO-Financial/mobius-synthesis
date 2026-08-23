import Mathlib
import RHLean.Analysis.CorrectedConductorBoundaryDefectGeneral

/-!
# Quantitative bound for the small corrected-conductor sector

The general corrected-conductor theorem removes interval bulk for every
`q > 1`, but periodicity alone is not an estimate.  This file adds the first
uniform quantitative consequence.

A corrected conductor packet is `q`-periodic.  Reduce its endpoint to one
incomplete conductor period.  On an interval of length `< q`, each divisor
boundary is bounded crudely by `2 q^2`; summing over at most `q` divisors gives
`2 q^3` for the complete conductor boundary defect.  The periodic raw DFT
coefficient is at most the torus modulus, while the smooth-site carrier has at
most the same cardinality.  After the common torus normalization the full
signed `raw - 2 * smooth` packet therefore satisfies

`||J_q(k,x)|| <= 6 q^3`.

Consequently all nontrivial conductors `q <= R` contribute at most
`6 (R+1) R^3`, hence `O(R^4)`, uniformly in the prefix length.  Choosing a
cutoff on the order of the eighth root of the arithmetic scale places this
entire growing conductor sector at square-root size.  The remaining Gram
problem is thereby restricted to conductor one and conductors above that
cutoff.

The constants are deliberately elementary.  No cancellation between distinct
conductors is used in this file.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

private theorem divisorResidueCount_eq_filterCard
    (I : Finset ℕ) (d a : ℕ) :
    divisorResidueCount I d a =
      (((I.filter fun m => Nat.ModEq d m a).card : ℕ) : ℤ) := by
  classical
  unfold divisorResidueCount
  calc
    (∑ m ∈ I, if Nat.ModEq d m a then (1 : ℤ) else 0) =
        ∑ m ∈ I with Nat.ModEq d m a, (1 : ℤ) := by
          rw [Finset.sum_filter]
    _ = (((I.filter fun m => Nat.ModEq d m a).card : ℕ) : ℤ) := by
      simp

private theorem abs_divisorResidueCount_le_card
    (I : Finset ℕ) (d a : ℕ) :
    |divisorResidueCount I d a| ≤ (I.card : ℤ) := by
  rw [divisorResidueCount_eq_filterCard]
  simp only [abs_of_nonneg (Int.natCast_nonneg _)]
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- On an interval shorter than `q`, any divisor boundary with `d <= q` has a
uniform quadratic bound.  The estimate is intentionally crude but independent
of the location and of the full prefix length. -/
theorem abs_divisorIntervalBoundary_le_two_mul_sq_of_short
    (d a lower upper q : ℕ)
    (hd : d ≤ q) (hq : 1 ≤ q)
    (hshort : upper - lower < q) :
    |divisorIntervalBoundary d a lower upper| ≤
      2 * (q : ℤ) ^ 2 := by
  unfold divisorIntervalBoundary divisorResidueBoundary
  have hcard : (Finset.Ioc lower upper).card = upper - lower := by
    exact Nat.card_Ioc lower upper
  rw [hcard]
  let c : ℤ := divisorResidueCount (Finset.Ioc lower upper) d a
  let r : ℕ := upper - lower
  have hc : |c| ≤ (r : ℤ) := by
    dsimp [c, r]
    have hc0 := abs_divisorResidueCount_le_card
      (Finset.Ioc lower upper) d a
    rw [hcard] at hc0
    exact hc0
  have hd0 : (0 : ℤ) ≤ d := by positivity
  have hq0 : (0 : ℤ) ≤ q := by positivity
  have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast hq
  have hdr : (d : ℤ) ≤ q := by exact_mod_cast hd
  have hrq : (r : ℤ) ≤ q := by
    exact_mod_cast Nat.le_of_lt hshort
  have hprod : (d : ℤ) * |c| ≤ (q : ℤ) * (r : ℤ) := by
    calc
      (d : ℤ) * |c| ≤ (q : ℤ) * |c| :=
        mul_le_mul_of_nonneg_right hdr (abs_nonneg c)
      _ ≤ (q : ℤ) * (r : ℤ) :=
        mul_le_mul_of_nonneg_left hc hq0
  have hqr : (q : ℤ) * (r : ℤ) ≤ (q : ℤ) ^ 2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left hrq hq0
  have hq_sq : (q : ℤ) ≤ (q : ℤ) ^ 2 := by
    have hnonneg : (0 : ℤ) ≤ (q : ℤ) * ((q : ℤ) - 1) :=
      mul_nonneg hq0 (sub_nonneg.mpr hq1)
    nlinarith
  calc
    |(d : ℤ) * c - (r : ℤ)| ≤ |(d : ℤ) * c| + |(r : ℤ)| :=
      abs_sub _ _
    _ = (d : ℤ) * |c| + (r : ℤ) := by
      rw [abs_mul, abs_of_nonneg hd0, abs_of_nonneg (Int.natCast_nonneg r)]
    _ ≤ (q : ℤ) * (r : ℤ) + (r : ℤ) := by
      exact add_le_add hprod le_rfl
    _ ≤ (q : ℤ) ^ 2 + (q : ℤ) := by
      exact add_le_add hqr hrq
    _ ≤ 2 * (q : ℤ) ^ 2 := by
      nlinarith

/-- Adding any whole number of conductor periods does not change the complete
conductor boundary defect. -/
theorem conductorBoundaryDefect_add_mul_conductor
    {q : ℕ} (hq : 1 < q)
    (a lower upper c : ℕ) (hlower : lower ≤ upper) :
    conductorBoundaryDefect q a lower (upper + c * q) =
      conductorBoundaryDefect q a lower upper := by
  induction c with
  | zero => simp
  | succ c ih =>
      have hle : lower ≤ upper + c * q := by omega
      calc
        conductorBoundaryDefect q a lower (upper + Nat.succ c * q) =
            conductorBoundaryDefect q a lower ((upper + c * q) + q) := by
              simp only [Nat.succ_mul, Nat.add_assoc]
        _ = conductorBoundaryDefect q a lower (upper + c * q) :=
          conductorBoundaryDefect_add_conductor hq a lower
            (upper + c * q) hle
        _ = conductorBoundaryDefect q a lower upper := ih

/-- Reduce a conductor boundary defect to the unique incomplete `q`-period
following the pinned lower endpoint. -/
theorem conductorBoundaryDefect_eq_short_remainder
    {q : ℕ} (hq : 1 < q)
    (a lower upper : ℕ) (hlower : lower ≤ upper) :
    conductorBoundaryDefect q a lower upper =
      conductorBoundaryDefect q a lower
        (lower + ((upper - lower) % q)) := by
  let n := upper - lower
  let r := n % q
  let c := n / q
  have hupper : upper = lower + n := by
    dsimp [n]
    omega
  have hdivmod : n = c * q + r := by
    dsimp [c, r]
    calc
      upper - lower = q * ((upper - lower) / q) + (upper - lower) % q :=
        (Nat.div_add_mod (upper - lower) q).symm
      _ = ((upper - lower) / q) * q + (upper - lower) % q := by
        rw [Nat.mul_comm q ((upper - lower) / q)]
  have hre : lower ≤ lower + r := Nat.le_add_right _ _
  have harg : upper = (lower + r) + c * q := by
    rw [hupper, hdivmod]
    omega
  calc
    conductorBoundaryDefect q a lower upper =
        conductorBoundaryDefect q a lower ((lower + r) + c * q) := by
          rw [harg]
    _ = conductorBoundaryDefect q a lower (lower + r) :=
      conductorBoundaryDefect_add_mul_conductor hq a lower (lower + r) c hre
    _ = conductorBoundaryDefect q a lower
        (lower + ((upper - lower) % q)) := by
      rfl

/-- Uniform cubic bound for every nontrivial conductor boundary defect.  This is
where exact periodicity becomes a quantitative estimate. -/
theorem abs_conductorBoundaryDefect_le_two_mul_cube
    {q : ℕ} (hq : 1 < q)
    (a lower upper : ℕ) (hlower : lower ≤ upper) :
    |conductorBoundaryDefect q a lower upper| ≤
      2 * (q : ℤ) ^ 3 := by
  classical
  rw [conductorBoundaryDefect_eq_short_remainder hq a lower upper hlower]
  let r := (upper - lower) % q
  have hqpos : 0 < q := Nat.zero_lt_of_lt hq
  have hrlt : r < q := by
    dsimp [r]
    exact Nat.mod_lt _ hqpos
  unfold conductorBoundaryDefect
  calc
    |∑ d ∈ q.divisors,
        μ (q / d) * divisorIntervalBoundary d a lower (lower + r)| ≤
      ∑ d ∈ q.divisors,
        |μ (q / d) * divisorIntervalBoundary d a lower (lower + r)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ q.divisors, 2 * (q : ℤ) ^ 2 := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hdq : d ≤ q := Nat.divisor_le hdmem
      have hbound := abs_divisorIntervalBoundary_le_two_mul_sq_of_short
        d a lower (lower + r) q hdq
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqpos))
        (by simpa using hrlt)
      rw [abs_mul]
      have hmu := ArithmeticFunction.abs_moebius_le_one (n := q / d)
      have hb0 : (0 : ℤ) ≤ |divisorIntervalBoundary d a lower (lower + r)| :=
        abs_nonneg _
      calc
        |μ (q / d)| * |divisorIntervalBoundary d a lower (lower + r)| ≤
            1 * |divisorIntervalBoundary d a lower (lower + r)| := by
              exact mul_le_mul_of_nonneg_right hmu hb0
        _ ≤ 2 * (q : ℤ) ^ 2 := by simpa using hbound
    _ = ((q.divisors.card : ℕ) : ℤ) * (2 * (q : ℤ) ^ 2) := by
      simp [Finset.sum_const]
    _ ≤ (q : ℤ) * (2 * (q : ℤ) ^ 2) := by
      have hcard : ((q.divisors.card : ℕ) : ℤ) ≤ (q : ℤ) := by
        exact_mod_cast Nat.card_divisors_le_self q
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * (q : ℤ) ^ 3 := by ring

private theorem norm_localPrimeComb_cast_le_one (p n : ℕ) :
    ‖(((localPrimeComb p n : ℤ) : ℂ))‖ ≤ 1 := by
  unfold localPrimeComb
  split_ifs <;> norm_num

private theorem norm_primeCombProduct_cast_le_one
    (S : Finset ℕ) (n : ℕ) :
    ‖(((∏ p ∈ S, localPrimeComb p n : ℤ) : ℂ))‖ ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      rw [Finset.prod_insert hp]
      push_cast at ih ⊢
      rw [norm_mul]
      have hS0 :
          0 ≤ ‖∏ x ∈ S, (((localPrimeComb x n : ℤ) : ℂ))‖ := norm_nonneg _
      have hp1 := norm_localPrimeComb_cast_le_one p n
      calc
        ‖(((localPrimeComb p n : ℤ) : ℂ))‖ *
            ‖∏ x ∈ S, (((localPrimeComb x n : ℤ) : ℂ))‖ ≤
          1 * ‖∏ x ∈ S, (((localPrimeComb x n : ℤ) : ℂ))‖ :=
            mul_le_mul_of_nonneg_right hp1 hS0
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = 1 := by norm_num

private theorem norm_seededPrimeComb_cast_le_one
    (S : Finset ℕ) (n : ℕ) :
    ‖(((seededPrimeComb S n : ℤ) : ℂ))‖ ≤ 1 := by
  unfold seededPrimeComb
  push_cast
  rw [norm_neg]
  have h := norm_primeCombProduct_cast_le_one S n
  push_cast at h
  exact h

/-- Every raw periodic Fourier coefficient is bounded by the torus modulus. -/
theorem norm_primorialPeriodicRawSpectrum_le_modulus
    (k : ℕ) (r : ZMod (primorialMinimalWheelSystem k).modulus) :
    ‖primorialPeriodicRawSpectrum k r‖ ≤
      ((primorialMinimalWheelSystem k).modulus : ℝ) := by
  unfold primorialPeriodicRawSpectrum primorialPeriodicRawTorusField
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  calc
    ‖∑ z : ZMod (primorialMinimalWheelSystem k).modulus,
        ZMod.stdAddChar (-(z * r)) *
          ((((primorialMinimalWheelSystem k).rawSite z.val : ℤ) : ℂ))‖ ≤
      ∑ z : ZMod (primorialMinimalWheelSystem k).modulus,
        ‖ZMod.stdAddChar (-(z * r)) *
          ((((primorialMinimalWheelSystem k).rawSite z.val : ℤ) : ℂ))‖ := by
            exact norm_sum_le _ _
    _ ≤ ∑ _z : ZMod (primorialMinimalWheelSystem k).modulus, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [norm_mul]
      have hchar : ‖ZMod.stdAddChar (-(z * r))‖ = 1 := by
        simp [ZMod.stdAddChar_apply]
      rw [hchar, one_mul]
      change
        ‖(((seededPrimeComb (primorialWheelPrimes k) z.val : ℤ) : ℂ))‖ ≤ 1
      exact norm_seededPrimeComb_cast_le_one (primorialWheelPrimes k) z.val
    _ = ((primorialMinimalWheelSystem k).modulus : ℝ) := by simp

/-- The arithmetic raw shell coefficient is itself bounded by the torus
modulus on every actual divisor conductor. -/
theorem norm_primorialRawConductorArithmeticCoefficient_le_modulus
    (k q : ℕ)
    (hqmem : q ∈ (primorialMinimalWheelSystem k).modulus.divisors) :
    ‖primorialRawConductorArithmeticCoefficient k q‖ ≤
      ((primorialMinimalWheelSystem k).modulus : ℝ) := by
  let Q := (primorialMinimalWheelSystem k).modulus
  have hQpos : 0 < Q := (primorialMinimalWheelSystem k).modulus_pos
  have hQne : Q ≠ 0 := Nat.ne_of_gt hQpos
  have hqpos : 0 < q := Nat.pos_of_mem_divisors hqmem
  have hqdiv : q ∣ Q := Nat.dvd_of_mem_divisors hqmem
  rcases hqdiv with ⟨m, hm⟩
  have hmpos : 0 < m := by
    subst Q
    nlinarith
  let r : ZMod Q := ((Q / q : ℕ) : ZMod Q)
  have hQdivq : Q / q = m := by
    rw [hm]
    simpa [Nat.mul_comm] using Nat.mul_div_left m hqpos
  have hmdvd : m ∣ Q := by
    refine ⟨q, ?_⟩
    simpa [Nat.mul_comm] using hm
  have hgcd : Q.gcd (Q / q) = Q / q := by
    apply Nat.gcd_eq_right_iff_dvd.mpr
    rw [hQdivq]
    exact hmdvd
  have horder : addOrderOf r = q := by
    dsimp [r]
    rw [ZMod.addOrderOf_coe (Q / q) hQne, hgcd, hQdivq]
    rw [hm]
    simpa [Nat.mul_comm] using Nat.mul_div_left q hmpos
  have hred : reducedAdditiveConductor r = q := by
    rw [reducedAdditiveConductor_eq_addOrderOf
      (primorialMinimalWheelSystem k) r]
    exact horder
  have hspec := norm_primorialPeriodicRawSpectrum_le_modulus k r
  rw [primorialPeriodicRawSpectrum_eq_rawConductorArithmeticCoefficient k r,
    hred] at hspec
  exact hspec

/-- The finite smooth divisor carrier is smaller than the ambient torus. -/
theorem card_primeWheelSmoothDivisorSites_le_modulus
    (W : PrimeWheelFiniteSystem) :
    (primeWheelSmoothDivisorSites W).card ≤ W.modulus := by
  calc
    (primeWheelSmoothDivisorSites W).card ≤ (Finset.range W.modulus).card := by
      apply Finset.card_le_card
      intro a ha
      have hupper : a ≤ W.upper := by
        exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1).2
      have halt : a < W.modulus := lt_of_le_of_lt hupper W.upper_lt_modulus
      exact Finset.mem_range.mpr halt
    _ = W.modulus := by simp

private theorem norm_smoothWeightedBoundarySum_le
    (W : PrimeWheelFiniteSystem) (x q : ℕ)
    (hq : 1 < q) (hlower : W.lower ≤ x) :
    ‖(((∑ a ∈ primeWheelSmoothDivisorSites W,
        μ a * conductorBoundaryDefect q a W.lower x : ℤ) : ℂ))‖ ≤
      (W.modulus : ℝ) * (2 * (q : ℝ) ^ 3) := by
  push_cast
  calc
    ‖∑ a ∈ primeWheelSmoothDivisorSites W,
        (((μ a : ℤ) : ℂ)) *
          (((conductorBoundaryDefect q a W.lower x : ℤ) : ℂ))‖ ≤
      ∑ a ∈ primeWheelSmoothDivisorSites W,
        ‖(((μ a : ℤ) : ℂ)) *
          (((conductorBoundaryDefect q a W.lower x : ℤ) : ℂ))‖ := by
            exact norm_sum_le _ _
    _ ≤ ∑ _a ∈ primeWheelSmoothDivisorSites W,
        (2 * (q : ℝ) ^ 3) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      have hmu : ‖(((μ a : ℤ) : ℂ))‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
      have hBint := abs_conductorBoundaryDefect_le_two_mul_cube hq a W.lower x hlower
      have hB :
          ‖(((conductorBoundaryDefect q a W.lower x : ℤ) : ℂ))‖ ≤
            2 * (q : ℝ) ^ 3 := by
        exact_mod_cast hBint
      have hB0 : 0 ≤ ‖(((conductorBoundaryDefect q a W.lower x : ℤ) : ℂ))‖ :=
        norm_nonneg _
      calc
        ‖(((μ a : ℤ) : ℂ))‖ *
            ‖(((conductorBoundaryDefect q a W.lower x : ℤ) : ℂ))‖ ≤
          1 * ‖(((conductorBoundaryDefect q a W.lower x : ℤ) : ℂ))‖ := by
            exact mul_le_mul_of_nonneg_right hmu hB0
        _ ≤ 2 * (q : ℝ) ^ 3 := by simpa using hB
    _ = ((primeWheelSmoothDivisorSites W).card : ℝ) *
        (2 * (q : ℝ) ^ 3) := by
      simp [Finset.sum_const]
    _ ≤ (W.modulus : ℝ) * (2 * (q : ℝ) ^ 3) := by
      have hcard : ((primeWheelSmoothDivisorSites W).card : ℝ) ≤ W.modulus := by
        exact_mod_cast card_primeWheelSmoothDivisorSites_le_modulus W
      exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-- **Uniform corrected-conductor bound.**  Every actual nontrivial conductor
packet is bounded independently of the prefix length by `6 q^3`. -/
theorem norm_primorialPeriodicRawJointConductorResponse_le_six_mul_cube
    (k x q : ℕ)
    (hqmem : q ∈ (primorialMinimalWheelSystem k).modulus.divisors)
    (hlower : (primorialMinimalWheelSystem k).lower ≤ x)
    (hupper : x ≤ (primorialMinimalWheelSystem k).upper)
    (hq : 1 < q) :
    ‖primorialPeriodicRawJointConductorResponse k x q‖ ≤
      6 * (q : ℝ) ^ 3 := by
  rw [primorialPeriodicRawJointConductorResponse_eq_boundaryDefectGeneral
    k x q hqmem hupper hq]
  rw [norm_mul]
  have hQpos : 0 < ((primorialMinimalWheelSystem k).modulus : ℝ) := by
    exact_mod_cast (primorialMinimalWheelSystem k).modulus_pos
  have hQinv :
      ‖(((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹)‖ =
        (((primorialMinimalWheelSystem k).modulus : ℝ))⁻¹ := by
    simp
  rw [hQinv]
  unfold primorialCorrectedConductorBoundaryNumerator
  have hrawC := norm_primorialRawConductorArithmeticCoefficient_le_modulus
    k q hqmem
  have hBint := abs_conductorBoundaryDefect_le_two_mul_cube hq 0
    (primorialMinimalWheelSystem k).lower x hlower
  have hB :
      ‖(((conductorBoundaryDefect q 0
        (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))‖ ≤
        2 * (q : ℝ) ^ 3 := by
    exact_mod_cast hBint
  have hsmooth := norm_smoothWeightedBoundarySum_le
    (primorialMinimalWheelSystem k) x q hq hlower
  calc
    (((primorialMinimalWheelSystem k).modulus : ℝ))⁻¹ *
        ‖primorialRawConductorArithmeticCoefficient k q *
            (((conductorBoundaryDefect q 0
              (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ)) +
          2 *
            (((∑ a ∈ primeWheelSmoothDivisorSites
                (primorialMinimalWheelSystem k),
              μ a * conductorBoundaryDefect q a
                (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))‖ ≤
      (((primorialMinimalWheelSystem k).modulus : ℝ))⁻¹ *
        (‖primorialRawConductorArithmeticCoefficient k q‖ *
            ‖(((conductorBoundaryDefect q 0
              (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))‖ +
          2 *
            ‖(((∑ a ∈ primeWheelSmoothDivisorSites
                (primorialMinimalWheelSystem k),
              μ a * conductorBoundaryDefect q a
                (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          ‖primorialRawConductorArithmeticCoefficient k q *
                (((conductorBoundaryDefect q 0
                  (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ)) +
              2 *
                (((∑ a ∈ primeWheelSmoothDivisorSites
                    (primorialMinimalWheelSystem k),
                  μ a * conductorBoundaryDefect q a
                    (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))‖ ≤
            ‖primorialRawConductorArithmeticCoefficient k q *
                (((conductorBoundaryDefect q 0
                  (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))‖ +
              ‖2 *
                (((∑ a ∈ primeWheelSmoothDivisorSites
                    (primorialMinimalWheelSystem k),
                  μ a * conductorBoundaryDefect q a
                    (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))‖ :=
              norm_add_le _ _
          _ = ‖primorialRawConductorArithmeticCoefficient k q‖ *
                ‖(((conductorBoundaryDefect q 0
                  (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))‖ +
              2 *
                ‖(((∑ a ∈ primeWheelSmoothDivisorSites
                    (primorialMinimalWheelSystem k),
                  μ a * conductorBoundaryDefect q a
                    (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))‖ := by
              simp
    _ ≤ (((primorialMinimalWheelSystem k).modulus : ℝ))⁻¹ *
        (((primorialMinimalWheelSystem k).modulus : ℝ) *
            (2 * (q : ℝ) ^ 3) +
          2 * (((primorialMinimalWheelSystem k).modulus : ℝ) *
            (2 * (q : ℝ) ^ 3))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul hrawC hB (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left hsmooth (by positivity))
    _ = 6 * (q : ℝ) ^ 3 := by
      field_simp
      ring

/-- Actual nontrivial conductor divisors up to a cutoff. -/
def primorialSmallNontrivialConductors (k R : ℕ) : Finset ℕ :=
  ((primorialMinimalWheelSystem k).modulus.divisors).filter fun q =>
    1 < q ∧ q ≤ R

/-- Combined corrected response of all nontrivial conductors up to `R`. -/
def primorialSmallNontrivialConductorSector
    (k x R : ℕ) : ℂ :=
  ∑ q ∈ primorialSmallNontrivialConductors k R,
    primorialPeriodicRawJointConductorResponse k x q

/-- **Growing-sector bound.**  All actual conductors `2 <= q <= R` together
contribute at most `6 (R+1) R^3`, uniformly in the prefix length. -/
theorem norm_primorialSmallNontrivialConductorSector_le
    (k x R : ℕ)
    (hlower : (primorialMinimalWheelSystem k).lower ≤ x)
    (hupper : x ≤ (primorialMinimalWheelSystem k).upper) :
    ‖primorialSmallNontrivialConductorSector k x R‖ ≤
      6 * (R + 1 : ℝ) * (R : ℝ) ^ 3 := by
  unfold primorialSmallNontrivialConductorSector
  calc
    ‖∑ q ∈ primorialSmallNontrivialConductors k R,
        primorialPeriodicRawJointConductorResponse k x q‖ ≤
      ∑ q ∈ primorialSmallNontrivialConductors k R,
        ‖primorialPeriodicRawJointConductorResponse k x q‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ _q ∈ primorialSmallNontrivialConductors k R,
        6 * (R : ℝ) ^ 3 := by
      apply Finset.sum_le_sum
      intro q hqset
      have hmem := Finset.mem_filter.mp hqset
      have hqmem : q ∈ (primorialMinimalWheelSystem k).modulus.divisors := hmem.1
      have hqgt : 1 < q := hmem.2.1
      have hqR : q ≤ R := hmem.2.2
      have hpacket := norm_primorialPeriodicRawJointConductorResponse_le_six_mul_cube
        k x q hqmem hlower hupper hqgt
      have hpow : (q : ℝ) ^ 3 ≤ (R : ℝ) ^ 3 := by
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hqR) 3
      exact hpacket.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    _ = ((primorialSmallNontrivialConductors k R).card : ℝ) *
        (6 * (R : ℝ) ^ 3) := by
      simp [Finset.sum_const]
    _ ≤ (R + 1 : ℝ) * (6 * (R : ℝ) ^ 3) := by
      have hcardNat : (primorialSmallNontrivialConductors k R).card ≤ R + 1 := by
        calc
          (primorialSmallNontrivialConductors k R).card ≤
              (Finset.range (R + 1)).card := by
            apply Finset.card_le_card
            intro q hqset
            have hmem := Finset.mem_filter.mp hqset
            exact Finset.mem_range.mpr (Nat.lt_succ_of_le hmem.2.2)
          _ = R + 1 := by simp
      have hcard : ((primorialSmallNontrivialConductors k R).card : ℝ) ≤ R + 1 := by
        exact_mod_cast hcardNat
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 6 * (R + 1 : ℝ) * (R : ℝ) ^ 3 := by ring

end RHLean.Analysis
