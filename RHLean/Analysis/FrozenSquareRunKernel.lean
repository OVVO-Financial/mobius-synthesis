import Mathlib
import RHLean.Arithmetic.DyadicFrozenPrefix
import RHLean.Analysis.NativePNTMertens
import RHLean.Analysis.SquareRunEscapeCovariance
import RHLean.Proof.PrimeCombReciprocalBandCancellation

open scoped ArithmeticFunction.Moebius BigOperators

/-!
# Frozen square-run kernel

This file packages the exact subdoubling identity from
`RHLean.Arithmetic.DyadicFrozenPrefix` in the divisor coordinate that is useful
for the next cancellation attack.

For a square run `[a^2,(b+1)^2)`, define

```text
w_{a,b}(d) = #{n in [a^2,(b+1)^2) : d | n}
           = floor((((b+1)^2)-1)/d) - floor((a^2-1)/d),
```

and the signed frozen kernel

```text
K(a,b) = sum_{1 <= d < a^2} mu(d) w_{a,b}(d).
```

On a subdoubling run `((b+1)^2 <= 2*a^2)`, every proper divisor consulted by
any new site lies strictly below `a^2`, so `K(a,b)` is exactly the negative new
Möbius mass.  No value of `mu` created inside the run appears in the kernel.

The named energy premise below deliberately squares the *whole signed divisor
sum*.  The subsequent Green--Kubo identity expands that square into the exact
divisor diagonal plus twice the signed divisor covariance.  In particular, no
termwise absolute value is taken before the `d`-sum.

The criterion equivalence is also recorded here.  The nontrivial direction is
not definitional: the kernel premise is only subdoubling-local.  A fixed
three-quarter anchor gives a contracting recurrence for square-prefix Mertens
energy, and the existing square-prefix interpolation then gives the global
Mertens/wheel criterion.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## Exact frozen kernel -/

/-- The divisor-incidence weight of `d` across the complete square run.
The closed floor form is proved immediately below. -/
def frozenFloorWeight (a b d : ℕ) : ℕ :=
  frozenRunDivisorWeight (a ^ 2) ((b + 1) ^ 2) d

/-- The frozen weight is literally the difference of the two reciprocal floors. -/
theorem frozenFloorWeight_eq_div_sub_div
    {a b d : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    frozenFloorWeight a b d =
      (((b + 1) ^ 2 - 1) / d - (a ^ 2 - 1) / d) := by
  have hbase : 1 ≤ a ^ 2 := by nlinarith
  have hNL : a ^ 2 ≤ (b + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  simpa [frozenFloorWeight] using
    (RHLean.Arithmetic.frozenRunDivisorWeight_eq_div_sub_div
      (N := a ^ 2) (L := (b + 1) ^ 2) (d := d) hbase hNL)

/-- The explicit signed frozen divisor kernel.  The `d = 0` coordinate is
excluded rather than silently carried as a zero term. -/
def frozenSquareRunKernel (a b : ℕ) : ℂ :=
  ∑ d ∈ Finset.Ico 1 (a ^ 2),
    (((μ d : ℤ) : ℂ)) * ((frozenFloorWeight a b d : ℕ) : ℂ)

/-- The explicit `d >= 1` kernel is exactly the cast of the static
correlation.  The missing `d = 0` term is zero. -/
theorem frozenSquareRunKernel_eq_staticCorrelation_cast
    (a b : ℕ) (ha : 1 ≤ a) :
    frozenSquareRunKernel a b =
      ((RHLean.Arithmetic.squareFrozenRunCorrelation a b : ℤ) : ℂ) := by
  have hA : 1 ≤ a ^ 2 := by nlinarith
  have hsplit :=
    Finset.sum_range_add_sum_Ico
      (fun d : ℕ =>
        (frozenRunDivisorWeight (a ^ 2) ((b + 1) ^ 2) d : ℤ) * μ d)
      hA
  have hIco :
      (∑ d ∈ Finset.Ico 1 (a ^ 2),
          (frozenRunDivisorWeight (a ^ 2) ((b + 1) ^ 2) d : ℤ) * μ d) =
        ∑ d ∈ Finset.range (a ^ 2),
          (frozenRunDivisorWeight (a ^ 2) ((b + 1) ^ 2) d : ℤ) * μ d := by
    simpa using hsplit
  have hcast := congrArg (fun z : ℤ => (z : ℂ)) hIco
  push_cast at hcast
  unfold frozenSquareRunKernel RHLean.Arithmetic.squareFrozenRunCorrelation
  simpa [frozenFloorWeight, mul_comm] using hcast

/-- Square-prefix Mertens is the complex cast of the half-open integer prefix at
the following square. -/
theorem squarePrefixMertens_eq_moebiusRangePrefix_square_cast (n : ℕ) :
    squarePrefixMertens n =
      ((RHLean.Arithmetic.moebiusRangePrefix ((n + 1) ^ 2) : ℤ) : ℂ) := by
  unfold squarePrefixMertens mertensSummatory RHLean.Arithmetic.moebiusRangePrefix
  rw [squarePrefixEndpoint_add_one]
  push_cast
  rfl

/-- **Exact frozen-run identity in square-prefix coordinates.**  On a
subdoubling run the frozen divisor kernel is the old square-prefix value minus
the new one. -/
theorem frozenSquareRunKernel_eq_squarePrefix_sub
    (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hsub : (b + 1) ^ 2 ≤ 2 * (a ^ 2)) :
    frozenSquareRunKernel a b =
      squarePrefixMertens (a - 1) - squarePrefixMertens b := by
  rw [frozenSquareRunKernel_eq_staticCorrelation_cast a b (by omega)]
  have hcorr :=
    RHLean.Arithmetic.squareFrozenRunCorrelation_eq_prefix_sub ha hab hsub
  rw [hcorr]
  push_cast
  have hA := squarePrefixMertens_eq_moebiusRangePrefix_square_cast (a - 1)
  have hpred : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
  rw [hpred] at hA
  have hB := squarePrefixMertens_eq_moebiusRangePrefix_square_cast b
  rw [← hA, ← hB]

/-- Direct restatement of the frozen-run mass identity in the new
kernel coordinate. -/
theorem squareFrozenRunMass_cast_eq_neg_frozenSquareRunKernel
    (a b : ℕ) (ha : 2 ≤ a)
    (hsub : (b + 1) ^ 2 ≤ 2 * (a ^ 2)) :
    ((RHLean.Arithmetic.squareFrozenRunMass a b : ℤ) : ℂ) =
      -frozenSquareRunKernel a b := by
  have hm :=
    RHLean.Arithmetic.squareFrozenRunMass_eq_neg_staticCorrelation a b ha hsub
  have hk := frozenSquareRunKernel_eq_staticCorrelation_cast a b (by omega)
  calc
    ((RHLean.Arithmetic.squareFrozenRunMass a b : ℤ) : ℂ) =
        ((-(RHLean.Arithmetic.squareFrozenRunCorrelation a b) : ℤ) : ℂ) := by
          rw [hm]
    _ = -((RHLean.Arithmetic.squareFrozenRunCorrelation a b : ℤ) : ℂ) := by
          push_cast
          rfl
    _ = -frozenSquareRunKernel a b := by rw [hk]

/-- The same exact identity against the repository's canonical square-run
increment. -/
theorem frozenSquareRunKernel_eq_neg_canonicalRun
    (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hsub : (b + 1) ^ 2 ≤ 2 * (a ^ 2)) :
    frozenSquareRunKernel a b =
      -(∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j) := by
  have hk := frozenSquareRunKernel_eq_squarePrefix_sub a b ha hab hsub
  have hc :=
    RHLean.Proof.sum_canonicalTotalIncrement_Ico_eq_squarePrefix_sub
      a b (by omega) (by omega)
  rw [hk, hc]
  ring

/-- Hence the kernel energy is *equal* to the existing signed square-run energy
on every subdoubling window. -/
theorem norm_frozenSquareRunKernel_sq_eq_canonicalRun
    (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hsub : (b + 1) ^ 2 ≤ 2 * (a ^ 2)) :
    ‖frozenSquareRunKernel a b‖ ^ 2 =
      ‖∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j‖ ^ 2 := by
  rw [frozenSquareRunKernel_eq_neg_canonicalRun a b ha hab hsub, norm_neg]

/-! ## The named RH-scale energy premise -/

/-- **Frozen square-run energy bound.**  The whole signed divisor sum is kept
intact until after summation.  The strict subdoubling condition is the natural
"frozen before the run" regime. -/
def FrozenSquareRunEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ,
        (b + 1) ^ 2 < 2 * a ^ 2 →
        ‖frozenSquareRunKernel a b‖ ^ 2 ≤
          C * Real.rpow (((b + 1) ^ 2 : ℕ) : ℝ) (1 + ε)

/-! ## Signed divisor covariance: no absolute values before the d-sum -/

/-- One real signed divisor coordinate of the frozen kernel. -/
def frozenSquareRunKernelTerm (a b d : ℕ) : ℝ :=
  ((μ d : ℤ) : ℝ) * (frozenFloorWeight a b d : ℝ)

/-- The same frozen kernel, viewed as a real signed sum. -/
def frozenSquareRunKernelReal (a b : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ico 1 (a ^ 2), frozenSquareRunKernelTerm a b d

/-- The complex kernel is a real cast. -/
theorem frozenSquareRunKernel_eq_real_cast (a b : ℕ) :
    frozenSquareRunKernel a b = (frozenSquareRunKernelReal a b : ℂ) := by
  unfold frozenSquareRunKernel frozenSquareRunKernelReal frozenSquareRunKernelTerm
  push_cast
  rfl

/-- Divisor-coordinate diagonal after the whole signed kernel has been exposed. -/
def frozenSquareRunKernelDiagonal (a b : ℕ) : ℝ :=
  signedBlockEnergy (frozenSquareRunKernelTerm a b) (a ^ 2) -
    signedBlockEnergy (frozenSquareRunKernelTerm a b) 1

/-- Exact within-kernel covariance in the frozen divisor coordinate. -/
def frozenSquareRunKernelCovariance (a b : ℕ) : ℝ :=
  signedBlockInnerCovariance (frozenSquareRunKernelTerm a b) 1 (a ^ 2)

/-- The real kernel sum is the generic signed-block window `[1,a^2)`. -/
theorem frozenSquareRunKernelReal_eq_prefix_sub
    (a b : ℕ) (ha : 1 ≤ a) :
    frozenSquareRunKernelReal a b =
      signedBlockPrefix (frozenSquareRunKernelTerm a b) (a ^ 2) -
        signedBlockPrefix (frozenSquareRunKernelTerm a b) 1 := by
  have hA : 1 ≤ a ^ 2 := by nlinarith
  unfold frozenSquareRunKernelReal signedBlockPrefix
  exact Finset.sum_Ico_eq_sub _ hA

/-- **Divisor Green--Kubo.**  This is the first analytic attack surface for the
kernel.  The full signed `d`-sum is squared first; only then is it decomposed
into diagonal plus twice covariance. -/
theorem frozenSquareRunKernel_energy_eq_diagonal_add_two_covariance
    (a b : ℕ) (ha : 1 ≤ a) :
    ‖frozenSquareRunKernel a b‖ ^ 2 =
      frozenSquareRunKernelDiagonal a b +
        2 * frozenSquareRunKernelCovariance a b := by
  have hreal := frozenSquareRunKernel_eq_real_cast a b
  have hpref := frozenSquareRunKernelReal_eq_prefix_sub a b ha
  have hGK :=
    signedBlockPrefix_sub_sq_eq_energy_sub_add_two_mul_inner
      (frozenSquareRunKernelTerm a b) 1 (a ^ 2)
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, sq_abs, hpref]
  simpa [frozenSquareRunKernelDiagonal, frozenSquareRunKernelCovariance] using hGK

/-! ## Reciprocal-band coordinates for the floor kernel -/

/-- The unfiltered reciprocal quotient band.  Its prime sub-band is exactly the
existing prime-comb reciprocal band. -/
def frozenReciprocalBand (W z : ℕ) : Finset ℕ :=
  Finset.Ioc (W / (z + 1)) (W / z)

@[simp] theorem mem_frozenReciprocalBand {W z d : ℕ} :
    d ∈ frozenReciprocalBand W z ↔ W / (z + 1) < d ∧ d ≤ W / z := by
  simp [frozenReciprocalBand]

/-- Every positive reciprocal band is a constant quotient cell. -/
theorem frozenReciprocalBand_div_eq
    {W z d : ℕ} (hz : 0 < z) (hd : d ∈ frozenReciprocalBand W z) :
    W / d = z := by
  rcases mem_frozenReciprocalBand.mp hd with ⟨hlower, hupper⟩
  have hlo : z * d ≤ W := by
    have h := (Nat.le_div_iff_mul_le hz).1 hupper
    simpa [Nat.mul_comm] using h
  have hhi : W < (z + 1) * d := by
    have h := (Nat.div_lt_iff_lt_mul (by omega : 0 < z + 1)).1 hlower
    simpa [Nat.mul_comm] using h
  exact Nat.div_eq_of_lt_le hlo hhi

/-- Compatibility with the already-formalized prime-comb reciprocal geometry. -/
theorem primeCombReciprocalBand_eq_filter_frozenReciprocalBand (W z : ℕ) :
    primeCombReciprocalBand W z =
      (frozenReciprocalBand W z).filter Nat.Prime := by
  rfl

/-- On one reciprocal band the upper endpoint part of the floor weight is
constant.  This is the exact bridge from the divisor kernel to reciprocal-band
coordinates; no magnitude bound is taken. -/
theorem frozenFloorWeight_upperQuotient_eq
    {b d z : ℕ} (hz : 0 < z)
    (hd : d ∈ frozenReciprocalBand (((b + 1) ^ 2) - 1) z) :
    ((((b + 1) ^ 2) - 1) / d) = z :=
  frozenReciprocalBand_div_eq hz hd

/-! ## Equivalence to the existing Mertens / square-run / wheel criterion -/

private theorem norm_sq_add_le_five_quarter (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤
      ((5 : ℝ) / 4) * ‖x‖ ^ 2 + 5 * ‖y‖ ^ 2 := by
  have hnorm := norm_add_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x + y‖ := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - 4 * ‖y‖)]

private theorem norm_sq_sub_le_two_frozen (x y : ℂ) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := by
    simpa [sub_eq_add_neg] using norm_add_le x (-y)
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x - y‖ := norm_nonneg (x - y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Physical square energy exponent written in root coordinates. -/
private theorem rpow_nat_square_one_add (n : ℕ) (ε : ℝ) :
    Real.rpow (((n ^ 2 : ℕ) : ℝ)) (1 + ε) =
      Real.rpow (n : ℝ) (2 + 2 * ε) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcast : ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ (2 : ℕ) := by
    push_cast
    ring
  have htwo : Real.rpow (n : ℝ) (2 : ℝ) = (n : ℝ) ^ (2 : ℕ) :=
    Real.rpow_natCast (n : ℝ) 2
  calc
    Real.rpow (((n ^ 2 : ℕ) : ℝ)) (1 + ε) =
        Real.rpow ((n : ℝ) ^ (2 : ℕ)) (1 + ε) := by rw [hcast]
    _ = Real.rpow (Real.rpow (n : ℝ) (2 : ℝ)) (1 + ε) := by rw [htwo]
    _ = Real.rpow (n : ℝ) ((2 : ℝ) * (1 + ε)) :=
      (Real.rpow_mul hn 2 (1 + ε)).symm
    _ = Real.rpow (n : ℝ) (2 + 2 * ε) := by
      congr 1
      ring

/-- If the run points backwards, its physical interval is empty and so is the
frozen kernel. -/
theorem frozenSquareRunKernel_eq_zero_of_succ_le
    {a b : ℕ} (hba : b + 1 ≤ a) :
    frozenSquareRunKernel a b = 0 := by
  have hsq : (b + 1) ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hba 2
  have hempty :
      frozenRunBlock (a ^ 2) ((b + 1) ^ 2) = ∅ := by
    ext n
    simp [frozenRunBlock]
    omega
  unfold frozenSquareRunKernel frozenFloorWeight frozenRunDivisorWeight
  rw [hempty]
  simp

/-- Global Mertens energy immediately implies the frozen kernel premise. -/
theorem frozenSquareRunEnergyBounded_of_mertensEnergyBounded
    (hM : MertensEnergyBoundedStatement) :
    FrozenSquareRunEnergyBoundedStatement := by
  have hS : SquarePrefixEnergyBoundedStatement :=
    squarePrefixEnergyBounded_of_mertensEnergyBounded hM
  intro ε hε
  rcases hS (2 * ε) (by linarith) with ⟨C, hC, hbound⟩
  refine ⟨4 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro a b hsub
  by_cases hab : a ≤ b
  · have ha2 : 2 ≤ a := by
      have hmono : (a + 1) ^ 2 ≤ (b + 1) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      by_contra hnot
      have hale : a ≤ 1 := by omega
      nlinarith
    have hk := frozenSquareRunKernel_eq_squarePrefix_sub a b ha2 hab hsub.le
    have hA := hbound (a - 1)
    have hB := hbound b
    have hpred : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
    rw [hpred] at hA
    have ha_le : a ≤ b + 1 := by omega
    have ha_le_real : (a : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by
      exact_mod_cast ha_le
    have hpowAB :
        Real.rpow (a : ℝ) (2 + 2 * ε) ≤
          Real.rpow ((b + 1 : ℕ) : ℝ) (2 + 2 * ε) :=
      Real.rpow_le_rpow (Nat.cast_nonneg a) ha_le_real
        (by linarith : 0 ≤ 2 + 2 * ε)
    have hA' :
        ‖squarePrefixMertens (a - 1)‖ ^ 2 ≤
          C * Real.rpow ((b + 1 : ℕ) : ℝ) (2 + 2 * ε) :=
      hA.trans (mul_le_mul_of_nonneg_left hpowAB hC)
    have htwo := norm_sq_sub_le_two_frozen
      (squarePrefixMertens (a - 1)) (squarePrefixMertens b)
    rw [hk]
    calc
      ‖squarePrefixMertens (a - 1) - squarePrefixMertens b‖ ^ 2 ≤
          2 * ‖squarePrefixMertens (a - 1)‖ ^ 2 +
            2 * ‖squarePrefixMertens b‖ ^ 2 := htwo
      _ ≤ 2 * (C * Real.rpow ((b + 1 : ℕ) : ℝ) (2 + 2 * ε)) +
            2 * (C * Real.rpow ((b + 1 : ℕ) : ℝ) (2 + 2 * ε)) := by
          nlinarith
      _ = 4 * C * Real.rpow (((b + 1) ^ 2 : ℕ) : ℝ) (1 + ε) := by
          rw [rpow_nat_square_one_add]
          ring
  · have hba : b + 1 ≤ a := by omega
    rw [frozenSquareRunKernel_eq_zero_of_succ_le hba]
    have hp0 : 0 ≤ Real.rpow (((b + 1) ^ 2 : ℕ) : ℝ) (1 + ε) :=
      Real.rpow_nonneg (by positivity) _
    have hrhs :
        0 ≤ 4 * C * Real.rpow (((b + 1) ^ 2 : ℕ) : ℝ) (1 + ε) :=
      mul_nonneg (mul_nonneg (by norm_num) hC) hp0
    simpa using hrhs

/-- A fixed three-quarter anchor.  It is above the `1/sqrt 2` freezing
threshold, while from scale `14` onward it is at most four-fifths of the
terminal root. -/
def frozenSquareAnchor (b : ℕ) : ℕ :=
  (3 * (b + 1) + 3) / 4

private theorem frozenSquareAnchor_lower (b : ℕ) :
    3 * (b + 1) ≤ 4 * frozenSquareAnchor b := by
  unfold frozenSquareAnchor
  omega

private theorem frozenSquareAnchor_upper (b : ℕ) :
    4 * frozenSquareAnchor b ≤ 3 * (b + 1) + 3 := by
  unfold frozenSquareAnchor
  omega

private theorem frozenSquareAnchor_pos (b : ℕ) : 1 ≤ frozenSquareAnchor b := by
  have h := frozenSquareAnchor_lower b
  omega

private theorem frozenSquareAnchor_le (b : ℕ) (hb : 14 ≤ b) :
    frozenSquareAnchor b ≤ b := by
  have h := frozenSquareAnchor_upper b
  omega

private theorem frozenSquareAnchor_five_le_four (b : ℕ) (hb : 14 ≤ b) :
    5 * frozenSquareAnchor b ≤ 4 * (b + 1) := by
  have h := frozenSquareAnchor_upper b
  omega

private theorem frozenSquareAnchor_subdoubling (b : ℕ) :
    (b + 1) ^ 2 < 2 * frozenSquareAnchor b ^ 2 := by
  have h := frozenSquareAnchor_lower b
  have hs := Nat.pow_le_pow_left h 2
  have hy : 0 < (b + 1) ^ 2 := by positivity
  nlinarith

private theorem frozenSquareAnchor_rpow_le
    (b : ℕ) (hb : 14 ≤ b) (ε : ℝ) (hε : 0 ≤ ε) :
    Real.rpow (frozenSquareAnchor b : ℝ) (2 + ε) ≤
      ((16 : ℝ) / 25) * Real.rpow ((b + 1 : ℕ) : ℝ) (2 + ε) := by
  let a := frozenSquareAnchor b
  let y := b + 1
  change Real.rpow (a : ℝ) (2 + ε) ≤
    ((16 : ℝ) / 25) * Real.rpow (y : ℝ) (2 + ε)
  have ha1 : 1 ≤ a := by dsimp [a]; exact frozenSquareAnchor_pos b
  have hy1 : 1 ≤ y := by dsimp [y]; omega
  have h5 : 5 * a ≤ 4 * y := by
    dsimp [a, y]
    exact frozenSquareAnchor_five_le_four b hb
  have hay : a ≤ y := by omega
  have hsNat : (5 * a) ^ 2 ≤ (4 * y) ^ 2 := Nat.pow_le_pow_left h5 2
  have hsReal :
      (a : ℝ) ^ 2 ≤ ((16 : ℝ) / 25) * (y : ℝ) ^ 2 := by
    have hsCast : ((5 * a : ℕ) : ℝ) ^ 2 ≤ ((4 * y : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hsNat
    push_cast at hsCast
    nlinarith
  have hayReal : (a : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast hay
  have he :
      Real.rpow (a : ℝ) ε ≤ Real.rpow (y : ℝ) ε :=
    Real.rpow_le_rpow (Nat.cast_nonneg a) hayReal hε
  have haPos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
  have hyPos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy1
  have htwoA : Real.rpow (a : ℝ) (2 : ℝ) = (a : ℝ) ^ (2 : ℕ) :=
    Real.rpow_natCast (a : ℝ) 2
  have htwoY : Real.rpow (y : ℝ) (2 : ℝ) = (y : ℝ) ^ (2 : ℕ) :=
    Real.rpow_natCast (y : ℝ) 2
  have haSplit :
      Real.rpow (a : ℝ) (2 + ε) =
        (a : ℝ) ^ 2 * Real.rpow (a : ℝ) ε := by
    calc
      Real.rpow (a : ℝ) (2 + ε) =
          Real.rpow (a : ℝ) 2 * Real.rpow (a : ℝ) ε :=
        Real.rpow_add haPos 2 ε
      _ = (a : ℝ) ^ 2 * Real.rpow (a : ℝ) ε := by
        rw [htwoA]
  have hySplit :
      Real.rpow (y : ℝ) (2 + ε) =
        (y : ℝ) ^ 2 * Real.rpow (y : ℝ) ε := by
    calc
      Real.rpow (y : ℝ) (2 + ε) =
          Real.rpow (y : ℝ) 2 * Real.rpow (y : ℝ) ε :=
        Real.rpow_add hyPos 2 ε
      _ = (y : ℝ) ^ 2 * Real.rpow (y : ℝ) ε := by
        rw [htwoY]
  rw [haSplit, hySplit]
  calc
    (a : ℝ) ^ 2 * Real.rpow (a : ℝ) ε ≤
        (((16 : ℝ) / 25) * (y : ℝ) ^ 2) * Real.rpow (a : ℝ) ε :=
      mul_le_mul_of_nonneg_right hsReal (Real.rpow_nonneg (by positivity) _)
    _ ≤ (((16 : ℝ) / 25) * (y : ℝ) ^ 2) * Real.rpow (y : ℝ) ε :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((16 : ℝ) / 25) *
        ((y : ℝ) ^ 2 * Real.rpow (y : ℝ) ε) := by ring

/-- The subdoubling kernel premise contracts to the full square-prefix Mertens
energy criterion. -/
theorem squarePrefixEnergyBounded_of_frozenSquareRunEnergyBounded
    (hF : FrozenSquareRunEnergyBoundedStatement) :
    SquarePrefixEnergyBoundedStatement := by
  intro ε hε
  rcases hF (ε / 2) (by linarith) with ⟨C, hC, hkernel⟩
  let B : ℝ := ∑ n ∈ Finset.range 14, ‖squarePrefixMertens n‖ ^ 2
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let D : ℝ := 25 * C + B
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hDC : 25 * C ≤ D := by dsimp [D]; linarith
  have hcontract : ((4 : ℝ) / 5) * D + 5 * C ≤ D := by
    nlinarith
  refine ⟨D, hD0, ?_⟩
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
      by_cases hsmall : b < 14
      · have hbmem : b ∈ Finset.range 14 := Finset.mem_range.mpr hsmall
        have hsingle : ‖squarePrefixMertens b‖ ^ 2 ≤ B := by
          dsimp [B]
          exact Finset.single_le_sum
            (fun n _ => sq_nonneg ‖squarePrefixMertens n‖) hbmem
        have hbase : (1 : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 1 ≤ b + 1)
        have hp :
            (1 : ℝ) ≤ Real.rpow ((b + 1 : ℕ) : ℝ) (2 + ε) :=
          Real.one_le_rpow hbase (by linarith)
        have hBD : B ≤ D := by dsimp [D]; linarith
        calc
          ‖squarePrefixMertens b‖ ^ 2 ≤ B := hsingle
          _ ≤ D := hBD
          _ ≤ D * Real.rpow ((b + 1 : ℕ) : ℝ) (2 + ε) := by
            simpa using mul_le_mul_of_nonneg_left hp hD0
      · have hb14 : 14 ≤ b := by omega
        let a := frozenSquareAnchor b
        have ha1 : 1 ≤ a := by dsimp [a]; exact frozenSquareAnchor_pos b
        have ha2 : 2 ≤ a := by
          have hle := frozenSquareAnchor_le b hb14
          have hlow := frozenSquareAnchor_lower b
          dsimp [a]
          omega
        have hab : a ≤ b := by dsimp [a]; exact frozenSquareAnchor_le b hb14
        have hsubStrict : (b + 1) ^ 2 < 2 * a ^ 2 := by
          dsimp [a]
          exact frozenSquareAnchor_subdoubling b
        have hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2 := hsubStrict.le
        have hprevIndex : a - 1 < b := by omega
        have hprev := ih (a - 1) hprevIndex
        have hpred : a - 1 + 1 = a := Nat.sub_add_cancel ha1
        rw [hpred] at hprev
        have hratio := frozenSquareAnchor_rpow_le b hb14 ε hε.le
        have hprevScaled :
            ‖squarePrefixMertens (a - 1)‖ ^ 2 ≤
              D * (((16 : ℝ) / 25) *
                Real.rpow ((b + 1 : ℕ) : ℝ) (2 + ε)) :=
          hprev.trans (mul_le_mul_of_nonneg_left hratio hD0)
        have hkRaw := hkernel a b hsubStrict
        have hk :
            ‖frozenSquareRunKernel a b‖ ^ 2 ≤
              C * Real.rpow ((b + 1 : ℕ) : ℝ) (2 + ε) := by
          calc
            ‖frozenSquareRunKernel a b‖ ^ 2 ≤
                C * Real.rpow (((b + 1) ^ 2 : ℕ) : ℝ) (1 + ε / 2) := hkRaw
            _ = C * Real.rpow ((b + 1 : ℕ) : ℝ) (2 + ε) := by
              rw [rpow_nat_square_one_add]
              congr 2
              ring
        have hkeq := frozenSquareRunKernel_eq_squarePrefix_sub a b ha2 hab hsub
        have hdecomp :
            squarePrefixMertens b =
              squarePrefixMertens (a - 1) + (-frozenSquareRunKernel a b) := by
          rw [hkeq]
          ring
        have hadd := norm_sq_add_le_five_quarter
          (squarePrefixMertens (a - 1)) (-frozenSquareRunKernel a b)
        rw [hdecomp]
        calc
          ‖squarePrefixMertens (a - 1) + (-frozenSquareRunKernel a b)‖ ^ 2 ≤
              ((5 : ℝ) / 4) * ‖squarePrefixMertens (a - 1)‖ ^ 2 +
                5 * ‖-frozenSquareRunKernel a b‖ ^ 2 := hadd
          _ = ((5 : ℝ) / 4) * ‖squarePrefixMertens (a - 1)‖ ^ 2 +
                5 * ‖frozenSquareRunKernel a b‖ ^ 2 := by rw [norm_neg]
          _ ≤ ((5 : ℝ) / 4) *
                (D * (((16 : ℝ) / 25) *
                  Real.rpow ((b + 1 : ℕ) : ℝ) (2 + ε))) +
                5 * (C * Real.rpow ((b + 1 : ℕ) : ℝ) (2 + ε)) := by
              gcongr
          _ = (((4 : ℝ) / 5) * D + 5 * C) *
                Real.rpow ((b + 1 : ℕ) : ℝ) (2 + ε) := by ring
          _ ≤ D * Real.rpow ((b + 1 : ℕ) : ℝ) (2 + ε) :=
            mul_le_mul_of_nonneg_right hcontract
              (Real.rpow_nonneg (by positivity) _)

/-- The frozen kernel criterion is exactly the ordinary global Mertens energy
criterion. -/
theorem frozenSquareRunEnergyBounded_iff_mertensEnergyBounded :
    FrozenSquareRunEnergyBoundedStatement ↔ MertensEnergyBoundedStatement := by
  constructor
  · intro hF
    exact mertensEnergyBounded_of_squarePrefixEnergyBounded
      (squarePrefixEnergyBounded_of_frozenSquareRunEnergyBounded hF)
  · exact frozenSquareRunEnergyBounded_of_mertensEnergyBounded

/-- Exact equivalence to the repository's maximal signed square-run criterion. -/
theorem frozenSquareRunEnergyBounded_iff_squareRunEnergyBounded :
    FrozenSquareRunEnergyBoundedStatement ↔ SquareRunEnergyBoundedStatement := by
  exact frozenSquareRunEnergyBounded_iff_mertensEnergyBounded.trans
    squareRunEnergyBounded_iff_mertensEnergy.symm

/-- Exact equivalence to the synchronized primorial-wheel residual criterion. -/
theorem frozenSquareRunEnergyBounded_iff_primorialResidualBounded :
    FrozenSquareRunEnergyBoundedStatement ↔
      PrimeWheelResidualBoundedStatement primorialWheelFamily := by
  exact frozenSquareRunEnergyBounded_iff_squareRunEnergyBounded.trans
    squareRunEnergyBounded_iff_primorialResidualBounded

/-! ## Exact floor normalization and reciprocal-band covariance descent -/

/-- The upper reciprocal-floor transform truncated at the prefix cutoff `A`. -/
def frozenTruncatedFloorTransform (A W : ℕ) : ℂ :=
  ∑ d ∈ Finset.Ico 1 A,
    (((μ d : ℤ) : ℂ)) * (((W / d : ℕ) : ℂ))

/-- At the lower square endpoint the complete Möbius-floor transform is exactly
`1`.  Thus the lower endpoint of the frozen kernel is not an analytic term at
all: it is a rigid Möbius-inversion constant. -/
theorem frozenTruncatedFloorTransform_squarePred_eq_one
    (a : ℕ) (ha : 2 ≤ a) :
    frozenTruncatedFloorTransform (a ^ 2) (a ^ 2 - 1) = 1 := by
  have htwo : 1 + 1 ≤ a ^ 2 := by nlinarith
  have hN : 1 ≤ a ^ 2 - 1 := Nat.le_sub_of_add_le htwo
  have hset : Finset.Ico 1 (a ^ 2) = Finset.Icc 1 (a ^ 2 - 1) := by
    ext d
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have h := nativeSumMoebiusMulFloor (a ^ 2 - 1) hN
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  push_cast at hc
  unfold frozenTruncatedFloorTransform
  rw [hset]
  simpa using hc

/-- The frozen kernel is exactly the difference of two signed reciprocal-floor
transforms on the same frozen divisor carrier. -/
theorem frozenSquareRunKernel_eq_truncatedFloorTransform_sub
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    frozenSquareRunKernel a b =
      frozenTruncatedFloorTransform (a ^ 2) (((b + 1) ^ 2) - 1) -
        frozenTruncatedFloorTransform (a ^ 2) (a ^ 2 - 1) := by
  unfold frozenSquareRunKernel frozenTruncatedFloorTransform
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  have hsq : a ^ 2 ≤ (b + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hpred : a ^ 2 - 1 ≤ (b + 1) ^ 2 - 1 := by omega
  have hdiv : (a ^ 2 - 1) / d ≤ (((b + 1) ^ 2) - 1) / d :=
    Nat.div_le_div_right hpred
  rw [frozenFloorWeight_eq_div_sub_div ha hab]
  rw [Nat.cast_sub hdiv]
  ring

/-- After Möbius inversion removes the lower endpoint, the entire kernel is one
truncated upper reciprocal-floor transform minus the rigid constant `1`. -/
theorem frozenSquareRunKernel_eq_truncatedUpper_sub_one
    (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    frozenSquareRunKernel a b =
      frozenTruncatedFloorTransform (a ^ 2) (((b + 1) ^ 2) - 1) - 1 := by
  rw [frozenSquareRunKernel_eq_truncatedFloorTransform_sub a b (by omega) hab,
    frozenTruncatedFloorTransform_squarePred_eq_one a ha]

/-- Real reciprocal-band family mass kernel.  It is the real form of the
existing exact family mass `-M(z)`. -/
def frozenReciprocalBandMassKernelReal (z : ℕ) : ℝ :=
  -realMertensLength (z + 1)

/-- Lower-prefix pair covariance carried by reciprocal quotient depth `z`. -/
def frozenReciprocalBandCovarianceKernel (z : ℕ) : ℝ :=
  realMertensPositiveLagPairSum (z + 1)

/-- The real mass kernel is exactly the existing complex reciprocal-band family
kernel after casting. -/
theorem frozenReciprocalBandMassKernelReal_cast_eq_primeCombFamilyKernel
    (z : ℕ) :
    ((frozenReciprocalBandMassKernelReal z : ℝ) : ℂ) =
      primeCombReciprocalBandFamilyKernel z := by
  unfold frozenReciprocalBandMassKernelReal primeCombReciprocalBandFamilyKernel
  push_cast
  exact congrArg Neg.neg (realMertensLength_cast_eq_mertensSummatory z)

/-- Adding the next lower-prefix Möbius coordinate changes the reciprocal-band
family mass by the exact sign flip `-mu(z+1)`. -/
theorem frozenReciprocalBandMassKernelReal_succ_sub (z : ℕ) :
    frozenReciprocalBandMassKernelReal (z + 1) -
      frozenReciprocalBandMassKernelReal z =
        -realMoebiusStep (z + 1) := by
  unfold frozenReciprocalBandMassKernelReal
  rw [realMertensLength_succ]
  ring

/-- The same successor changes lower-prefix pair covariance by the current
prefix times the new Möbius coordinate. -/
theorem frozenReciprocalBandCovarianceKernel_succ_sub (z : ℕ) :
    frozenReciprocalBandCovarianceKernel (z + 1) -
      frozenReciprocalBandCovarianceKernel z =
        realMoebiusStep (z + 1) * realMertensLength (z + 1) := by
  unfold frozenReciprocalBandCovarianceKernel
  rw [realMertensPositiveLagPairSum_succ]
  ring

/-- **Mass/covariance coupling.**  The covariance response is exactly mass
level times mass increment.  Hence an outward reciprocal-band update creates
positive covariance and a restoring update creates negative covariance, with no
probabilistic assumption and no absolute values. -/
theorem frozenReciprocalBandCovarianceKernel_succ_sub_eq_mass_mul_mass_diff
    (z : ℕ) :
    frozenReciprocalBandCovarianceKernel (z + 1) -
        frozenReciprocalBandCovarianceKernel z =
      frozenReciprocalBandMassKernelReal z *
        (frozenReciprocalBandMassKernelReal (z + 1) -
          frozenReciprocalBandMassKernelReal z) := by
  rw [frozenReciprocalBandCovarianceKernel_succ_sub,
    frozenReciprocalBandMassKernelReal_succ_sub]
  unfold frozenReciprocalBandMassKernelReal
  ring

/-- One post-root prime family in reciprocal band `z` has exactly the
lower-scale covariance kernel at depth `z`. -/
theorem primeCombReciprocalBand_familyPairCovariance_eq
    {W z p : ℕ} (hz : 0 < z) (hpRoot : Nat.sqrt W < p)
    (hp : p ∈ primeCombReciprocalBand W z) :
    largePrimeFamilyPairSum p (z + 1) =
      frozenReciprocalBandCovarianceKernel z := by
  have hsq : W < p ^ 2 := (Nat.sqrt_lt').1 hpRoot
  have hW : W < p * p := by simpa [pow_two] using hsq
  have h := largePrimeFamilyPairSum_postRoot
    (primeCombReciprocalBand_prime hp) hW
  rw [primeCombReciprocalBand_div_eq hz hp] at h
  simpa [frozenReciprocalBandCovarianceKernel] using h

/-- Total post-root family covariance in one reciprocal band. -/
def primeCombPostRootReciprocalBandPairCovariance (W z : ℕ) : ℝ :=
  ∑ p ∈ primeCombPostRootReciprocalBand W z,
    largePrimeFamilyPairSum p (z + 1)

/-- **Whole-band covariance descent.**  Every post-root family in a quotient
band is covariance-isomorphic to the same completed lower prefix, so the whole
band is exactly prime cardinality times lower-scale covariance. -/
theorem primeCombPostRootReciprocalBandPairCovariance_eq_card_mul
    (W z : ℕ) (hz : 0 < z) :
    primeCombPostRootReciprocalBandPairCovariance W z =
      ((primeCombPostRootReciprocalBand W z).card : ℝ) *
        frozenReciprocalBandCovarianceKernel z := by
  unfold primeCombPostRootReciprocalBandPairCovariance
  calc
    (∑ p ∈ primeCombPostRootReciprocalBand W z,
        largePrimeFamilyPairSum p (z + 1)) =
      ∑ _p ∈ primeCombPostRootReciprocalBand W z,
        frozenReciprocalBandCovarianceKernel z := by
          apply Finset.sum_congr rfl
          intro p hp
          rcases mem_primeCombPostRootReciprocalBand.mp hp with
            ⟨hpBand, hpRoot⟩
          exact primeCombReciprocalBand_familyPairCovariance_eq hz hpRoot hpBand
    _ = ((primeCombPostRootReciprocalBand W z).card : ℝ) *
        frozenReciprocalBandCovarianceKernel z := by simp

end RHLean.Analysis
