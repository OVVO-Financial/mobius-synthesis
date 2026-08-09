import Mathlib
import RHLean.Analysis.PrimeWheelCoconductorTail
import RHLean.Analysis.PrimeWheelDirichletResponse

open scoped BigOperators
open AddChar

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- The pointwise elementary geometric-series majorant for one additive
frequency.  The zero frequency contributes the interval length exactly.  Every
nonzero frequency is bounded simultaneously by the trivial interval length and
by the exact geometric-series denominator. -/
def primeWheelDirichletPointBound
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (r : ZMod W.modulus) : ℝ :=
  if r = 0 then
    (N : ℝ)
  else
    min (N : ℝ) (2 / ‖ZMod.stdAddChar r - 1‖)

/-- Explicit finite high-co-conductor bound obtained by summing the exact
geometric-series majorant over the selected frequencies.  It depends only on
the torus modulus, the cutoff, and the interval length. -/
def primeWheelCoconductorTailGeometricBound
    (W : PrimeWheelFiniteSystem) (N D : ℕ) : ℝ :=
  ∑ r : ZMod W.modulus,
    if D < additiveCoconductor r then
      primeWheelDirichletPointBound W N r
    else 0

@[simp] private theorem norm_stdAddChar_eq_one
    {Q : ℕ} [NeZero Q] (r : ZMod Q) :
    ‖ZMod.stdAddChar r‖ = 1 := by
  simp [ZMod.stdAddChar_apply]

@[simp] private theorem norm_primeWheelPinnedPhase_eq_one
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    ‖primeWheelPinnedPhase W r‖ = 1 := by
  simp [primeWheelPinnedPhase]

private theorem stdAddChar_nat_mul
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) (j : ℕ) :
    ZMod.stdAddChar (((j : ℕ) : ZMod W.modulus) * r) =
      ZMod.stdAddChar r ^ j := by
  simpa [nsmul_eq_mul] using
    (AddChar.map_nsmul_eq_pow
      (ZMod.stdAddChar : AddChar (ZMod W.modulus) ℂ) j r)

/-- The finite Dirichlet response is bounded trivially by its length. -/
theorem norm_primeWheelDirichletKernel_le_length
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (r : ZMod W.modulus) :
    ‖primeWheelDirichletKernel W N r‖ ≤ (N : ℝ) := by
  unfold primeWheelDirichletKernel
  calc
    ‖∑ j ∈ Finset.range N,
        ZMod.stdAddChar (((j : ℕ) : ZMod W.modulus) * r)‖ ≤
        ∑ j ∈ Finset.range N,
          ‖ZMod.stdAddChar (((j : ℕ) : ZMod W.modulus) * r)‖ := by
      exact norm_sum_le _ _
    _ = (N : ℝ) := by simp

/-- For a nonzero additive frequency, exact geometric summation gives the
reciprocal chord-length bound. -/
theorem norm_primeWheelDirichletKernel_le_geometric
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (r : ZMod W.modulus) (hr : r ≠ 0) :
    ‖primeWheelDirichletKernel W N r‖ ≤
      2 / ‖ZMod.stdAddChar r - 1‖ := by
  have hchar : ZMod.stdAddChar r ≠ 1 := by
    intro h
    have hzero : r = 0 :=
      ZMod.injective_stdAddChar (by simpa using h)
    exact hr hzero
  have hsum :
      primeWheelDirichletKernel W N r =
        ∑ j ∈ Finset.range N, ZMod.stdAddChar r ^ j := by
    unfold primeWheelDirichletKernel
    apply Finset.sum_congr rfl
    intro j hj
    exact stdAddChar_nat_mul W r j
  rw [hsum, geom_sum_eq hchar N, norm_div]
  have hnum : ‖ZMod.stdAddChar r ^ N - 1‖ ≤ (2 : ℝ) := by
    calc
      ‖ZMod.stdAddChar r ^ N - 1‖ ≤
          ‖ZMod.stdAddChar r ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        simp
        norm_num
  have hden : 0 < ‖ZMod.stdAddChar r - 1‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hchar)
  exact (div_le_div_iff_of_pos_right hden).2 hnum

/-- Combined pointwise Dirichlet bound. -/
theorem norm_primeWheelDirichletKernel_le_pointBound
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (r : ZMod W.modulus) :
    ‖primeWheelDirichletKernel W N r‖ ≤
      primeWheelDirichletPointBound W N r := by
  unfold primeWheelDirichletPointBound
  by_cases hr : r = 0
  · subst r
    simp [primeWheelDirichletKernel]
  · simp only [hr, if_false]
    exact le_min
      (norm_primeWheelDirichletKernel_le_length W N r)
      (norm_primeWheelDirichletKernel_le_geometric W N r hr)

private theorem prefixWindow_char_sum_eq_phase_mul_dirichlet
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (r : ZMod W.modulus)
    (hupper : W.lower + N ≤ W.upper) :
    (∑ b : ZMod W.modulus,
      W.torusPrefixWindow (W.lower + N) b *
        ZMod.stdAddChar (b * r)) =
      primeWheelPinnedPhase W r * primeWheelDirichletKernel W N r := by
  have h := prefixWindowSpectrum_neg_eq_phase_mul_dirichlet W N r hupper
  unfold PrimeWheelFiniteSystem.prefixWindowSpectrum at h
  rw [ZMod.dft_apply] at h
  simpa only [smul_eq_mul, mul_neg, neg_neg, mul_comm] using h

private theorem shifted_prefixWindow_char_sum_eq_phase_mul_dirichlet
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (a r : ZMod W.modulus)
    (hupper : W.lower + N ≤ W.upper) :
    (∑ b : ZMod W.modulus,
      W.torusPrefixWindow (W.lower + N) b *
        ZMod.stdAddChar ((b - a) * r)) =
      ZMod.stdAddChar (-(a * r)) *
        primeWheelPinnedPhase W r *
          primeWheelDirichletKernel W N r := by
  calc
    (∑ b : ZMod W.modulus,
      W.torusPrefixWindow (W.lower + N) b *
        ZMod.stdAddChar ((b - a) * r)) =
        ∑ b : ZMod W.modulus,
          ZMod.stdAddChar (-(a * r)) *
            (W.torusPrefixWindow (W.lower + N) b *
              ZMod.stdAddChar (b * r)) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hchar :
          ZMod.stdAddChar ((b - a) * r) =
            ZMod.stdAddChar (-(a * r)) *
              ZMod.stdAddChar (b * r) := by
        rw [← map_add_eq_mul]
        congr 1
        ring
      rw [hchar]
      ring
    _ = ZMod.stdAddChar (-(a * r)) *
        ∑ b : ZMod W.modulus,
          W.torusPrefixWindow (W.lower + N) b *
            ZMod.stdAddChar (b * r) := by
      rw [Finset.mul_sum]
    _ = ZMod.stdAddChar (-(a * r)) *
        primeWheelPinnedPhase W r *
          primeWheelDirichletKernel W N r := by
      rw [prefixWindow_char_sum_eq_phase_mul_dirichlet W N r hupper]
      ring

/-- The shifted high-co-conductor response is exactly a frequency sum of pinned
Dirichlet kernels with unit-modulus phase factors. -/
theorem primeWheelCoconductorTailWindowResponse_eq_frequencySum
    (W : PrimeWheelFiniteSystem) (N D : ℕ)
    (a : ZMod W.modulus)
    (hupper : W.lower + N ≤ W.upper) :
    primeWheelCoconductorTailWindowResponse W (W.lower + N) D a =
      ∑ r : ZMod W.modulus,
        if D < additiveCoconductor r then
          ZMod.stdAddChar (-(a * r)) *
            primeWheelPinnedPhase W r *
              primeWheelDirichletKernel W N r
        else 0 := by
  classical
  unfold primeWheelCoconductorTailWindowResponse
    primeWheelCoconductorTailKernel
  calc
    (∑ b : ZMod W.modulus,
      W.torusPrefixWindow (W.lower + N) b *
        ∑ r : ZMod W.modulus,
          if D < additiveCoconductor r then
            ZMod.stdAddChar ((b - a) * r)
          else 0) =
        ∑ b : ZMod W.modulus,
          ∑ r : ZMod W.modulus,
            if D < additiveCoconductor r then
              W.torusPrefixWindow (W.lower + N) b *
                ZMod.stdAddChar ((b - a) * r)
            else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases htail : D < additiveCoconductor r <;> simp [htail]
    _ = ∑ r : ZMod W.modulus,
        ∑ b : ZMod W.modulus,
          if D < additiveCoconductor r then
            W.torusPrefixWindow (W.lower + N) b *
              ZMod.stdAddChar ((b - a) * r)
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r : ZMod W.modulus,
        if D < additiveCoconductor r then
          ZMod.stdAddChar (-(a * r)) *
            primeWheelPinnedPhase W r *
              primeWheelDirichletKernel W N r
        else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases htail : D < additiveCoconductor r
      · simp only [htail, if_true]
        rw [shifted_prefixWindow_char_sum_eq_phase_mul_dirichlet
          W N a r hupper]
      · simp [htail]

/-- Uniform, non-circular high-co-conductor interval estimate.  The bound is
independent of the shift `a` and uses only exact finite geometric summation. -/
theorem norm_primeWheelCoconductorTailWindowResponse_le_geometricBound
    (W : PrimeWheelFiniteSystem) (N D : ℕ)
    (a : ZMod W.modulus)
    (hupper : W.lower + N ≤ W.upper) :
    ‖primeWheelCoconductorTailWindowResponse W (W.lower + N) D a‖ ≤
      primeWheelCoconductorTailGeometricBound W N D := by
  rw [primeWheelCoconductorTailWindowResponse_eq_frequencySum
    W N D a hupper]
  unfold primeWheelCoconductorTailGeometricBound
  calc
    ‖∑ r : ZMod W.modulus,
        if D < additiveCoconductor r then
          ZMod.stdAddChar (-(a * r)) *
            primeWheelPinnedPhase W r *
              primeWheelDirichletKernel W N r
        else 0‖ ≤
      ∑ r : ZMod W.modulus,
        ‖if D < additiveCoconductor r then
          ZMod.stdAddChar (-(a * r)) *
            primeWheelPinnedPhase W r *
              primeWheelDirichletKernel W N r
        else 0‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ r : ZMod W.modulus,
        if D < additiveCoconductor r then
          primeWheelDirichletPointBound W N r
        else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases htail : D < additiveCoconductor r
      · simpa [htail] using
          (norm_primeWheelDirichletKernel_le_pointBound W N r)
      · simp [htail]

end RHLean.Analysis
