import Mathlib
import RHLean.Analysis.PrimeWheelFourierReduction

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Zero-padded raw seeded field on the arithmetic block. -/
def torusRawBlockField
    (W : PrimeWheelFiniteSystem) : ZMod W.modulus → ℂ :=
  fun z =>
    if W.lower < z.val ∧ z.val ≤ W.upper then
      ((W.rawSite z.val : ℤ) : ℂ)
    else 0

/-- Zero-padded smooth-core field on the arithmetic block. -/
def torusSmoothCoreBlockField
    (W : PrimeWheelFiniteSystem) : ZMod W.modulus → ℂ :=
  fun z =>
    if W.lower < z.val ∧ z.val ≤ W.upper then
      ((W.smoothCoreSite z.val : ℤ) : ℂ)
    else 0

/-- Pointwise raw-minus-twice-smooth decomposition on the common torus. -/
theorem torusJointField_eq_raw_sub_two_smooth
    (W : PrimeWheelFiniteSystem) :
    W.torusJointField = fun z =>
      W.torusRawBlockField z - 2 * W.torusSmoothCoreBlockField z := by
  funext z
  unfold torusJointField torusRawBlockField torusSmoothCoreBlockField
    correctedSite correctedPrimeWheelSite rawSite smoothCoreSite
  by_cases hz : W.lower < z.val ∧ z.val ≤ W.upper
  · simp [hz]
  · simp [hz]

/-- DFT of the zero-padded raw block field. -/
def rawBlockSpectrum
    (W : PrimeWheelFiniteSystem) : ZMod W.modulus → ℂ :=
  ZMod.dft W.torusRawBlockField

/-- DFT of the zero-padded smooth-core block field. -/
def smoothCoreBlockSpectrum
    (W : PrimeWheelFiniteSystem) : ZMod W.modulus → ℂ :=
  ZMod.dft W.torusSmoothCoreBlockField

/-- Exact coefficientwise joint-spectrum subtraction. -/
theorem jointSpectrum_eq_raw_sub_two_smooth
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    W.jointSpectrum r =
      W.rawBlockSpectrum r - 2 * W.smoothCoreBlockSpectrum r := by
  unfold jointSpectrum rawBlockSpectrum smoothCoreBlockSpectrum
  rw [W.torusJointField_eq_raw_sub_two_smooth]
  simp only [ZMod.dft_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  have hscalar :
      (∑ x : ZMod W.modulus,
          ZMod.stdAddChar (-(x * r)) *
            (2 * W.torusSmoothCoreBlockField x)) =
        2 * ∑ x : ZMod W.modulus,
          ZMod.stdAddChar (-(x * r)) * W.torusSmoothCoreBlockField x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hscalar]

/-- Explicit finite additive-character formula for the raw coefficient. -/
theorem rawBlockSpectrum_apply
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    W.rawBlockSpectrum r =
      ∑ z : ZMod W.modulus,
        ZMod.stdAddChar (-(z * r)) • W.torusRawBlockField z := by
  exact ZMod.dft_apply W.torusRawBlockField r

/-- Explicit finite additive-character formula for the smooth-core coefficient. -/
theorem smoothCoreBlockSpectrum_apply
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    W.smoothCoreBlockSpectrum r =
      ∑ z : ZMod W.modulus,
        ZMod.stdAddChar (-(z * r)) • W.torusSmoothCoreBlockField z := by
  exact ZMod.dft_apply W.torusSmoothCoreBlockField r

/-- Full signed raw/core energy decomposition for one pinned interval. -/
theorem spectralPrefix_raw_smooth_decomposition
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    W.spectralPrefix x =
      ((W.modulus : ℂ)⁻¹) *
        ∑ r : ZMod W.modulus,
          (W.rawBlockSpectrum r - 2 * W.smoothCoreBlockSpectrum r) *
            W.prefixWindowSpectrum x (-r) := by
  unfold spectralPrefix
  apply congrArg (fun z : ℂ => ((W.modulus : ℂ)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro r hr
  rw [W.jointSpectrum_eq_raw_sub_two_smooth]

end RHLean.Arithmetic.PrimeWheelFiniteSystem
