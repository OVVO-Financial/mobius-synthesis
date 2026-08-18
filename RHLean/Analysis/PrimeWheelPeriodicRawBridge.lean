import Mathlib
import RHLean.Arithmetic.PrimorialWheelMinimalTorus
import RHLean.Analysis.PrimeWheelJointSpectrum
import RHLean.Analysis.PrimeWheelTorusRealization

/-!
# Periodic raw-field realization on the minimal primorial torus

The canonical torus realization zero-pads the whole corrected arithmetic block.
That is ideal for the lossless residual identity, but it hides the complete
periodic CRT spectrum of the raw seeded prime comb.

The manuscript uses a sharper realization: choose the smallest multiple of the
complete raw period that lies beyond the arithmetic endpoint, leave the raw comb
untruncated on that torus, and zero-pad only the smooth-core correction.  The
pinned prefix window is supported inside the arithmetic block, so this
alternative field has exactly the same pairing with every admissible prefix.

This restores the periodic raw spectrum while retaining the actual corrected
Möbius residual.  No analytic estimate is asserted here.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- The raw seeded prime comb left untruncated on the minimal common torus. -/
def primorialPeriodicRawTorusField
    (k : ℕ) : ZMod (primorialMinimalWheelSystem k).modulus → ℂ :=
  fun z => ((((primorialMinimalWheelSystem k).rawSite z.val : ℤ) : ℂ))

/-- Alternative actual joint field: periodic raw comb minus the same zero-padded
smooth-core correction used by the finite wheel realization. -/
def primorialPeriodicRawJointTorusField
    (k : ℕ) : ZMod (primorialMinimalWheelSystem k).modulus → ℂ :=
  fun z =>
    primorialPeriodicRawTorusField k z -
      2 * (primorialMinimalWheelSystem k).torusSmoothCoreBlockField z

/-- Pair the alternative field with the same pinned arithmetic prefix window. -/
def primorialPeriodicRawPrefixPairing
    (k x : ℕ) : ℂ :=
  finiteTorusPairing
    (primorialPeriodicRawJointTorusField k)
    ((primorialMinimalWheelSystem k).torusPrefixWindow x)

/-- On every admissible prefix, the alternative periodic-raw field and the
canonical zero-padded joint field agree after multiplication by the prefix
window.  Outside the window both products vanish; inside it the raw block field
is exactly the untruncated raw site. -/
theorem primorialPeriodicRawJoint_mul_prefixWindow_eq
    (k x : ℕ)
    (hupper : x ≤ (primorialMinimalWheelSystem k).upper)
    (z : ZMod (primorialMinimalWheelSystem k).modulus) :
    primorialPeriodicRawJointTorusField k z *
        (primorialMinimalWheelSystem k).torusPrefixWindow x z =
      (primorialMinimalWheelSystem k).torusJointField z *
        (primorialMinimalWheelSystem k).torusPrefixWindow x z := by
  have hjoint :
      (primorialMinimalWheelSystem k).torusJointField z =
        (primorialMinimalWheelSystem k).torusRawBlockField z -
          2 * (primorialMinimalWheelSystem k).torusSmoothCoreBlockField z :=
    congrFun
      ((primorialMinimalWheelSystem k).torusJointField_eq_raw_sub_two_smooth) z
  rw [hjoint]
  by_cases hwin :
      (primorialMinimalWheelSystem k).lower < z.val ∧ z.val ≤ x
  · have hblock :
        (primorialMinimalWheelSystem k).lower < z.val ∧
          z.val ≤ (primorialMinimalWheelSystem k).upper :=
      ⟨hwin.1, hwin.2.trans hupper⟩
    simp [primorialPeriodicRawJointTorusField,
      primorialPeriodicRawTorusField,
      PrimeWheelFiniteSystem.torusPrefixWindow,
      PrimeWheelFiniteSystem.torusRawBlockField,
      hwin, hblock]
  · simp [PrimeWheelFiniteSystem.torusPrefixWindow, hwin]

/-- The periodic-raw pairing is exactly the minimal wheel's canonical torus
prefix pairing. -/
theorem primorialPeriodicRawPrefixPairing_eq_torusPrefixPairing
    (k x : ℕ)
    (hupper : x ≤ (primorialMinimalWheelSystem k).upper) :
    primorialPeriodicRawPrefixPairing k x =
      (primorialMinimalWheelSystem k).torusPrefixPairing x := by
  classical
  unfold primorialPeriodicRawPrefixPairing
    PrimeWheelFiniteSystem.torusPrefixPairing
    finiteTorusPairing
  apply Finset.sum_congr rfl
  intro z hz
  exact primorialPeriodicRawJoint_mul_prefixWindow_eq k x hupper z

/-- Hence the periodic-raw torus realizes the minimal wheel residual on every
nonempty pinned prefix. -/
theorem primorialPeriodicRawPrefixPairing_eq_minimalResidual
    (k : ℕ) {x : ℕ}
    (hlower : (primorialMinimalWheelSystem k).lower < x)
    (hupper : x ≤ (primorialMinimalWheelSystem k).upper) :
    primorialPeriodicRawPrefixPairing k x =
      ((((primorialMinimalWheelSystem k).residual x : ℤ) : ℂ)) := by
  rw [primorialPeriodicRawPrefixPairing_eq_torusPrefixPairing k x hupper]
  exact
    (primorialMinimalWheelSystem k).canonicalTorusRealizationCertificate.pairing_eq_residual
      x hlower hupper

/-- The same pairing is exactly the historical primorial-wheel residual used by
earlier layers.  Thus the new torus changes only Fourier coordinates, not the
arithmetic signal. -/
theorem primorialPeriodicRawPrefixPairing_eq_residual
    (k : ℕ) {x : ℕ}
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    primorialPeriodicRawPrefixPairing k x =
      ((((primorialWheelSystem k).residual x : ℤ) : ℂ)) := by
  have hlowerMin : (primorialMinimalWheelSystem k).lower < x := by
    exact hlower
  have hupperMin : x ≤ (primorialMinimalWheelSystem k).upper := by
    exact hupper
  rw [primorialPeriodicRawPrefixPairing_eq_minimalResidual
    k hlowerMin hupperMin]
  rw [primorialMinimalWheel_residual_eq_primorialWheel_residual k hupper]

/-- Fourier-side pairing of the same alternative field and prefix window. -/
def primorialPeriodicRawSpectralPrefix
    (k x : ℕ) : ℂ :=
  finiteTorusSpectralPairing
    (primorialPeriodicRawJointTorusField k)
    ((primorialMinimalWheelSystem k).torusPrefixWindow x)

/-- The alternative periodic-raw prefix pairing has the exact finite Fourier
representation on the minimal common torus. -/
theorem primorialPeriodicRawPrefixPairing_eq_spectralPrefix
    (k x : ℕ) :
    primorialPeriodicRawPrefixPairing k x =
      primorialPeriodicRawSpectralPrefix k x := by
  exact finiteTorusPairing_eq_spectral
    (primorialPeriodicRawJointTorusField k)
    ((primorialMinimalWheelSystem k).torusPrefixWindow x)

/-- The periodic-raw spectral prefix is another exact spectral representation
of the historical corrected wheel residual. -/
theorem primorialPeriodicRawSpectralPrefix_eq_residual
    (k : ℕ) {x : ℕ}
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    primorialPeriodicRawSpectralPrefix k x =
      ((((primorialWheelSystem k).residual x : ℤ) : ℂ)) := by
  rw [← primorialPeriodicRawPrefixPairing_eq_spectralPrefix k x]
  exact primorialPeriodicRawPrefixPairing_eq_residual k hlower hupper

/-- DFT of the untruncated raw field on the minimal common torus. -/
def primorialPeriodicRawSpectrum
    (k : ℕ) : ZMod (primorialMinimalWheelSystem k).modulus → ℂ :=
  ZMod.dft (primorialPeriodicRawTorusField k)

/-- DFT of the alternative actual joint field. -/
def primorialPeriodicRawJointSpectrum
    (k : ℕ) : ZMod (primorialMinimalWheelSystem k).modulus → ℂ :=
  ZMod.dft (primorialPeriodicRawJointTorusField k)

/-- Exact coefficientwise signed decomposition for the alternative spectrum.
Unlike the zero-padded raw-block transform, the first term here is the DFT of
the full periodic raw comb. -/
theorem primorialPeriodicRawJointSpectrum_eq_raw_sub_two_smooth
    (k : ℕ) (r : ZMod (primorialMinimalWheelSystem k).modulus) :
    primorialPeriodicRawJointSpectrum k r =
      primorialPeriodicRawSpectrum k r -
        2 * (primorialMinimalWheelSystem k).smoothCoreBlockSpectrum r := by
  unfold primorialPeriodicRawJointSpectrum primorialPeriodicRawSpectrum
    primorialPeriodicRawJointTorusField
    PrimeWheelFiniteSystem.smoothCoreBlockSpectrum
  simp only [ZMod.dft_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  have hscalar :
      (∑ x : ZMod (primorialMinimalWheelSystem k).modulus,
          ZMod.stdAddChar (-(x * r)) *
            (2 * (primorialMinimalWheelSystem k).torusSmoothCoreBlockField x)) =
        2 * ∑ x : ZMod (primorialMinimalWheelSystem k).modulus,
          ZMod.stdAddChar (-(x * r)) *
            (primorialMinimalWheelSystem k).torusSmoothCoreBlockField x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hscalar]

end RHLean.Analysis
