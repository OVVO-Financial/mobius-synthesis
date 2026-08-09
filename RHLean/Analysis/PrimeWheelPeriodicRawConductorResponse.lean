import Mathlib
import RHLean.Analysis.PrimeWheelPeriodicRawBridge
import RHLean.Analysis.PrimeWheelHarmonicCriterion

/-!
# Conductor packets for the periodic-raw realization

After the natural-period reduction, the actual corrected primorial-wheel
residual has a second exact spectral realization in which the raw seeded comb is
left periodic and only the smooth correction is zero-padded.  This file groups
that exact response by reduced additive conductor before taking any norm.

The raw and smooth terms are kept in the same conductor packet, and every
packet satisfies an exact `raw - 2 * smooth` identity.  A shell on which the raw
spectrum is constant collapses exactly to its additive-character kernel.  This
is the finite Ramanujan-kernel step needed before any analytic estimate.

These are finite regrouping theorems only; no cancellation estimate is asserted.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- One frequency atom for the periodic raw spectrum. -/
def primorialPeriodicRawSpectralAtom
    (k x : ℕ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus) : ℂ :=
  ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
    primorialPeriodicRawSpectrum k r) *
      (primorialMinimalWheelSystem k).prefixWindowSpectrum x (-r)

/-- One frequency atom for the zero-padded smooth correction. -/
def primorialPeriodicSmoothSpectralAtom
    (k x : ℕ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus) : ℂ :=
  ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
    (primorialMinimalWheelSystem k).smoothCoreBlockSpectrum r) *
      (primorialMinimalWheelSystem k).prefixWindowSpectrum x (-r)

/-- One frequency atom for the actual signed periodic-raw joint spectrum. -/
def primorialPeriodicRawJointSpectralAtom
    (k x : ℕ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus) : ℂ :=
  ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
    primorialPeriodicRawJointSpectrum k r) *
      (primorialMinimalWheelSystem k).prefixWindowSpectrum x (-r)

/-- The signed raw/smooth subtraction is retained at each individual frequency. -/
theorem primorialPeriodicRawJointSpectralAtom_eq_raw_sub_two_smooth
    (k x : ℕ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus) :
    primorialPeriodicRawJointSpectralAtom k x r =
      primorialPeriodicRawSpectralAtom k x r -
        2 * primorialPeriodicSmoothSpectralAtom k x r := by
  unfold primorialPeriodicRawJointSpectralAtom
    primorialPeriodicRawSpectralAtom primorialPeriodicSmoothSpectralAtom
  rw [primorialPeriodicRawJointSpectrum_eq_raw_sub_two_smooth]
  ring

/-- The complete periodic-raw spectral prefix is the sum of its frequency atoms. -/
theorem primorialPeriodicRawSpectralPrefix_eq_sum_atoms
    (k x : ℕ) :
    primorialPeriodicRawSpectralPrefix k x =
      ∑ r : ZMod (primorialMinimalWheelSystem k).modulus,
        primorialPeriodicRawJointSpectralAtom k x r := by
  unfold primorialPeriodicRawSpectralPrefix finiteTorusSpectralPairing
    primorialPeriodicRawJointSpectralAtom
    primorialPeriodicRawJointSpectrum
    PrimeWheelFiniteSystem.prefixWindowSpectrum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Raw contribution carried by one reduced additive conductor. -/
def primorialPeriodicRawConductorResponse
    (k x q : ℕ) : ℂ :=
  ∑ r : ZMod (primorialMinimalWheelSystem k).modulus,
    if q = reducedAdditiveConductor r then
      primorialPeriodicRawSpectralAtom k x r
    else 0

/-- Smooth-core contribution carried by the same reduced additive conductor. -/
def primorialPeriodicSmoothConductorResponse
    (k x q : ℕ) : ℂ :=
  ∑ r : ZMod (primorialMinimalWheelSystem k).modulus,
    if q = reducedAdditiveConductor r then
      primorialPeriodicSmoothSpectralAtom k x r
    else 0

/-- Actual corrected contribution carried by one reduced additive conductor. -/
def primorialPeriodicRawJointConductorResponse
    (k x q : ℕ) : ℂ :=
  ∑ r : ZMod (primorialMinimalWheelSystem k).modulus,
    if q = reducedAdditiveConductor r then
      primorialPeriodicRawJointSpectralAtom k x r
    else 0

/-- Every conductor packet preserves the exact signed raw-minus-smooth
interaction before any norm or triangle inequality is introduced. -/
theorem primorialPeriodicRawJointConductorResponse_eq_raw_sub_two_smooth
    (k x q : ℕ) :
    primorialPeriodicRawJointConductorResponse k x q =
      primorialPeriodicRawConductorResponse k x q -
        2 * primorialPeriodicSmoothConductorResponse k x q := by
  classical
  unfold primorialPeriodicRawJointConductorResponse
    primorialPeriodicRawConductorResponse
    primorialPeriodicSmoothConductorResponse
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hq : q = reducedAdditiveConductor r
  · simp only [hq, if_true]
    exact primorialPeriodicRawJointSpectralAtom_eq_raw_sub_two_smooth k x r
  · simp [hq]

/-- Exact conductor partition of the complete actual periodic-raw response. -/
theorem primorialPeriodicRawSpectralPrefix_eq_sum_conductorResponses
    (k x : ℕ) :
    primorialPeriodicRawSpectralPrefix k x =
      ∑ q ∈ Finset.range ((primorialMinimalWheelSystem k).modulus + 1),
        primorialPeriodicRawJointConductorResponse k x q := by
  classical
  rw [primorialPeriodicRawSpectralPrefix_eq_sum_atoms]
  unfold primorialPeriodicRawJointConductorResponse
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hcond :
      reducedAdditiveConductor r ≤ (primorialMinimalWheelSystem k).modulus := by
    unfold reducedAdditiveConductor
    split_ifs
    · exact Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (primorialMinimalWheelSystem k).modulus_pos)
    · exact Nat.div_le_self _ _
  have hmem :
      reducedAdditiveConductor r ∈
        Finset.range ((primorialMinimalWheelSystem k).modulus + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hcond)
  simp [hmem]

/-- The historical corrected residual therefore has an exact signed conductor
expansion in the periodic-raw coordinates. -/
theorem primorialPeriodicRawResidual_eq_sum_conductorResponses
    (k : ℕ) {x : ℕ}
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    ((((primorialWheelSystem k).residual x : ℤ) : ℂ)) =
      ∑ q ∈ Finset.range ((primorialMinimalWheelSystem k).modulus + 1),
        primorialPeriodicRawJointConductorResponse k x q := by
  rw [← primorialPeriodicRawSpectralPrefix_eq_residual k hlower hupper]
  exact primorialPeriodicRawSpectralPrefix_eq_sum_conductorResponses k x

/-- The window response carried by one reduced-conductor shell after factoring
out a shell-constant raw Fourier coefficient. -/
def primeWheelReducedConductorWindowResponse
    (W : PrimeWheelFiniteSystem) (x q : ℕ) : ℂ :=
  ∑ r : ZMod W.modulus,
    if q = reducedAdditiveConductor r then
      ((W.modulus : ℂ)⁻¹) * W.prefixWindowSpectrum x (-r)
    else 0

/-- Additive-character kernel of one reduced-conductor shell. -/
def primeWheelReducedConductorKernel
    (W : PrimeWheelFiniteSystem) (q : ℕ) (z : ZMod W.modulus) : ℂ :=
  ∑ r : ZMod W.modulus,
    if q = reducedAdditiveConductor r then
      ZMod.stdAddChar (z * r)
    else 0

/-- Physical-space pairing of a pinned prefix with one reduced-conductor
character kernel. -/
def primeWheelReducedConductorRamanujanWindow
    (W : PrimeWheelFiniteSystem) (x q : ℕ) : ℂ :=
  ((W.modulus : ℂ)⁻¹) *
    ∑ z : ZMod W.modulus,
      W.torusPrefixWindow x z * primeWheelReducedConductorKernel W q z

/-- Primorial specialization of the generic reduced-conductor window response. -/
abbrev primorialReducedConductorWindowResponse
    (k x q : ℕ) : ℂ :=
  primeWheelReducedConductorWindowResponse (primorialMinimalWheelSystem k) x q

/-- Primorial specialization of the generic reduced-conductor kernel. -/
abbrev primorialReducedConductorKernel
    (k q : ℕ)
    (z : ZMod (primorialMinimalWheelSystem k).modulus) : ℂ :=
  primeWheelReducedConductorKernel (primorialMinimalWheelSystem k) q z

/-- Primorial specialization of the generic Ramanujan-kernel window. -/
abbrev primorialReducedConductorRamanujanWindow
    (k x q : ℕ) : ℂ :=
  primeWheelReducedConductorRamanujanWindow
    (primorialMinimalWheelSystem k) x q

/-- DFT of the prefix window at `-r`, with the double sign simplified before
entering any conductor-shell sum. -/
private theorem primeWheelPrefixWindowSpectrum_neg
    (W : PrimeWheelFiniteSystem) (x : ℕ) (r : ZMod W.modulus) :
    W.prefixWindowSpectrum x (-r) =
      ∑ z : ZMod W.modulus,
        ZMod.stdAddChar (z * r) * W.torusPrefixWindow x z := by
  unfold PrimeWheelFiniteSystem.prefixWindowSpectrum
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z hz
  have harg : -(z * (-r)) = z * r := by ring
  rw [harg]

/-- Sum of the shell-restricted window transforms is exactly the pinned window
paired with the shell character kernel. -/
theorem primeWheelReducedConductor_prefixSpectrumSum_eq_kernelPairing
    (W : PrimeWheelFiniteSystem) (x q : ℕ) :
    (∑ r : ZMod W.modulus,
      if q = reducedAdditiveConductor r then
        W.prefixWindowSpectrum x (-r)
      else 0) =
      ∑ z : ZMod W.modulus,
        W.torusPrefixWindow x z * primeWheelReducedConductorKernel W q z := by
  classical
  calc
    (∑ r : ZMod W.modulus,
      if q = reducedAdditiveConductor r then
        W.prefixWindowSpectrum x (-r)
      else 0) =
      ∑ r : ZMod W.modulus,
        if q = reducedAdditiveConductor r then
          ∑ z : ZMod W.modulus,
            ZMod.stdAddChar (z * r) * W.torusPrefixWindow x z
        else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          by_cases hq : q = reducedAdditiveConductor r
          · simp only [hq, if_true]
            rw [primeWheelPrefixWindowSpectrum_neg W x r]
          · simp [hq]
    _ =
      ∑ r : ZMod W.modulus,
        ∑ z : ZMod W.modulus,
          if q = reducedAdditiveConductor r then
            ZMod.stdAddChar (z * r) * W.torusPrefixWindow x z
          else 0 := by
            apply Finset.sum_congr rfl
            intro r hr
            by_cases hq : q = reducedAdditiveConductor r
            · simp [hq]
            · simp [hq]
    _ =
      ∑ z : ZMod W.modulus,
        ∑ r : ZMod W.modulus,
          if q = reducedAdditiveConductor r then
            ZMod.stdAddChar (z * r) * W.torusPrefixWindow x z
          else 0 := by
            rw [Finset.sum_comm]
    _ =
      ∑ z : ZMod W.modulus,
        W.torusPrefixWindow x z *
          ∑ r : ZMod W.modulus,
            if q = reducedAdditiveConductor r then
              ZMod.stdAddChar (z * r)
            else 0 := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r hr
              by_cases hq : q = reducedAdditiveConductor r
              · simp [hq]
                ring
              · simp [hq]
    _ =
      ∑ z : ZMod W.modulus,
        W.torusPrefixWindow x z * primeWheelReducedConductorKernel W q z := by
          rfl

/-- Primorial specialization of the generic shell-kernel pairing. -/
theorem primorialReducedConductor_prefixSpectrumSum_eq_kernelPairing
    (k x q : ℕ) :
    (∑ r : ZMod (primorialMinimalWheelSystem k).modulus,
      if q = reducedAdditiveConductor r then
        (primorialMinimalWheelSystem k).prefixWindowSpectrum x (-r)
      else 0) =
      ∑ z : ZMod (primorialMinimalWheelSystem k).modulus,
        (primorialMinimalWheelSystem k).torusPrefixWindow x z *
          primorialReducedConductorKernel k q z := by
  exact primeWheelReducedConductor_prefixSpectrumSum_eq_kernelPairing
    (primorialMinimalWheelSystem k) x q

/-- The normalized shell window response is exactly its Ramanujan-kernel
pairing. -/
theorem primeWheelReducedConductorWindowResponse_eq_ramanujanWindow
    (W : PrimeWheelFiniteSystem) (x q : ℕ) :
    primeWheelReducedConductorWindowResponse W x q =
      primeWheelReducedConductorRamanujanWindow W x q := by
  classical
  unfold primeWheelReducedConductorWindowResponse
    primeWheelReducedConductorRamanujanWindow
  calc
    (∑ r : ZMod W.modulus,
      if q = reducedAdditiveConductor r then
        ((W.modulus : ℂ)⁻¹) * W.prefixWindowSpectrum x (-r)
      else 0) =
      ((W.modulus : ℂ)⁻¹) *
        ∑ r : ZMod W.modulus,
          if q = reducedAdditiveConductor r then
            W.prefixWindowSpectrum x (-r)
          else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r hr
            by_cases hq : q = reducedAdditiveConductor r
            · simp [hq]
            · simp [hq]
    _ =
      ((W.modulus : ℂ)⁻¹) *
        ∑ z : ZMod W.modulus,
          W.torusPrefixWindow x z * primeWheelReducedConductorKernel W q z := by
            rw [primeWheelReducedConductor_prefixSpectrumSum_eq_kernelPairing]

/-- Primorial specialization of the normalized shell-window identity. -/
theorem primorialReducedConductorWindowResponse_eq_ramanujanWindow
    (k x q : ℕ) :
    primorialReducedConductorWindowResponse k x q =
      primorialReducedConductorRamanujanWindow k x q := by
  exact primeWheelReducedConductorWindowResponse_eq_ramanujanWindow
    (primorialMinimalWheelSystem k) x q

/-- If the periodic raw spectrum is constant on a reduced-conductor shell, its
entire shell response factors exactly as that coefficient times the normalized
Ramanujan window.  The constancy hypothesis is an explicit theorem argument,
not an axiom or hidden estimate. -/
theorem primorialPeriodicRawConductorResponse_eq_constant_mul_ramanujanWindow
    (k x q : ℕ) (C : ℂ)
    (hconst : ∀ r : ZMod (primorialMinimalWheelSystem k).modulus,
      q = reducedAdditiveConductor r →
        primorialPeriodicRawSpectrum k r = C) :
    primorialPeriodicRawConductorResponse k x q =
      C * primorialReducedConductorRamanujanWindow k x q := by
  classical
  rw [← primorialReducedConductorWindowResponse_eq_ramanujanWindow]
  change primorialPeriodicRawConductorResponse k x q =
    C * primeWheelReducedConductorWindowResponse
      (primorialMinimalWheelSystem k) x q
  unfold primorialPeriodicRawConductorResponse
    primorialPeriodicRawSpectralAtom
    primeWheelReducedConductorWindowResponse
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hq : q = reducedAdditiveConductor r
  · simp only [hq, if_true]
    rw [hconst r hq]
    ring
  · simp [hq]

/-- Under the same exact shell-constancy hypothesis, the actual corrected
packet is raw Ramanujan response minus twice the smooth packet.  This is the
signed form that later estimates must preserve. -/
theorem primorialPeriodicRawJointConductorResponse_eq_constantRamanujan_sub_two_smooth
    (k x q : ℕ) (C : ℂ)
    (hconst : ∀ r : ZMod (primorialMinimalWheelSystem k).modulus,
      q = reducedAdditiveConductor r →
        primorialPeriodicRawSpectrum k r = C) :
    primorialPeriodicRawJointConductorResponse k x q =
      C * primorialReducedConductorRamanujanWindow k x q -
        2 * primorialPeriodicSmoothConductorResponse k x q := by
  rw [primorialPeriodicRawJointConductorResponse_eq_raw_sub_two_smooth]
  rw [primorialPeriodicRawConductorResponse_eq_constant_mul_ramanujanWindow
    k x q C hconst]

end RHLean.Analysis
