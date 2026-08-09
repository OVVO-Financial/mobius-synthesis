import Mathlib
import RHLean.Analysis.FiniteTorusFourierPairing
import RHLean.Arithmetic.PrimeWheelFiniteSystem

open scoped ArithmeticFunction.Moebius BigOperators ComplexConjugate

noncomputable section

namespace RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Zero-padded corrected field on the common finite torus. -/
def torusJointField (W : PrimeWheelFiniteSystem) : ZMod W.modulus → ℂ :=
  fun z =>
    if W.lower < z.val ∧ z.val ≤ W.upper then
      ((W.correctedSite z.val : ℤ) : ℂ)
    else 0

/-- Pinned interval window `(lower,x]`, represented on the same finite torus. -/
def torusPrefixWindow (W : PrimeWheelFiniteSystem) (x : ℕ) : ZMod W.modulus → ℂ :=
  fun z => if W.lower < z.val ∧ z.val ≤ x then 1 else 0

/-- Physical-space pairing of the joint field with the pinned interval window. -/
def torusPrefixPairing (W : PrimeWheelFiniteSystem) (x : ℕ) : ℂ :=
  RHLean.Analysis.finiteTorusPairing W.torusJointField (W.torusPrefixWindow x)

/-- A torus realization certificate records the lossless zero-padding statement.
It contains only a finite equality, and can be discharged independently of all
analytic estimates. -/
structure TorusRealizationCertificate (W : PrimeWheelFiniteSystem) : Prop where
  pairing_eq_residual :
    ∀ x : ℕ, W.lower < x → x ≤ W.upper →
      W.torusPrefixPairing x = ((W.residual x : ℤ) : ℂ)

/-- Unnormalized DFT of the complete signed joint field. -/
def jointSpectrum (W : PrimeWheelFiniteSystem) : ZMod W.modulus → ℂ :=
  ZMod.dft W.torusJointField

/-- Unnormalized DFT of the pinned interval window. -/
def prefixWindowSpectrum
    (W : PrimeWheelFiniteSystem) (x : ℕ) : ZMod W.modulus → ℂ :=
  ZMod.dft (W.torusPrefixWindow x)

/-- Exact Fourier-side prefix expression.  The `-r` on the window transform is
forced by the sign convention of `ZMod.dft`. -/
def spectralPrefix (W : PrimeWheelFiniteSystem) (x : ℕ) : ℂ :=
  ((W.modulus : ℂ)⁻¹) *
    ∑ r : ZMod W.modulus,
      W.jointSpectrum r * W.prefixWindowSpectrum x (-r)

/-- The finite Fourier representation is exactly the physical-space pairing. -/
theorem torusPrefixPairing_eq_spectralPrefix
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    W.torusPrefixPairing x = W.spectralPrefix x := by
  exact RHLean.Analysis.finiteTorusPairing_eq_spectral
    W.torusJointField (W.torusPrefixWindow x)

/-- Once the lossless zero-padding certificate is supplied, the spectral prefix
is exactly the arithmetic raw-minus-twice-smooth residual. -/
theorem spectralPrefix_eq_residual
    (W : PrimeWheelFiniteSystem)
    (torusCert : W.TorusRealizationCertificate)
    {x : ℕ} (hlower : W.lower < x) (hupper : x ≤ W.upper) :
    W.spectralPrefix x = ((W.residual x : ℤ) : ℂ) := by
  rw [← W.torusPrefixPairing_eq_spectralPrefix]
  exact torusCert.pairing_eq_residual x hlower hupper

/-- A single frequency contribution to the pinned prefix. -/
def spectralPrefixAtom
    (W : PrimeWheelFiniteSystem) (x : ℕ) (r : ZMod W.modulus) : ℂ :=
  ((W.modulus : ℂ)⁻¹) *
    W.jointSpectrum r * W.prefixWindowSpectrum x (-r)

/-- The spectral prefix is the complete sum of all frequency atoms. -/
theorem spectralPrefix_eq_sum_atoms
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    W.spectralPrefix x =
      ∑ r : ZMod W.modulus, W.spectralPrefixAtom x r := by
  unfold spectralPrefix spectralPrefixAtom
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Full signed frequency-frequency Gram entry for a pinned interval. -/
def intervalGramEntry
    (W : PrimeWheelFiniteSystem) (x : ℕ)
    (r s : ZMod W.modulus) : ℂ :=
  W.spectralPrefixAtom x r * conj (W.spectralPrefixAtom x s)

/-- Full signed Gram energy; no off-diagonal term is discarded. -/
def intervalGramEnergy
    (W : PrimeWheelFiniteSystem) (x : ℕ) : ℂ :=
  ∑ r : ZMod W.modulus,
    ∑ s : ZMod W.modulus, W.intervalGramEntry x r s

/-- The complete signed Gram energy is the squared modulus of the spectral
prefix.  This is a special-vector quadratic form, not an entrywise negativity
statement. -/
theorem intervalGramEnergy_eq_mul_conj
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    W.intervalGramEnergy x = W.spectralPrefix x * conj (W.spectralPrefix x) := by
  rw [W.spectralPrefix_eq_sum_atoms, map_sum]
  unfold intervalGramEnergy intervalGramEntry
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]

/-- Real-valued Gram energy. -/
def intervalGramNormSq
    (W : PrimeWheelFiniteSystem) (x : ℕ) : ℝ :=
  ‖W.spectralPrefix x‖ ^ 2

end RHLean.Arithmetic.PrimeWheelFiniteSystem
