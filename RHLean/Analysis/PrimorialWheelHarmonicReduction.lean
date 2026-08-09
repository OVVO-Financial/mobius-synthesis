import RHLean.Analysis.PrimeWheelHarmonicCriterion
import RHLean.Analysis.PrimeWheelJointSpectrum
import RHLean.Analysis.PrimeWheelRHBridge
import RHLean.Analysis.PrimeWheelTorusRealization
import RHLean.Arithmetic.PrimorialWheelPrefixIdentity

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Concrete RH-scale harmonic statement for the synchronized primorial-wheel
family. -/
def PrimorialWheelHarmonicNonconcentration : Prop :=
  PrimeWheelHarmonicNonconcentration primorialWheelFamily

/-- Concrete arithmetic residual statement for the synchronized primorial-wheel
family. -/
def PrimorialWheelResidualBoundedStatement : Prop :=
  PrimeWheelResidualBoundedStatement primorialWheelFamily

/-- The concrete spectral prefix is exactly the corresponding Mertens increment. -/
theorem primorialWheel_spectralPrefix_eq_mertens_sub
    (k : ℕ) {x : ℕ}
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    (primorialWheelSystem k).spectralPrefix x =
      mertensSummatory x - mertensSummatory (primorialBlockLower k) := by
  rw [(primorialWheelSystem k).spectralPrefix_eq_residual
    (primorialWheelSystem k).canonicalTorusRealizationCertificate
    hlower hupper]
  exact primorialWheel_residual_cast_eq_mertens_sub k hlower hupper

/-- For the concrete primorial family, the harmonic statement and the arithmetic
residual statement are definitionally equivalent after the proved lossless
torus realization. -/
theorem primorialWheel_harmonic_iff_residual :
    PrimorialWheelHarmonicNonconcentration ↔
      PrimorialWheelResidualBoundedStatement := by
  exact primeWheelHarmonicNonconcentration_iff_residualBounded
    primorialWheelFamily
    (canonicalPrimeWheelTorusCertificates primorialWheelFamily)

/-- The remaining elementary global transfer package for the concrete family. -/
def PrimorialWheelMertensBridge : Prop :=
  PrimeWheelMertensBridge primorialWheelFamily

/-- Once the global primorial-block transfer and the classical Mertens/RH
criterion are supplied as ordinary theorems, the concrete finite harmonic
statement is equivalent to RH. -/
theorem primorialWheel_harmonic_iff_riemannHypothesis
    (bridge : PrimeWheelMertensBridge primorialWheelFamily)
    (criterion : MertensEnergyBoundedStatement ↔ RiemannHypothesisStatement) :
    PrimorialWheelHarmonicNonconcentration ↔ RiemannHypothesisStatement := by
  exact primeWheelHarmonicNonconcentration_iff_riemannHypothesis
    primorialWheelFamily
    (canonicalPrimeWheelTorusCertificates primorialWheelFamily)
    bridge criterion

end RHLean.Analysis
