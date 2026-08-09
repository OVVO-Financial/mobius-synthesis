import RHLean.Analysis.PrimeWheelHarmonicCriterion
import RHLean.Analysis.SquarePrefixMertensBridge
import RHLean.Proof.RiemannHypothesisBridge
import RHLean.Analysis.PrimeWheelPeriodicRawAttack

noncomputable section

namespace RHLean.Analysis

/-- Global arithmetic transfer for a synchronized wheel family.

This structure isolates the elementary but separate task of proving that the
block residual criterion is exactly the ordinary global Mertens-energy
criterion.  It contains theorem fields only and introduces no axiom. -/
structure PrimeWheelMertensBridge (W : PrimeWheelFamily) : Prop where
  residual_iff_mertensEnergy :
    PrimeWheelResidualBoundedStatement W ↔ MertensEnergyBoundedStatement

/-- Complete conditional bridge from the finite harmonic nonconcentration
statement to the repository's protected global Mertens criterion. -/
theorem primeWheelHarmonicNonconcentration_iff_mertensEnergy
    (W : PrimeWheelFamily)
    (torusCert : PrimeWheelTorusCertificates W)
    (bridge : PrimeWheelMertensBridge W) :
    PrimeWheelHarmonicNonconcentration W ↔ MertensEnergyBoundedStatement := by
  exact (primeWheelHarmonicNonconcentration_iff_residualBounded W torusCert).trans
    bridge.residual_iff_mertensEnergy

/-- Zero-friction final integration point.  The classical Mertens/RH
equivalence is accepted as an ordinary theorem argument, matching the existing
repository adapter. -/
theorem primeWheelHarmonicNonconcentration_iff_riemannHypothesis
    (W : PrimeWheelFamily)
    (torusCert : PrimeWheelTorusCertificates W)
    (bridge : PrimeWheelMertensBridge W)
    (criterion : MertensEnergyBoundedStatement ↔ RiemannHypothesisStatement) :
    PrimeWheelHarmonicNonconcentration W ↔ RiemannHypothesisStatement := by
  exact (primeWheelHarmonicNonconcentration_iff_mertensEnergy
    W torusCert bridge).trans criterion

/-- One-direction closure theorem in the form used by downstream proof routes. -/
theorem riemannHypothesis_of_primeWheelHarmonicNonconcentration
    (W : PrimeWheelFamily)
    (torusCert : PrimeWheelTorusCertificates W)
    (bridge : PrimeWheelMertensBridge W)
    (criterion : MertensEnergyBoundedStatement ↔ RiemannHypothesisStatement)
    (hnc : PrimeWheelHarmonicNonconcentration W) :
    RiemannHypothesisStatement :=
  (primeWheelHarmonicNonconcentration_iff_riemannHypothesis
    W torusCert bridge criterion).mp hnc

end RHLean.Analysis
