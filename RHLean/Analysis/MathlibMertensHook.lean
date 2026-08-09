import RHLean.Analysis.ConcreteSquarePrefixGeometry

noncomputable section

namespace RHLean.Analysis

/--
The zero-friction integration point for a future mathlib Mertens theorem.

A caller supplies the classical equivalence itself; no project-specific bridge,
realization, indexing adapter, or structure constructor appears in the theorem
signature.
-/
theorem squarePrefix_highUniformLocalBounded_iff_riemannHypothesis_of_classical_iff
    (partition : SquarePrefixGeometricPartition)
    (criterion : MertensEnergyBoundedStatement ↔ RiemannHypothesisStatement) :
    SquarePrefixHighUniformLocalBoundedStatement partition ↔
      RiemannHypothesisStatement := by
  exact squarePrefix_highUniformLocalBounded_iff_riemannHypothesis
    partition ⟨criterion⟩

end RHLean.Analysis
