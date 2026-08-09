import RHLean.Proof.CanonicalGapAncestryQuadraticClosure

/-!
# The reduction is unconditional down to the classical Mertens statement

Given a `ClassicalMertensRHCriterion`, `CanonicalGapAncestryQuadraticClosure` proves

```text
ProjectedRenewalQuadraticBoundedStatement Λ ↔ RiemannHypothesisStatement.
```

The criterion is never constructed in this project. Reading the chain, it is consumed
at exactly one step: everything from the projected-renewal Gram form down to
`MertensEnergyBoundedStatement` is proved outright.

This module records that unconditional reduction and isolates the direction needed by
the program.

* `projectedRenewalQuadraticBounded_iff_mertensEnergyBounded` proves the reduction
  unconditionally down to `‖M(x)‖^2 ≤ C (x+1)^(1+ε)`. No criterion, realization,
  partition, or low-increment control is supplied by the caller; the only hypothesis is
  `0 ≤ Λ`.

* `projectedRenewalQuadraticBounded_imp_riemannHypothesis` shows that the implication
  from the projected-renewal estimate to RH needs only the forward implication
  `MertensEnergyBoundedStatement → RiemannHypothesisStatement`, not the full
  equivalence.

The two directions of the classical criterion have different analytic requirements.
The forward direction follows from the Dirichlet series
`∑ μ(n) n^(-s) = 1/ζ(s)`: partial summation gives convergence on `re s > 1/2`, the
limit is analytic there, it agrees with `1/ζ` on `re s > 1`, and the identity theorem
forces `ζ ≠ 0` on `re s > 1/2`; the functional equation reflects this to the left half.
No contour shifting or zero-free region is needed. The reverse direction requires the
harder contour argument.

Only the forward direction appears in the implication proved below. The repository's
stronger equivalence theorem still requires the full classical criterion.

Nothing here proves `ProjectedRenewalQuadraticBoundedStatement`. Given a
`ClassicalMertensRHCriterion`, the existing terminal equivalence identifies that
statement with RH, so proving the estimate would prove RH.
-/

namespace RHLean.Proof

namespace TerminalMertensReduction

open RHLean.Proof.CanonicalGapAncestryQuadraticClosure

/-- The reduction is unconditional down to the classical Mertens statement. No
`ClassicalMertensRHCriterion`, supplied partition, or low-increment control is needed;
the only hypothesis is `0 ≤ Λ`. -/
theorem projectedRenewalQuadraticBounded_iff_mertensEnergyBounded
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ProjectedRenewalQuadraticBoundedStatement Λ ↔
      RHLean.Analysis.MertensEnergyBoundedStatement := by
  calc
    ProjectedRenewalQuadraticBoundedStatement Λ ↔
        CanonicalHighUniformLocalBoundedStatement Λ :=
      projectedRenewalQuadraticBounded_iff_canonicalHigh hΛ
    _ ↔ RHLean.Analysis.SquarePrefixHighUniformLocalBoundedStatement
          (canonicalSquarePrefixGeometricPartition Λ (canonicalLowIncrementControl Λ)) :=
      canonicalHighUniformLocalBounded_iff_partition Λ (canonicalLowIncrementControl Λ)
    _ ↔ RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement :=
      (RHLean.Analysis.squarePrefix_uniformLocalBounded_iff_highUniformLocalBounded _).symm
    _ ↔ RHLean.Analysis.MertensEnergyBoundedStatement :=
      RHLean.Analysis.squarePrefix_uniformLocalBounded_iff_mertensEnergyBounded

/-- Given only the forward implication `M(x) = O(x^{1/2+ε}) → RH`, the
projected-renewal estimate implies the Riemann Hypothesis. The reverse implication of
the classical criterion is not used. -/
theorem projectedRenewalQuadraticBounded_imp_riemannHypothesis
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (forward : RHLean.Analysis.MertensEnergyBoundedStatement →
      RHLean.Analysis.RiemannHypothesisStatement) :
    ProjectedRenewalQuadraticBoundedStatement Λ →
      RHLean.Analysis.RiemannHypothesisStatement :=
  fun h => forward ((projectedRenewalQuadraticBounded_iff_mertensEnergyBounded hΛ).mp h)

/-- The one-directional classical input needed for the terminal implication. A proof of
this is enough to derive RH from the projected-renewal estimate without assuming the
reverse RH-to-Mertens direction. -/
def MertensForwardCriterion : Prop :=
  RHLean.Analysis.MertensEnergyBoundedStatement →
    RHLean.Analysis.RiemannHypothesisStatement

/-- The full classical criterion supplies the forward half. Thus the terminal
implication uses only this weaker one-directional assumption; no strict separation of
the two propositions is claimed here. -/
theorem mertensForwardCriterion_of_classical
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion) :
    MertensForwardCriterion :=
  criterion.iff_riemannHypothesis.mp

end TerminalMertensReduction

end RHLean.Proof
