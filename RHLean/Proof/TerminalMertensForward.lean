import RHLean.Analysis.MertensEnergyRHForward
import RHLean.Proof.TerminalMertensReduction

/-!
# Discharge the terminal forward Mertens criterion

The analytic continuation, identity theorem, and completed-zeta reflection now
construct the one direction of the classical Mertens criterion that the terminal
proof actually uses.  This file plugs that theorem into
`TerminalMertensReduction` and records the resulting unconditional implication
from the projected-renewal estimate to Mathlib's Riemann Hypothesis.

The reverse implication `RH → MertensEnergyBoundedStatement` is not needed by
this forward route and is not asserted here.
-/

noncomputable section

namespace RHLean.Proof

namespace TerminalMertensForward

open RHLean.Analysis
open CanonicalGapAncestryQuadraticClosure
open TerminalMertensReduction

/-- The previously external forward Mertens criterion is now constructed from
the repository's Mellin continuation and completed-zeta reflection. -/
theorem mertensForwardCriterion : MertensForwardCriterion := by
  intro hM
  change RiemannHypothesis
  exact riemannHypothesis_of_mertensEnergy hM

/-- Consequently the terminal implication no longer needs a classical
Mertens/RH criterion supplied by the caller. Once the projected-renewal
quadratic estimate is proved, RH follows outright. -/
theorem projectedRenewalQuadraticBounded_imp_riemannHypothesis_unconditional
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ProjectedRenewalQuadraticBoundedStatement Λ →
      RiemannHypothesisStatement :=
  projectedRenewalQuadraticBounded_imp_riemannHypothesis
    hΛ mertensForwardCriterion

end TerminalMertensForward

end RHLean.Proof
