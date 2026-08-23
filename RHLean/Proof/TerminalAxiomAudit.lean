import RHLean.Proof.CanonicalGapAncestryQuadraticClosure
import RHLean.Proof.SquareRootAncestryParentFibres

/-!
# Axiom footprint of the terminal reduction

`scripts/audit_assumptions.sh` greps the sources for unfinished-proof placeholders and
for declared opaque constants. That is necessary but not sufficient: it inspects text,
not the kernel's record of what a proof actually depends on, and it cannot see anything
inherited through an import.

This module closes that gap for the theorems that carry the reduction to RH. Each
`#print axioms` below asks the kernel directly, while `#guard_msgs` makes the expected
answer part of the build: an added dependency changes the message and fails compilation.
The expected answer for every theorem is exactly

```text
[propext, Classical.choice, Quot.sound]
```

the three standard axioms of Lean's logic used throughout Mathlib. Any other name in
these lists -- in particular `sorryAx`, which is what an unfinished proof compiles to,
or any project-declared axiom -- fails this module and invalidates the corresponding
reduction claim.

Note what this does **not** certify. These are equivalences and implications, not
proofs of their left-hand sides. `ProjectedRenewalQuadraticBoundedStatement` remains
an open analytic proposition; nothing in the project proves it. Likewise,
`ClassicalMertensRHCriterion` is a structure taken as an ordinary theorem argument,
not an axiom, so it does not appear in these lists. The RH endpoint remains conditional
on supplying that classical criterion.

The square-root legal-ancestry Gram reduction is imported here as well so the ordinary
root build type-checks its exact endpoint and parent-fibre identities. Its new analytic
amplification statement remains an explicitly open proposition and is not added to the
axiom guards below.
-/

namespace RHLean.Proof

namespace TerminalAxiomAudit

-- The terminal equivalence: the projected-renewal quadratic bound is RH, given the
-- classical Mertens criterion.
/--
info: 'RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_riemannHypothesis

-- The algebraic half of the chain: the projected-renewal bound is exactly canonical
-- (HS). This one is unconditional.
/--
info: 'RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_canonicalHigh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_canonicalHigh

-- The analytic half: canonical (HS) is RH, given the criterion.
/--
info: 'RHLean.Proof.canonicalHighUniformLocalBounded_iff_riemannHypothesis_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Proof.canonicalHighUniformLocalBounded_iff_riemannHypothesis_realized

end TerminalAxiomAudit

end RHLean.Proof
