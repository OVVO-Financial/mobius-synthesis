## Research classification

- [ ] Maintenance or documentation only; no Lean mathematical source changed.
- [ ] Canonical `H_{k,n}` quantitative frontier advance.
- [ ] Cross-track synthesis advance.

## Current-status accuracy

The current baseline contains a proved generalized affine PNT contraction and conditional square-root conversion theorems, while the physical cutoff law and the canonical `H_{k,n}` RH-scale exponent remain open.

- [ ] I have not described the improved affine PNT contraction as an unconditional square-root bound.
- [ ] I have not described a conditional cutoff or intercept bridge as proving its hypothesis.
- [ ] I have not advanced `boundary/frontier.json` unless the witness proves the canonical `MobiusSynthesisBoundary` predicate.
- [ ] If this PR concerns physical cutoff control, I have stated explicitly whether it is one-sided infrastructure, a cross-track synthesis theorem, or a canonical `H_{k,n}` advance.

### Quantitative lane

If this PR improves the canonical analytic frontier, update `boundary/frontier.json` and provide:

- Previous frontier:
- New frontier:
- Witness module:
- Witness theorem:
- Certified exponent, if using `power_bound`:

The witness theorem must prove the canonical predicate from `RHLean.Analysis.MobiusSynthesisBoundary`.

Improving a cubic contraction constant, an affine intercept, or a sufficient cutoff law does not by itself advance this ledger unless the witness proves the recorded canonical target.

### Synthesis lane

If this PR adds exact synthesis structure without improving the `H_{k,n}` exponent, increment `boundary/synthesis.json` by exactly one and provide:

- Synthesis summary:
- Witness module:
- Witness theorem:
- Square-block anchors used:
- Prime-wheel anchors used:

The anchors must already exist on the base branch and must occur directly in the printed Lean witness declaration. Importing both initiatives without using both does not pass.

Exact bridge identities, transfer results, shared residual statements, sampling theorems, signed frontier compatibility results, and other cross-track theorems are allowed when they genuinely couple square-block and prime-wheel machinery.

## Validation

- [ ] `lake build RHLean --wfail`
- [ ] `bash scripts/audit_assumptions.sh`
- [ ] The research witness type-checks.
- [ ] `#print axioms` reports only standard logical axioms.
- [ ] For the synthesis lane, the witness directly invokes both track anchors.
- [ ] The strict low-slope affine contraction and conditional square-root scale bridge still elaborate.
