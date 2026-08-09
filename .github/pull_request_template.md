## Research classification

- [ ] Maintenance or documentation only; no Lean mathematical source changed.
- [ ] Quantitative frontier advance.
- [ ] Cross-track synthesis advance.

### Quantitative lane

If this PR improves the analytic frontier, update `boundary/frontier.json` and provide:

- Previous frontier:
- New frontier:
- Witness module:
- Witness theorem:
- Certified exponent, if using `power_bound`:

The witness theorem must prove the canonical predicate from `RHLean.Analysis.MobiusSynthesisBoundary`.

### Synthesis lane

If this PR adds exact synthesis structure without improving the `H_{k,n}` exponent, increment `boundary/synthesis.json` by exactly one and provide:

- Synthesis summary:
- Witness module:
- Witness theorem:
- Square-block anchors used:
- Prime-wheel anchors used:

The anchors must already exist on the base branch and must occur directly in the printed Lean witness declaration. Importing both initiatives without using both does not pass.

Exact bridge identities, transfer results, shared residual statements, and compatibility theorems are allowed when they genuinely couple square-block and prime-wheel machinery in synthesis form.

## Validation

- [ ] `lake build RHLean --wfail`
- [ ] The research witness type-checks.
- [ ] `#print axioms` reports only standard logical axioms.
- [ ] For the synthesis lane, the witness directly invokes both track anchors.
