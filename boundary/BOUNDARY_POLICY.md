# Möbius synthesis PR boundary policy

The required PR check is `boundary-advance`.

The gate is intentionally a **scope gate**, not a mathematical novelty oracle. It should prevent the synthesis repository from becoming a dumping ground for one-sided square-block work, one-sided prime-wheel work, or notation-only churn. It should not require every useful synthesis PR to immediately improve the final bound on the nonzero response.

The standalone repository begins from the synchronized mathematical baseline recorded in `boundary/synthesis.json`. That baseline includes the representative reciprocal-interval square-wheel theorem and starts at `revision = 0`; it is publication provenance, not prior standalone PR history.

A Lean-source research PR therefore has two accepted lanes.

## Lane A: quantitative frontier advance

`RHLean/Analysis/MobiusSynthesisBoundary.lean` retains the canonical quantitative endpoint for

`H_{k,n} = squareWheelNonzeroSampleResponse (...)`.

`boundary/frontier.json` records the strongest certified quantitative state. A quantitative PR must make one of the strict transitions below:

1. `exact_reduction -> power_bound`, with a rational exponent strictly below `1`;
2. `power_bound(r_old) -> power_bound(r_new)`, with `r_new < r_old`;
3. either open state -> `rh_scale`.

The candidate manifest names a Lean module and theorem. The workflow creates an independent Lean `example` whose type is exactly the claimed canonical predicate and asks Lean to check it. This lane therefore still requires a genuine quantitative strengthening of the existing `H_{k,n}` boundary.

## Lane B: cross-track synthesis advance

A PR may instead add an exact theorem that advances the **synthesis architecture** without yet improving the exponent on `H_{k,n}`.

`boundary/synthesis.json` is a monotone standalone ledger for this lane. The publication baseline is descriptive and does not consume a repository PR revision. A candidate must increment `revision` by exactly one and record a `last_witness` containing:

- the changed Lean module;
- the new witness theorem;
- a nonempty summary of the synthesis step;
- one or more `square_anchors` naming pre-existing square-block declarations;
- one or more `prime_wheel_anchors` naming pre-existing prime-wheel declarations.

The accepted square-side families include square-prefix, square-block, survivor, lifetime, death-shell, and ancestry declarations. The accepted wheel-side families include primorial, prime-wheel, Ramanujan, conductor, and coconductor declarations.

The checker requires every declared anchor to pre-exist on the base branch. After Lean loads the candidate theorem, the workflow prints the theorem declaration and verifies that the declared square and wheel anchors actually occur in it. Merely importing both tracks is therefore insufficient.

This lane intentionally allows exact identities, transfer theorems, shared residual statements, sampling theorems, compatibility results, or other structural results when they genuinely couple the two initiatives in synthesis form.

## What still fails

The gate rejects a Lean research PR if it does not satisfy either lane.

In particular, the following do not qualify by themselves:

- an isolated square-block theorem with no prime-wheel participation;
- an isolated prime-wheel theorem with no square-block participation;
- a new basis, reindexing, or equivalent energy confined to one track;
- a theorem that merely imports both tracks but whose declaration does not invoke both;
- newly invented anchor declarations used to self-certify the same PR;
- a quantitative frontier edit that does not strictly strengthen the certified bound.

A cross-track theorem can be exact and can leave the `H_{k,n}` exponent unchanged.

## Maintenance changes

A PR that does not change `RHLean.lean` or a Lean file below `RHLean/` may leave both research ledgers unchanged. This permits documentation, CI, and repository maintenance without pretending such work is mathematical progress.

Any Lean mathematical source change must carry either a quantitative frontier certificate or a cross-track synthesis certificate.

## Trust model

The workflow uses `pull_request_target` only to obtain the workflow and checker from the trusted base branch. It then checks out the candidate with persisted Git credentials disabled and grants only read access. The candidate cannot make its own edited copy of `scripts/check_boundary_advance.py` decide the current PR.

The Lean build runs with no GitHub token exported to the build step. The quantitative contract itself is rejected if modified in the same research PR.

After the witness type-checks, the workflow runs `#print axioms` and rejects dependencies outside Lean's standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`. In particular, a contributor cannot make a fresh axiom whose type is the desired result and use that as a research advance.

## Repository settings

For the standalone `mobius-synthesis` repository, protect the default branch and make the status check named `boundary-advance` required. Also enable Code Owner review for the gate infrastructure listed in `.github/CODEOWNERS`.

This workflow runs from `.github/workflows/` in this repository.
