# Möbius Synthesis PR boundary policy

The required PR check is `boundary-advance`.

The gate is a **scope gate**, not a mathematical novelty oracle. It prevents the repository from becoming a dumping ground for one-sided square-block work, one-sided prime-wheel work, or notation-only churn, while allowing exact cross-track structure that genuinely advances the shared architecture.

## Current research-status note

The repository has two quantitative descriptions that must be kept distinct.

1. `boundary/frontier.json` certifies the **canonical square-wheel nonzero-response frontier** `H_{k,n}`. Its certified kind remains `exact_reduction`, because no pointwise power exponent below `1` has been proved for that object.
2. The native PNT layer has a **proved generalized affine envelope and strict low-slope cubic contraction**, plus conditional square-root conversion theorems from explicit cutoff or intercept laws. The missing theorem there is RH-compatible physical cutoff control.

The second fact is genuine quantitative progress, but it does **not** mutate the first certificate. A PR must never change `boundary/frontier.json` merely because it improves an affine PNT contraction constant or proves another conditional conversion theorem. The canonical `H_{k,n}` certificate advances only when the canonical predicate itself is strengthened.

`CURRENT_PROOF_ROUTE.md` records both live quantitative fronts and their relationship.

## Lane A: canonical quantitative frontier advance

`RHLean/Analysis/MobiusSynthesisBoundary.lean` retains the canonical quantitative endpoint

```text
H_{k,n} = squareWheelNonzeroSampleResponse (...).
```

`boundary/frontier.json` records the strongest certified direct bound. A quantitative PR must make one of these strict transitions:

1. `exact_reduction -> power_bound`, with rational exponent strictly below `1`;
2. `power_bound(r_old) -> power_bound(r_new)`, with `r_new < r_old`;
3. either open state -> `rh_scale`.

The candidate manifest names a Lean module and theorem. The workflow creates an independent Lean `example` whose type is exactly the claimed canonical predicate and asks Lean to check it.

Improving a generalized PNT slope, an intercept, a local Selberg constant, or a physical-scale sufficient condition does not by itself count as a Lane A transition unless the witness proves the canonical `H_{k,n}` predicate recorded by the ledger.

## Lane B: cross-track synthesis advance

A PR may instead add an exact theorem that advances the **synthesis architecture** without yet improving the exponent on `H_{k,n}`.

`boundary/synthesis.json` is the monotone ledger for this lane. A candidate must increment `revision` by exactly one and record a `last_witness` containing:

- the changed Lean module;
- the new witness theorem;
- a nonempty summary of the synthesis step;
- one or more `square_anchors` naming pre-existing square-block declarations;
- one or more `prime_wheel_anchors` naming pre-existing prime-wheel declarations.

The accepted square-side families include square-prefix, square-block, survivor, lifetime, death-shell, and ancestry declarations. The accepted wheel-side families include primorial, prime-wheel, Ramanujan, conductor, and coconductor declarations.

The checker requires every declared anchor to pre-exist on the base branch. After Lean loads the candidate theorem, the workflow prints the theorem declaration and verifies that the declared square and wheel anchors actually occur in it. Merely importing both tracks is insufficient.

This lane intentionally allows exact identities, transfer theorems, shared residual statements, sampling theorems, compatibility results, and other structural results when they genuinely couple the two initiatives.

## How the PNT-scale route fits the gate

A future theorem proving the missing physical cutoff law should be classified according to what its **Lean declaration actually establishes**:

- if it also proves a stricter canonical `H_{k,n}` bound, use Lane A;
- if it is a new theorem genuinely coupling established square-block and prime-wheel declarations, use Lane B;
- if it is one-sided quantitative infrastructure, it does not qualify until it is packaged into a synthesis-facing theorem.

This preserves the repository's purpose: verified synthesis-facing research status rather than every isolated experiment.

## What still fails

The gate rejects a Lean research PR if it satisfies neither lane. In particular, these do not qualify by themselves:

- an isolated square-block theorem with no prime-wheel participation;
- an isolated prime-wheel theorem with no square-block participation;
- a new basis, reindexing, or equivalent energy confined to one track;
- a theorem that merely imports both tracks but whose declaration invokes neither jointly;
- newly invented anchor declarations used to self-certify the same PR;
- a quantitative frontier edit that does not strictly strengthen the certified canonical bound;
- relabeling a conditional square-root conversion theorem as an unconditional RH-scale result;
- relabeling the improved affine PNT contraction as a certified `H_{k,n}` exponent.

## Maintenance changes

A PR that does not change `RHLean.lean` or a Lean file below `RHLean/` may leave both research ledgers unchanged. This permits documentation, CI, and repository maintenance without pretending such work is mathematical progress.

Any Lean mathematical source change must carry either a quantitative frontier certificate or a cross-track synthesis certificate.

## Trust model

The workflow uses `pull_request_target` only to obtain the workflow and checker from the trusted base branch. It then checks out the candidate with persisted Git credentials disabled and grants only read access. The candidate cannot make an edited copy of `scripts/check_boundary_advance.py` decide its own PR.

The Lean build runs with no GitHub token exported to the build step. The quantitative contract itself is rejected if modified in the same research PR.

After the witness type-checks, the workflow runs `#print axioms` and rejects dependencies outside Lean's standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`. In particular, a contributor cannot add an axiom whose type is the desired result and use that as a research advance.

## Repository settings

Protect the default branch and make the status check named `boundary-advance` required. Enable Code Owner review for the gate infrastructure listed in `.github/CODEOWNERS`.
