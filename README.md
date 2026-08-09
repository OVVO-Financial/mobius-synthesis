# Möbius Synthesis

**Möbius Synthesis** joins the square-block and prime-wheel Möbius-cancellation developments into one machine-checked bridge. It is not a third independent route to the Riemann Hypothesis. Its role is to identify where the two coordinate systems describe the same arithmetic residual, expose the exact algebra already available from both tracks, and isolate the analytic estimates that remain open.

Companion standalone repositories:

- Square blocks: https://github.com/OVVO-Financial/square-block-mobius
- Prime wheels: https://github.com/OVVO-Financial/prime-wheel-mobius

The root manifest `RHLean.lean` imports **248 Lean modules**, every one of which resolves to a file under `RHLean/`. See `MODULES.md` for the module inventory and `SEAMS.md` for the elementary prime-sieve and PNT-centering seams.

## Two coordinate systems, one residual

Square blocks expose the lifetime and geometric organization of the Möbius field: complete square-prefix endpoints, canonical factor geometry, transport, survivor and death-shell structure, ancestry, and signed Gram architectures.

Prime wheels expose the spectral and residue-class organization of the same field: exact Möbius recovery, finite-torus Fourier decomposition, conductor structure, Ramanujan reduction, divisor-boundary formulas, and Mertens transfer.

The synthesis identifies exact seams between these descriptions before any unresolved asymptotic estimate is invoked.

Let

- `L_k` and `U_k` be the synchronized primorial-block endpoints;
- `W_k = primorialMinimalWheelSystem k` be the minimal-torus wheel;
- `Q_k` be its modulus;
- `X_n = (n+1)^2 - 1` be a complete square-prefix endpoint;
- `R_k(x)` be the corrected wheel residual.

At a complete square sample inside the block, the checked square-wheel identity has the form

```math
R_k(X_n) = H_{k,n} + \rho_{k,n} R_k(U_k),
\qquad
\rho_{k,n} = \frac{X_n-L_k}{Q_k}.
```

The nonzero response `H_{k,n}` is represented in Lean by `squareWheelNonzeroSampleResponse`.

## Zero-mode elimination and contraction

`RHLean.Analysis.SquareWheelZeroModeElimination` removes the self-referential zero mode exactly. At a distinguished terminal complete square sample `n_*`,

```math
R_k(U_k) = \frac{H_{k,n_*}+T_{k,n_*}}{1-\rho_{k,n_*}},
```

where the terminal interpolation term satisfies the checked square-root-scale estimate

```math
|T_{k,n_*}|^2 < 9(U_k+1).
```

`RHLean.Analysis.SquareWheelQuantitativeBridge` proves that from synchronized block `k >= 2`,

```math
Q_k > 6U_k,
```

and therefore every complete square sample in the block has

```math
0 <= \rho_{k,n} < 1/6.
```

Thus the zero-frequency feedback is uniformly contractive and the incomplete terminal square is already at square-root scale.

The same module defines `primorialExpansionReindexedNumerator` and proves the exact bridge from the square-side nonzero response to the fully collapsed wheel numerator after zero-mode subtraction.

## Elementary prime-sieve seam

The current synthesis also contains an elementary square-root prime-sieve route into the same square-wheel object.

`RHLean.Proof.PrimeSievePostSqrtGap` proves, under `sqrt x < y`, the exact finite identity

```text
M_y^+(x) - M(x)
  = 2 * sum_{y < q <= x, q prime} M(floor(x/q)).
```

`RHLean.Proof.PrimeSieveSquareRootTransport` specializes this at `x = R^2 - 1`, `y = R` and identifies the pre-large-prime state with the existing square-block smooth and transport variables. This connects fresh-prime parity directly to the square-root transport term already present in the square-block development.

No prime-distribution estimate is used in this layer.

## PNT centering and reciprocal quotient intervals

`RHLean.Analysis.PrimeSievePNTCentering` splits the exact prime tail into a deterministic logarithmic-integral density bulk plus the exact prime-indicator discrepancy. Its singleton density is

```text
density(q) = Li(q) - Li(q-1).
```

After applying the actual square-wheel zero-mode centering, the canonical nonzero response is written exactly as

```math
H_{k,n}
  = \text{centered PNT-corrected comb}
    - 2\,\text{centered prime error}.
```

The synchronized module `RHLean.Analysis.PrimeSieveQuotientPNTError` reindexes the prime error by

```text
d = floor(x/q).
```

For every positive quotient, the literal fibre is proved equal to the reciprocal interval

```text
max(y, floor(x/(d+1))) < q <= floor(x/d).
```

The singleton Li masses telescope on each such interval. Consequently the exact PNT error becomes a finite Mertens-weighted family of classical prime-count-minus-Li discrepancies:

```text
sum_d M(d) *
  (prime count on reciprocal interval - Li mass on reciprocal interval).
```

The same module reindexes the deterministic PNT bulk and the exact prime tail, proves the deterministic Li contribution cancels algebraically in the corrected all-plus identity, and pushes the reciprocal-interval error through the square-wheel center.

The resulting checked synthesis identity is

```math
H_{k,n}
  = \text{centered PNT-corrected comb}
    - 2\,\text{centered Mertens-weighted reciprocal prime discrepancy}.
```

In Lean this is `primorialMinimalSquareWheelNonzeroResponse_eq_pntCorrected_sub_two_reciprocalError`, with the corresponding norm transfer in `norm_primorialMinimalSquareWheelNonzeroResponse_le_reciprocalPNT`.

## Current analytic boundary

The terminal quantitative criterion remains

```math
|H_{k,n}| \ll_{\varepsilon} (X_n+1)^{1/2+\varepsilon}
```

uniformly over synchronized complete-square samples.

That estimate is **not proved**.

The synchronized exact work makes the present analytic boundary more explicit rather than closing it. One current representation separates the problem into two centered components:

1. control of the centered PNT-corrected comb;
2. control of the centered Mertens-weighted reciprocal-interval prime-count discrepancies, including the short reciprocal intervals near the square-root edge.

No pointwise or averaged PNT-error theorem, short-interval prime theorem, Bombieri-Vinogradov estimate, large-sieve estimate, power saving, or unconditional proof of RH is claimed by these exact reductions.

If the required RH-scale bound for `H_{k,n}` is established, the existing zero-mode elimination, square interpolation, Mertens transfer, Mellin continuation, zeta identity continuation, and terminal RH bridge carry it through the remaining formal chain.

## What counts as synthesis progress

The repository should continue to use both initiatives in synthesis form. A useful exact theorem need not immediately improve the exponent on `H_{k,n}` if it genuinely creates a new square-block and prime-wheel bridge.

The `boundary-advance` policy therefore has two research lanes:

- **Quantitative frontier:** a theorem strictly improves the certified bound on the canonical nonzero response or proves the RH-scale predicate.
- **Cross-track synthesis:** a new exact theorem directly invokes established square-block and prime-wheel declarations and advances the shared bridge, transfer, sampling, compatibility, or residual architecture.

One-sided square-block work, one-sided prime-wheel work, imports that do not actually couple the tracks, and purely cosmetic alternate representations do not qualify as synthesis progress by themselves. See `boundary/BOUNDARY_POLICY.md` for the machine-enforced policy.

## Machine-checked status at the synchronized baseline

The checked source currently includes, among other results:

1. minimal-torus Möbius recovery on synchronized primorial blocks;
2. equality of the minimal and historical wheel residuals on the arithmetic range;
3. exact square sampling of the wheel residual;
4. exact zero-mode splitting and elimination;
5. square-root-scale terminal interpolation;
6. factor-six modulus separation and uniform `1/6` contraction;
7. exact expansion-reindexed numerator identification of the nonzero response;
8. Ramanujan and divisor-boundary reductions on the prime-wheel side;
9. elementary post-square-root prime-sieve and square-root transport identities;
10. exact PNT centering of the prime tail;
11. exact reciprocal quotient-fibre reindexing of the PNT error;
12. the reciprocal-interval representation and norm transfer for `H_{k,n}`;
13. Mertens, Mellin, zeta-continuation, and terminal RH transfer infrastructure.

These are exact structural, centering, reindexing, and transfer theorems. They do not by themselves provide the unresolved analytic cancellation estimate.

## Direct synthesis modules

The modules most directly relevant to the current synthesis seam include:

```text
RHLean.Proof.PrimeSievePostSqrtGap
RHLean.Proof.PrimeSieveSquareRootTransport
RHLean.Analysis.PrimeSievePNTCentering
RHLean.Analysis.PrimeSieveQuotientPNTError
RHLean.Arithmetic.PrimorialWheelMinimalTorus
RHLean.Arithmetic.PrimeProductLowerBound
RHLean.Analysis.SquareWheelNesting
RHLean.Analysis.SquareWheelQuadraticSampling
RHLean.Analysis.SquareWheelZeroModeElimination
RHLean.Analysis.SquareWheelQuantitativeBridge
RHLean.Analysis.PrimeWheelPeriodicRawBridge
RHLean.Analysis.PrimeWheelRawConductorMobiusReindex
RHLean.Analysis.PrimeWheelRawBoundaryMobiusPairing
RHLean.Analysis.PrimeWheelRawBoundaryExpansionCollapse
RHLean.Analysis.PrimeWheelFullConductorUniformPacket
RHLean.Analysis.PrimeWheelFullConductorMobiusReindexedResidual
RHLean.Analysis.PrimeWheelSmoothConductorMobiusReindex
RHLean.Analysis.PrimeWheelRamanujanIdentification
RHLean.Analysis.PrimeWheelRamanujanBoundaryReduction
RHLean.Analysis.PrimeWheelRamanujanBoundaryBulkReduction
RHLean.Analysis.RamanujanDivisorBoundary
RHLean.Analysis.RamanujanDivisorBoundaryBulk
RHLean.Analysis.PrimorialWheelMertensTransfer
RHLean.Analysis.MertensEnergyRHForward
RHLean.Analysis.MertensMellinLSeriesBridge
RHLean.Analysis.MertensMellinContinuation
RHLean.Analysis.MertensZetaIdentityContinuation
RHLean.Proof.TerminalMertensForward
RHLean.Proof.TerminalMertensReduction
RHLean.Proof.RiemannHypothesisBridge
RHLean.Proof.TerminalAxiomAudit
```

`MODULES.md` gives the fuller track-level inventory and records the **34-module increase** from the original 214-module inventory to the current 248-module manifest.

## Repository layout

This repository contains:

- `README.md` — synthesis overview and current status;
- `MODULES.md` — Lean source map and module inventory;
- `SEAMS.md` — elementary prime-sieve and PNT-centering seams;
- `RHLean.lean` — authoritative import manifest;
- `RHLean/` — Lean source tree;
- `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json` — pinned project metadata;
- `boundary/` — quantitative and cross-track research ledgers and policy;
- `.github/` — PR policy and workflow material;
- `scripts/check_boundary_advance.py` — trusted boundary checker.

There is currently no `paper/` directory. Nothing here is re-exported back into either companion repository.

## Verification

From the repository root:

```bash
lake build RHLean --wfail
```

The `Baseline coupling audit` workflow runs the same build in CI, then prints the synthesis theorem together with its axiom dependencies. It fails if that theorem rests on `sorryAx`, if no axiom report is produced, or if the statement loses either its square-block or its prime-wheel anchor.

## Status convention

- **Machine checked** means the statement is represented by a checked theorem or definition in the synchronized Lean source.
- **Exact reduction** means finite algebra, reindexing, centering, or transfer with no asymptotic estimate smuggled in.
- **Open analytic target** means an estimate is still unresolved and must not be described as established.
- Numerical experiments and finite-range checks are diagnostic evidence only.

At the synchronized mathematical baseline, the square-wheel bridge, elementary prime-sieve seam, PNT centering, reciprocal quotient reindexing, and transfer infrastructure are machine checked. The RH-scale bound on the canonical nonzero response remains open.

## License

Licensed under the Apache License, Version 2.0; see [LICENSE](LICENSE).
