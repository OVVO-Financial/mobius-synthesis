# Elementary and PNT-centering seams

This note records the seam theorems that join the square-block and prime-wheel
descriptions: the elementary prime-sieve bridge, the PNT-centering module, and
the reciprocal-quotient PNT-error module that connects them.

## Elementary prime-sieve bridge

The elementary prime-sieve bridge is carried by:

```text
RHLean.Proof.PrimeSievePostSqrtGap
RHLean.Proof.PrimeSieveSquareRootTransport
```

The first proves the arbitrary post-square-root identity for the all-plus prime-comb state:

```text
M_y^+(x) - M(x)
  = 2 * sum_{y < q <= x, q prime} M(floor(x/q))
```

under `sqrt x < y`. The second specializes to `x = R^2 - 1`, `y = R` and identifies the pre-large-prime state with the original square-block `smooth + transport`, so its difference from the completed Mertens state is exactly twice the existing square-root transport term.

The existing PNT-centering module

```text
RHLean.Analysis.PrimeSievePNTCentering
```

uses the repository's singleton logarithmic-integral density

```text
density(q) = Li(q) - Li(q-1)
```

and proves

```text
H_{k,n} = centered PNT-corrected comb - 2 * centered prime error.
```

The library includes

```text
RHLean.Analysis.PrimeSieveQuotientPNTError
```

It proves that for positive `d=floor(x/q)` the literal quotient fibre is the reciprocal interval

```text
max(y, floor(x/(d+1))) < q <= floor(x/d),
```

that the singleton Li masses telescope across this interval, and that the exact PNT error is

```text
sum_d M(d) *
  (prime count on reciprocal interval - Li mass of reciprocal interval).
```

It also reindexes the deterministic PNT bulk and exact prime tail, proves the deterministic Li contribution cancels algebraically in the corrected all-plus identity, and pushes the reciprocal-interval error through the same square-wheel zero-mode centering used by `H_{k,n}`.

These are exact finite realization, centering, and reindexing theorems. They assert no PNT error estimate, Bombieri-Vinogradov estimate, large-sieve estimate, RH-scale power saving, or new axiom. The centered PNT-corrected comb remains a separate analytic target from the explicit reciprocal-interval prime-distribution error.

## Build completeness

The library is build-complete as a standalone Lean project: `RHLean.lean` is the
authoritative import manifest, and every module it imports resolves to a file
under `RHLean/`. When the manifest gains an import, the module and the manifest
change together, so the formal statements never depend on a file that is not
present here.
