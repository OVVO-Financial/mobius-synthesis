# Möbius Synthesis — Lean source map

This repository intentionally contains the full import-audited `RHLean` library rather than a minimal transitive closure. `RHLean.lean` is the authoritative file-by-file inventory. The manifest currently imports **248 Lean modules**, and every imported `RHLean.*` module resolves to the corresponding path under `RHLean/`.

## Elementary prime-sieve seam

The synthesis now records an elementary seam beneath the later square-wheel Fourier bridge.

`RHLean.Proof.PrimeSievePostSqrtGap` defines the all-plus prime-comb state by reversing the seed orientation of the existing `seededPrimeComb`. After all primes through a cutoff `y` strictly above `sqrt x` have acted, it proves the exact identity

```text
M_y^+(x) - M(x)
  = 2 * sum_{y < q <= x, q prime} M(floor(x/q)).
```

The proof is finite bookkeeping only. Under square-root coverage, every unresolved squarefree source has one remaining prime factor `q > y`; applying that fresh prime changes its sign once. The module reindexes the unresolved sources by their unique canonical `(c,q)` pair and identifies the cofactor-first batch with the lower-scale Mertens prime tail.

`RHLean.Proof.PrimeSieveSquareRootTransport` specializes this theorem to the complete square endpoint `x = R^2 - 1`, `y = R`, and identifies the two prime-sieve states with the original square-block smooth and transport variables:

```text
before remaining large-prime flips = smooth + transport
after all prime flips              = smooth - transport = M(R^2-1)
```

In particular it proves

```text
before - M(R^2-1) = 2 * transport
before + M(R^2-1) = 2 * smooth.
```

`RHLean.Analysis.PrimeSievePNTCentering` then separates the explicit prime tail into a deterministic logarithmic-integral density bulk and the exact prime-indicator discrepancy. Its singleton density uses the same Li convention as the existing exact-activity prime-density route:

```text
density(q) = Li(q) - Li(q-1).
```

The module proves the exact split

```text
prime tail = PNT bulk + prime-distribution error
```

and pushes it through the **actual** square-wheel zero-mode centering coefficient `(X_n-L_k)/Q_k`. Thus the canonical nonzero response has the exact forms

```text
H_{k,n} = centered PNT-corrected comb - 2 * centered prime error
```

and

```text
H_{k,n}
  = centered all-plus comb
    - 2 * centered PNT bulk
    - 2 * centered prime error.
```

`RHLean.Analysis.PrimeSieveQuotientPNTError` reindexes that prime error by the exact quotient `d=floor(x/q)`. For every positive quotient the literal fibre is proved equal to

```text
max(y, floor(x/(d+1))) < q <= floor(x/d),
```

and the singleton Li masses telescope across this entire reciprocal interval. The resulting fibre discrepancy is therefore exactly

```text
prime count on the reciprocal interval - Li mass of that interval,
```

weighted by the lower-scale Mertens value `M(d)`. The module reindexes the deterministic bulk, exact prime tail, and PNT error in these coordinates, proves the Li bulk cancels algebraically in the corrected all-plus identity, and pushes the reciprocal-interval error through the same square-wheel centering used by `H_{k,n}`.

These modules also prove the corresponding norm-transfer inequalities. They are exact interfaces, not prime-distribution estimates: no PNT error bound, Bombieri–Vinogradov estimate, large-sieve estimate, or RH-scale power saving is asserted. The centered PNT-corrected comb remains a separate analytic target from the reciprocal-interval prime-distribution error.

## Square-block track

The square-block side is centered on:

- square-prefix Mertens endpoints and interpolation;
- canonical largest-prime and cofactor decomposition;
- low and high height partition and low occupancy;
- squared-complex Fermat and cofactor geometry;
- square-root transport and dyadic compression;
- lifetime active sets, death shells, and survivor reduction;
- canonical gap and ancestry, signed Gram, and terminal quadratic closure;
- zero-cutoff ancestry and the square-root ancestry root and successor constructions.

Representative entry modules include `SquarePrefixMertensBridge`, `CanonicalHighSectorCore`, `CanonicalLowOccupancy`, `SquareBlockSurvivorBridge`, `LifetimeEndpointDecomposition`, `CanonicalGapAncestryQuadraticClosure`, `CanonicalGapAncestryZeroCutoff`, `SquareRootAncestryRoot`, and `SquareRootAncestrySuccessor`.

## Prime-wheel track

The prime-wheel side is centered on:

- deterministic Möbius reconstruction and primorial-wheel arithmetic;
- finite torus Fourier pairing;
- arithmetic and complete spectra;
- reduced additive conductors and conductor Gram decomposition;
- periodic raw response and coconductor subtraction;
- Möbius reindexing of raw and smooth conductor families;
- raw boundary pairing and expansion collapse;
- full-conductor uniform packets and the reindexed residual;
- classical Ramanujan identification;
- boundary and bulk divisor-residue reductions;
- Mertens transfer.

Representative entry modules include `PrimeWheelFiniteSystem`, `PrimeWheelMobiusRecovery`, `PrimeWheelFourierReduction`, `PrimeWheelConductorGram`, `PrimeWheelPeriodicRawBridge`, `PrimeWheelRawConductorMobiusReindex`, `PrimeWheelRawBoundaryMobiusPairing`, `PrimeWheelRawBoundaryExpansionCollapse`, `PrimeWheelFullConductorMobiusReindexedResidual`, `PrimeWheelRamanujanIdentification`, `PrimeWheelRamanujanBoundaryBulkReduction`, and `RamanujanDivisorBoundaryBulk`.

## Synthesis seam

The modules most directly joining the two descriptions include:

- `RHLean.Proof.PrimeSievePostSqrtGap`
- `RHLean.Proof.PrimeSieveSquareRootTransport`
- `RHLean.Analysis.PrimeSievePNTCentering`
- `RHLean.Analysis.PrimeSieveQuotientPNTError`
- `RHLean.Arithmetic.PrimorialWheelMinimalTorus`
- `RHLean.Arithmetic.PrimeProductLowerBound`
- `RHLean.Analysis.SquareWheelNesting`
- `RHLean.Analysis.SquareWheelQuadraticSampling`
- `RHLean.Analysis.SquareWheelZeroModeElimination`
- `RHLean.Analysis.SquareWheelQuantitativeBridge`
- `RHLean.Analysis.PrimeWheelRawConductorMobiusReindex`
- `RHLean.Analysis.PrimeWheelRawBoundaryMobiusPairing`
- `RHLean.Analysis.PrimeWheelRawBoundaryExpansionCollapse`
- `RHLean.Analysis.PrimeWheelFullConductorMobiusReindexedResidual`
- `RHLean.Analysis.PrimeWheelSmoothConductorMobiusReindex`
- `RHLean.Analysis.PrimeWheelRamanujanIdentification`
- `RHLean.Analysis.PrimeWheelRamanujanBoundaryReduction`
- `RHLean.Analysis.PrimeWheelRamanujanBoundaryBulkReduction`
- `RHLean.Analysis.RamanujanDivisorBoundary`
- `RHLean.Analysis.RamanujanDivisorBoundaryBulk`
- `RHLean.Analysis.PrimorialWheelMertensTransfer`

The prime-sieve modules give the elementary seam: fresh-prime parity produces the square-root transport variable exactly, Li-density centering exposes its deterministic prime bulk and exact prime-count discrepancy, and quotient-fibre reindexing identifies that discrepancy with classical prime-count-minus-Li errors on explicit reciprocal intervals. `SquareWheelQuantitativeBridge` remains the synthesis-facing quantitative endpoint of the later spectral bridge: it proves the factor-six modulus separation, the uniform square-sample ratio bound below `1/6`, defines `primorialExpansionReindexedNumerator`, and identifies `squareWheelNonzeroSampleResponse` with the expansion-reindexed numerator after the zero mode is removed. The PNT modules prove that the same `H_{k,n}` can simultaneously be read through the actual wheel centering as a complementary centered arithmetic term plus the centered reciprocal-interval prime-distribution error.

## Mertens and zeta bridge

The library also contains the forward analytic chain needed around the terminal Mertens and zeta statements:

- `RHLean.Analysis.DivisorUpperMobius`
- `RHLean.Analysis.MertensStepFunction`
- `RHLean.Analysis.MertensStepGrowth`
- `RHLean.Analysis.MertensPowerGrowth`
- `RHLean.Analysis.MertensEnergyRHForward`
- `RHLean.Analysis.MertensMellinLSeriesBridge`
- `RHLean.Analysis.MertensMellinContinuation`
- `RHLean.Analysis.MertensZetaIdentityContinuation`
- `RHLean.Proof.TerminalMertensForward`
- `RHLean.Proof.TerminalMertensReduction`
- `RHLean.Proof.MutablePNTClosure`
- `RHLean.Proof.RiemannHypothesisBridge`
- `RHLean.Proof.TerminalAxiomAudit`

## Modules added since the original 214-module inventory

The current manifest contains **34** modules beyond the original 214-module inventory. The previous revision reached 247 modules; this change adds the one new reciprocal-quotient PNT-error module while retaining the PNT-centering, elementary prime-sieve bridge, and earlier survivor additions.

Previously synchronized 21-module delta:

```text
RHLean.Analysis.DivisorUpperMobius
RHLean.Analysis.MertensEnergyRHForward
RHLean.Analysis.MertensMellinContinuation
RHLean.Analysis.MertensMellinLSeriesBridge
RHLean.Analysis.MertensPowerGrowth
RHLean.Analysis.MertensStepFunction
RHLean.Analysis.MertensStepGrowth
RHLean.Analysis.MertensZetaIdentityContinuation
RHLean.Analysis.PrimeWheelFullConductorMobiusReindexedResidual
RHLean.Analysis.PrimeWheelFullConductorUniformPacket
RHLean.Analysis.PrimeWheelRamanujanBoundaryBulkReduction
RHLean.Analysis.PrimeWheelRawBoundaryExpansionCollapse
RHLean.Analysis.PrimeWheelRawBoundaryMobiusPairing
RHLean.Analysis.PrimeWheelRawConductorMobiusReindex
RHLean.Analysis.PrimeWheelSmoothConductorMobiusReindex
RHLean.Analysis.RamanujanDivisorBoundaryBulk
RHLean.Analysis.SquareWheelQuantitativeBridge
RHLean.Proof.CanonicalGapAncestryZeroCutoff
RHLean.Proof.SquareRootAncestryRoot
RHLean.Proof.SquareRootAncestrySuccessor
RHLean.Proof.TerminalMertensForward
```

Subsequent 11-module synchronization:

```text
RHLean.Proof.SurvivorDyadicStaticCancellation
RHLean.Proof.SurvivorLargePrimeRootBoundary
RHLean.Proof.SurvivorPairEffectiveModulus
RHLean.Proof.SurvivorPrimeFaceFrontier
RHLean.Proof.SurvivorPrimeFaceRealization
RHLean.Proof.SurvivorResidueCollisionReindex
RHLean.Proof.SurvivorResidueCovariance
RHLean.Proof.SurvivorResidueCovarianceCriterion
RHLean.Proof.SurvivorResiduePrimeToggle
RHLean.Proof.PrimeSievePostSqrtGap
RHLean.Proof.PrimeSieveSquareRootTransport
```

PNT synchronization:

```text
RHLean.Analysis.PrimeSievePNTCentering
RHLean.Analysis.PrimeSieveQuotientPNTError
```

## Scope policy

For synthesis, dependency completeness is more important than keeping the tree small. Modules that look auxiliary, experimental, geometric, or intermediate are therefore retained whenever they are part of the audited root import manifest.

The invariant is simple: every internal import in `RHLean.lean` must resolve to a corresponding file under `RHLean/`. When the manifest gains an imported module, the module and the manifest change together, so the formal statements never silently depend on a file that is not present here.
