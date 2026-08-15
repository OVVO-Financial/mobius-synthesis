# Möbius Synthesis — Lean source map

This repository contains the complete import-audited `RHLean` library used by the current Möbius Synthesis research snapshot.

`RHLean.lean` is the authoritative inventory. It imports **374 Lean modules**, and every imported `RHLean.*` module resolves under `RHLean/`.

This file groups the source by research function. For the exhaustive file-by-file list, read `RHLean.lean` itself.

## 1. Square-block architecture

The square-block layer contains complete-square, cofactor, lifetime, death-shell, survivor, ancestry, and signed Gram geometry. Representative modules include:

```text
RHLean.Analysis.ConcreteSquarePrefixGeometry
RHLean.Analysis.SquarePrefixHeightPartition
RHLean.Analysis.SquarePrefixMertensBridge
RHLean.Analysis.SquareBlockDeathProcess
RHLean.Analysis.SquareBlockSurvivorBridge
RHLean.Analysis.SquareRootMatchedTransport
RHLean.Analysis.SquareRootPositiveSmoothCollapse
RHLean.Analysis.SquareRootTransportRealization
RHLean.Proof.LifetimeActiveSet
RHLean.Proof.LifetimeEndpointDecomposition
RHLean.Proof.LifetimeEndpointDiscrepancyAttack
RHLean.Proof.LifetimeOverlapGramCriterion
RHLean.Proof.DeathProcessArithmetic
RHLean.Proof.DeathProcessShellIdentity
RHLean.Proof.SurvivorFarUpperRigidity
RHLean.Proof.CanonicalGapAncestryQuadraticClosure
RHLean.Proof.CanonicalGapAncestryZeroCutoff
RHLean.Proof.SquareRootAncestryRoot
RHLean.Proof.SquareRootAncestrySuccessor
```

## 2. Prime-wheel architecture

The prime-wheel layer contains finite Möbius recovery, partial-wheel error support, torus and conductor decompositions, Ramanujan reductions, finite-wheel quantitative statements, and exact boundary identities. Representative modules include:

```text
RHLean.Arithmetic.PrimeWheelFiniteSystem
RHLean.Arithmetic.PrimeWheelMobiusRecovery
RHLean.Arithmetic.PrimeWheelPartialError
RHLean.Arithmetic.PrimeWheelPartialErrorThreshold
RHLean.Arithmetic.PrimorialReciprocalMobiusFactorization
RHLean.Arithmetic.PrimorialTruncatedWheelBoundary
RHLean.Analysis.FiniteWheelRestrictedFloor
RHLean.Analysis.FiniteWheelReciprocalMertensImprovement
RHLean.Analysis.PrimeWheelFourierReduction
RHLean.Analysis.PrimeWheelConductorGram
RHLean.Analysis.PrimeWheelPeriodicRawBridge
RHLean.Analysis.PrimeWheelRawConductorMobiusReindex
RHLean.Analysis.PrimeWheelRawBoundaryMobiusPairing
RHLean.Analysis.PrimeWheelRawBoundaryExpansionCollapse
RHLean.Analysis.PrimeWheelFullConductorMobiusReindexedResidual
RHLean.Analysis.PrimeWheelRamanujanIdentification
RHLean.Analysis.PrimeWheelRamanujanBoundaryBulkReduction
RHLean.Analysis.RamanujanDivisorBoundaryBulk
```

## 3. Square-wheel synthesis seam

The canonical cross-track seam includes:

```text
RHLean.Proof.PrimeSievePostSqrtGap
RHLean.Proof.PrimeSieveSquareRootTransport
RHLean.Analysis.PrimeSievePNTCentering
RHLean.Analysis.PrimeSieveQuotientPNTError
RHLean.Analysis.SquareWheelNesting
RHLean.Analysis.SquareWheelQuadraticSampling
RHLean.Analysis.SquareWheelZeroModeElimination
RHLean.Analysis.SquareWheelQuantitativeBridge
RHLean.Analysis.PrimorialWheelMertensTransfer
```

These modules identify the canonical nonzero response `H_{k,n}`, eliminate its zero-mode feedback, realize the post-square-root prime-sieve state in square-block coordinates, and express the prime-distribution component as Mertens-weighted discrepancies over exact reciprocal intervals.

The direct quantitative endpoint remains the open `NonzeroResponseRHScale` predicate in `RHLean.Analysis.MobiusSynthesisBoundary`.

## 4. Native Selberg--Erdős prime number theorem

The ordinary prime number theorem is proved by the native reciprocal-fibre route. Main layers include:

```text
RHLean.Analysis.NativePNTLogSums
RHLean.Analysis.NativePNTChebyshev
RHLean.Analysis.NativePNTMertens
RHLean.Analysis.NativePNTSelberg
RHLean.Analysis.NativePNTMobiusMoments
RHLean.Analysis.NativePNTMobiusSecondMoment
RHLean.Analysis.NativePNTSummatorySelberg
RHLean.Analysis.NativePNTErrorMass
RHLean.Analysis.NativePNTErdosContraction
RHLean.Analysis.NativePNTSquarePrefixMobiusError
RHLean.Analysis.NativePNTSquarePrefixGoodMass
RHLean.Analysis.NativePNTSquarePrefixGoodMassRate
RHLean.Analysis.NativePNTSquarePrefixCompensated
RHLean.Analysis.NativePNTSquarePrefixContraction
RHLean.Analysis.NativePNTSquarePrefixCubic
RHLean.Analysis.NativePNTSquarePrefixPNT
RHLean.Analysis.NativePNTSquarePrefixTransfer
RHLean.Analysis.NativePNTAxer
RHLean.Analysis.NativePNTTransfer
RHLean.Analysis.NativePNTQuantitativeStatements
```

The endpoint is

```text
RHLean.Analysis.nativePNTSquarePrefixPrimeNumberTheorem.
```

## 5. Generalized PNT affine-envelope layer

The quantitative layer separates slope contraction from intercept growth:

```text
RHLean.Analysis.NativePNTBoundContraction
RHLean.Analysis.NativePNTLowSlopeContraction
RHLean.Analysis.NativePNTCubicContractionInequality
RHLean.Analysis.NativePNTQuadraticBudget
RHLean.Analysis.NativePNTReciprocalSquareCore
RHLean.Analysis.NativePNTInterceptOnsetCore
RHLean.Analysis.NativePNTInterceptOnset
RHLean.Analysis.NativePNTInterceptExplicitStep
RHLean.Analysis.NativePNTInterceptStep
RHLean.Analysis.NativePNTInterceptPropagation
RHLean.Analysis.NativePNTInterceptAbsorption
RHLean.Analysis.NativePNTInterceptRecurrence
RHLean.Analysis.NativePNTInterceptTail
RHLean.Analysis.NativePNTInterceptGrowth
RHLean.Analysis.NativePNTInterceptMildUpdates
RHLean.Analysis.NativePNTOptimalInterceptCore
RHLean.Analysis.NativePNTOptimalInterceptStep
RHLean.Analysis.NativePNTOptimalInterceptGrowth
RHLean.Analysis.NativePNTTailAffineEnvelope
RHLean.Analysis.NativePNTTailOptimalIntercept
RHLean.Analysis.NativePNTReciprocalInterceptPowerBound
```

The key bound-changing theorem

```text
nativePNTError_abs_le_two_sqrt_of_reciprocalInterceptLaw
```

turns `D(alpha) <= K / alpha` into a `2 * sqrt(K*N)` Chebyshev error bound.

## 6. Moving-cutoff and state-dependent contraction layer

The physical onset of a contracted tail is recorded explicitly in:

```text
RHLean.Analysis.NativePNTEvolvingRemainder
RHLean.Analysis.NativePNTEvolvingTailState
RHLean.Analysis.NativePNTEvolvingTailStep
RHLean.Analysis.NativePNTEvolvingTailCompensation
RHLean.Analysis.NativePNTEvolvingTailObstruction
RHLean.Analysis.NativePNTRemainderProfileCore
RHLean.Analysis.NativePNTRemainderProfileCompose
RHLean.Analysis.NativePNTSquarePrefixQuadraticBudget
RHLean.Analysis.NativePNTSquarePrefixSmallQuotient
RHLean.Analysis.NativePNTSquarePrefixTailGeometry
RHLean.Analysis.NativePNTSquarePrefixTailErrorPartition
RHLean.Analysis.NativePNTSquarePrefixTailMass
RHLean.Analysis.NativePNTSquarePrefixTailIntervalAbel
RHLean.Analysis.NativePNTSquarePrefixTailIntervalUpper
RHLean.Analysis.NativePNTSquarePrefixTailLogInterval
RHLean.Analysis.NativePNTSquarePrefixTailGood
RHLean.Analysis.NativePNTSquarePrefixTailBad
RHLean.Analysis.NativePNTSquarePrefixTailGoodRetention
RHLean.Analysis.NativePNTSquarePrefixTailReciprocalBound
RHLean.Analysis.NativePNTSquarePrefixTailCompensation
RHLean.Analysis.NativePNTSquarePrefixTailStep
RHLean.Analysis.NativePNTSquarePrefixTailContraction
```

The state-dependent Selberg family is:

```text
RHLean.Analysis.PrimeSieveStateDependentSelbergPositiveGainCore
RHLean.Analysis.PrimeSieveStateDependentSelbergPositiveGainTrajectoryCore
RHLean.Analysis.PrimeSieveStateDependentSelbergPositiveGainCubicBudget
RHLean.Analysis.PrimeSieveStateDependentSelbergPositiveGainClosure
RHLean.Analysis.PrimeSieveStateDependentSelbergPositiveGain
RHLean.Analysis.PrimeSieveStateDependentSelbergScalePersistence
```

`PrimeSieveStateDependentSelbergScalePersistence` defines `NativePNTQuadraticTailScaleLaw` and proves

```text
nativePNTError_abs_le_sqrt_of_quadraticTailScaleLaw
nativePNTError_abs_le_sqrt_of_stateDependentCubicGain.
```

These are conditional square-root conversion theorems. The required quadratic physical cutoff law itself remains open.

## 7. Formal obstruction to the sign-blind moving-tail state

`RHLean.Analysis.NativePNTEvolvingTailObstruction` proves that the canonical absolute first remainder contains a linear factorial floor and the absolute second remainder contains an `N log N`-scale floor. Its theorem

```text
nativePNTEvolvingTailCost_ge_canonical_obstruction
```

applies to the whole evolving cost and rules out that specific sign-blind state as a mechanism for the required cubic gain at fixed polynomial physical scale as the slope tends to zero.

## 8. Dyadic and reciprocal signed-packet investigations

The many-fibre and dyadic packet layers include:

```text
RHLean.Analysis.PrimeSieveBaseEightShallowAttack
RHLean.Analysis.PrimeSieveClassicalDyadicVariation
RHLean.Analysis.PrimeSieveClassicalMobiusChord
RHLean.Analysis.PrimeSieveDyadicAnalyticBridge
RHLean.Analysis.PrimeSieveDyadicChordEnergy
RHLean.Analysis.PrimeSieveDyadicCoherentAbel
RHLean.Analysis.PrimeSieveDyadicPacketDissipation
RHLean.Analysis.PrimeSieveDyadicPacketEnvelopeStep
RHLean.Analysis.PrimeSieveDyadicPacketReverseCarleson
RHLean.Analysis.PrimeSieveDyadicPacketShallowDeep
RHLean.Analysis.PrimeSieveDyadicSignedPackets
RHLean.Analysis.PrimeSieveReciprocalChildVariance
RHLean.Analysis.PrimeSievePNTGoodMassAmplification
RHLean.Analysis.PrimeSievePNTGoodMassChargeAttack
RHLean.Analysis.PrimeSievePNTResidualEnvelope
RHLean.Analysis.PRoughSquarePrefixEnergy
RHLean.Analysis.PrimeAveragedCubeEnergy
RHLean.Analysis.WheelRoughSquarePrefixEnergy
```

These modules retain exact decompositions, tested mechanisms, and structural obstructions. `boundary/dead_lanes.json` records the no-go conclusions.

## 9. Signed local surplus and second Selberg layer

The signed attack begins with

```text
RHLean.Analysis.NativePNTSignedLocalSurplus
RHLean.Analysis.NativePNTSignedWheelRemainder
```

followed by the log-square cell layer

```text
RHLean.Analysis.NativePNTSignedLogSquarePrimeCells
RHLean.Analysis.NativePNTSignedLogSquarePositiveDyadicKernel
RHLean.Analysis.NativePNTSignedLogSquareDyadicCell
RHLean.Analysis.NativePNTSignedLogSquareSquareStage
```

and the exact second-Selberg layer

```text
RHLean.Analysis.NativePNTSignedSecondSelberg
RHLean.Analysis.NativePNTSignedSecondSelbergWheelFrontier
RHLean.Analysis.NativePNTSignedSecondSelbergFrontierCharge
```

`NativePNTSignedSecondSelberg` proves the signed recurrence before a current-scale absolute remainder is inserted. `NativePNTSignedSecondSelbergWheelFrontier` classifies the unresolved partial-wheel support into signed prime-square and distinct-prime-pair faces. `NativePNTSignedSecondSelbergFrontierCharge` proves the square-root quotient collapse and contains the strengthened low-slope affine-envelope contraction.

## 10. Current quantitative headline

```text
nativePNTSquarePrefixLowSlopeCubicConstant = 1 / 178200000.
```

For `0 < alpha <= 3/2`,

```text
nativePNTSquarePrefixHasAffineEnvelope_lowSlope_cubic_step
```

advances any proved affine envelope at slope `alpha` to one at

```math
alpha - alpha^3 / 178200000.
```

`nativePNTSquarePrefixLowSlope_affineEnvelope_strictly_tighter` also certifies that this update is strictly stronger than the previous square-prefix cubic step.

This is the current proved generalized-PNT contraction. It does **not** prove the required physical cutoff law and therefore does not by itself yield an unconditional square-root error bound.

## 11. Mertens and zeta transfer layer

```text
RHLean.Analysis.DivisorUpperMobius
RHLean.Analysis.MertensStepFunction
RHLean.Analysis.MertensStepGrowth
RHLean.Analysis.MertensPowerGrowth
RHLean.Analysis.MertensEnergyRHForward
RHLean.Analysis.MertensMellinLSeriesBridge
RHLean.Analysis.MertensMellinContinuation
RHLean.Analysis.MertensZetaIdentityContinuation
RHLean.Proof.TerminalMertensForward
RHLean.Proof.TerminalMertensReduction
RHLean.Proof.RiemannHypothesisBridge
RHLean.Proof.TerminalAxiomAudit
```

These modules formalize the forward analytic transfer once an appropriate RH-scale estimate is available.

## 12. Status summary

```text
ordinary PNT                                PROVED
explicit generalized affine PNT bound       PROVED
strict low-slope cubic contraction           PROVED
quadratic-cutoff -> sqrt(N) bridge           PROVED CONDITIONALLY
reciprocal-intercept -> 2 sqrt(N) bridge     PROVED CONDITIONALLY
absolute moving-tail obstruction             PROVED
signed second Selberg recurrence              PROVED EXACTLY
signed square-root wheel frontier             PROVED EXACTLY
RH-compatible physical cutoff law             OPEN
canonical H_{k,n} exponent 1/2+epsilon        OPEN
RH                                             OPEN
```

The authoritative exhaustive module inventory is `RHLean.lean`.
