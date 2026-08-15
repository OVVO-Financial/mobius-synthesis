# Möbius Synthesis

**Möbius Synthesis** is a standalone research-status repository for the square-block and prime-wheel Möbius program. It joins the two coordinate systems, carries the native Selberg--Erdős prime number theorem, and records the strongest currently machine-checked quantitative PNT contraction without overstating the remaining RH-scale step.

`RHLean.lean` is the authoritative source inventory and currently imports **374 Lean modules**. `MODULES.md` maps the source layers, `SEAMS.md` records their exact interfaces, and `CURRENT_PROOF_ROUTE.md` states what is proved, what remains open, and which mechanisms are currently live.

## Current research status

There are four distinct machine-checked levels, and they must not be conflated.

### 1. The ordinary prime number theorem is proved unconditionally

The repository contains an elementary Selberg--Erdős proof ending at

```text
RHLean.Analysis.nativePNTSquarePrefixPrimeNumberTheorem
  : Tendsto
      (fun N => (Nat.primeCounting N : ℝ) * Real.log N / N)
      atTop (𝓝 1)
```

The proof is built inside the reciprocal-fibre Möbius architecture. It does not import a zero-free region, Perron formula, Tauberian theorem, or an external PNT theorem.

### 2. A generalized affine PNT bound is proved and contracts strictly

The quantitative layer works with

```text
nativePNTError N = nativePsi N - N.
```

At slope `alpha`, `nativePNTHasAffineEnvelope alpha` means that some nonnegative intercept `D` satisfies

```math
|\psi(N)-N| \le \alpha N + D
```

for every `N`.

For

```math
0 < \alpha \le \frac32,
```

Lean proves that an affine envelope at slope `alpha` implies one at

```math
\alpha_{new}
  = \alpha - \frac{\alpha^3}{178200000}.
```

The key declarations are

```text
RHLean.Analysis.nativePNTSquarePrefixHasAffineEnvelope_lowSlope_cubic_step
RHLean.Analysis.nativePNTSquarePrefixLowSlope_affineEnvelope_strictly_tighter.
```

The low-slope cubic coefficient is

```text
1 / 178200000
```

and is exactly `32/5` times the earlier fully rederived square-prefix coefficient `1 / 1140480000`. This is a genuine contraction of an already-proved generalized PNT error bound. It is not an RH-scale power bound.

### 3. The square-root conversion theorems are already formalized

The moving-cutoff route defines `NativePNTQuadraticTailScaleLaw K`: for each small target slope `eta`, a true tail begins at some cutoff `M` satisfying

```math
M\eta^2 \le K.
```

From that law Lean proves

```math
|\psi(N)-N| \le \sqrt{KN}
```

through

```text
RHLean.Analysis.nativePNTError_abs_le_sqrt_of_quadraticTailScaleLaw
RHLean.Analysis.nativePNTError_abs_le_sqrt_of_stateDependentCubicGain.
```

The affine-intercept route defines `NativePNTReciprocalInterceptLaw K`. From

```math
D(\alpha) \le \frac K\alpha
```

Lean proves

```math
|\psi(N)-N| \le 2\sqrt{KN}
```

through

```text
RHLean.Analysis.nativePNTError_abs_le_two_sqrt_of_reciprocalInterceptLaw.
```

Thus the missing result is not a square-root optimization lemma. The conversion machinery is already present.

### 4. The missing theorem is RH-compatible physical scale control

What is **not** proved is the required cutoff law itself. In particular, the repository does not yet prove unconditionally that repeated architecture-native contractions reach target slope `eta` with terminal physical cutoff

```math
M(\eta)=O(\eta^{-2}),
```

nor the stronger reciprocal cutoff control sufficient for the affine-intercept route.

This is the present quantitative bottleneck.

`RHLean.Analysis.NativePNTEvolvingTailObstruction` proves that the canonical sign-blind evolving-tail state carries an unavoidable `N log N`-scale floor. The active route therefore keeps the second Selberg recurrence signed before taking norms.

## Signed second Selberg architecture

`RHLean.Analysis.NativePNTSignedSecondSelberg` opens the second Selberg layer before absolute values. Its exact kernel is

```math
K_2(n)
 = (\Lambda * \Lambda)(n)-\Lambda(n)\log n
 = \Lambda_2(n)-2\Lambda(n)\log n.
```

The exact recurrence exposes

```text
E(N) log(N)^2
  = signed Selberg remainder * log(N)
    - Lambda signed remainder mass
    + dyadic Lambda_2 cell mass
    + top boundary mass
    - 2 * Lambda-log signed error mass
    - floor-log signed defect mass.
```

No current-scale positive remainder is inserted and no `Lambda_2` contribution is replaced termwise by its absolute value.

The supporting modules

```text
NativePNTSignedLogSquarePrimeCells
NativePNTSignedLogSquarePositiveDyadicKernel
NativePNTSignedLogSquareDyadicCell
NativePNTSignedLogSquareSquareStage
```

place the log-square mass on complete-square cells and identify the exact dyadic ownership used by the signed recurrence.

## Exact prime-wheel frontier at square-root scale

`RHLean.Analysis.NativePNTSignedSecondSelbergWheelFrontier` classifies the actual unresolved partial-wheel sites under

```math
N < 2y^2.
```

Every nonzero frontier site is exactly one of two signed faces:

```text
prime square q^2:
  K_2(q^2) = -(log q)^2

distinct prime product q r:
  K_2(qr) = 2 log q log r.
```

`RHLean.Analysis.NativePNTSignedSecondSelbergFrontierCharge` proves that every such site has reciprocal quotient `N / n = 1`, hence

```text
nativePNTSignedSecondSelbergWheelFrontierErrorMass y N
  = - nativePNTSignedSecondSelbergWheelFrontierCharge y N.
```

This is an exact signed frontier statement. No positivity is asserted for the total frontier charge.

## Two live quantitative fronts

### A. Canonical square-wheel nonzero response

For synchronized primorial blocks and complete-square samples,

```math
R_k(X_n)=H_{k,n}+\rho_{k,n}R_k(U_k),
\qquad 0\le\rho_{k,n}<\frac16.
```

The zero mode is eliminated exactly, and the canonical direct RH target remains

```math
|H_{k,n}| \ll_\varepsilon (X_n+1)^{1/2+\varepsilon}.
```

That estimate is **not proved**. `boundary/frontier.json` therefore remains at `exact_reduction`.

The exact reciprocal-interval coordinate is

```math
H_{k,n}
  = C_{k,n}^{PNT}-2E_{k,n}^{rec},
```

where the second term is a centered Mertens-weighted family of prime-count-minus-Li discrepancies on explicit reciprocal intervals.

### B. Generalized-PNT contraction with controlled physical scale

The newer quantitative route starts from the proved affine PNT envelope, iterates a state-dependent cubic contraction, records the physical cutoff at every step, and asks for an RH-compatible terminal scale. The formal square-root conversion is already present. The live arithmetic task is to prove the scale law from the signed square-block and prime-wheel structure.

```text
proved affine PNT envelope
  -> proved strict cubic slope contraction
  -> OPEN: architecture-native cutoff law
  -> proved conditional sqrt(N) Chebyshev bridge.
```

The signed second-Selberg and wheel-frontier modules target the open middle arrow.

## Historical exact synthesis seam

The exact square-wheel seam remains part of the current architecture.

`RHLean.Proof.PrimeSievePostSqrtGap` proves, under `sqrt x < y`,

```text
M_y^+(x) - M(x)
  = 2 * sum_{y < q <= x, q prime} M(floor(x/q)).
```

`RHLean.Proof.PrimeSieveSquareRootTransport` realizes that identity at complete square endpoints in square-block smooth and transport variables.

`RHLean.Analysis.PrimeSievePNTCentering` and `PrimeSieveQuotientPNTError` reindex the prime error by

```text
d = floor(x/q),
```

with exact reciprocal interval

```text
max(y, floor(x/(d+1))) < q <= floor(x/d).
```

These are exact finite identities and do not independently supply the missing RH-scale cancellation.

## What is proved versus open

Machine checked:

- exact square-block and prime-wheel Möbius architectures;
- exact square-wheel zero-mode elimination and uniform `1/6` feedback contraction;
- exact reciprocal-interval PNT centering of the canonical nonzero response;
- unconditional native Selberg--Erdős prime number theorem;
- generalized affine PNT envelopes and iteration infrastructure;
- conditional square-root conversion from quadratic cutoff growth;
- conditional square-root conversion from reciprocal affine-intercept growth;
- a formal obstruction to the canonical absolute evolving-tail state;
- exact signed second-Selberg recurrence on square-stage cells;
- exact signed prime-square and mixed-prime wheel-frontier classification;
- exact wheel-frontier error-mass collapse to the negative frontier charge;
- strict low-slope cubic contraction with coefficient `1 / 178200000`.

Still open:

- the architecture-native cutoff law needed to keep repeated contraction at quadratic reciprocal physical scale;
- the stronger reciprocal cutoff or intercept law;
- the canonical `H_{k,n}` bound at exponent `1/2 + epsilon`;
- an unconditional RH-scale Mertens or Chebyshev power bound;
- the Riemann Hypothesis.

## Direct current-status modules

```text
RHLean.Analysis.NativePNTCubicContractionInequality
RHLean.Analysis.PrimeSieveStateDependentSelbergScalePersistence
RHLean.Analysis.NativePNTTailAffineEnvelope
RHLean.Analysis.NativePNTTailOptimalIntercept
RHLean.Analysis.NativePNTReciprocalInterceptPowerBound
RHLean.Analysis.NativePNTEvolvingTailObstruction
RHLean.Analysis.NativePNTSignedLocalSurplus
RHLean.Analysis.NativePNTSignedLogSquarePrimeCells
RHLean.Analysis.NativePNTSignedLogSquarePositiveDyadicKernel
RHLean.Analysis.NativePNTSignedLogSquareDyadicCell
RHLean.Analysis.NativePNTSignedLogSquareSquareStage
RHLean.Analysis.NativePNTSignedSecondSelberg
RHLean.Analysis.NativePNTSignedWheelRemainder
RHLean.Analysis.NativePNTSignedSecondSelbergWheelFrontier
RHLean.Analysis.NativePNTSignedSecondSelbergFrontierCharge
```

The exact synthesis-facing modules remain important as well:

```text
RHLean.Proof.PrimeSievePostSqrtGap
RHLean.Proof.PrimeSieveSquareRootTransport
RHLean.Analysis.PrimeSievePNTCentering
RHLean.Analysis.PrimeSieveQuotientPNTError
RHLean.Analysis.SquareWheelZeroModeElimination
RHLean.Analysis.SquareWheelQuantitativeBridge
RHLean.Analysis.PrimorialWheelMertensTransfer
RHLean.Analysis.MertensMellinContinuation
RHLean.Analysis.MertensZetaIdentityContinuation
RHLean.Proof.RiemannHypothesisBridge
```

## Repository layout

- `README.md` — current research status;
- `CURRENT_PROOF_ROUTE.md` — canonical live proof route and bottleneck;
- `MODULES.md` — source-layer map;
- `SEAMS.md` — exact interfaces between square-block, wheel, PNT, and scale layers;
- `RHLean.lean` — authoritative 374-module import manifest;
- `RHLean/` — Lean source tree;
- `boundary/` — canonical direct-H frontier, cross-track synthesis ledger, and closed-lane record;
- `.github/` and `scripts/` — CI, assumption audit, and research-scope gate;
- `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json` — pinned Lean project metadata.

## Verification

From the repository root:

```bash
bash scripts/local_ci.sh
```

The local and hosted baseline audits build `RHLean` with warnings fatal, audit unfinished proofs and project-local axioms, and print axiom dependencies for the headline synthesis theorem, the native PNT endpoint, the strengthened low-slope affine contraction, and the conditional square-root scale bridge.

## Status convention

- **Machine checked** means the statement is represented by a Lean theorem or definition in this repository.
- **Exact reduction** means finite algebra, reindexing, centering, or transfer with no unproved asymptotic estimate hidden inside it.
- **Conditional bound-changing theorem** means Lean proves the implication from an explicit scale or intercept law; it does not mean that law has been established.
- **Open analytic target** means the required estimate or scale law is unresolved.
- Numerical experiments are diagnostic evidence only.

## License

Licensed under the Apache License, Version 2.0; see `LICENSE`.
