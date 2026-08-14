# Möbius Synthesis seams

This note records the exact interfaces joining the square-block, prime-wheel, native PNT, and physical-scale layers.

The project has two quantitative descriptions that must remain distinct:

- a direct square-wheel target `H_{k,n}` whose RH-scale exponent remains open; and
- a proved generalized affine PNT contraction whose missing input is an RH-compatible physical cutoff law.

These are related quantitative fronts, not competing definitions of the same theorem.

## 1. Elementary prime-sieve to square-root transport seam

```text
RHLean.Proof.PrimeSievePostSqrtGap
RHLean.Proof.PrimeSieveSquareRootTransport
```

Under `sqrt x < y`, the first proves

```text
M_y^+(x) - M(x)
  = 2 * sum_{y < q <= x, q prime} M(floor(x/q)).
```

The second specializes to `x = R^2 - 1`, `y = R`, and identifies the pre-large-prime state with square-block smooth and transport variables. This is exact finite algebra.

## 2. PNT centering to reciprocal intervals

```text
RHLean.Analysis.PrimeSievePNTCentering
RHLean.Analysis.PrimeSieveQuotientPNTError
```

use the singleton logarithmic-integral density

```text
density(q) = Li(q) - Li(q-1)
```

and reindex by

```text
d = floor(x/q).
```

For positive `d`, the exact quotient fibre is

```text
max(y, floor(x/(d+1))) < q <= floor(x/d).
```

The Li masses telescope on that interval, so the exact prime error becomes a finite Mertens-weighted family of prime-count-minus-Li discrepancies.

After square-wheel zero-mode centering,

```math
H_{k,n}=C_{k,n}^{PNT}-2E_{k,n}^{rec}.
```

The identity is exact. It does not justify bounding the two terms independently and discarding their relative sign.

## 3. Square-wheel zero-mode seam

```text
RHLean.Analysis.SquareWheelQuadraticSampling
RHLean.Analysis.SquareWheelZeroModeElimination
RHLean.Analysis.SquareWheelQuantitativeBridge
```

prove

```math
R_k(X_n)=H_{k,n}+\rho_{k,n}R_k(U_k)
```

and, on synchronized blocks,

```math
0\le\rho_{k,n}<\frac16.
```

Thus the zero mode is already uniformly contractive. The unresolved direct quantitative target is the size of `H_{k,n}`.

## 4. Native PNT to Möbius endpoint seam

The square-prefix Selberg--Erdős chain proves the ordinary prime number theorem unconditionally:

```text
RHLean.Analysis.nativePNTSquarePrefixPrimeNumberTheorem.
```

`RHLean.Analysis.NativePNTAxer` connects the same arithmetic architecture to the Mertens summatory function. The native PNT layer also carries a quantitative affine-envelope state, so this seam is not purely qualitative.

## 5. Affine PNT envelope seam

`RHLean.Analysis.NativePNTTailAffineEnvelope` proves that a true tail estimate beginning at physical cutoff `M`,

```math
|\psi(N)-N|\le\alpha N
\qquad (N\ge M),
```

globalizes to an affine envelope with finite-prefix intercept

```math
D=(\log 4+3)M.
```

`RHLean.Analysis.NativePNTOptimalInterceptCore` and `NativePNTTailOptimalIntercept` connect this explicit envelope to the least admissible intercept.

## 6. Reciprocal intercept to square-root error seam

`RHLean.Analysis.NativePNTReciprocalInterceptPowerBound` defines

```text
NativePNTReciprocalInterceptLaw K
NativePNTReciprocalTailCutoffLaw K.
```

From an affine envelope with intercept `K / alpha`,

```text
nativePNTError_abs_le_two_sqrt_of_reciprocalInterceptLaw
```

proves

```math
|\psi(N)-N|\le2\sqrt{KN}.
```

The reciprocal law itself remains open.

## 7. State-dependent cubic contraction to quadratic cutoff seam

`RHLean.Analysis.PrimeSieveStateDependentSelbergScalePersistence` records the physical cutoff at every contraction step.

Its target law

```text
NativePNTQuadraticTailScaleLaw K
```

requires, for every small target slope `eta`, a cutoff `M` satisfying

```math
M\eta^2\le K
```

and a genuine tail estimate of slope `eta` beyond `M`.

Then

```text
nativePNTError_abs_le_sqrt_of_quadraticTailScaleLaw
```

proves

```math
|\psi(N)-N|\le\sqrt{KN}.
```

The wrapper

```text
nativePNTError_abs_le_sqrt_of_stateDependentCubicGain
```

shows that an explicit cubic scale chain with the same terminal-scale property is sufficient.

## 8. Formal obstruction seam

`RHLean.Analysis.NativePNTEvolvingTailObstruction` applies to the canonical absolute evolving-tail state.

It proves that the first absolute remainder contains a linear factorial floor, the second contains an `N log N`-scale floor, and the full evolving cost retains that floor up to the explicitly bounded negative tail compensation.

At fixed polynomial physical scale in the reciprocal slope, this is incompatible with the desired cubic gain as the slope tends to zero. The conclusion is not that cubic contraction is impossible; the repository already proves cubic contraction. The conclusion is that this particular sign-blind state cannot deliver the required scale law.

## 9. Log-square cells to signed second Selberg seam

```text
RHLean.Analysis.NativePNTSignedLogSquarePrimeCells
RHLean.Analysis.NativePNTSignedLogSquarePositiveDyadicKernel
RHLean.Analysis.NativePNTSignedLogSquareDyadicCell
RHLean.Analysis.NativePNTSignedLogSquareSquareStage
```

reindex `Lambda_2 = mu * log^2` into finite Möbius log-square fibres, expose fresh-prime endpoint atoms, and place the surviving odd-kernel mass on exact complete-square activity bands.

`RHLean.Analysis.NativePNTSignedSecondSelberg` then proves

```math
K_2(n)
=(\Lambda*\Lambda)(n)-\Lambda(n)\log n
=\Lambda_2(n)-2\Lambda(n)\log n
```

and the exact recurrence

```text
E(N) log(N)^2
  = signed Selberg remainder * log(N)
    - Lambda signed remainder mass
    + dyadic Lambda_2 cell mass
    + top boundary mass
    - 2 * Lambda-log signed error mass
    - floor-log signed defect mass.
```

This seam preserves cancellation until the last possible stage.

## 10. Partial prime wheel to signed second-kernel frontier seam

`RHLean.Arithmetic.PrimeWheelPartialErrorThreshold` localizes the unresolved partial-wheel error below twice the square of the wheel cutoff.

`RHLean.Analysis.NativePNTSignedSecondSelbergWheelFrontier` evaluates the signed second-Selberg kernel on that support. Under

```math
N<2y^2,
```

every frontier site is exactly one of:

```text
q^2, q prime, y < q:
  K_2(q^2) = -(log q)^2

q r, q and r distinct primes, y < q, y < r:
  K_2(qr) = 2 log q log r.
```

No third face occurs.

## 11. Frontier charge to PNT error seam

`RHLean.Analysis.NativePNTSignedSecondSelbergFrontierCharge` defines the unresolved frontier finset and its signed raw charge.

The same square-root geometry proves, for every frontier site,

```text
N / n = 1.
```

Since `nativePNTError 1 = -1`,

```text
nativePNTSignedSecondSelbergWheelFrontierErrorMass_eq_neg_charge
```

gives

```text
frontier error mass = - frontier charge.
```

No termwise absolute value and no auxiliary remainder enters this seam.

## 12. Good-mass density to strengthened affine contraction seam

The fully rederived square-prefix good-mass theorem supplies the density coefficient

```text
beta^2 / 6600000.
```

In the low-slope regime `0 < alpha <= 3/2`, choosing

```math
\beta=\frac{2\alpha}{3}
```

gives

```text
nativePNTSquarePrefixLowSlopeCubicConstant = 1 / 178200000.
```

Thus

```text
nativePNTSquarePrefixHasAffineEnvelope_lowSlope_cubic_step
```

proves

```math
\alpha\mapsto\alpha-\frac{\alpha^3}{178200000}.
```

`nativePNTSquarePrefixLowSlope_affineEnvelope_strictly_tighter` certifies that this is strictly stronger than the previous square-prefix step.

## 13. What is still missing

The following implications are formalized:

```text
quadratic physical cutoff law
  -> sqrt(N) Chebyshev bound

reciprocal intercept law
  -> 2 sqrt(N) Chebyshev bound.
```

The missing implication is

```text
signed square-block and wheel-frontier arithmetic
  -> RH-compatible physical cutoff law.
```

The direct route remains

```text
signed square-wheel H_{k,n}
  -> RH-scale H bound
  -> RH-scale Mertens transfer,
```

with the first quantitative arrow still open.

## 14. Build completeness

`RHLean.lean` imports 366 modules and is the authoritative exhaustive manifest. The baseline audit builds the full manifest and checks the axiom dependencies of the synthesis theorem, the native PNT endpoint, the strengthened affine contraction, and the conditional square-root scale bridge.
