# Current Möbius Synthesis proof route

**Status:** canonical wording for the active research route.

The direct RH-scale target for the square-wheel nonzero response remains open. In parallel, the repository now has a proved generalized affine PNT contraction together with formal square-root conversion theorems. The current bottleneck is therefore precise: **prove that the architecture realizes repeated contraction at RH-compatible physical scale.**

## 1. Preserve the square-block and prime-wheel coordinates

The architecture has two descriptions of the same Möbius cancellation problem.

The square-block side organizes complete-square endpoints

```math
X_t=(t+1)^2-1,
```

reciprocal fibres, smooth and transport terms, good shells, and square-stage Selberg cells.

The prime-wheel side organizes exact fresh-prime action, partial-wheel errors, unresolved square-root frontier faces, conductor structure, and the square-wheel nonzero response.

A successful quantitative step must respect both facts:

1. the arithmetic is organized by complete-square and reciprocal-fibre geometry;
2. unresolved wheel error near square-root scale is a signed prime-face object, not a generic positive remainder.

## 2. Retain the direct synthesis target

For synchronized primorial blocks and complete-square samples,

```math
R_k(X_n)=H_{k,n}+\rho_{k,n}R_k(U_k),
\qquad
0\le\rho_{k,n}<\frac16.
```

The zero mode is eliminated exactly. The canonical direct target remains

```math
|H_{k,n}|\ll_\varepsilon (X_n+1)^{1/2+\varepsilon}.
```

`boundary/frontier.json` remains at `exact_reduction`: no nontrivial pointwise exponent for `H_{k,n}` has been certified.

The exact PNT-centered coordinate is

```math
H_{k,n}=C_{k,n}^{PNT}-2E_{k,n}^{rec},
```

where `E^{rec}` is the centered Mertens-weighted reciprocal-interval prime-count discrepancy. A proof may attack this signed combined object directly. It is not the only live quantitative formulation.

## 3. Start the second route from the proved generalized affine PNT envelope

Write

```text
nativePNTError N = nativePsi N - N.
```

The quantitative PNT layer works with

```text
nativePNTHasAffineEnvelope alpha,
```

meaning that there exists a nonnegative intercept `D` such that

```math
|\psi(N)-N|\le\alpha N+D
```

for every `N`.

This is a proved PNT bound. The repository has explicit canonical and optimal-intercept machinery for these envelopes.

## 4. Use the strengthened cubic contraction

For

```math
0<\alpha\le\frac32,
```

`RHLean.Analysis.nativePNTSquarePrefixHasAffineEnvelope_lowSlope_cubic_step` proves

```math
\alpha
\longmapsto
\alpha-\frac{\alpha^3}{178200000}.
```

The same module proves that this update is strictly tighter than the earlier fully rederived square-prefix update with constant

```text
1 / 1140480000.
```

The new constant is larger by the exact factor `32/5`, so the one-step decrement is 6.4 times stronger in the low-slope regime.

This is a quantitative contraction of an already-proved affine PNT envelope. It does not yet control where, in physical `N`, the newly contracted tail begins.

## 5. Separate slope depth from physical cutoff

A tail state at `(M,alpha)` means

```math
|\psi(N)-N|\le\alpha N
```

for every `N >= M`.

A finite cubic scale chain records

```text
(M_0,a_0) -> (M_1,a_1) -> ... -> (M_n,a_n)
```

with

```math
a_{j+1}=a_j-ca_j^3.
```

`PrimeSieveStateDependentSelbergScalePersistence` proves that if each contraction is available from the recorded old cutoff to the recorded new cutoff, then the true PNT tail persists through the entire chain.

The key separation is

```text
scalar contraction depth        already controlled
physical onset M_n              still needs arithmetic control.
```

## 6. The square-root conversion theorem is already proved

`NativePNTQuadraticTailScaleLaw K` requires that for each small target slope `eta` there exists a cutoff `M` such that

```math
M\eta^2\le K
```

and

```math
|\psi(N)-N|\le\eta N
```

for all `N >= M`.

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

packages the same conclusion from a cubic scale law.

There is also an affine-intercept route. `NativePNTReciprocalInterceptLaw K` requires

```math
D(\alpha)\le\frac K\alpha,
```

and

```text
nativePNTError_abs_le_two_sqrt_of_reciprocalInterceptLaw
```

proves

```math
|\psi(N)-N|\le2\sqrt{KN}.
```

Therefore the missing result is a scale theorem.

## 7. State the open quantitative theorem correctly

The primary current target is to prove, from the actual square-block and prime-wheel arithmetic, a physical cutoff law strong enough to feed one of the existing square-root bridges.

The moving-cutoff target is essentially

```math
M(\eta)=O(\eta^{-2}).
```

The reciprocal-intercept route asks for the stronger physical cutoff behavior needed to make the global affine intercept `O(1/alpha)`.

No such law is currently proved.

A proof that only improves the scalar cubic constant while leaving the cutoff growth uncontrolled is insufficient for the final step.

## 8. Do not return to the absolute evolving-tail state

`RHLean.Analysis.NativePNTEvolvingTailObstruction` proves a structural obstruction for the canonical sign-blind evolving remainder.

The first absolute remainder contains the factorial defect at linear scale. Self-composition pushes that to an `N log N`-scale floor. The full evolving-tail cost satisfies a lower bound of the form

```math
N\log N-\alpha N\log^2N
```

up to the explicit lower-order terms in the theorem.

At a fixed polynomial physical scale in `1/alpha`, that floor overwhelms the desired cubic `alpha^3 N log^2 N` budget as `alpha -> 0`.

So the absolute evolving-tail state is not the route to the required cutoff law. A successor must preserve additional signs before taking norms.

## 9. Keep the second Selberg layer signed

`RHLean.Analysis.NativePNTSignedSecondSelberg` supplies the exact replacement coordinate.

Its kernel is

```math
K_2(n)
=(\Lambda*\Lambda)(n)-\Lambda(n)\log n
=\Lambda_2(n)-2\Lambda(n)\log n.
```

The exact recurrence is

```text
E(N) log(N)^2
  = signed Selberg remainder * log(N)
    - Lambda signed remainder mass
    + signed second-kernel error mass
    - floor-log signed defect mass.
```

The cell-exposed form refines the signed second-kernel term to

```text
+ dyadic Lambda_2 cell mass
+ top boundary mass
- 2 * Lambda-log signed error mass.
```

Nothing is replaced by an auxiliary current-scale absolute remainder. This is the acceptance coordinate for a future scale-improving theorem.

## 10. Use square-stage log-square cells

The modules

```text
NativePNTSignedLogSquarePrimeCells
NativePNTSignedLogSquarePositiveDyadicKernel
NativePNTSignedLogSquareDyadicCell
NativePNTSignedLogSquareSquareStage
```

reindex `Lambda_2` into finite Möbius log-square fibres, identify fresh-prime two-endpoint atoms, split the odd-Möbius kernel from its even correction, and place the surviving mass on complete-square exact-activity bands.

A future gain must be owned by the actual square-stage cells. A free many-`d` packet not tied back to square-block geometry does not satisfy the proof architecture.

## 11. Use the exact signed prime-wheel frontier

At partial-wheel cutoff `y`, under

```math
N<2y^2,
```

every actual nonzero wheel-error site is one of exactly two faces.

Prime square:

```math
n=q^2,
\qquad
K_2(n)=-(\log q)^2.
```

Distinct large-prime pair:

```math
n=qr,
\qquad
K_2(n)=2\log q\log r.
```

`NativePNTSignedSecondSelbergFrontierCharge` proves that every such site has reciprocal quotient

```text
N / n = 1
```

and therefore

```text
frontier error mass = - frontier charge.
```

This is exact. The total frontier charge is signed; no positivity theorem is available or claimed.

A successor theorem must exploit the aggregate signed structure of these faces together with the remaining signed Selberg terms. Taking termwise absolute values would return to the obstruction already formalized.

## 12. What a successful next quantitative theorem must do

A useful theorem should satisfy both acceptance criteria.

**Architecture criterion.** It must act on the actual square-stage, reciprocal-fibre, or partial-wheel frontier objects already identified, preserving the many-fibre or multi-prime signs that survive the exact reductions.

**Contraction criterion.** It must improve the effective physical scale of the proved generalized PNT contraction. The target is not another representation theorem and not merely a better local constant.

The decisive question is

```text
Can the signed square-stage and wheel-frontier ledger produce the next
contracted tail before the cutoff grows faster than O(eta^-2)?
```

## 13. Relationship to the direct H route

The direct square-wheel target and generalized-PNT scale target are compatible formulations of the desired square-root cancellation scale.

The direct route asks for

```math
|H_{k,n}|\ll_\varepsilon X_n^{1/2+\varepsilon}
```

and then uses zero-mode elimination and Mertens-to-zeta transfer.

The second route asks for RH-compatible physical persistence of the native PNT contraction and then invokes the proved square-root Chebyshev bridge.

The second route is further advanced at the quantitative-inequality level because the slope contraction and square-root optimization are formalized; its unresolved part is the physical onset.

## 14. Retained warnings

- Bounding `C^{PNT}` and `E^{rec}` separately by triangle inequality discards the signed cancellation visible in their exact combination.
- Fixed-`q` survivor pairing is a representation change, not a complete cancellation mechanism; any useful survivor theorem must act across prime fibres or against another signed frontier.
- The single-prime dyadic Li-residual mechanism does not control its coherent mode and must not be revived by merely enlarging finite ranges.
- The canonical absolute evolving-tail state is formally obstructed at polynomial physical scale.
- Numerical correlations and envelopes are diagnostics only.

See `boundary/dead_lanes.json` for the closed-lane record.

## 15. Once a scale law is proved

```text
proved affine PNT envelope
  -> proved cubic contraction
  -> OPEN: RH-compatible moving cutoff law
  -> proved sqrt(N) Chebyshev error bridge
```

In parallel, the direct synthesis chain remains

```text
square blocks + prime wheels
  -> H_{k,n}
  -> OPEN: direct RH-scale signed cancellation
  -> M(x)=O_epsilon(x^(1/2+epsilon))
  -> Mellin continuation of 1/zeta
  -> zero-free half-plane
  -> functional-equation reflection
  -> RH.
```

The repository must keep the distinction between a **conditional conversion theorem** and the **unconditional hypothesis that still has to be supplied**.

## Compressed current status

```text
ORDINARY PNT: PROVED

GENERALIZED PNT ENVELOPE: PROVED
  -> low-slope cubic contraction: PROVED, coefficient 1/178200000
  -> physical cutoff law: OPEN
  -> sqrt(N) conversion from that law: PROVED

SIGNED SECOND SELBERG LEDGER: PROVED EXACTLY
  -> square-stage cells: PROVED EXACTLY
  -> signed wheel-frontier classification: PROVED EXACTLY
  -> frontier error mass = -charge below 2 y^2: PROVED EXACTLY
  -> aggregate scale-saving theorem: OPEN

DIRECT H_{k,n} RH-SCALE BOUND: OPEN
RH: OPEN
```
