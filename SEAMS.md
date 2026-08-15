# Exact seams between the proof layers

This document records the interfaces that should remain stable while the quantitative proof evolves.

## 1. Three-slot degree-one seam

For the three active slots of a four-cell,

$$
S_k=(\mu(4k+1),\mu(4k+2),\mu(4k+3)),
$$

the degree-one characters recover the direct signed coordinate sums and hence

$$
M(4K)=W_a(K)+W_b(K)+W_c(K).
$$

This seam converts the finite 27-state language into the actual Mertens quantity without probabilistic assumptions.

**Formal modules:** `RHLean.Analysis.ThreeSlotMertensDegreeOneProjection` and `RHLean.Arithmetic.PrimeWheelThreeSlotRecovery`.

## 2. Signed prime-wheel seam

For the canonical prime set through the physical square-root cutoff,

$$
W_j(K)=R_j(K)-2H_j(K).
$$

Therefore

$$
M(4K)=\sum_{j=1}^3\bigl(R_j(K)-2H_j(K)\bigr).
$$

The correction term must remain inside the signed field. Separate absolute bounds on `R` and `H` do not preserve this cancellation.

**Formal modules:** `RHLean.Arithmetic.PrimeWheelThreeSlotRecovery` and `RHLean.Arithmetic.PrimeCombFiniteDifferenceRecovery`.

## 3. Endpoint seam

The complete-cell identity now extends to every physical cutoff. With $K=\lfloor X/4\rfloor$,

$$
|M(X)-M(4K)|\le 3.
$$

Thus an RH-scale complete-cell estimate immediately transfers to arbitrary $X$ with a bounded additive correction.

**Formal module:** `RHLean.Arithmetic.MobiusFourCellEndpointTransfer`.

## 4. Recovered-energy seam

The canonical square-root-covered corrected wheel equals the ordinary Möbius prefix at every cutoff. Its squared energy criterion is equivalent to the global Mertens-energy statement and to the square-prefix energy criterion.

The forward analytic bridge then converts the Mertens-energy criterion to the formal Riemann hypothesis statement.

**Formal modules:** `RHLean.Analysis.PrimeWheelRecoveredMertensCriterion`, `RHLean.Analysis.SquarePrefixMertensBridge`, and `RHLean.Analysis.MertensEnergyRHForward`.

## 5. Physical collision seam

The finite collision frontier is partitioned into pairable labels, fixed labels, and mate-crosses-cutoff labels. The pairable part cancels under the separately verified physical sign law.

The corrected field now also has the exact square-kill law. Therefore fixed labels forced into selected-prime square hits contribute zero, and the full physical frontier reduces to the cutoff defect alone.

The remaining defect has at most three labels, so any unit-bounded integer weight on one frontier has total absolute defect mass at most three.

**Formal modules:** `RHLean.Arithmetic.PrimeSquareCollisionPairingFrontier` and `RHLean.Arithmetic.PrimeWheelCorrectedLocalFlip`.

## 6. Global collision-chain seam

The local constant `3` is useful only if it is charged with bounded global multiplicity. `SquarePrefixCollisionDefectChain` makes that requirement explicit.

If a square stage $n$ is represented by at most $n+1$ such charged frontiers, then

$$
|M((n+1)^2-1)|\le 3(n+1)
$$

and

$$
|M((n+1)^2-1)|^2\le 9(n+1)^2.
$$

The chain statement for every $n$ implies the square-prefix and global Mertens-energy criteria.

**Formal module:** `RHLean.Analysis.PrimeBoundaryDefectBridge`.

This seam identifies the exact unresolved arithmetic theorem: construct the chain from the real square-prefix frontier without charging a constant independently to every prime pair.

## 7. Fresh-prime finite-difference seam

The unordered divisor-difference operator

$$
D_S f(x)=\sum_{d\mid\prod_{p\in S}p}\mu(d)f(\lfloor x/d\rfloor)
$$

satisfies

$$
D_{S\cup\{p\}}f=D_Sf-D_S(\operatorname{shift}_p f)
$$

for a fresh prime $p$. This moves the sign flip inside the old-prime fibre and therefore freezes the other selected prime coordinates algebraically.

**Formal modules:** `RHLean.Arithmetic.PrimeCombFiniteDifference` and `RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime`.

## 8. Boolean derivative seam

For arbitrary Boolean support, exact first, second, and third coordinate derivatives are available. In particular the two-pivot stencil is

$$
I(u)-I(a+u)-I(b+u)+I(a+b+u),
$$

and the three-pivot form is the corresponding eight-state derivative.

The actual fixed-prime survivor fibre inherits these identities. For $q\ge7$, coordinates $2$, $3$, and $5$ give an exact eight-state survivor stencil with local magnitude at most $4$.

**Formal modules:** `RHLean.Arithmetic.BooleanCubeFiniteDifference` and `RHLean.Proof.SurvivorPrimeFaceFiniteDifference`.

## 9. Residue second-toggle seam

A residue mask invariant under a second square-one prime coordinate survives the first-failure pairing. At parity modulus $2$, primes $3$ and $5$ reduce the high survivor mass to six explicit codimension-two corner sums.

This is the preferred residue-level support description for a signed covariance or corner-energy estimate.

**Formal modules:** `RHLean.Arithmetic.TruncatedBooleanCubeMaskedSecondToggle` and `RHLean.Proof.SurvivorResidueSecondToggle`.

## 10. Dyadic parity seam

For odd upper prime $q$, parity residue $0$ is the odd-cofactor channel and residue $1$ is the even-cofactor channel. The exact signed parity Gram retains the cross-channel interaction that a positive residue-energy bound can discard.

Canonical source admissibility is unchanged under $d\mapsto2d$ for odd $d$ and $q>2$, so nonzero dyadic pair mass is supported on exactly three geometric crossing shells.

**Formal modules:** `RHLean.Proof.SurvivorDyadicStaticCancellation`, `RHLean.Proof.SurvivorDyadicActivityMismatch`, and `RHLean.Proof.SurvivorResidueCovarianceCriterion`.

## 11. Renewal and square-wheel seam

The weighted renewal telescope realizes the far-upper reciprocal Mertens transform exactly. The revision-3 synthesis theorem substitutes that renewal realization into the established square-prefix decomposition and then into the synchronized primorial square-wheel zero-mode center.

No estimate is asserted at this seam; it provides exact coordinates for a future contraction.

**Formal modules:** `RHLean.Analysis.MobiusRenewalTelescope` and `RHLean.Analysis.MobiusRenewalSquareWheelSynthesis`.

## 12. Acceptance criterion for quantitative progress

A proposed estimate should satisfy both conditions:

1. preserve the square-block and prime-wheel architecture, including the signed cancellations exposed above;
2. contract the proven bound toward

$$
X^{1/2+\varepsilon}
$$

for the Mertens amplitude, equivalently exponent $1+\varepsilon$ for squared energy.

Unsigned population improvements, local constant defects without bounded charging, or Cauchy--Schwarz steps that erase the signed parity cross term do not by themselves advance the RH-scale frontier.
