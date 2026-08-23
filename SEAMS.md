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

## 12. Combined-residual seam

With $X=R^2-1$, centering the cofactor-first transport against the smooth logarithmic-integral main term produces two residuals: the reciprocal-cutoff floor rounding $Q_R$ and the prime-counting discrepancy $E_R$. The seam is that they are combined *before* the cofactor sum, as the single channel weight

$$
\big(\pi(\lfloor X/c\rfloor)-\pi(R)\big)-\big(\mathrm{Li}(X/c)-\mathrm{Li}(R)\big),
$$

so no later step can take a norm of one without the other. Crossing this seam in the other direction — bounding $Q_R$ and $E_R$ separately and recombining — discards the cancellation that carries the prime-count drift, and only the one-way triangle inequality survives.

**Formal module:** `RHLean.Analysis.SquareRootCombinedSignedResidual`.

## 13. Orientation seam

The smooth mass splits by canonical orientation, and the two parts are at different scales from their sum. The matched object $A_R^{\mathrm{born}}-T_R$ is the one at square-root scale; the complete smooth mass $A_R=M(X)+T_R$ carries the whole transport drift. Any future decomposition must keep the orientation split rather than working with $A_R$.

The gap this leaves is explicit: $M(X)=A_R^{\mathrm{pos}}+(A_R^{\mathrm{born}}-T_R)$, so a matched bound needs the positive orientation at the same scale before it reaches the square-prefix Mertens value.

**Formal modules:** `RHLean.Analysis.SquareRootBornSmoothReciprocalForm` and `RHLean.Analysis.SquareRootSmoothParityClasses`.

## 14. Reciprocal seam

Both orientations and the transport term are expressible as rough Möbius prefixes at reciprocal cutoffs. This is the common coordinate system in which the matched difference is a single signed sum over the whole prime range, with no norm taken anywhere. A successor route should enter and leave through this form rather than introducing a fresh basis.

**Formal module:** `RHLean.Analysis.SquareRootBornSmoothReciprocalForm`.

## 16. Shallow-crossing seam

The reciprocal packet does not have to be processed to the end. For endpoint and cutoff sequences with $x_n\to\infty$ and a fixed reciprocal depth $K_0$ eventually above the cutoff, a negative finite reciprocal coefficient at $K_0$ forces the intact upper-middle packet to cross at some depth $K\le K_0$, and for every $C>0$ that depth is eventually at most $C\log x_n$.

The seam is that the crossing statement is endpoint-parametric. It does not depend on the square parametrization or on any particular certified depth; the square case is the instance $x_R=R^2-1$, $y_R=R$.

**Formal modules:** `RHLean.Analysis.SquareRootShallowReciprocalCrossing` and `RHLean.Proof.SquareRootTruncatedPacketEquivalences`.

## 17. Post-crossing tail seam

Two objects must not be conflated at this seam: the raw transport tail, which is the increment from the partial packet to the fully processed post-root packet, and the coupled tail, which adds the complete square-root-smooth population to that increment. The exact terminal identity is

$$
M(R^2-1)=\text{partial crossing residual}+\text{coupled tail},
$$

so the raw increment alone is not the terminal Mertens remainder. Once the partial residual is bounded by an absolute shallow depth, a critical root-scale estimate for the coupled tail is equivalent to the square-prefix Mertens energy criterion. The eventual crossing theorem supplies the shallow residual unconditionally; it does not supply the coupled-tail estimate.

**Formal module:** `RHLean.Analysis.SquareRootPostCrossingTail`.

## 18. Renewal normal-form seam

The crossing residual is a shallow linear combination of the same lower-scale Mertens states that occur in the exact recursive replacement row, and that signed structure must survive. Three exact descriptions are available for $1\le K<R$: a direct remaining-layer cap, an Abel form, and a lower-triangular renewal row obtained by subtracting the shallow crossing coefficients from the complete replacement row *before* any norm.

Under the replacement-fibre dictionary the packet layer is the negative cofactor-one prime face, so every fully admitted shallow layer cancels its prime diagonal exactly and the crossing layer retains precisely the negative count of unfilled seats. The last form is the genuinely nonlocal bilinear proof object; entering it with a diagonal estimate or a triangle inequality discards what it was built to keep.

**Formal modules:** `RHLean.Analysis.SquareRootPostCrossingRenewal`, `RHLean.Proof.RecursivePrimeReplacement`, and `RHLean.Proof.ReplacementFibreOrientationSplit`.

## 19. Canonical rough-covariance seam

Pushing the complete renewal back onto the cofactor coordinate gives

$$
\text{coupled tail}=\text{explicit packet baseline}-\sum_c\mu(c)\,\mathrm{Resp}(c),
$$

where each cofactor response carries both its diagonal reciprocal-prime multiplicity and every strict quotient descendant. The remaining obligation is therefore a literal finite correlation between the Möbius parity field and one intact rough-prime response field, and the module also records its centered mean/covariance form. No mean-zero assertion, norm split, or independence hypothesis is used to reach it, and none may be introduced when crossing back.

**Formal module:** `RHLean.Analysis.SquareRootCanonicalRoughCovariance`.

## 20. Prime-count-free transport seam

Every floor difference in the upper-prime transport is the cardinality of a finite quotient interval, so the transport is a signed sum over triples $(c,t,k)$ with weight $\mu(c)(-1)^{|t|}$ and the high region present only as two hyperbolic cutoff inequalities. At the square endpoint the geometry then forces every low face of product at least $R$ to vanish, so both coordinates live on the same full Boolean cube of primes up to $R$.

On that symmetric carrier the canonical least-prime cofactor/quotient involution cancels every interior state and leaves

$$
M(R^2-1)=M(R)-\mathrm{canonicalDefect},
$$

with the defect confined to one adjacent multiplicative shell frontier. The seam requirement is that no prime-counting coefficient be reintroduced downstream: the entire remaining ledger is low-wheel signs plus cutoff inequalities.

**Formal modules:** `RHLean.Proof.LowWheelTransportTripleCarrier`, `RHLean.Proof.LowWheelDoubleCubeTransport`, and `RHLean.Proof.LowWheelCanonicalDefectReduction`.

## 21. Strong-Mertens corridor seam

Downstream contour code sees exactly one positive constant $A$ and one left boundary

$$
\sigma_A(T)=1-\frac{A}{(\log T)^{9}},
$$

with the reciprocal-zeta estimate, the zero-free region, and the bounded-height zero-free box already reconciled behind it. The seam requirement is that no consumer destructs those existential theorems again, and that no wide-strip reciprocal-zeta hypothesis is introduced at the corridor.

**Formal modules:** `RHLean.Analysis.StrongMertensLogNineCorridor` and `RHLean.Analysis.StrongMertensZetaKernel`.

## 22. Reciprocal-moment seam

The contour stack ends at a bound on $M(N)$, while the centered K2 argument consumes the reciprocal logarithmic Möbius moments

$$
A_m(N)=\sum_{n\le N}\frac{\mu(n)(\log n)^m}{n}.
$$

The finite Abel identity between them is exact for every $N$; the two analytic facts it needs — summability of the Abel increments and vanishing of the endpoint term — are kept as explicit hypotheses, which is what makes the bridge itself unconditional. A Mertens decay bound of the shape $|M(x)|\le Cx\exp(-c(\log x)^{1/10})$ discharges both.

**Formal modules:** `RHLean.Analysis.StrongMertensRecipMomentTransfer` and `RHLean.Analysis.K2RecipMomentAnalyticClosure`.

## 23. Signed second-Selberg seam

The exact signed kernel

$$
K_2(n)=(\Lambda*\Lambda)(n)-\Lambda(n)\log n
$$

has reciprocal mass $O(\log N)$, against the logarithmic-square size of the positive second von Mangoldt kernel. That is an unconditional signed cancellation, and it is lost the moment the two pieces are estimated separately. The summatory shortcut is calibrated at the same seam: the summatory kernel differs from $-2E(N)\log N$ by only $O(N)$, so a linear summatory bound would require exactly the logarithmic improvement of the physical PNT error that the onset analysis does not yet supply.

**Formal modules:** `RHLean.Analysis.NativePNTSignedSecondSelbergReciprocal` and `RHLean.Analysis.NativePNTSignedSecondSelbergFactorFourBridge`.

## 24. Conductor Gram seam

The corrected-conductor sector is split by *boundary divisor*, not by the original conductor, so removing the small reindexed boundary divisors leaves one collapsed signed core containing the conductor-one bulk, every large raw expansion layer, and the fully collapsed smooth term. No absolute value is placed on a high-conductor packet, and the complete cross-conductor interaction stays inside one Gram quantity.

The elementary uniform bound $\lVert J_q(k,x)\rVert\le6q^3$ is what makes the split usable: all nontrivial conductors $q\le R$ contribute $O(R^4)$ uniformly in the prefix length, so a cutoff on the order of the eighth root of the arithmetic scale puts that growing sector at square-root size.

**Formal modules:** `RHLean.Analysis.CorrectedConductorHighSectorGram` and `RHLean.Analysis.CorrectedConductorSmallSectorBound`.

## 25. Fixed-amplification seam

The open square-root endpoint statement may carry an arbitrary fixed absolute constant $A$,

$$
(M(R^2-1)-1)^2\le A\,R^2K_R,
$$

and still close the standard Mertens energy criterion: choose an onset with $4A\le R^{\varepsilon}$ and run strong induction on the physical integer, at a cost of $O(R^2)$ for the unfinished part of one square block. The seam requirement is therefore *not* a subunit contraction. It is also not fibrewise: the cross-region reduction routes the endpoint amplification through fixed critical-envelope bounds on the two already-signed channels, without splitting the matched channel by distinguished prime.

**Formal modules:** `RHLean.Proof.SquareRootAmplificationClosure` and `RHLean.Proof.SquareRootCrossRegionAmplification`.

## 26. Ordered prime-extension seam

The prime-wheel fresh-prime mechanics and the canonical square-root ancestry flow meet on the factor pair $(q,c)$. The ancestry parent strips the largest prime factor of the core, while abstract fresh-prime insertion may adjoin a prime in any order, so unrestricted equivariance is false. It is exact precisely on the ordered submove where the adjoined prime exceeds every prime already present in the parent core. Any transport bridge across this seam must be chronological.

**Formal modules:** `RHLean.Proof.WheelToLedgerEquivariance` and `RHLean.Proof.WheelToLedgerPushforward`.

## 27. Endpoint-sequence seam

Every integer inside a complete square block lies within distance $R$ of one of the two completed-square endpoints, and the Mertens summatory function changes by at most the length of an integer interval. Arbitrary interior points therefore contribute only an explicit $2R^2$ baseline beyond adjacent endpoint energy, so the completed-square sequence carries the whole obligation and no separate arbitrary-point target is needed.

**Formal module:** `RHLean.Analysis.NearestSquareEndpointDomination`.

## 28. Acceptance criterion for quantitative progress

A proposed estimate should satisfy both conditions:

1. preserve the square-block and prime-wheel architecture, including the signed cancellations exposed above;
2. contract the proven bound toward

$$
X^{1/2+\varepsilon}
$$

for the Mertens amplitude, equivalently exponent $1+\varepsilon$ for squared energy.

Unsigned population improvements, local constant defects without bounded charging, or Cauchy--Schwarz steps that erase the signed parity cross term do not by themselves advance the RH-scale frontier.

Three further filters follow from the recorded obstructions. A proposal whose saving is a product of local multipliers of the form $1-c/q$ is capped at a power of a logarithm and cannot reach a power of $R$. A proposal that decomposes the transport population into cancelling orbits plus a bounded boundary must say what happens to the same-sign top block, which equals its own cardinality. And a proposal that reaches the target through Cauchy--Schwarz on a coefficient family must show the family is arithmetically constructible, since the optimal coefficients already encode the answer.

Three further filters follow from the newer obstructions. A proposal that cancels the inert top block one-for-one against the middle prime fibres must decide the sign of $2\pi(X_R/2)-\pi(X_R)-\pi(R)$, which first-order PNT does not determine because the leading $X/\log X$ terms cancel. A proposal that charges a bounded collision defect must transport the label to a different arithmetic fibre before reading its corrected weight, because the literal same-site realization is refuted. And a proposal built on fresh-prime equivariance between the wheel and the ancestry ledger must restrict to the ordered extension, since the unrestricted move is false.
