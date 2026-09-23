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

## 28. Processed-seat carrier seam

The low-prime sequential layer and the fresh-prime matching meet on `squareRootLowPrimeProcessedSeatCarrier`, the complete processed seat carrier. Every state a fresh low prime can still act on appears exactly once, tagged by cofactor and channel, so the matching is a map on one finite object rather than a relation between successively redefined populations. Both the running telescope and the quadratic energy telescope are stated on this carrier, and both are exact.

**Formal modules:** `RHLean.Proof.SquareRootLowPrimeProcessedSeatCarrier`, `RHLean.Proof.SquareRootLowPrimeProcessedSeatMatching`, `RHLean.Proof.SquareRootLowPrimeRunningTelescope`, and `RHLean.Proof.SquareRootLowPrimeGlobalEnergyTelescope`.

## 29. Move-order seam

Two sign-reversing involutions on the same finite signed region have stable sets of equal signed mass. This is the seam that makes the fresh-prime move order a free choice: a large exposed frontier under the chronological order may be replaced by the stable set of the descending order without estimating any alternating path between them. The statement is finite parity and carries no arithmetic.

**Formal module:** `RHLean.Proof.FiniteOthelloMatching`.

## 30. No-liberty seam

The stable population of the descending processed-seat matching and the tagged four-class endpoint boundary are indexed by different types, so literal Finset equality is not the target. The seam is a weight-preserving finite equivalence together with pointwise agreement of signed weight; given one, the whole signed sum transfers and tagged boundary mass is the running imbalance.

This is the one seam in the package whose crossing map is not yet assembled, and an injective weight-preserving classifier is enough for quantitative closure; the full equivalence is needed only when surjectivity is also available. Each of the four endpoint classes — head, partial packet, born no-successor, and Go root equality — now has its own branch with membership, injectivity and exact weight preservation proved, the product-wall branch of the source dichotomy is removed outright by the arithmetic of the schedule cutoff, and the target-side budget is $3R+21$. What is open is the classifier that routes every source state to a branch, together with the one named `Partial` budget. A cardinality match between the two sides still does not cross this seam.

**Formal modules:** `RHLean.Proof.SquareRootLowPrimeOppositeFixedClassification`, `RHLean.Proof.SquareRootLowPrimeNoLibertyBoundaryHome`, `RHLean.Proof.SquareRootLowPrimeNoLibertyFiniteEquiv`, and the branch modules `RHLean.Proof.SquareRootLowPrimeHeadClassifierBranch`, `RHLean.Proof.SquareRootLowPrimePartialEndpointCarrier`, `RHLean.Proof.SquareRootLowPrimeBornSeatPartnerEmbedding`, and `RHLean.Proof.SquareRootLowPrimeBornExitClassifierBranch`.

## 31. Go transport seam

The Go crossing population and the global low-wheel transport carrier meet on the incidence $(t,x)=(\{r\},(d,q))$. A strict crossing $R<rq$ is already a transport state of weight $\mu(qd)$, and because the birth boundary forces $d>1$ with every prime factor of $d$ below $r$, the canonical least-prime pivot lies in the parent, so the canonical toggle supplies the opposite-sign partner inside the transport identity. Only the exact equality $rq=R$ fails to cross this seam, and it is a root-boundary population of cardinality at most $R$, not unfinished recursion.

**Formal modules:** `RHLean.Proof.SquareRootLowPrimeGoGlobalPartner` and `RHLean.Proof.SquareRootLowPrimeGoRootEqualityBoundary`.

## 32. Recoupling seam

The processed-seat terminal state and the historical $A_R-T_R$ architecture meet at $P_R=R-\lfloor\sqrt R\rfloor$. The terminal state is $M(R^2-1)+\sum_{q\le R}M(q-1)$ minus the partial crossing packet and the near-root rectangle, whose combined norm is at most $R+K$. Crossing this seam in the other direction is what guarantees the low-prime coordinate system introduces no new analytic obligation: the only non-elementary amplitude left is the old matched core, and the conditional endpoint theorems above it assert nothing about that core's size.

**Formal modules:** `RHLean.Proof.SquareRootLowPrimeSmoothTransportRecoupling` and `RHLean.Proof.SquareRootLowPrimeMatchedFrontierBound`.

## 33. Cumulative Othello wall seam

The sitewise Othello laws are played on a whole region rather than site by site. The carrier toggle $\tau_p$ is an involution whose moving states are exactly the $p^2$-free sites, where $\mu(\tau_p n)=-\mu n$, and whose frozen states are exactly the square hits, which carry no mass. Hence the signed mass of any finite region equals the signed mass of its escape part, and for the ordered prefix carrier $(L,x]$ that escape part is exactly two walls: the anchor wall $n\le pL$ and the cutoff wall $x<np$. This is an equality, and the whole interior has cancelled in mated pairs.

The scope matters at this seam. It is a pairing by two cycles of one fixed prime, not an alternating-component argument, and it contains no birth-to-capture cancellation. Peeling a list of distinguished primes preserves the equality on the iterated boundary, so what remains to prove is a multiplicity bound on that boundary.

**Formal modules:** `RHLean.Proof.GlobalPrefixCarrierOthello`, `RHLean.Proof.PrefixCarrierOthelloWalls`, and `RHLean.Analysis.PrimeWheelRunOthelloBoundary`.

## 34. Lifetime run seam

An atom of the square-time process has a birth stage and a capture stage, and its activity indicator is the indicator of the half-open lifetime. Activity increments telescope over a run, so an atom born after the run starts and captured before it ends contributes exactly zero, whatever its lifetime was. The length of the lifetime appears nowhere in the statement or the proof, which is the property a cumulative run needs and which a fixed-prime pairing does not supply.

The seam is faithful because death is proved permanent on the actual active predicate: for a nonnegative cutoff slope the moving-high threshold is nondecreasing, so there is no resurrection between birth and capture. What is proved is interval structure plus endpoint telescope; explicit birth and capture times are not constructed, and the aggregate run identity is stated in the existing $\mathrm{Active}=\mathrm{Birth}-\mathrm{Death}$ coordinates.

**Formal module:** `RHLean.Proof.LifetimeRunCancellation`.

## 35. Frozen square-run seam

Admitting one fresh Euler prime $p$ to a finite old universe $S$ acts on a signed window by

$$
W_{S\cup\{p\}}(A,B)=W_S(A,B)-W_S(\lfloor A/p\rfloor,\lfloor B/p\rfloor).
$$

A new prime therefore leaves one compressed predecessor-cube window, not another independent copy of an old parent. Combined with the frozen square-run kernel $K(a,b)=M(a^2-1)-M((b+1)^2-1)$ and the canonical endpoint involution $M(R^2-1)=M(R)-D_R$, this gives

$$
K(a,b)=(M(a)-M(b+1))+(D_{b+1}-D_a),
$$

whose Mertens gap costs at most the root interval length $b+1-a$. The energy of the *change* in the canonical downcross frontier is therefore equivalent, with no loss, to the frozen-square-run, global Mertens-energy, signed square-run, and primorial-residual criteria.

**Formal modules:** `RHLean.Arithmetic.DyadicFrozenPrefix`, `RHLean.Analysis.FrozenSquareRunKernel`, and `RHLean.Analysis.FrozenSquareRunDowncrossBridge`.

## 36. Common frozen-owner seam

After exact late-parent cancellation the downcross ledger is the canonically oriented Euler first-crossing ledger, and on one oriented state the quotient coordinate is the canonical pivot. The Boolean faces charging that state are exactly the frozen faces of the old universe below the pivot whose products lie in the state's ownership window, so the state's signed face mass is one frozen predecessor-window mass.

The seam is what makes a run difference safe to square. Both endpoint sums extend to the union of their state carriers, each state keeps the *same* canonical owner at both endpoints, and only its two window endpoints move with the root. Predecessor-cube cancellation is therefore preserved state by state before any norm is taken.

**Formal modules:** `RHLean.Proof.LowWheelCanonicalRepeatedMovableCancellation`, `RHLean.Proof.LowWheelCanonicalOrientedFrozenFibres`, and `RHLean.Proof.LowWheelCanonicalOrientedRunFibres`.

## 37. One-carrier seam

Five descriptions of the same signed object are now proved equal, before any norm: the squared-Fermat vertical factor strip, the ordered Euler cut ledger, the canonically oriented downcross ledger, the signed prefix lifetime residual, and the canonical defect ledger. One tagged occurrence $(t,(c,p))$ carries its low face product, crossing prime, rough cofactor, parent and child integers, Möbius sign, and exact half-open root lifetime simultaneously, so an atom is followed through all roots without rebuilding its coordinates at each endpoint.

The energy propositions on these coordinates are stated as open `Prop`s and then proved equal to the pre-existing canonical oriented-run seam. That is the discipline this seam enforces: a change of coordinates removes duplicate seams and supplies no quantitative cancellation, so a new coordinate is only admitted together with the theorem that its energy statement is the old one.

**Formal modules:** `RHLean.Proof.OrderedEulerCutProjection`, `RHLean.Proof.ComplexVerticalIntervalEulerBridge`, `RHLean.Proof.ComplexVerticalFiberSpacing`, and `RHLean.Proof.SignedPrefixEventLifetime`.

## 38. Line Green--Kubo seam

On the physical child-line carrier the event variable is $\mathrm{event}(n)=\mu(n)\chi(n)$, zero when the child has the same status at both endpoints and $\mp\mu(n)$ on birth and death. Its sum is exactly the vertical-interval mass, so squaring the *whole signed population* before any absolute value gives the finite identity

$$
\lVert V(a,b)\rVert^2=D_{\text{line}}+2\,C_{\text{line}}.
$$

The diagonal is then bounded by the exact squarefree population rather than by the pointwise envelope $1$, and the active-child carrier is exactly the squarefree shell $\{n: R<n<R^2\}$, with fresh-prime membership instability exactly the two physical walls birth and top escape. The limiting $40/30/30$ law is therefore used only in the safe direction, to sharpen the diagonal; no sign balance is asserted on the arithmetically selected birth/death set. What is left is the positive aggregate covariance among distinct physical lines, and nothing else.

**Formal modules:** `RHLean.Proof.ComplexVerticalLineGreenKubo` and `RHLean.Proof.ComplexVerticalLineSquarefreeDiagonal`.

## 39. Reciprocal Euler compression seam

On the RH-critical reciprocal covariance carrier a fresh-prime parent/child pair is not deleted but compressed back onto the parent:

$$
v_R(c)+v_R(cp)=\Bigl(1-\frac1p\Bigr)v_R(c)+\frac{\mu(c)}{cp}\,(T+E-B).
$$

The interior receives the same Euler contraction as the native reciprocal fibre, and every failure of exact contraction is confined to the order-threshold, top-escape and lower-root birth channels, suppressed by the reciprocal child cofactor. The factors accumulate exactly on the Boolean cube, and on a complete sub-root wheel the threshold channel is literally empty, so the critical signed boundary is exactly post-root top escape minus lower-root birth.

The seam has a stated direction of travel. Recoupling the zero mode moves it from the centered coordinate to the uncentered correlation $\mathrm{Corr}_R=M(R-1)-M(X_R)$, which is the object whose critical control is equivalent to the square-prefix energy criterion; a post-root fresh prime gives no new contraction, so useful contraction has to be earned on sub-root primes.

**Formal modules:** `RHLean.Proof.CanonicalRoughReciprocalCompression`, `RHLean.Proof.CanonicalRoughCompleteSubrootDefectReduction`, `RHLean.Proof.CanonicalRoughCriticalCorrelationContraction`, and `RHLean.Proof.CanonicalRoughCriticalDefectWindows`.

## 40. Telescope and Abel-return seam

One physical defect shell is not an independent error. With its native $1/p$ restored it is exactly

$$
T_{P\cup\{p\}}(N)-\Bigl(1-\frac1p\Bigr)T_P(N),
$$

the discrepancy between the true next truncated Euler cube and the uniform Euler contraction. Transporting these over a descending prime list is therefore a telescope, not a sum of absolute defect costs, and it closes on the single final boundary $T_L(N)-\prod_{q\in L}(1-1/q)$.

The return trip is exact in both coordinates. The reciprocal-weighted upper column telescopes to one terminal boundary; the literal physical columns carry no $1/q$, so they produce a prime-weighted discrete boundary variation, which finite summation by parts closes into the primitive $\sum_{n<K}B_n(X)-K\,B_K(X)$. The RH-critical object attached to the physical columns is that combination, not the endpoint boundary alone, and the reciprocal weight that makes the compression work costs only an absolute constant on the way back to the unweighted numerator.

**Formal modules:** `RHLean.Proof.CanonicalRoughTruncatedWheelDefectTelescope`, `RHLean.Proof.CanonicalRoughTruncatedWheelManyPrimeTelescope`, `RHLean.Proof.CanonicalRoughBoundaryProfileAbelReturn`, `RHLean.Proof.CanonicalRoughColumnAbelBridge`, and `RHLean.Proof.CanonicalRoughFiniteAbelReturn`.

## 41. Block partition and family-descent seam

For signed blocks, $S^2=E+2X$. Cross-block coherence is therefore pinned by the total mass and the block energy rather than free, and the magnitude-first step $|S|\le\sum_j|B_j|$ discards exactly twice the cross-covariance defect. Instantiated at the square blocks this partitions the global integer-order covariance into within-block and cross-block parts on one carrier, with no domination hypothesis anywhere.

Two exact facts sit on this seam and pull in opposite directions. The square-block energy exceeds the exact squarefree diagonal by precisely twice the aggregate within-block covariance, so bounding $E$ *is* the RH-scale problem and its measured linearity must not be promoted; but every refinement step moves energy into children plus an explicit signed cross term, with the leaf energy exactly the linear squarefree diagonal. And a post-root prime family is an isometric copy of a lower-scale prefix for pair covariance, since $\mu(pc)\mu(pd)=\mu(c)\mu(d)$ reverses family mass while preserving family covariance. Refinement and descent, not a bound on $E$, are what this seam offers.

**Formal modules:** `RHLean.Analysis.BlockCovarianceDecomposition`, `RHLean.Analysis.BlockCovarianceRefinement`, `RHLean.Analysis.MertensCovarianceDescent`, and `RHLean.Analysis.SquareRunEscapeCovariance`.

## 42. First-jump recombination seam

The first-jump residual does not cross this seam one first-jump prime at a time. For $R/2<p$ the packing factor is $1$, yet the canonical $p$-slice stays live under every later oriented owner in $(p,(R^2-1)/p]$ and aggregates to the negative cardinality of that interval; the proposed cofactor-column replacement fails on finite tests for the same reason.

What does cross is the recombination. The first-jump aggregate must be joined with the square-root-dense piece before any norm is taken, and the recombined scalar is exactly `lowWheelCanonicalDefectLedger R` — through the vertical-line normalization, the signed squarefree shell between $R$ and $R^2$. From there a uniform reciprocal-prefix bound of size $(\log R+1)/R$ suffices, with no first-jump-prime or cofactor-column norm inserted anywhere.

**Formal modules:** `RHLean.Proof.LowWheelCanonicalSqrtDenseContraction`, `RHLean.Proof.FirstJumpPrimeSliceObstruction`, `RHLean.Proof.GlobalFirstJumpCofactorCompression`, and `RHLean.Proof.GlobalFirstJumpCriticalCorrelationBridge`.

## 43. Unconditional forward-consumer seam

The reduction from the projected-renewal Gram form down to $\lVert M(x)\rVert^2\le C(x+1)^{1+\varepsilon}$ is proved outright: no criterion, realization, partition, or low-increment control is supplied by the caller. What used to sit above it was the classical Mertens criterion, accepted as an ordinary theorem argument.

That argument is now constructed internally in the one direction the route uses. Partial summation on $\sum\mu(n)n^{-s}$ gives convergence on $\mathrm{Re}\,s>1/2$, the limit is analytic there and agrees with $1/\zeta$ on $\mathrm{Re}\,s>1$, the identity theorem forces $\zeta\ne0$ on $\mathrm{Re}\,s>1/2$, and the functional equation reflects this to the left half — with no contour shifting and no zero-free region. The reverse direction still needs the harder contour argument and is not asserted. Consequently the terminal consumer has the square-prefix energy estimate as its only hypothesis, and that theorem is guarded by `#print axioms` alongside the others.

**Formal modules:** `RHLean.Proof.TerminalMertensReduction` and `RHLean.Proof.TerminalMertensForward`.

## 44. Post-root exponent-transfer seam

In the Bessel identity

$$
2E(W)=M(W)^2-\text{complementDiagonalResidual}(W)-\text{familyMertensSquareEnergy}(W)
$$

both subtracted terms are nonnegative, so $E(W)\le M(W)^2/2$ holds unconditionally: no cancellation, no record hypothesis, no sieve. That one line is the seam. It makes the post-root power remainder, the power envelope, the record-excess statement, the falling finite-difference statement, the Mertens square envelope and the Mertens energy criterion a single equivalence class.

Read quantitatively rather than as a bi-implication it is a transfer with an exact exchange rate: a Mertens bound of exponent $\theta$ gives remainder exponent $2\theta$, and the compiled bootstrap gives the converse. So the seam carries a string, and the string is a no-go: nothing in the post-root or record machinery can move the remainder exponent without first moving the Mertens exponent. What can still move is the unconditional constant, and it does — the odd dyadic-annulus representation is worth a factor of nine, and the compiled strong Mertens estimate gives a genuinely subquadratic envelope against an elementary lower bound of order $-W^{3/2}$.

**Formal modules:** `RHLean.Proof.PostRootCovarianceGlobalExponentTransfer` and `RHLean.Proof.PostRootCovarianceUnconditionalDecayScratch`.

## 45. Record-step seam

The finite-horizon envelope advances only at a positive record, and its whole mass is the cumulative record excess, so the record step is where the remaining quantitative problem lives. Three exact facts cross this seam.

The one-step innovation budget splits **without any triangle inequality**, into a physical outer row seat and a square-wall departure seat, because the two mechanisms have disjoint support: at a prime-square endpoint $W+1=p^2$ both the physical Möbius row and the inherited row total vanish, and away from a prime square the departure vanishes. A positive record at $N$ forces $\mathrm{envelope}(N)\cdot N^{\varepsilon}<\mathrm{innovation}(N)$, a full endpoint power stronger than naive localization, with the gain coming from the record hypothesis and not from an absolute value. And the departure is supported exactly on prime squares, so its whole normalized sum is bounded unconditionally by $p^2$ sparsity alone.

What does not cross is the record-conditioned outer row — the record-breaking physical new row after inherited high transport has been removed. That is the whole remaining arithmetic seam on this carrier, and the record indicator in the surviving majorant is load-bearing: dropping it leaves a positive part whose normalized sum is not expected to converge.

**Formal modules:** `RHLean.Proof.PostRootCovarianceRecordAbsorption`, `RHLean.Proof.PostRootCovarianceRecordSquareCharge`, and `RHLean.Proof.PostRootCovarianceRecordSquareChargeClosure`.

## 46. Frozen relocation seam

Moving the largest cofactor prime out of the cofactor and into the quotient, $(t,(c,p))\mapsto(t,(c/q,qp))$, is injective with an explicit inverse, so the frozen nontrivial-cofactor ledger is exactly minus the signed mass of its image. The image is disjoint from the entire downcross carrier, since every image state has normalized root-side parent above $R$: this is a genuine relocation onto the post-root side, not an internal reshuffle. With the already-proved movable cancellation the endpoint identity sharpens to

$$
D_R=U_R+F_R^{c=1}-T_R .
$$

The seam is one-way, and the module that says so is as important as the one that crosses it. Every high-prime population here is indexed by a prime strictly above the root, while an image state has pivot $p<q\le c<R$ and quotient $qp$ whose only primes are $q$ and $p$: the image is rough-free below the root. The two populations are complementary, not nested, and the proposed containment holds only vacuously. Independently, a sign-reversing bijection cannot change a magnitude, so $\lVert T_R\rVert=\lVert F_R^{c>1}\rVert$ and bounding the relocated ledger *is* bounding the frozen sector. No reindexing can supply that bound.

**Formal modules:** `RHLean.Proof.LowWheelFrozenCofactorTopBottomCancellation` and `RHLean.Proof.LowWheelFrozenCofactorTopImageHighPrimeObstruction`.

## 47. Saturated second-contact seam

Erasing the largest frozen-cofactor prime $q$ from the product-one face sends the predecessor face into the strict lower-scale annulus $X_R/q^2<P(V)\le X_R/q$, reversing the Boolean sign exactly once and so restoring the original frozen source sign. Injectivity is proved through ordered-Euler-cut uniqueness rather than circularly.

Which lower endpoint is used decides whether the seam closes. Subtracting the recursive Go law at both endpoints of one window cancels both completed anchors and both fixed lower-prefix columns, but the endpoint form requires the lower cutoff to be unfinished at its own owner — exactly the cube condition $q^3\le X_R$. On the natural $X_R/q^2$ carrier an unrestricted Mertens gap $M(q-1)-M(X_R/q^2)$ survives outside that gate: a terminal leaf of the original open problem rather than a descended one. Raising the endpoint to $\max(R,X_R/q^2)$ puts the image genuinely above the root, the owner then sits below the lower cutoff for free, the gate disappears and both anchors cancel at every prime owner below the root. The superseded theorems are kept as the recorded no-go.

The correct order of operations is also part of this seam: sum the complete signed owner windows first, then telescope their moving upper endpoints globally. Estimating owner by owner discards what the global Stokes form retains.

**Formal modules:** `RHLean.Proof.LowWheelFrozenSecondContactDescent`, `RHLean.Proof.LowWheelFrozenSecondContactWindowDescent`, `RHLean.Proof.LowWheelFrozenSecondContactWindowReassembly`, and `RHLean.Proof.LowWheelFrozenSecondContactGlobalTelescope`.

## 48. Parent-product seam

The frozen $q^2$ square residual becomes an honest Möbius object in four exact steps, none of which takes a norm. Each residual cofactor is reindexed by its unique owner, with the source-scale factor $\mu(A)$ kept **outside** the daughter sum because the primes below the old pivot are encoded there. Every $(A,d)$ in a daughter window is realized by a genuine ordered Euler cut with child $A\cdot d$, so the product carries the true weight $\mu(A)\mu(d)$, and for a fixed owner the product map is injective across *different* source scales. Flattening then gives a $(q,m)$ carrier, proved to lie in the post-root $q$-smooth strip, with the reverse inclusion proved constructively — Bertrand appearing only as a finite carrier-saturation device.

What comes out is not a residual at all. The reassembly identifies the *existing* historical matching fixed transport exactly:

$$
T_{\mathrm{match}}=F_{R^-}(X_R)+\sum_{q<R}F_{q^-}(R)-1 ,
$$

so after this seam no hidden source scale, interval-prime cube, or $q^2$ floor term is left in that transport.

**Formal modules:** `RHLean.Proof.LowWheelFrozenSquareResidualQ2Reindex`, `RHLean.Proof.LowWheelFrozenSquareResidualParentProduct`, `RHLean.Proof.LowWheelFrozenSquareResidualParentSurjectivity`, `RHLean.Proof.LowWheelFrozenSquareResidualRootFloored`, and `RHLean.Proof.LowWheelFrozenSquareResidualTransportClosure`.

## 49. Stable far-wall renewal seam

The outer far prime $p>R$ has zero $p^2$ daughter scale, so it is the wrong Euler coordinate to recurse on; the low cofactor $c<R$ still carries its complete squarefree history. Stripping $q=P^+(c)$ and splitting at the second-$q$ wall gives the raw far transport as $\mathrm{unitFace}-\mathrm{descendedMass}-\mathrm{crossingMass}$, with the descended half a literal far slice of the $q^2$ child transport.

What makes this a seam rather than a rewrite is that the return is a strict arithmetic descent. A crossing product is indexed by $(q,dp)$ and returns to low cofactor $d$; a second crossing strips the canonical largest prime of $d$, which is strictly smaller, and the second-contact load decreases strictly along compatible steps. The branch terminates at cofactor one, where the arithmetic is completely explicit: for a fixed far prime with $A=\lfloor X_R/p\rfloor$, the condition $qp\le X_R<q^2p$ is exactly $\sqrt A<q\le A$, so the incoming multiplicity is literally a prime count in a reciprocal interval.

The owner tag is retained throughout, because different owners may descend to the same state; forgetting it is permitted only with its exact multiplicity.

**Formal modules:** `RHLean.Proof.StableFarWallLowCofactorQ2Descent`, `RHLean.Proof.StableFarWallExactQ2Split`, `RHLean.Proof.StableFarWallRenewalDescent`, `RHLean.Proof.StableFarWallRenewalTerminalPrimeCount`, and `RHLean.Proof.StableFarWallUnitRenewalCentering`.

## 50. Mellin interpolation seam

The zero-factor raw law and the reciprocal Euler law are not two mechanisms. For any scalar weight with $w(cp)=z\,w(c)$, the exact raw pair law gives

$$
w(c)r_R(c)+w(cp)r_R(cp)=(1-z)\,w(c)r_R(c)+z\,w(c)\,\mathrm{Boundary}_R(c,p),
$$

so the parent coefficient is $1-z$. At $z=1$, that is $0$: the raw annihilation. For the Mellin weight $w_s(n)=n^{-s}$ one has $z=p^{-s}$, so $s=0$ recovers the raw annihilation and $s=1$ the reciprocal Euler factor $1-1/p$. The memory factor is therefore the endpoint difference of one multiplicative interpolation, and differentiating in $s$ necessarily produces the logarithmic prime weight $\log p$.

The companion law says the boundary is not lost in the change of coordinates: on a complete descending prefix both coefficient-mismatch ledgers vanish and $p\,(\mathrm{EulerNext}-\mathrm{RawNext})=(p-1)B_p$. The signed boundary is transported to the difference of the next states with exactly the Euler factor $1-1/p$.

**Formal modules:** `RHLean.Proof.PostRootPartnerMellinInterpolation`, `RHLean.Proof.PostRootPartnerEulerMemory`, and `RHLean.Proof.PostRootPartnerReciprocalCompression`.

## 51. Physical daughter seam

A physical $q^2$ hit carrier partitions disjointly by its actual least *odd* square-prime owner, so summing the genuine daughter over those fibres recovers the Mertens daughter exactly, at every cutoff and with no endpoint error. Prime $2$ is not a contact owner: it is base mod-four geometry, and its algebraic two-step remainder is kept explicit rather than folded in.

Everything after the parent recurrence is packaged, which is what makes the remaining hypothesis irreducible. Three subcritical coefficients are compiled: $(5/4)\cdot4\cdot(19/23)^2\cdot(1/4)$ with the prime-11 factor, $3\cdot(5/4)\cdot(1/9+1/25+1/49)$ on the exceptional owners alone, and $4\cdot(36/35)\cdot(17/72)=34/35$ from the sharp odd-owner budget with the Young split. The third needs no selected-prime observable, tensor substitution, frame mask, or extra Mertens hypothesis at all.

Crossing this seam requires the daughters to be *fully signed and fully reassembled* first. A frame estimate that squares the children before reassembling them is bounding a different object, and the package proves it is a different object.

**Formal modules:** `RHLean.Proof.PhysicalQ2BookkeepingSynthesis`, `RHLean.Proof.PhysicalQ2FourFrameTerminalSynthesis`, `RHLean.Proof.PhysicalQ2TerminalSynthesis`, and `RHLean.Proof.SignedTransportAmplificationAudit`.

## 52. Least-square ownership seam

Least-square ownership is local: $q$ owns a physical edge exactly when $q^2$ hits one of the six active affine forms and no smaller prime square does, with no ambient prefix in the statement. The super-orbit for $q$ contains the selected primes, every prime below $q$, and $q$ itself, so once the reserved square product exceeds one square block, $q$ cannot occur in the complete interior. Constructing a maximal feasible wheel turns that into a certificate, and since every physical square contact is odd, the only possible complete owners are $3$, $5$ and $7$.

The seam is deliberately not crossed at the observable. The blocker's signed mass still uses the selected-prime projection, while the true Möbius observable is what the recovery carrier needs; identifying the two requires a separate parity compensation, and the package keeps them apart so the remaining parent-side seam stays visible rather than being absorbed into a later norm.

**Formal modules:** `RHLean.Analysis.OutsidePrimeLeastSquareBlocker`, `RHLean.Analysis.OutsidePrimeLeastSquareMaximalWheelConstruction`, `RHLean.Proof.ExceptionalDeletionParentPartition`, and `RHLean.Proof.ExceptionalSignedPacketIdentification`.

## 53. Weight-one tensor seam

Multiplication by the prime-11 Euler sign has average $19/23$ on the $115$ zero-free residue classes, so every weight-one combination is multiplied by $19/23$ and its square by $(19/23)^2$. That upgrades to a deterministic tensor theorem: a complementary weight field on a modulus **coprime** to $11^2$ may vary arbitrarily and the complete product orbit still sees the same scalar. No independence assumption is used anywhere.

The limit of the seam is compiled alongside it, which is what makes it usable. The theorem permits an arbitrary field on a coprime complementary coordinate; it does not permit an arbitrary function of the same $11^2$ coordinate. And even on a retained cell, the selected-prime projection carries only the selected sign while the Mertens-visible observable carries the parity of every prime factor. Both distinctions are certified finitely, so neither can be hidden inside a later norm estimate.

The sharpest form is a refutation, not a caveat. On the complete aligned period the actual Möbius complement does not satisfy the weight-one factor: the actual and stripped coordinate masses are $-8$ and $-14$, so the observed one-period multiplier is $4/7$ rather than $19/23$. Crossing this seam with the recovered field therefore requires constructing a genuine coprime complementary coordinate, or an exact signed compensation that removes the correlation — substituting the recovered field into the tensor law is proved not to work.

One related identity belongs here for the same reason. The literal Go predecessor cube is not the full Mertens daughter until the high transport is retained, since $M(Y)=F_{q^-}(Y)-\mathrm{highTransport}(Y)$ and for owner $3$ the frozen Go piece can already be zero while the full Mertens child is nonzero. Any final action on this layer must preserve that signed compensation.

**Formal modules:** `RHLean.Analysis.ElevenWeightOneFirstMoment`, `RHLean.Analysis.FinitePrimeHigherWeightOne`, and `RHLean.Analysis.PhysicalRecoveredPrimeTensorCompatibility`.

## 54. Rough-seat seam

For a finite prime set $S$, adjoining a fresh prime is one multiplicative finite difference, $K_{S\cup\{p\}}(X)=K_S(X)-K_S(\lfloor X/p\rfloor)$, and the full signed wheel Fubini-reindexes before any norm into

$$
M(B)=\sum_{B/W<n\le B,\ (n,W)=1}\mu(n)\,K_S(\lfloor B/n\rfloor).
$$

Every overlap between exponentially many signed divisor bands is thereby collapsed into one integer coefficient on each physical rough seat, with no absolute value, density estimate or wheel-depth loss. That signed truncated kernel is then identified with the chronological frozen prime cube already used by the first-owner and Go machinery, so this is a bridge between existing coordinates rather than a new carrier.

**Formal modules:** `RHLean.Proof.PrimeWheelRoughSeatCorrelation`, `RHLean.Proof.PrimeWheelFrozenRoughSeatBridge`, and `RHLean.Proof.PrimeWheelProperSubwheelDepthTwo`.

## 55. Acceptance criterion for quantitative progress

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

Four further filters follow from the routes closed in this revision. A proposal that bounds the covariance by a count of surviving support must say why it escapes the linear frontier: the minimising pivot has frontier density $2/\pi^2$, so the capacity term stays quadratic even after the exact squarefree diagonal is subtracted, and the canonical downcross ledger has superlinear unsigned mass. A proposal that matches along state-dependent prime edges on a raw interval carrier must say what happens to the top-half primes, all of which have the single legal move $p\mapsto1$ and therefore force a fixed set of size at least $\pi(x)-\pi(x/2)-1$. A proposal that estimates the first-jump residual one first-jump prime, or one cofactor column, at a time is already refuted; the aggregate has to be recombined with the square-root-dense piece before any norm. And a proposal that splits a square-run covariance into a fixed-prime descended leaf plus an escape remainder must note that on a subdoubling run the leaf is empty, so the escape is the whole covariance and the split is circular.

Six further filters follow from the routes closed in this revision. A proposal that improves the post-root remainder exponent must say which Mertens exponent it moved, because the two are locked together by an unconditional factor of two. A proposal that computes a frame constant for the exceptional $q^2$ contacts must say why it is not bounding the assembled coefficient norm, which an exact finite witness separates from the recursive Mertens energy the induction consumes. A proposal that iterates finite-wheel band counting must beat the audited positive floor on the leading coefficient, which the $1-1/p^2$ per-prime gain does not. A proposal that enumerates the largest-prime stable defect must first note that its linear bound *is* the terminal seam, and that the cardinality route is dead by a full power. A proposal that uses the frozen second-contact window at its loose $X_R/q^2$ endpoint must handle the unrestricted Mertens gap that survives the cube gate; the saturated endpoint removes it for free. And a proposal that relocates the frozen top image into the high-prime population must note that the two are complementary rather than nested, and that the relocation is norm preserving in any case.

One filter is specific to the no-liberty seam. A proposal that closes the processed-seat route must produce the weight-preserving equivalence itself. Equal cardinalities on the two sides, a bijection that does not preserve signed weight, or an estimate on either population separately all leave the seam uncrossed, because what transfers the signed sum is the weight-preservation hypothesis and nothing weaker.
