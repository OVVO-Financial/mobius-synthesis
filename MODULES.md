# Principal modules

The standalone source lives under `RHLean/`, and the root module `RHLean.lean` imports every shipped module.

## Three-slot recovery and endpoint transfer

- `RHLean.Analysis.ThreeSlotMertensDegreeOneProjection`
  - encodes the 27 three-slot Möbius states;
  - proves the exact degree-one regrouping;
  - identifies `M(4K)` with the sum of the three signed coordinate projections.

- `RHLean.Arithmetic.PrimeWheelThreeSlotRecovery`
  - identifies each active coordinate with the canonical square-root-covered `R - 2H` slot field.

- `RHLean.Arithmetic.MobiusFourCellEndpointTransfer`
  - proves exact resummation of complete four-cells;
  - proves `|M(X) - M(4 * floor(X/4))| <= 3`;
  - transfers complete-cell estimates to arbitrary physical cutoffs.

## Recovered-wheel and analytic criterion

- `RHLean.Analysis.PrimeWheelRecoveredMertensCriterion`
  - identifies the recovered prime-wheel prefix with the ordinary Möbius prefix and analytic Mertens summatory function;
  - proves equivalence of the recovered-wheel, global Mertens-energy, and square-prefix energy criteria.

- `RHLean.Analysis.MertensEnergyRHForward`
  - carries the Mertens-energy bound through reciprocal continuation, zero-freeness, and completed-zeta reflection to the formal Riemann hypothesis statement.

## Collision geometry and exact defect reduction

- `RHLean.Arithmetic.PrimeSquareCollisionKernel`
  - proves exact adjacent-cell square-collision exclusion;
  - proves a square hit isolates its active slot;
  - for primes above $6$, proves the next active cell is a complete prime miss.

- `RHLean.Arithmetic.PrimeSquareCollisionCRT`
  - realizes distinct-prime square collisions as nine exact CRT label classes.

- `RHLean.Arithmetic.PrimeSquareCollisionInvolution`
  - keeps physical collision labels distinct from local exponent states;
  - defines the sign-flip involution algebra.

- `RHLean.Arithmetic.PrimeSquareCollisionPairingFrontier`
  - partitions a finite frontier into pairable, fixed, and mate-crosses-cutoff pieces;
  - proves exact pair cancellation;
  - proves the cutoff defect has cardinality at most three;
  - proves unit-bounded integer defect mass has absolute value at most three.

- `RHLean.Arithmetic.PrimeWheelCorrectedLocalFlip`
  - proves the actual corrected `R - 2H` field reverses sign under a genuine selected-prime exponent flip;
  - proves selected-prime square hits kill the corrected field exactly;
  - removes the fixed-point contribution and reduces the physical frontier to the explicit cutoff defect.

- `RHLean.Analysis.PrimeBoundaryDefectBridge`
  - defines `SquarePrefixCollisionDefectChain`;
  - proves any such chain gives `|M((n+1)^2-1)| <= 3(n+1)` and square energy at most `9(n+1)^2`;
  - proves a chain at every square stage implies the square-prefix and global Mertens-energy criteria.

## Canonical finite differences

- `RHLean.Arithmetic.PrimeCombFiniteDifference`
  - defines the unordered Möbius divisor-difference operator.

- `RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime`
  - proves the fresh-prime recurrence inside the old-prime fibre.

- `RHLean.Arithmetic.BooleanCubeFiniteDifference`
  - proves exact one-, two-, and three-coordinate finite-difference formulas for arbitrary Boolean support;
  - supplies the four-state second derivative and eight-state third derivative.

- `RHLean.Arithmetic.TruncatedBooleanCubeSecondToggle`
  - pairs a first-failure frontier in a second coordinate and leaves two explicit codimension-two corner types.

- `RHLean.Arithmetic.TruncatedBooleanCubeMaskedSecondToggle`
  - preserves an additional invariant mask during the second toggle, the form needed for residue fibres.

## Survivor finite differences, parity, and dyadic shells

- `RHLean.Proof.SurvivorPrimeFaceFiniteDifference`
  - applies generic Boolean finite differences to the actual survivor selector;
  - proves the exact `3-5` four-state and `2-3-5` eight-state survivor stencils;
  - bounds one two-pivot stencil by `2` and one three-pivot stencil by `4`.

- `RHLean.Proof.SurvivorResidueSecondToggle`
  - proves a second square-one prime preserves the residue-conditioned first-failure pairing;
  - at modulus `2`, reduces the high survivor mass to six explicit `3-5` corner sums.

- `RHLean.Proof.SurvivorDyadicStaticCancellation`
  - performs exact odd-parent and doubled-child cancellation before norms;
  - identifies parity residue `0` and `1` with odd and even cofactor channels.

- `RHLean.Proof.SurvivorDyadicActivityMismatch`
  - proves canonical source admissibility is invariant under adjoining prime `2` for odd cofactors and upper prime above `2`;
  - confines every nonzero dyadic pair contribution to three explicit geometric shells.

- `RHLean.Proof.SurvivorResidueCovarianceCriterion`
  - records the exact diagonal-plus-cross-covariance identity;
  - exposes the signed parity Gram and its cross-channel term before Cauchy--Schwarz;
  - isolates the remaining covariance-budget power-saving statement.

## Renewal, affine excursion, and square-wheel synthesis

- `RHLean.Analysis.MobiusRenewalTelescope`
  - proves the exact weighted renewal telescope for Mertens floor shifts.

- `RHLean.Analysis.MobiusRenewalSquareWheelSynthesis`
  - realizes the far-upper survivor reciprocal Mertens transform in renewal coordinates;
  - substitutes that exact realization into the synchronized primorial square-wheel zero-mode center;
  - was the synthesis-ledger revision-3 witness.

- `RHLean.Analysis.AffineExcursion`
- `RHLean.Analysis.PrimeSieveAffineExcursion`
- `RHLean.Analysis.PrimeSieveBackwardAffineExcursion`
- `RHLean.Analysis.PrimeSieveLipschitzExcursion`
- `RHLean.Analysis.PrimeSieveAbelTwoObligations`
  - provide exact affine-excursion and Abel-coordinate infrastructure for a quantitative contraction argument.

- `RHLean.Analysis.SquareRootTransportRealization`
  - realizes the original square-root transport identity and positive-smooth plus matched decomposition.

- `RHLean.Analysis.PrimeSievePNTCentering`
  - identifies the canonical nonzero square-wheel response as exact zero-mode centering of the Mertens summatory function.

## Square-root orientation, combined residual, and reciprocal form

- `RHLean.Analysis.SquareRootCombinedSignedResidual`
  - defines the combined signed residual $D_R$ channel by channel, before the cofactor sum, so the floor rounding and the prime-counting discrepancy are never separable;
  - proves $D_R=Q_R+E_R$, the two-term centering $T_R=T_R^{\mathrm{sm}}+D_R$, and the matched form;
  - proves the Gram identity, so centering changes no norm;
  - proves the combined RH-scale statement equivalent to the square-prefix criterion;
  - records the one-way triangle bound, to document what separating costs.

- `RHLean.Analysis.SquareRootBornSmoothReciprocalForm`
  - defines the rough lower-scale Möbius prefix $\mathrm{Rough}(q,B)$ and its window form;
  - proves the smoothness cutoff automatic on the born orientation;
  - proves the born-smooth reciprocal form and the unified signed sum for $A_R^{\mathrm{born}}-T_R$;
  - proves the exact main-term match, with the combined residual carried whole;
  - states the RH-scale target on the unified form and proves it equivalent to the square-prefix criterion.

- `RHLean.Analysis.SquareRootSmoothParityClasses`
  - proves the parity-class form of the complete smooth mass;
  - names the positive-orientation RH-scale statement;
  - proves that the matched criterion and the positive-orientation statement together bound the square-prefix Mertens Gram.

## Shallow reciprocal crossing and the post-crossing tail

- `RHLean.Analysis.SquareRootShallowReciprocalCrossing`
  - proves endpoint-parametric eventual crossing of the intact upper-middle packet at some reciprocal depth `K <= K_0`;
  - proves that depth is eventually below $C\log x_n$ for every $C>0$;
  - recovers the square geometry as the instance $x_R=R^2-1$, $y_R=R$, with the single numeric witness checked by `native_decide`.

- `RHLean.Analysis.SquareRootPostCrossingTail`
  - separates the raw transport tail from the coupled tail, which adds the complete square-root-smooth population;
  - proves the terminal identity $M(R^2-1)=\text{crossing residual}+\text{coupled tail}$;
  - proves a critical root-scale coupled-tail estimate equivalent to the square-prefix Mertens energy criterion.

- `RHLean.Analysis.SquareRootPostCrossingRenewal`
  - proves three exact normal forms for the coupled tail: a remaining-layer cap, an Abel form, and a lower-triangular renewal row;
  - identifies the packet layer with the negative cofactor-one prime face, so every admitted shallow layer cancels its prime diagonal exactly;
  - recombines both orientations into one signed Type-II cofactor-prime window mass in native reciprocal-prime coordinates.

- `RHLean.Analysis.SquareRootCanonicalRoughCovariance`
  - pushes the complete renewal row back onto the cofactor coordinate;
  - proves the coupled tail equals an explicit packet baseline minus $\sum_c\mu(c)\,\mathrm{Resp}(c)$;
  - exposes the remaining obligation as a literal finite correlation, and its centered mean/covariance form, between the Möbius parity field and one rough-prime response field.

- `RHLean.Proof.SquareRootTruncatedPacketEquivalences`
  - identifies the truncated upper/middle packet with the negative prime tail above the inverse cutoff and with the unresolved-source Möbius mass.

- `RHLean.Analysis.SquareRootMiddleSequentialCoherence`
  - composes the harmonic-layer, reciprocal-fibre, Abel, prime-dilate, and frozen-universe coordinates without replacing any of them, and records which reindexings are *not* contractions.

## Prime-count-free low-wheel transport

- `RHLean.Proof.LowWheelSurvivorInclusionExclusion` and `RHLean.Proof.LowWheelSurvivorFloorExpansion`
  - expand high-prime survivor frequencies over the low-prime Boolean cube and convert each multiplicity into an exact floor difference, removing the prime-counting function.

- `RHLean.Proof.LowWheelTransportTripleCarrier`
  - reduces the upper-prime transport to a signed sum over triples $(c,t,k)$ with weight $\mu(c)(-1)^{|t|}$ and two hyperbolic cutoff inequalities.

- `RHLean.Proof.LowWheelDoubleCubeTransport`
  - removes the cofactor-face truncation using the square-root geometry, placing both coordinates on the same full Boolean cube of primes up to $R$.

- `RHLean.Proof.LowWheelCanonicalPairingFrontier`, `RHLean.Proof.LowWheelCanonicalCofactorQuotientPairing`, and `RHLean.Proof.LowWheelCanonicalDefectReduction`
  - cancel every interior transport state by the canonical least-prime involution;
  - prove `transport = smooth - M(R) + canonicalDefect` and hence $M(R^2-1)=M(R)-\mathrm{canonicalDefect}$;
  - place every defect term on one adjacent multiplicative shell frontier.

- `RHLean.Proof.LowWheelSequentialPrimeWindows`, `RHLean.Proof.LowWheelSequentialRoughWindowFold`, `RHLean.Proof.LowWheelSequentialWindowTelescope`, and `RHLean.Proof.LowWheelSequentialSmoothRoughBoundary`
  - realize sequential low-wheel cells as reciprocal prime-dilate windows and expose the smooth/rough boundary form, where a fresh prime creates the reciprocal shell and an older prime coordinate collapses the interior of the remaining smooth cube.

- `RHLean.Proof.LowWheelDoubleFaceFiniteDifference` and `RHLean.Proof.LowWheelDoubleCubeSequentialFold`
  - supply the mixed second finite difference on the two sign coordinates and the sequential fold used by the savings argument.

## Strong Mertens corridor and reciprocal moments

- `RHLean.Analysis.StrongMertensLogNineCorridor`
  - reconciles the reciprocal-zeta estimate, the zero-free region, and the bounded-height zero-free box into one constant $A$ and one left boundary $\sigma_A(T)=1-A/(\log T)^9$.

- `RHLean.Analysis.StrongMertensZetaKernel`
  - supplies the reusable reciprocal-zeta kernel, handling the removable value at the pole by the residue limit.

- `RHLean.Analysis.StrongMertensLogNineContour`, `RHLean.Analysis.StrongMertensLogNineEnvelope`, `RHLean.Analysis.StrongMertensLogNineHorizontal`, `RHLean.Analysis.StrongMertensLogNineBounds`, and `RHLean.Analysis.StrongMertensSmallHeight`
  - carry out the residue-free contour pull, the five-leg envelope, and the boundary and small-height estimates on that shared corridor.

- `RHLean.Analysis.StrongMertensLogNineBalanceCore` and `RHLean.Analysis.StrongMertensLogNineBalance`
  - balance at $r=(\log X)^{1/10}$, $T=e^r$, $\varepsilon=e^{-(A/4)r}$, turning every envelope into an exponential decay in $r$.

- `RHLean.Analysis.StrongMertensSmoothing` and `RHLean.Analysis.StrongMertensSmoothingFinite`
  - contain the finite sharp-cutoff bridge, with no prime number theorem or reciprocal-zeta estimate used.

- `RHLean.Analysis.StrongMertensRecipMomentTransfer`
  - is the exact finite Abel bridge from $M(N)$ to the reciprocal logarithmic Möbius moments $A_m(N)$, with the two analytic facts kept as hypotheses.

## Centered K2 and the signed second Selberg kernel

- `RHLean.Analysis.K2CenteredFinite` and `RHLean.Analysis.K2CenteredClassicalInterface`
  - hold the finite Abel identities and the factor-four corollary, which is independent of the unknown centered constant.

- `RHLean.Analysis.K2RecipMomentAnalyticClosure`
  - removes the zeta pole, factors the reciprocal germ as $(s-1)q(s)$, and reads $(1/\zeta)''(1)=-2\gamma$ directly, leaving one explicit Abel-boundary target.

- `RHLean.Analysis.NativePNTSignedSecondSelbergReciprocal`
  - proves unconditionally that $K_2(n)=(\Lambda*\Lambda)(n)-\Lambda(n)\log n$ has only $O(\log N)$ reciprocal mass, removing a full logarithm from the constant mode.

- `RHLean.Analysis.NativePNTSignedSecondSelbergFactorFourBridge`
  - performs fresh-prime cancellation at a fixed physical product and calibrates the summatory shortcut exactly against $-2E(N)\log N$.

- `RHLean.Analysis.NativePNTNormalizedSignedRecurrence`, `RHLean.Analysis.NativePNTNormalizedReciprocal`, and `RHLean.Analysis.NativePNTNormalizedContinuity`
  - divide the signed first Selberg recurrence by the endpoint, giving a scale-free near-averaging law with an absolute remainder rather than a growing intercept.

## Corrected-conductor Gram

- `RHLean.Analysis.CorrectedConductorHighSectorGram`
  - splits the all-conductor raw boundary pairing by boundary divisor rather than conductor, keeping the whole cross-conductor interaction inside one Gram quantity.

- `RHLean.Analysis.CorrectedConductorSmallSectorBound`
  - proves the uniform packet bound $\lVert J_q(k,x)\rVert\le6q^3$, hence $O(R^4)$ for all nontrivial conductors $q\le R$, uniformly in the prefix length.

- `RHLean.Analysis.CorrectedConductorHighSectorCutoffError`, `RHLean.Analysis.CorrectedConductorHighCoreExpansion`, and `RHLean.Analysis.CorrectedConductorBoundaryDefectGeneral`
  - supply the cutoff error, the large expansion-point core form, and the general boundary defect law.

## Endpoint criteria and amplification

- `RHLean.Analysis.ThreeSlotDegreeOneCriterion`
  - names the squared $K^{1/2+\varepsilon}$ demand on the combined signed mode $W_a+W_b+W_c$ and proves it equivalent to the recovered-wheel, Mertens-energy, and square-prefix criteria.

- `RHLean.Analysis.NearestSquareEndpointDomination`
  - bounds the interior excursion of a complete square block by the larger adjacent endpoint plus one root-scale term, so arbitrary interior points cost only an explicit $2R^2$ baseline.

- `RHLean.Proof.SquareRootAmplificationClosure`
  - proves that a *fixed* absolute amplification constant in the square-root endpoint statement already implies the standard Mertens energy criterion; no subunit contraction is required.

- `RHLean.Proof.SquareRootCrossRegionAmplification`
  - reduces that endpoint amplification to fixed critical-envelope bounds on the two already-signed channels, without splitting the matched channel by distinguished prime.

- `RHLean.Proof.SquareRootLegalAncestryGramReduction`, `RHLean.Proof.SquareRootAncestryParentFibres`, and `RHLean.Proof.SquareRootAncestryExtensionWindows`
  - expand the square-root ancestry successor over parent fibres and generic prime-extension windows.

## Replacement fibres, ledger equivariance, and the T sector

- `RHLean.Proof.RecursivePrimeReplacement`, `RHLean.Proof.ReplacementFibreOrientationSplit`, and `RHLean.Proof.ReplacementFibreCofactorWindows`
  - give the recursive replacement row at a square endpoint and split each reciprocal fibre exactly into root and smooth orientations, with primes as the special face $c=1$.

- `RHLean.Proof.WheelToLedgerEquivariance` and `RHLean.Proof.WheelToLedgerPushforward`
  - prove that fresh-prime equivariance holds exactly on the ordered submove where the adjoined prime exceeds every prime in the parent core, and push the ancestry cross ledger forward to ordered wheel edges.

- `RHLean.Analysis.LargePrimeTTransport`
  - proves that a large prime $q>R$ over a cofactor $c<R$ creates no new Möbius zero and removes none, acting as a pure sign flip on the zero-free sector, and derives the finite eight-state consequences.

- `RHLean.Analysis.DeterministicTGreenKuboComparison`
  - proves the deterministic square expansion $T(K)^2=\mathrm{diagonal}(K)+2\,\mathrm{positiveLagPairs}(K)$ and isolates the aggregate positive-lag correlation as a named proposition rather than an axiom.

- `RHLean.Analysis.PhysicalDegreeOneLeastSquareChannels`, `RHLean.Analysis.PhysicalDegreeOneTransitionEstimate`, and `RHLean.Analysis.PhysicalDegreeOneMixingConjecture`
  - carry the exact three-slot physical transition pushforward and isolate the single remaining quantitative statement, weaker than full transition uniformity.

- `RHLean.Analysis.BalancedPrimeBilinearCentering`
  - proves the inclusion-exclusion form of the balanced coefficient and its exact five-piece centering against an arbitrary density.

- `RHLean.Analysis.OutsidePrimeDeletionMask` and `RHLean.Analysis.OutsidePrimeLeastSquareEndpoint`
  - isolate the outside-prime square deletion on complete CRT orbits exactly, with the selected signed degree-one observable kept intact.

- `RHLean.Proof.PrimeCombVisualizationDynamics`, `RHLean.Proof.PrimeCombVisualizationFrames`, and `RHLean.Proof.PrimeCombVisualizationRecurrence`
  - prove the frozen primorial universe identity and the ordered fresh-prime recurrence, keeping that finite-universe quantity distinct from the unrestricted Mertens function.

## Proved structural obstructions

- `RHLean.Analysis.SquareRootTransportTopFibreNoGo`
  - proves the top block of the transport transform equals its own cardinality, so it admits no internal cancellation;
  - proves the block nonempty by Bertrand, and exhibits it as an exact summand of the transport term.

- `RHLean.Analysis.PhysicalSquareCRTTransfer`
  - partitions the physical zero-free transition population into complete aligned CRT periods and the square-clock boundary, with the boundary defined as the literal incomplete-period cells.

- `RHLean.Analysis.PhysicalSquareCRTPeriodNoGo`
  - bounds the square-block transition window by $2R+2$ cells;
  - proves the complete-period core empty whenever the selected prime-square product exceeds that width, so the interior mass vanishes and the whole physical mass is boundary.

- `RHLean.Analysis.FinitePrimeTMixing`
  - records the exact finite-prime local count law and the weight-one Walsh multiplier used by the recombination layer.

- `RHLean.Analysis.SquareRootPrimeCountGap`
  - proves the exact signed count gap `middle - top = 2*pi(X_R/2) - pi(X_R) - pi(R)` between the middle-prime and inert-top populations, and records that its sign is a second-order prime-counting question which first-order PNT does not decide.

- `RHLean.Analysis.PrimeBoundaryCollisionQuotientNoGo`
  - refutes the strongest literal bounded collision-defect quotient: weighting every defect label by the corrected field on its own square-hit site forces every bounded chain mass to zero, contradicting the first nontrivial square prefix.

- `RHLean.Arithmetic.PrimeSquareCollisionPhysicalFibreNoGo`
  - proves the same for the literal physical collision-site fibre and closes the adjacent-cell escape for $p\ge7$.

- `RHLean.Analysis.SquareRootSmoothRenewalInstantiation`
  - proves the original square-root transport is one copy of the strict upper-prime Mertens transform, not the doubled proper-multiple prime-wheel mass, and records only that normalization and its obstruction.

## Research boundary and export guards

- `RHLean.Analysis.MobiusSynthesisBoundary`
  - contains the protected quantitative boundary types.

- `RHLean.Proof.TerminalAxiomAudit`
  - asks the kernel for the axiom dependencies of the theorems carrying the reduction to the Riemann hypothesis statement and pins the answer with `#guard_msgs`, so an added dependency fails the build.

- `boundary/frontier.json`
  - records the monotone quantitative frontier.

- `boundary/synthesis.json`
  - records exact cross-track synthesis advances; the refreshed export is at revision 5.

- `scripts/check_markdown_math.py`
  - rejects unsupported GitHub Markdown TeX delimiter forms outside code.

- `.github/workflows/markdown-math.yml`
  - runs that audit automatically on every push and pull request.

The quantitative frontier is unchanged: the missing theorem is still genuine RH-scale control of the signed Möbius field. The new modules sharpen the exact defect representation that must be bounded, remove the prime-counting function from the transport entirely, reduce the post-crossing obligation to one finite Möbius/rough-prime correlation, show that a fixed amplification constant already suffices, and close a further proposed route with a kernel-checked refutation.
