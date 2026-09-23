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

- `RHLean.Analysis.SquareRootFixedCrossing18349`
  - records the exact finite sign change of the reciprocal coefficient between depths $18348$ and $18349$;
  - combines it with the proved fixed-depth limit to pin the crossing at the single depth $18349$ for every sufficiently large endpoint, so every fresh prime processed after the crossing exceeds $18349$.

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

## Finite Othello parity and matching primitives

- `RHLean.Proof.FiniteOthelloMatching`
  - proves that a matching involution with at most one stable state bounds the signed mass of a finite region by one;
  - proves that two sign-reversing involutions on the same signed region have stable sets of equal signed mass, so the move order may be chosen freely;
  - contains no arithmetic, no asymptotic estimate, and no RH input.

- `RHLean.Proof.AlternatingSignMatchingParity`
  - supplies the alternating sign-matching parity invariant used by the Othello layer.

- `RHLean.Proof.FiniteLeastToggleDuality`
  - proves the least-coordinate toggle duality behind the canonical cofactor/quotient involutions.

## Processed-seat carrier and the two matchings

- `RHLean.Proof.SquareRootLowPrimeProcessedSeatCarrier` and `RHLean.Proof.SquareRootLowPrimeProcessedSeatMatching`
  - define the complete processed low-prime seat carrier and the sequential fresh-prime matching on it.

- `RHLean.Proof.SquareRootLowPrimeProcessedMatchingInvolution`
  - packages the entire fresh-prime chronology as one involution, pairing each state at the first stage that removes it and fixing the rest;
  - proves carrier preservation, involutivity, sign reversal on every moved state, and that the fixed set is exactly the iterated matching frontier.

- `RHLean.Proof.SquareRootLowPrimeDescendingPivotStability` and `RHLean.Proof.SquareRootLowPrimeOppositeFixedClassification`
  - play the same legal edges in descending fresh-prime order;
  - prove carrier preservation, involutivity, sign reversal, that the stable set is the descending processed-seat frontier, and that the stable mass is `squareRootLowPrimeRunningImbalanceReal` by finite cancellation on the full carrier.

- `RHLean.Proof.SquareRootLowPrimeNoLibertyBoundaryHome`
  - assigns canonical homes to the terminal no-liberty boundary and defines its signed weight.

- `RHLean.Proof.SquareRootLowPrimeNoLibertyFiniteEquiv`
  - states the weight-preserving interface at the seam between the stable processed-seat population and the tagged endpoint boundary, as a pointwise map between finite subtypes rather than a Finset equality, since the two live in different coordinate types;
  - packages the already-proved equality of the stable set with the descending processed frontier as a value-preserving subtype equivalence;
  - proves that any such equivalence transfers the whole signed sum, hence identifies tagged boundary mass with the running imbalance, and records that an injective weight-preserving classifier is enough for quantitative closure, the full equivalence being needed only when surjectivity is also available;
  - leaves the arithmetic construction itself as the open obstruction, over the four endpoint classes head, partial packet, born no-successor, and Go root equality. The individual branches are built in the processed-seat classifier section below.

## Low-prime running state, telescopes, and the matched frontier

- `RHLean.Proof.SquareRootLowPrimeRunningTelescope`
  - proves the exact real telescope for the low-prime running state and that composite cutoffs contribute no change.

- `RHLean.Proof.SquareRootLowPrimeGlobalEnergyTelescope`
  - proves the exact quadratic energy telescope over a whole fresh-prime interval;
  - records that a global energy decrement bound is *equivalent* to the terminal square bound, so assuming terminal control does not supply a dissipation proof.

- `RHLean.Proof.SquareRootLowPrimeMatchedFrontierBound`
  - bounds the real deep increments by the cardinality of the remaining owned response-matching frontier, with no raw response weight and no number-of-fresh-primes factor left.

- `RHLean.Proof.SquareRootLowPrimeMatchingFrontierSaturation` and `RHLean.Proof.SquareRootLowPrimeMatchingFrontierRootCharge`
  - prove fresh-prime saturation of the complete response matching frontier and its root-seat charge.

- `RHLean.Proof.SquareRootLowPrimeSmoothTransportRecoupling`
  - proves the terminal state equals $M(R^2-1)+\sum_{q\le R}M(q-1)$ minus the partial crossing packet and the near-root rectangle, whose combined norm is at most $R+K$;
  - proves conditionally that $\lVert\mathrm{Matched}_R\rVert\le 3R\sqrt K$ gives $T(P_R)^2\le 25R^2K$ and hence the signed response-child energy decrement;
  - does not assert that matched bound, and so introduces no new low-prime analytic obligation.

## Canonical low-wheel downcross and repeated-parent layers

- `RHLean.Proof.LowWheelOthelloDowncrossGeometry`, `RHLean.Proof.LowWheelOthelloOppositeMove`, and `RHLean.Proof.LowWheelOthelloRepeatedInvolution`
  - carry the canonical downcross Othello on a lightweight carrier, with the opposite move and the repeated-parent involution.

- `RHLean.Proof.LowWheelCanonicalDowncrossParentFibers`, `RHLean.Proof.LowWheelCanonicalDowncrossLatePairing`, and `RHLean.Proof.LowWheelCanonicalDowncrossLateCancellation`
  - fibre the canonical root-downcross frontier by parent and cancel the late-parent multiplicity exactly.

- `RHLean.Proof.LowWheelCanonicalRepeatedParentClassification`, `RHLean.Proof.LowWheelCanonicalRepeatedTerminalCutoff`, and `RHLean.Proof.LowWheelCanonicalRepeatedTerminalInternalMate`
  - classify repeated parents, split the terminal boundary exactly at the cutoff, and supply an existing physical mate for the internal part.

- `RHLean.Proof.LowWheelExternalTerminalParentSplit`, `RHLean.Proof.LowWheelExternalTerminalFaceLedger`, and `RHLean.Proof.LowWheelExternalTerminalEightRootBound`
  - partition the external high-prime grid by canonical downcross parent and reach square-root-scale external cancellation.

- `RHLean.Proof.LowWheelFullFaceQuotientOthello` and `RHLean.Proof.LowWheelLeastLargestOthello`
  - realize the full face/quotient involution and the least-prime/largest-prime Othello on the same physical transport carrier.

## The Go boundary layer

- `RHLean.Proof.SquareRootLowPrimeGoRecursiveDescent`, `RHLean.Proof.SquareRootLowPrimeGoTwoBoundaryShell`, and `RHLean.Proof.SquareRootLowPrimeGoBirthBoundary`
  - descend through the unique smaller prime owner and prove the stopping set is a genuine two-boundary shell terminating on the born first-failure boundary.

- `RHLean.Proof.SquareRootLowPrimeGoGlobalPartner`
  - embeds every strict crossing incidence $R<rq$ as a literal state of the global low-wheel transport carrier with weight $\mu(qd)$;
  - proves the canonical least-prime pivot lies in the parent, so the canonical toggle supplies an opposite-sign partner inside the transport identity without any estimate.

- `RHLean.Proof.SquareRootLowPrimeGoRootEqualityBoundary`
  - isolates the single uncovered incidence $rq=R$, charges it injectively to its parent coordinate $d<R$, and bounds its cardinality and signed Möbius mass by $R$.

- `RHLean.Proof.SquareRootLowPrimeGoCrossingMateLedger`, `RHLean.Proof.SquareRootLowPrimeGoFourthPowerCutoff`, and `RHLean.Proof.SquareRootLowPrimeGoWallPartnerReassembly`
  - record the strict crossing mates as an existing transport subledger, confine the second-boundary defect to the fourth-power owner band, and reassemble the literal first-owner wall with its partner.

## Creation-to-response energy

- `RHLean.Proof.SquareRootLowPrimeCreationResponseCarriers` and `RHLean.Proof.SquareRootLowPrimeCanonicalCreationResponseMap`
  - define the literal shallow-creation and deep-response carriers and the canonical fresh-prime map between them.

- `RHLean.Proof.CreationResponseFrontierCancellation` and `RHLean.Proof.CreationResponseOthelloInvolution`
  - prove exact creation-to-response frontier cancellation and present the matching as a finite Othello involution.

- `RHLean.Proof.SquareRootLowPrimeCanonicalCreationResponseEnergy`, `RHLean.Proof.SquareRootLowPrimeCreationResponseEnergyGate`, and the Eulerian and native gate variants
  - reduce the creation-to-response energy and state the dissipation gates it has to pass.

- `RHLean.Proof.SquareRootLowPrimeDeepResponseAtoms` and `RHLean.Proof.SquareRootLowPrimeResponseSeatAtomEquiv`
  - identify deep response weights as uniquely owned prime-extension atoms and the abstract unit seats as a literal enumeration of the born/post-root prime partners.

## Global Othello cancellation on a cumulative carrier

The sitewise Othello laws describe what one move does to one site. A cumulative
sum asks a different question, and these modules play the same laws on a whole
region at once, before any absolute value is taken.

- `RHLean.Proof.GlobalPrefixCarrierOthello`
  - defines the carrier toggle `tau_p`, an involution of the naturals whose moving states are exactly the `p^2`-free sites, where `mu (tau_p n) = -mu n`, and whose frozen states are exactly the square hits, which carry no Möbius mass;
  - proves that the signed mass of any finite region equals the signed mass of its escape part, so the whole interior cancels in mated pairs;
  - proves the same equality survives peeling a list of distinguished primes, leaving the iterated boundary;
  - states the scope honestly: this is a global *pairing* by two cycles of one fixed prime, not an alternating-component argument, and it contains no birth-to-capture cancellation.

- `RHLean.Proof.PrefixCarrierOthelloWalls`
  - identifies the escape part of the ordered prefix carrier `(L, x]` with exactly two walls, the anchor wall `n <= p*L` and the cutoff wall `x < n*p`;
  - records the honest single-prime population bounds for both walls, which are the quantities an iterated multiplicity theorem has to control rather than a saving in themselves.

- `RHLean.Proof.AdaptivePrimeMatching`
  - isolates the state-dependent notion the no-liberty architecture actually uses, in which the matching prime may depend on the state, and derives sign reversal rather than assuming it;
  - proves the raw prefix carrier `(0, x]` admits no liberty-exhausting mate, since every squarefree site has a legal move and such a mate would force `M(x)=0`;
  - proves every adaptive mate on `(0, x]` has fixed set of size at least `pi(x) - pi(x/2) - 1`, because all top-half primes compete for the single neighbour `1`;
  - is a negative control, not a template: it shows the processed-seat multiplicity is mathematically load-bearing.

- `RHLean.Proof.LifetimeRunCancellation`
  - proves the genuinely trajectory-based statement: an atom born after a run starts and captured before it ends contributes zero whatever its lifetime, since the activity increments telescope;
  - proves death is permanent on the actual active predicate, so the half-open interval model is faithful;
  - states the aggregate run identity in the existing `Active = Birth - Death` endpoint coordinates, and records that explicit birth and capture times are not constructed.

- `RHLean.Analysis.PrimeWheelRunOthelloBoundary`
  - rewrites the pinned primorial-wheel residual as the anchor wall plus the cutoff wall of its prefix carrier;
  - does the same for a whole consecutive run of complete square blocks, composing the known square telescope with the fixed-prime wall reduction;
  - proves that an iterated boundary of RH-scale population gives the Mertens energy criterion, so the remaining problem is a multiplicity bound on a run boundary rather than a statement about individual Möbius seats.

## Signed block covariance and the descent formulation

- `RHLean.Analysis.BlockCovarianceDecomposition`
  - proves `S^2 = E + 2X` for signed blocks, so cross-block coherence is pinned by the total mass and the block energy rather than free;
  - measures exactly what a magnitude-first step discards, namely twice the cross-covariance defect;
  - instantiates at the literal square blocks, giving the partition of the global integer-order covariance into within-block and cross-block parts on one carrier.

- `RHLean.Analysis.BlockCovarianceRefinement`
  - proves `E - Q = 2 sum_j C_j`, so proving the square-block energy is of RH scale *is* proving the aggregate within-block covariance is, and the measured linearity must not be promoted;
  - proves each refinement step moves energy into children plus an explicit signed cross term, with the leaf energy exactly the linear squarefree diagonal;
  - proves a post-root prime family is an isometric copy of a lower-scale prefix for pair covariance, since multiplication by `p` reverses family mass but preserves `mu(pc)mu(pd) = mu(c)mu(d)`.

- `RHLean.Analysis.MertensCovarianceDescent`
  - states the one-sided positive-lag frontier as a descent on the signed aggregate covariance itself, and proves that forbidding a minimal supercritical excursion gives the Mertens energy criterion;
  - proves the sharper support bound `C <= (F^2-Q)/2` once the lag-zero diagonal is kept, and records that it is still quadratic;
  - separates the false Mertens threshold `C > Z/2` from the RH threshold `C <= x^(1+o(1))`, and records that support exhaustion alone cannot close the argument.

- `RHLean.Analysis.SquareRunEscapeCovariance`
  - states the seam at run level, where a uniform bound on every consecutive complete-square run finishes the wheel by deterministic bookkeeping;
  - proves the exact window Green--Kubo identity and splits the covariance into a descended part and an escape remainder, exactly for any proposed descended part;
  - proves that a nonpositive descended part together with RH-scale escape covariance gives the global Mertens energy criterion;
  - records what the escape part must contain, in particular the cross-square-block pairs any narrower descended part leaves behind.

- `RHLean.Analysis.SquareRunTopEscapeClassification`
  - proves that on a subdoubling run, stripping a prime from a physical endpoint sends it strictly below the run anchor, so a first-owner pair is necessarily a boundary cube and the same-prime negative leaf is empty;
  - concludes that the natural fixed-prime descended leaf contributes exactly zero on precisely the windows where the frozen-prefix mechanism applies, and that an RH-scale bound on the resulting top escape is equivalent to the Mertens energy criterion.

- `RHLean.Analysis.SquareRunFreshPrimeCubeBoundary`
  - proves the unique fresh-prime owner cube of a subdoubling run always straddles both run boundaries, so four-corner cancellation is genuinely nonlocal in square time and the run does not decompose into complete interior cubes.

## Frozen square runs and the canonical downcross frontier

- `RHLean.Arithmetic.DyadicFrozenPrefix` and `RHLean.Analysis.FrozenSquareRunKernel`
  - package the subdoubling identity in the divisor coordinate: on a run with `(b+1)^2 <= 2a^2`, the signed frozen kernel $K(a,b)=\sum_{d<a^2}\mu(d)\,w_{a,b}(d)$ is exactly the negative new Möbius mass, and no value of `mu` created inside the run appears in it;
  - square the whole signed divisor sum rather than any term of it, and prove the resulting criterion equivalent to the global Mertens and wheel criteria through a three-quarter anchor recurrence.

- `RHLean.Analysis.FrozenSquareRunDowncrossBridge`
  - proves the fresh-prime window law `W_{S+p}(A,B) = W_S(A,B) - W_S(A/p, B/p)`, so a new Euler prime contributes one compressed predecessor-cube window rather than an independent copy of a parent;
  - combines the frozen kernel with the canonical endpoint involution `M(R^2-1) = M(R) - D_R` to give `K(a,b) = (M(a)-M(b+1)) + (D_{b+1}-D_a)`, whose Mertens gap costs at most the root interval length;
  - proves the resulting difference-only statement equivalent to the frozen-square-run, global Mertens-energy, signed square-run, and primorial-residual criteria;
  - applies exact late-parent cancellation at both endpoints, so the difference is literally that of the canonically oriented Euler first-crossing ledgers.

- `RHLean.Proof.LowWheelCanonicalOrientedFrozenFibres` and `RHLean.Proof.LowWheelCanonicalOrientedRunFibres`
  - identify the Boolean faces charging one oriented state with the frozen faces of the old prime universe below its canonical pivot, so a state's signed face mass is one frozen predecessor-window mass;
  - regroup both run endpoints onto a common state carrier in which each state keeps the same canonical owner and only its two window endpoints move with the root.

- `RHLean.Proof.LowWheelCanonicalSqrtDenseContraction`
  - proves that a face of product at most `R` that is triply predecessor-dense above `sqrt R` has every coordinate at most `sqrt R`, so the dense part of a frozen window collapses exactly onto the smaller Boolean cube;
  - proves a first jump above `sqrt R` admits no later prime coordinate at all, so the first-jump residual is an exact one-dimensional high-prime ledger with a completed lower-scale Mertens gap at each prime.

- `RHLean.Proof.LowWheelCanonicalDowncrossBoundaryMultiplicity`
  - proves boundary multiplicity: the faces charging one boundary state are carried injectively into a single state-dependent integer window, so a state's whole ownership set is one interval;
  - proves at most `R` of the $2^{\pi(R)}$ faces carry any downcross mass, and gives the first unconditional inequality on the ledger norm;
  - proves the unsigned ledger mass already dominates `pi(R^2-1) - pi(R)` at the empty face alone, so no bound of the shape `C*R` can be reached by discarding signs.

- `RHLean.Proof.SquareRootCanonicalDowncrossFinalSeam` and `RHLean.Proof.SquareRootCanonicalOrientedEpsilonBound`
  - name the quantitative proposition at the seam and prove it implies the square-prefix energy criterion and the native formal Riemann hypothesis theorem;
  - record that the linear form $\lVert D_R\rVert\le CR$ is strictly stronger than RH needs, since it would give the strong Mertens bound, and state the correct $1+\varepsilon$ seam instead;
  - reindex the faces charging one physical state by the squarefree integers of a single interval, which is the dependence-aware replacement for treating limiting Möbius frequencies as independent local probabilities.

## Reciprocal Euler compression on the canonical rough carrier

- `RHLean.Proof.LowWheelCanonicalRepeatedExternalTerminalMassBridge`, `RHLean.Proof.LowWheelCanonicalRepeatedMassReduction`, and `RHLean.Proof.LowWheelCanonicalRepeatedMovableCancellation`
  - record the prime-deletion Hall obstruction, put the centered rough covariance numerator on a sequential Euler-prime carrier, and open the parent/child difference into the loss, order-threshold and birth channels;
  - prove the late-parent downcross ledger vanishes exactly, leaving only the canonically oriented first-crossing ledger.

- `RHLean.Proof.CanonicalRoughReciprocalCompression`
  - transports the native square-prefix mechanism onto the RH-critical carrier: $v_R(c) + v_R(cp) = (1-1/p)\,v_R(c) + \mu(c)/(cp)\,(T+E-B)$;
  - proves the Euler factors accumulate exactly on the two-prime Boolean square, the finite model for a chronological descending compression.

- `RHLean.Proof.CanonicalRoughDefectLedgerBound`, `RHLean.Proof.CanonicalRoughManyPrimeContraction`, `RHLean.Proof.CanonicalRoughQuantitativeContraction`, and `RHLean.Proof.CanonicalRoughFiniteAbelReturn`
  - inject each of the three signed channels into an explicit reciprocal window, giving the first global estimate on `T`, `E` and `B`, and say plainly that the triangle inequality it uses is the step the record advises against;
  - iterate the same law over an arbitrary ascending chain, collapsing the Boolean cube onto its base with the complete Euler product attached and the defect bounded by an explicitly summed ledger;
  - return from reciprocal prefixes to the unweighted numerator by exact finite summation by parts, so the reciprocal weight costs only an absolute constant.

- `RHLean.Proof.CanonicalRoughCriticalCorrelationContraction` and `RHLean.Proof.CanonicalRoughCriticalDefectWindows`
  - recouple the zero mode, so the *uncentered* correlation `Corr_R = M(R-1) - M(X_R)` obeys the same defect law, and iterate on the actual compressed parent carriers with an explicit transported survivor ledger;
  - sharpen the scaled defect floor to the norm of one signed reciprocal Möbius boundary sum, keeping the `T/E/B` signs coupled, and prove a post-root fresh prime supplies no new contraction.

- `RHLean.Proof.CanonicalRoughCompleteSubrootDefectReduction`
  - proves the threshold-loss channel literally empty on a complete sub-root Euler cube, sending top escapes strictly beyond the root and births strictly below it, so the critical signed boundary is exactly post-root top escape minus lower-root birth.

- `RHLean.Proof.CanonicalRoughTruncatedWheelDefectTelescope` and `RHLean.Proof.CanonicalRoughTruncatedWheelManyPrimeTelescope`
  - identify one physical defect shell, with its native `1/p` restored, as the discrepancy between the true next truncated Euler cube and the uniform Euler contraction;
  - telescope those discrepancies over an arbitrary descending prime list to the single final truncated-wheel boundary, a structural identity in place of the earlier majorant.

- `RHLean.Proof.CanonicalRoughBoundaryProfileAbelReturn` and `RHLean.Proof.CanonicalRoughColumnAbelBridge`
  - prove the unweighted physical columns produce a prime-weighted discrete boundary variation, not one terminal boundary, and close it by finite Abel summation into the primitive $\sum_{n<K} B_n(X) - K\,B_K(X)$;
  - identify the column aggregate with that primitive over both a full prime prefix and a half-open band, and state precisely why these columns are still canonical rather than physical.

- `RHLean.Proof.CanonicalRoughAdaptiveCriticalCompression`, `RHLean.Proof.CanonicalRoughAdaptiveLargestPrimeElimination`, `RHLean.Proof.CanonicalRoughAdaptiveRawAnnihilation`, `RHLean.Proof.CanonicalRoughAdaptiveWeightedEulerCompression`, and `RHLean.Proof.CanonicalRoughAdaptiveWeightedIteration`
  - delete only the paired child copy, so no survivor mass is frozen and every still-unpaired state stays available to later prime coordinates;
  - prove a descending schedule leaves no nontrivial squarefree survivor, and that the unweighted critical correlation annihilates with coefficient zero rather than an Euler factor;
  - isolate the coefficient mismatch created by a missing commuting-square corner as the only obstruction to transporting an Euler coefficient, and iterate to a chronological formula with two signed ledgers and no frozen survivor.

## The complex vertical line and its Green--Kubo coordinate

- `RHLean.Proof.OrderedEulerCutProjection`
  - keeps one tagged occurrence intact and projects it simultaneously to its low face product, crossing prime, rough cofactor, parent and child integers, and half-open root lifetime;
  - proves membership in the oriented tagged boundary at root `R` is exactly one interval condition, so an atom can be followed through all roots without rebuilding its sign or factor coordinates.

- `RHLean.Proof.ComplexVerticalIntervalEulerBridge`
  - reindexes the signed mass of the squared vertical factor strip and proves it exactly equal to the canonical oriented Euler run ledger, to the canonical defect ledger, and to the signed prefix lifetime residual;
  - states the energy proposition as an open `Prop` and proves it equal to the pre-existing oriented-run seam, so the coordinate change introduces and hides no estimate.

- `RHLean.Proof.ComplexVerticalFiberSpacing`
  - formalizes the arithmetic geometry of one squared Fermat vertical fibre: terminal residue classes, the quadratic finite-difference law, quadratically growing Euler displacement, uniqueness of the active cut at one root, charge agreement between two representations, and the impossibility of two successive pivot transitions on a subdoubling run.

- `RHLean.Proof.ComplexVerticalLineGreenKubo`
  - defines one real event variable per physical child integer, zero for unchanged status and $\mp\mu(n)$ for birth and death, whose sum is the vertical-interval mass;
  - proves the finite Green--Kubo identity $\lVert V\rVert^2 = D + 2C$ and the unconditional one-sided inequality, so the diagonal is already at root-square scale and only the positive aggregate line covariance can be supercritical;
  - proves a completely stable prime family has exactly the lower-prefix covariance, so prime-stable covariance is recursive rather than new.

- `RHLean.Proof.ComplexVerticalLineSquarefreeDiagonal`
  - proves the active-child carrier is exactly the squarefree shell $\{n : R < n < R^2\}$, with a constructive converse;
  - identifies fresh-prime membership instability with exactly two physical walls, birth and top escape, so the line-event mask carries no further instability population;
  - sharpens the diagonal from the envelope `1` to `mu(n)^2`, using the limiting zero density only in the safe direction.

- `RHLean.Proof.SignedPrefixEventLifetime`
  - puts arrival and completion on the common physical-state carrier and telescopes the run one root at a time through the lifetime theorem;
  - proves the resulting residual is exactly the canonical oriented run difference, and states the corresponding energy bound as an open `Prop` equal to the already-exposed seam.

## First-jump residual and its recombination

- `RHLean.Proof.FirstJumpPrimeSliceObstruction`
  - proves the fixed first-jump-prime input is too strong: for `R/2 < p` the packing factor is `1`, yet the canonical `p`-slice stays live under every later owner in `(p, (R^2-1)/p]` and aggregates to the negative cardinality of that interval.

- `RHLean.Proof.GlobalFirstJumpCofactorCompression`
  - expands every statewise first-jump residual on one common low-cofactor carrier by choosing the fresh coordinate `2`, then swaps to global cofactor columns by finite Fubini;
  - retains the proposed column estimate only as a diagnostic conditional, and proves the exact correction instead: the first-jump aggregate must be recombined with the square-root-dense piece before any norm, and the recombined scalar is the canonical defect ledger.

- `RHLean.Proof.GlobalFirstJumpCriticalCorrelationBridge`
  - proves a uniform reciprocal-prefix bound of size $(\log R + 1)/R$ gives the root-scale bound on the recombined canonical defect, with no first-jump-prime or cofactor-column norm inserted anywhere;
  - subtracts the post-root prime families from the global positive-lag pair sum on a reciprocal-band carrier, identifies the total family covariance with an energy difference, and shows the exact remainder is the Bessel defect, so a linear remainder statement and a linear Bessel bound are the same hypothesis;
  - promotes the first-separation owner on the quadratic carrier: the owner of a pair strictly decreases under stripping, the parent's fresh-prime set is the owner erased from the child's, and a physical pair is one mixed corner of its owner's fresh-prime square, so stripping the owner reverses the pair weight exactly.

- `RHLean.Proof.EndpointCubeAnalyticClosure`
  - carries the endpoint-cube product packing down to the lower scales verbatim;
  - realizes the post-root family subtraction on literal pair carriers, proving that two distinct post-root primes cannot divide a common physical site and hence that distinct family pair carriers are disjoint, so the scalar subtraction is a genuine partition rather than an inclusion-exclusion estimate.

- `RHLean.Proof.PrimeCombReciprocalBandCancellation`
  - packages the one-prime post-root score law on the reciprocal quotient bands, on which every prime shares a quotient, a seat set, a signed cofactor channel and a score correction;
  - proves a complete post-root prime family is an exact sign-reversed copy of the completed lower prefix, and computes the adjacent-band finite difference $D(z+1)-D(z) = -2\mu(z+1)$.

- `RHLean.Proof.VanishingTransitionRelevanceBase`
  - measures a transition support on the linear scale of the square block and proves that vanishing relevance forces the normalized square-block discrepancy to vanish, leaving the construction of the genuine severed support as a separate input.

## Viole clock and sequential Euler closure

- `RHLean.Analysis.VioleClockSignedHistoryBudget`
  - packages the exact propagation budget in which strong induction supplies the new slope on proper reciprocal quotients, the old tail supplies the transition strip, and only the finite history remains signed;
  - analyses the subdoubling seed, where the recursive and transition ledgers vanish and the seed clause is therefore equivalent to the desired endpoint contraction, so the new arithmetic input has to enter before this consumer.

- `RHLean.Analysis.VioleSequentialEulerClosure`
  - proves that when one wheel cutoff resolves both endpoints the signed Selberg remainder disappears and the whole discrepancy is one explicit Euler forcing;
  - gives the direct block form `D = -(protected block correlation + (L-M))`, so the endpoint update is `E(L) = E(M) - P` with complete energy change `P^2 - 2E(M)P`;
  - expands the shared reciprocal drift atom by atom, where adjoining one fresh prime obeys the same Möbius cancellation law with an exact positive absolute surplus.

## Survivor and processed-response bridges

- `RHLean.Proof.SquareWheelSurvivorProcessedResponseBridge`
  - partitions the endpoint survivor population before any norm into the matched orientation and the complementary positive orientation, and maps the matched part with owner in the processed window into the processed-seat atoms, preserving cofactor, partner and signed weight pointwise.

- `RHLean.Proof.SquareWheelSurvivorOwnerResidual`
  - splits the survivor carrier into the processed-compatible sector, the owner-window residual and the positive orientation, so the signed mass of the positive orientation is a dependent coordinate rather than a carrier needing its own bridge;
  - proves the above-cutoff sector has cardinality at most `R` by the near-root rectangle.

- `RHLean.Proof.SquareWheelSurvivorShallowBridge`
  - transports the shallow sector with `K < c` into the creation carrier through the existing equivalences, and proves that on the bounded core `c <= K` the correct bridge is a signed mass identity whose only discrepancy is the already-existing partial crossing packet.

## Processed-seat classifier branches

The no-liberty seam has one outstanding *construction*, and these modules build
it branch by branch. Each proves membership, injectivity and exact weight
preservation for one target class, or removes one branch of the source
dichotomy outright.

- `RHLean.Proof.SquareRootLowPrimeProcessedCreationResponseInvolution`, `RHLean.Proof.SquareRootLowPrimeProcessedCreationResponseFixedClassification`, and `RHLean.Proof.SquareRootLowPrimeCanonicalMatchingInvolution`
  - conjugate the canonical creation-to-response matching onto the exact processed-seat universe, so both Othello moves act on the same carrier;
  - classify the three kinds of fixed state of the first involution, and package the quantitative canonical matcher as the second involution whose fixed set is the canonical Euler terminal frontier.

- `RHLean.Proof.SquareRootLowPrimeStructuralKey` and `RHLean.Proof.SquareRootLowPrimeCreationResponseStructuralKey`
  - isolate the key $(\gcd(c,K!),\ \text{seat})$ preserved by every fresh-prime extension, hence by both involutions, so every alternating component lies in one key fibre.

- `RHLean.Proof.SquareRootLowPrimeShallowProcessedCreationEquiv` and `RHLean.Proof.SquareRootLowPrimeDeepProcessedSeatBridge`
  - prove the shallow non-head processed carrier is canonically the tagged creation carrier and the deep non-head part is definitionally the owned response-seat universe, with no finite-cardinality choice used.

- `RHLean.Proof.SquareRootLowPrimeHeadClassifierBranch`, `RHLean.Proof.SquareRootLowPrimePartialEndpointCarrier`, `RHLean.Proof.SquareRootLowPrimeBornSeatPartnerEmbedding`, and `RHLean.Proof.SquareRootLowPrimeBornExitClassifierBranch`
  - record the Head branch outright; isolate the `Partial` branch on the sign-homogeneous compressed carrier, proving the `mu(c)=1` side condition rather than assuming it and reducing the branch to one named budget stated so no downstream file can discharge it by an arithmetic encoding;
  - build the seat-index to prime-partner coordinate change for the born home and prove it exactly weight preserving, then supply the `BornExit` membership, injectivity and weight preservation from the literal response atom.

- `RHLean.Proof.SquareRootLowPrimeNonBornFalloutResponseTail` and `RHLean.Proof.SquareRootLowPrimeResponseReentryBirthWitness`
  - remove the product-wall branch of the first-owner fallout entirely by the arithmetic of the schedule cutoff, so the unclassified seats are the parent/child response-window difference the tree already decomposes;
  - prove a non-born seat can evade its first owner only by forcing a strictly larger newly born prime, so the owner prime strictly increases and the ascent cannot cycle, with the re-entry window bounded by the birth boundary it creates.

- `RHLean.Proof.SquareRootLowPrimeSquareDefectCarrierCause` and `RHLean.Proof.SquareRootLowPrimeStructuralEndpointNormalization`
  - reduce the outward four-corner square defect on this carrier to exactly two boundary events, a hyperbolic endpoint crossing or a seat-count crossing, with no interior residual;
  - turn the displacement-owner obstruction into a well-founded normalization that shortens the schedule and preserves the canonical key.

- `RHLean.Proof.SquareRootLowPrimeFixedPartialPacketResidual` and `RHLean.Proof.SquareRootLowPrimeFixedBoundaryBudget`
  - certify that at the fixed reciprocal depth the compressed partial packet has fewer than $21$ unit cells uniformly in `R`, and assemble the target-side budget $3R+21$ over the four homes;
  - improve only the target side, and neither assume nor manufacture the still-open source-to-boundary classifier.

## Mertens tracking: the terminal obstruction

- `RHLean.Proof.SquareRootLowPrimeNearRootRemainder` and `RHLean.Proof.SquareRootLowPrimePacketFreeMassTransfer`
  - prove the above-cutoff response collapses to the negative near-root remainder, a nonnegative sum of post-root prime prefix counts over the near-root primes;
  - prove the partial packet occurs once on each side of the mass-transfer identity with the same sign, so it cancels and the remaining statement is packet-free.

- `RHLean.Proof.SquareRootLowPrimeMatchedCoreBound` and `RHLean.Proof.SquareRootLowPrimeMatchedCoreMertensObstruction`
  - state the branch target with no fixed constant, in a full-norm and a real-part form, the second being the minimal hypothesis for the terminal imbalance;
  - identify the matched core exactly as `M(R^2-1)` minus one literal positive-orientation middle source mass, reindexed to a canonical source carrier, and decline to assert that bounding it is equivalent to a standalone bound on `M(R^2-1)`.

- `RHLean.Analysis.SquareRootMatchedDegreeOneRecovery`
  - keeps the Mertens-visible correction inside the norm: with $H_R=\sum_{p\le R}M(p-1)$ the orientation split reads $M(R^2-1)=\mathrm{matched}_R-H_R$, so the matched-channel target alone is not the bound the square-prefix or three-slot criterion consumes;
  - bounds the terminal low-prime state against the Mertens sample by $R+K$, and against the complete four-cell degree-one sample by $R+K+3$, as recovery estimates rather than bounds on the amplitude;
  - retains $-H_R$ inside the norm in the final equivalence, assuming no separate bound on either term.

- `RHLean.Proof.SquareRootMertensMiddleTracking`, `RHLean.Proof.SquareRootMertensPositiveTracking`, and `RHLean.Proof.SquareRootMertensAncestralTracking`
  - state the terminal proposition in literal real and integer coordinates and compose it in one theorem to the terminal real imbalance;
  - record that $M(R^2-1) - A_{\mathrm{pos}}(R)$ is *exactly* the matched channel, so the tracking hypothesis is literally the matched-channel bound and reaches the terminal imbalance at $CR + R + K$ rather than $(C+8)R + K$;
  - record why bounding the two terms separately would not help: it would force $M(x) = O(\sqrt x)$, so the content is entirely in the correlation between them.

## The unconditional forward consumer

- `RHLean.Proof.TerminalMertensReduction`
  - proves the reduction from the projected-renewal Gram form down to $\lVert M(x)\rVert^2 \le C(x+1)^{1+\varepsilon}$ outright, with no criterion, realization, partition or low-increment control supplied by the caller;
  - separates the two directions of the classical criterion by their analytic requirements, and records that only the forward direction is used.

- `RHLean.Proof.TerminalMertensForward`
  - constructs that forward direction internally from the Dirichlet series for $1/\zeta$, partial summation, the identity theorem and the completed-zeta reflection, with no contour shifting or zero-free region;
  - records the resulting unconditional implication from the square-prefix energy estimate to Mathlib's Riemann hypothesis, which is the terminal analytic consumer for the arithmetic project;
  - proves the first global consequence of the fresh-prime rough-partner boundary law: along one ancestry chain signed boundaries telescope to endpoint capacities, and after root crossing the positive loss mass telescopes on its own.

## The post-root covariance record process

- `RHLean.Proof.PostRootCovarianceGlobalExponentTransfer`
  - proves `E(W) <= M(W)^2 / 2` unconditionally, because both terms subtracted in the Bessel identity are nonnegative, with no cancellation, record hypothesis or sieve;
  - turns every compiled reduction into one equivalence class: the power remainder, the power envelope, the record-excess statement, the falling finite-difference statement, the Mertens square envelope, and the Mertens energy criterion;
  - reads the same line quantitatively as an exchange rate — Mertens exponent $\theta$ gives remainder exponent $2\theta$, and the bootstrap gives the converse — so no work inside the record machinery can move one without the other;
  - improves the unconditional *constant* instead, to $E(W)\le 9(W+4)^2/32$, since one quarter of every block of four is not squarefree.

- `RHLean.Proof.PostRootCovariancePowerEnvelope`, `RHLean.Proof.PostRootCovarianceRowEnergy`, and `RHLean.Proof.PostRootMertensSquareFiniteDifference`
  - define the finite-horizon envelope and its one-step innovation, bound a single row by the preceding Mertens square, and restore the linear coordinate of the falling energy while keeping the family energies signed.

- `RHLean.Proof.PostRootCovarianceRecordAbsorption`
  - splits the innovation budget into a physical outer row and a square-wall departure *without* a triangle inequality, because the two have disjoint support: at a prime-square endpoint the physical row and the inherited row total both vanish, and away from one the departure vanishes;
  - proves a positive record at `N` forces `envelope(N) * N^ε < innovation(N)`, a full endpoint power stronger than naive localization, with the gain coming from the record hypothesis rather than an absolute value;
  - bounds the whole normalized departure sum unconditionally from `p^2` sparsity alone, and proves a summable record-conditioned envelope reaches the protected Mertens energy criterion;
  - records that the record indicator is load-bearing: dropping it leaves a positive part whose normalized sum is not expected to converge.

- `RHLean.Proof.PostRootCovarianceRecordSquareCharge` and `RHLean.Proof.PostRootCovarianceRecordSquareChargeClosure`
  - cancel the diagonal squares exactly by fresh-prime transport, so twice the outer row is a difference of discrete Mertens-square increments, and integrality at a record converts that into a one-sided charge against the cumulative square gap;
  - supply the complementary low case, giving an exhaustive record-step dichotomy with no family norm, prime count, or cancellation hypothesis.

- `RHLean.Proof.PostRootCovarianceLcmBoundary`, `RHLean.Proof.PostRootCovarianceLcmBoundaryClosure`, and `RHLean.Proof.PostRootCovarianceLcmInteriorPacking`
  - keep the full pair geometry rather than the many-to-one parent map, splitting the remainder by whether the squarefree pair cube fits below the endpoint, with the pair lcm as the intrinsic cube coordinate;
  - prove that stripping the chronological first separating prime scales the pair lcm exactly by that owner, turning the super-endpoint carrier into a literal first-wall-crossing problem;
  - aggregate the product packing of all removed interiors.

- `RHLean.Proof.PostRootCovarianceWheelCounting`, `RHLean.Proof.PostRootCovariancePrimeWheel210Scratch`, and `RHLean.Proof.PostRootCovarianceUnconditionalDecayScratch`
  - improve the finite-wheel constants at 6, 30 and 210 and audit their iteration, proving where the method stops: density contracts by $1-1/p$ but the extra child intervals cost $1+1/p$, so separate-band counting gains only $1-1/p^2$ and its leading coefficient has a positive floor;
  - pull two unconditional facts back onto the current carrier — the odd dyadic-annulus representation, worth a factor of nine on the quadratic constant, and the compiled strong Mertens estimate, which gives a genuinely subquadratic upper envelope against an elementary lower bound of order $-W^{3/2}$.

## The stable far-prime wall and its renewal

- `RHLean.Proof.StableFarPrimeWallTransport` and `RHLean.Proof.StableFarWallOwnedCensus`
  - expose the wall in three exact classical coordinates — the low-cofactor Mertens fibre at each far prime, an inert positive top-half block against the lower fibres that must cancel it, and the complementary term in the all-integer renewal telescope — retaining `M(X_R)` explicitly so the classical seam is identified rather than hidden;
  - put the unit face and both owned images on one carrier, where injectivity across both populations makes `UnitFace - InternalMate - TopImage` the negative Möbius mass of a single disjoint integer carrier.

- `RHLean.Proof.StableFarWallLowCofactorQ2Descent`, `RHLean.Proof.StableFarWallExactQ2Split`, and `RHLean.Proof.StableFarWallQ2ChildFarSlice`
  - recurse on the low cofactor rather than the outer far prime, which has zero `p^2` daughter scale, stripping the canonical largest prime before any norm;
  - give the exact raw far transport as `unitFace - descendedMass - crossingMass`, and prove the descended half is literally a far slice of the `q^2` child transport at cutoff `X_R/q^2`, with the converse reconstruction.

- `RHLean.Proof.StableFarWallCrossingRenewal`, `RHLean.Proof.StableFarWallRenewalDescent`, and `RHLean.Proof.StableFarWallCrossingOwnerWindow`
  - prove every surviving crossing is an actual signed return to the same physical wall, with the owner tag retained because different owners may descend to the same state;
  - prove the return is a strict arithmetic descent: the next stripped owner is the canonical largest prime of a smaller cofactor, and the second-contact load decreases strictly along compatible steps;
  - make the remaining multiplicity arithmetic, as an exact prime window `r < q < R` with `q*r*e*p <= X_R < q^2*r*e*p`.

- `RHLean.Proof.StableFarWallRenewalTerminal`, `RHLean.Proof.StableFarWallRenewalTerminalPrimeCount`, and `RHLean.Proof.StableFarWallUnitRenewalCentering`
  - identify the terminal branches at a fixed far prime as the finite interval `q*p <= X_R < q^2*p`, which for `A = ⌊X_R/p⌋` is exactly $\sqrt A < q \le A$ — the incoming renewal count is a prime count in a reciprocal interval;
  - center the unit sector on its physical homes, giving a two-level centered incidence normal form with every owner multiplicity retained and no norm taken.

- `RHLean.Proof.StableFarWallAdaptiveFourCornerBridge`
  - identifies the stable-far `q^2` renewal and the adaptive rough-prime descent as two coordinates on one arithmetic square, where a descending schedule processes the far prime first and the four-corner theorem then zeroes both lower corners permanently. This is cross-prime cancellation that ownerwise `q^2` norms cannot see.

- `RHLean.Proof.StableFarWallSignedReassembly`, `RHLean.Proof.StableFarRenewalDyadicTwoShell`, `RHLean.Proof.StableFarAdaptiveLedgerCollapse`, `RHLean.Proof.StableFarCoordinateOverlap`, `RHLean.Proof.StableFarOwnedSmoothShell`, and `RHLean.Proof.StableFarOwnedSmoothShellCompletion`
  - keep the far prime attached while the low cofactor is stripped, so the tagged map carries the true Möbius weight and owner multiplicity is never silently forgotten;
  - identify the owned terminal products with the complete squarefree `R`-smooth shell $(R,R^2)$, eliminate the duplicated root coordinates against the older canonical fixed-state sector, and collapse the old four-term root correction to a single root atom minus the near transport — after which the complete signed adaptive raw ledger *is* the canonical rough correlation.

## Frozen second contact and the q-square residual

- `RHLean.Proof.LowWheelFrozenSecondContactDescent` and `RHLean.Proof.LowWheelFrozenSecondContactRoughPrefix`
  - erase the largest frozen-cofactor prime to land the predecessor face in the strict lower-scale annulus `X_R/q^2 < P(V) <= X_R/q`, with the Boolean sign reversal exactly undoing that of the product-one mate, and injectivity proved through ordered-Euler-cut uniqueness rather than circularly;
  - identify the complete frozen cofactor fibre with the nonunit squarefree rough prefix and cancel it against an actual subledger of the existing physical transport, retaining an arbitrary test function so every integer fibre and multiplicity is preserved.

- `RHLean.Proof.LowWheelFrozenSecondContactWindowReassembly` and `RHLean.Proof.LowWheelFrozenSecondContactWindowDescent`
  - subtract the recursive Go law at both window endpoints so both anchors and both fixed lower-prefix columns cancel, then interchange the double sum so the *child* owner indexes the outer column;
  - prove the endpoint form's gate is exactly the cube condition `q^3 <= X_R`, exhibit the unrestricted Mertens gap that survives outside it, and then raise the lower endpoint to `max R (X_R/q^2)`, where the owner sits below the cutoff for free and the gate disappears entirely;
  - retain the superseded theorems as the recorded no-go, so the loose endpoint is not reintroduced.

- `RHLean.Proof.LowWheelFrozenSecondContactGlobalTelescope` and `RHLean.Proof.LowWheelFrozenSecondContactScaleFlux`
  - sum the complete signed owner windows *first* and telescope their moving upper endpoints globally, giving the signed Stokes form of the ledger with no owner-by-owner estimate;
  - record a structural limit of the local prime toggle on this carrier: multiplying above the canonical owner crosses the endpoint and deleting the owner destroys the second-contact inequality, so cancellation that changes the old owner must come from a different global reassembly;
  - add two genuinely smaller coordinates, the reciprocal depth with $k^2 < R$ and the source scale with `B = ⌊X_R/A⌋ < R`.

- `RHLean.Proof.LowWheelFrozenSquareResidualQ2Reindex`, `RHLean.Proof.LowWheelFrozenSquareResidualQ2Telescope`, `RHLean.Proof.LowWheelFrozenSquareResidualParentProduct`, `RHLean.Proof.LowWheelFrozenSquareResidualParentCarrier`, `RHLean.Proof.LowWheelFrozenSquareResidualParentGeometry`, and `RHLean.Proof.LowWheelFrozenSquareResidualParentSurjectivity`
  - reindex each residual cofactor by its unique owner, keeping the source-scale Möbius factor outside the daughter sum because the primes below the old pivot are encoded there;
  - prove every `(A,d)` in a daughter window is a genuine ordered Euler cut with child `A*d`, so the product carries the true weight `mu(A)*mu(d)`, and that for fixed owner the product map is injective *across* source scales;
  - flatten to a `(q,m)` carrier, prove it lies in the post-root `q`-smooth strip, and then prove the reverse inclusion constructively, using Bertrand only as a finite carrier-saturation device.

- `RHLean.Proof.LowWheelFrozenSquareResidualRootFloored` and `RHLean.Proof.LowWheelFrozenSquareResidualTransportClosure`
  - reduce one owner fibre to a difference of frozen predecessor prefixes, identifying the first sum with the already-compiled root-floored lower column;
  - eliminate the remaining moving root-floored column entirely, giving an exact formula for the *existing* historical matching transport, `T_match = F_{R^-}(X_R) + \sum_{q<R} F_{q^-}(R) - 1`, with no hidden source scale, interval-prime cube or `q^2` floor term left.

- `RHLean.Proof.LowWheelFrozenCofactorTopBottomCancellation` and `RHLean.Proof.LowWheelFrozenCofactorTopImageHighPrimeObstruction`
  - perform the global subtraction the pointwise toggle never took: the move is injective with an explicit inverse, the frozen nontrivial-cofactor ledger is exactly minus its image mass, and the image is disjoint from the whole downcross carrier, giving `D_R = U_R + F_R^{c=1} - T_R`;
  - close the obvious next move, proving the image is rough-free below the root while every high-prime population is indexed above it, so the two are complementary rather than nested and the containment holds only vacuously;
  - prove the relocation is norm preserving, so bounding the relocated ledger *is* bounding the frozen sector and no reindexing can supply that bound.

- `RHLean.Proof.LowWheelLargestDefectSeamEquivalence`
  - records that the largest-prime stable defect is the terminal seam rather than a reduction of it, since the coordinate synthesis is an identity of the same signed object and the two linear bounds are equivalent in both directions;
  - classifies the exact pointwise carrier before any norm, splits it at the largest-prime root scale, and leaves the two RH-scale bounds explicit and open.

## The physical q-square terminal synthesis

- `RHLean.Proof.PhysicalQ2BookkeepingSynthesis`
  - proves the full physical `q^2` hit carrier partitions disjointly by its actual least *odd* square-prime owner, so summing the genuine daughter over those fibres recovers the Mertens daughter exactly, at every cutoff and with no endpoint error;
  - separates prime `2` out as base mod-four geometry rather than another contact channel, while keeping its nonzero algebraic two-step remainder explicit.

- `RHLean.Proof.PhysicalQ2TerminalSynthesis`, `RHLean.Proof.PhysicalQ2ExceptionalTerminalSynthesis`, and `RHLean.Proof.PhysicalQ2FourFrameTerminalSynthesis`
  - package everything *after* the parent recurrence, so the remaining hypothesis is irreducible: no `q=2` convention, least-owner transfer, daughter normalization, floor endpoint, reciprocal-square budget, strong induction or terminal wiring remains outside the theorem;
  - give three subcritical coefficients — $(5/4)\cdot4\cdot(19/23)^2\cdot(1/4)=1805/2116$ with the prime-11 factor, $3\cdot(5/4)\cdot(1/9+1/25+1/49)=1891/2940$ on the exceptional owners alone, and $4\cdot(36/35)\cdot(17/72)=34/35$ using the sharp odd-owner budget and the Young split;
  - establish that the third of these needs **no** selected-prime observable, tensor substitution, frame mask, or extra Mertens hypothesis.

- `RHLean.Proof.SignedTransportAmplificationAudit`, `RHLean.Proof.SquareRootLowPrimeSharpFrameBudget`, and `RHLean.Proof.SquareRootLowPrimeTSectorQ2Renormalization`
  - normalize the amplification target to the fully recovered shifted state rather than the matched channel alone, and record the finite obstruction to requesting a subunit constant in the all-`R` formulation;
  - sharpen the daughter budgets to `1/2` for all prime owners and `1/4` when owner `2` is absent, so frame loss `2`, or `4` on odd primes, still closes the same linear-energy induction;
  - combine the exact prime-11 square factor $(19/23)^2<3/4$ with the `q^2` daughter budget into a strictly subcritical branching coefficient, while stating clearly that the physical endpoint is *not* asserted to satisfy that recurrence.

- `RHLean.Proof.LogSquareCorrectionQ2Tower`, `RHLean.Proof.RoughDyadicQ2Compression`, `RHLean.Analysis.TwoWheelQ2Compensation`, and `RHLean.Proof.TwoWheelQ2GoCompatibility`
  - prove the logarithmic square correction is a `q^2`-and-deeper Mertens tower with no first-power term hidden in it;
  - carry the ordinary dyadic compression *inside* the `q`-rough carrier, since adjoining `2` preserves the predecessor-wheel condition on every nonzero atom, with owner `2` deliberately excluded;
  - isolate the local compatibility `g(x) - Δ_q g(x) - Δ_q g(x/q) = g(x/q^2)`, so a square deletion is not the daughter by itself, and identify the Go/recovery compatibility defect as the existing signed high-transport column rather than a new analytic error.

- `RHLean.Proof.FinalCompensatedParentReduction` and `RHLean.Proof.FrozenTopFarAdaptiveRawBridge`
  - combine the `q^2` reassembly with the canonical frozen reduction on one signed endpoint, giving `core + frozenTopFar = q2Residual + rootBoundary`, so the genuinely hard comparison is the `q^2` low-side packet against the frozen/top/far high-side packet;
  - put that residual directly onto the canonical rough-correlation carrier and then onto the adaptive zero-factor descent, so the raw boundary ledger is attached to the literal physical residual instead of a parallel coordinate system.

## Outside-prime ownership and the exceptional owners

- `RHLean.Analysis.OutsidePrimeLeastSquareBlocker`, `RHLean.Analysis.OutsidePrimeLeastSquareMaximalWheel`, and `RHLean.Analysis.OutsidePrimeLeastSquareMaximalWheelConstruction`
  - prove least-square ownership is genuinely local, with no ambient prefix in the statement, and bound the complete least-owner super-orbit period by the square-block length;
  - construct the finite maximal feasible wheel that forces every complete outside least-square owner below 11, by a maximality argument rather than an assumed certificate.

- `RHLean.Analysis.OutsidePrimeCompleteDeletionFirstMoment`
  - gives genuinely summable owner bounds, $|\chi^T m_q|\le 18K/q^2$ on complete periods and $18(K/q^2+1)$ on an arbitrary prefix, with the absolute value taken only after the signed owner channel has been formed;
  - states plainly that this does not yet identify the least-square super-orbit Schur block with the Go daughter block.

- `RHLean.Proof.ExceptionalDeletionParentPartition`, `RHLean.Proof.ExceptionalOwnerEnergyClosure`, and `RHLean.Proof.ExceptionalTransportCoboundary`
  - reduce the complete interior owner schedule to `{3,5,7}` at carrier and signed-mass level, deliberately keeping the observable the selected-prime field so the remaining parity transfer stays visible as the parent-side seam;
  - keep the three channel coefficients separate, proving the linear envelope under the sufficient budget $\alpha_3/9+\alpha_5/25+\alpha_7/49<1$ with exact constant $C/(1-\beta)$;
  - prove the chronological high column is an exact prime coboundary whose potential is the frozen cube, so the exceptional predecessor cubes vanish beyond `X >= 1470`.

- `RHLean.Proof.ExceptionalContactFrameEnergyNoGo`, `RHLean.Proof.ExceptionalSignedPacketIdentification`, `RHLean.Proof.JointDaughterCrossEnergyAudit`, and `RHLean.Analysis.PhysicalDaughterEnergyObstructions`
  - refute the six-contact frame route three ways: the contact classes are the *images* of the offsets under $a\mapsto -a/4 \bmod q^2$, the frame constant is two for an arbitrary field by mod-four pairing, and the assembled coefficient norm is a different object from the recursive Mertens energy, separated by an exact finite witness at `Y = 2`;
  - give the exact forward dictionary from the true Möbius observable on a complete owner carrier, and exclude replacing an uncompensated nine-edge local block by a scalar linear image of one square-dilated value;
  - record that a joint-daughter coefficient below one requires negative cross-*owner* energy, which within-daughter cancellation does not assert, and that the selected deletion field has positive periodic drift so its square cannot lie in a uniformly linear envelope.

- `RHLean.Analysis.PhysicalExceptionalLocalIntertwine`
  - begins the physical local-block theorem on the actual least-square channels, keeping `q=3` as one unrestricted recovered interval while treating `q=5` and `q=7` as exact finite incidence sums, since their masks are not contiguous once smaller channels are removed.

## Finite-prime weight-one layers and what they may not assume

- `RHLean.Analysis.ElevenWeightOneFirstMoment` and `RHLean.Analysis.FinitePrimeHigherWeightOne`
  - package the finite arithmetic law as an operator on first moments: multiplication by the prime-11 Euler sign has average `19/23` on the 115 zero-free classes, so every weight-one combination is multiplied by `19/23` and its square by $(19/23)^2$;
  - upgrade that to a deterministic CRT tensor theorem in which the complementary field on a coprime modulus varies arbitrarily, with no independence assumption, and supply the same certificates at 13 and 17.

- `RHLean.Analysis.PhysicalRecoveredPrimeTensorCompatibility`
  - makes two transfer issues impossible to hide inside a later norm: the tensor theorem permits an arbitrary field on a *coprime complementary* coordinate but not an arbitrary function of the same `11^2` coordinate, and the selected-prime projection carries only the selected sign while the Mertens-visible observable carries the parity of every prime factor.

- `RHLean.Analysis.PartialMomentSchurTarget` and `RHLean.Analysis.PhysicalPartialMomentSchur`
  - prove the four-block directional split of a second moment about an arbitrary target, and that the scaled Schur complement `W*Q_t - m_t m_t^T` is exactly target independent, with no positivity or probability normalization;
  - instantiate it on the eight-state zero-free transition rows, showing exactly where a target shift goes: into the rank-one first-moment term, not the Schur covariance.

## Mellin interpolation and partner Euler memory

- `RHLean.Proof.PostRootPartnerReciprocalCompression` and `RHLean.Proof.PostRootPartnerEulerMemory`
  - convert a post-root raw boundary into a cofactor-weighted reciprocal parent mass exactly, and prove the cofactor-weighted step creates no new mismatch on a complete descending prefix;
  - prove a complete descending schedule leaves no final raw mass, and establish the memory law `p*(EulerNext - RawNext) = (p-1)*B_p`: the signed boundary is transported between coordinates with the Euler factor, not discarded.

- `RHLean.Proof.PostRootPartnerMellinInterpolation` and `RHLean.Proof.PostRootPartnerLogAlignment`
  - show the zero-factor raw law and the reciprocal Euler law are the two endpoint specializations of one weighted fresh-prime identity: with `w(cp) = z*w(c)` the parent coefficient is `1-z`, which is `0` at `s=0` and `1-1/p` at `s=1` for the Mellin weight, so differentiating in `s` necessarily produces `log p`;
  - state the remaining physical seam as an equality of finite signed pushforward measures against an arbitrary test observable, rather than one scalar checksum, with no Perron inversion or PNT estimate used.

## Prime-wheel rough seats

- `RHLean.Proof.PrimeWheelRoughSeatCorrelation` and `RHLean.Proof.PrimeWheelFrozenRoughSeatBridge`
  - collapse every overlap between exponentially many signed divisor bands into one integer coefficient on each physical rough seat, with no absolute value or wheel-depth loss;
  - identify that signed truncated kernel with the chronological frozen prime cube already used by the first-owner and Go machinery.

- `RHLean.Proof.PrimeWheelProperSubwheelDepthTwo` and `RHLean.Analysis.RoughWheelFiniteCounting`
  - stop the wheel at `Y` before the endpoint is resolved and open the moving predecessor column at its own fresh prime, so when `X < (Y+1)^3` the square residual is already an ordinary lower Mertens state, giving the exact algebraic form of the prime/semiprime cancellation;
  - keep the residue count and both incomplete periods explicit, with the estimate uniform in the wheel.

## Go defect reduction onto the saturated carrier

- `RHLean.Proof.SquareRootLowPrimeGoFullFacePartner` and `RHLean.Proof.SquareRootLowPrimeGoFullFaceResidualAbsorption`
  - put every prime factor of the complete squarefree child on the Boolean face, so a second-boundary defect is a literal occurrence of the tagged transport carrier with no singleton crossing hypothesis and no root-equality exception;
  - prove the far part of the mate image is already a subcarrier of the hard physical residual, because a defect mate has a face prime strictly *above* its pivot while a frozen top image has all face primes strictly below, so the Go correction cancels there rather than adding a scalar error term.

- `RHLean.Proof.SquareRootLowPrimeGoReducedSourcePacket` and `RHLean.Proof.SquareRootLowPrimeGoRootFloorTerminalSplit`
  - record that exactly one source copy survives mate deletion, classify it at its `q^2` boundary as the pre-contact state whose next `q`-move crosses the endpoint, and identify the complement exactly with the old hard residual so mate deletion relocates the packet rather than creating a second remainder;
  - classify the root-floor half as a canonical root-downcross with frozen `c=1` shape, hence either unique-parent or repeated internal terminal.

- `RHLean.Proof.SquareRootLowPrimeGoDefectAncestryGeneration`, `RHLean.Proof.SquareRootLowPrimeGoDefectCanonicalSeed`, and `RHLean.Proof.SquareRootLowPrimeCanonicalSeedSourceBridge`
  - identify the defect as a literal restriction of the generation-one ancestry field, with no new observable, and place its canonical child inside the existing saturated seed window, the root-floor incidence failing that predicate at one named condition only.

- `RHLean.Proof.SquareRootLowPrimeCombinedTaggedElevenPushforward` and `RHLean.Proof.SquareRootLowPrimeCombinedResidualSourceNormalForm`
  - place the full-face Go source on the *existing saturated* second-contact carrier rather than the superseded loose window, splitting the defect canonically into a saturated child population and an explicit root-floor failure with the correct signed orientation;
  - rewrite the opaque far set-difference residual in the source/partner coordinates and perform the six finite population comparisons in one common tagged currency.

## Dyadic survivor splice

- `RHLean.Proof.DyadicSurvivorMertensInvariant` and `RHLean.Proof.DyadicSurvivorMatchedSplice`
  - identify the physical survivor boundary left after pairing an odd high-prime state with its doubled child — the odd dyadic band `W/(2p) < c <= W/p` — with the already-formalized upper-prime Mertens transform;
  - remove the abstract transport symbol from the matched born-smooth channel by exact rewrite, with no norm or new estimate.

## Closed routes

A published research record should say which routes were tried and abandoned,
not only which ones worked. `boundary/dead_lanes.json` is that record: each
entry names the claim, the obstruction that closes it, the Lean or numerical
evidence, and what new information would reopen it. It now carries twenty-two
entries, and every one is closed by a compiled theorem in this package rather
than by a failed attempt.

Six were added with this revision, and between them they retire most of what a
reader would try next: improving the post-root exponent inside the record
machinery, computing a six-contact frame constant for the exceptional owners,
iterating finite-wheel band counting, enumerating the largest-prime defect
carrier, keeping the frozen second-contact window at its loose endpoint, and
absorbing the frozen top image into the external high-prime population. A
seventh kind of closure appears here for the first time: `stronger-than-rh`,
for a route whose hypothesis is sound but already implies more than the Riemann
hypothesis, so proving it is harder than the target rather than a step toward
it.

The modules that carried the earlier response-forest, response-matching,
external-terminal-mass and repeated-mass experiments are no longer retired. They
are listed above under the reciprocal Euler compression and processed-seat
sections, where they now carry the canonical rough covariance carrier, the exact
late-parent cancellation, and the two Othello wrappers the classifier uses.

## Research boundary and export guards

- `RHLean.Analysis.MobiusSynthesisBoundary`
  - contains the protected quantitative boundary types.

- `RHLean.Proof.TerminalAxiomAudit`
  - asks the kernel for the axiom dependencies of the theorems carrying the reduction to the Riemann hypothesis statement and pins the answer with `#guard_msgs`, so an added dependency fails the build.

- `boundary/frontier.json`
  - records the monotone quantitative frontier.

- `boundary/synthesis.json`
  - records exact cross-track synthesis advances; the refreshed export is at revision 6. The gate moves that number only for a witness that directly invokes pre-existing anchors from *both* source tracks, so a republication carrying many upstream advances forward records them under `companion_witnesses` instead of manufacturing revisions for them.

- `scripts/check_markdown_math.py`
  - rejects unsupported GitHub Markdown TeX delimiter forms outside code.

- `.github/workflows/markdown-math.yml`
  - runs that audit automatically on every push and pull request.

- `boundary/dead_lanes.json`
  - records the routes that are closed, with the obstruction that closes each one and what would reopen it.

- `boundary/BOUNDARY_POLICY.md`
  - states the scope gate the two lanes above enforce.

The quantitative frontier is unchanged: the missing theorem is still genuine RH-scale control of the signed Möbius field, and `boundary/frontier.json` therefore still certifies `exact_reduction`. What has changed, again, is where that control has to be earned.

Five things are new in this revision.

1. **The post-root loop is closed, and the closure is a no-go.** Both terms subtracted in the Bessel identity are nonnegative, so $E(W)\le M(W)^2/2$ holds unconditionally — no cancellation, no record hypothesis, no sieve. That single line makes the remainder, envelope, record-excess, falling finite-difference, Mertens square envelope and Mertens energy statements one equivalence class, and read quantitatively it is an exchange rate with exponent factor exactly two. Nothing inside the post-root or record machinery can move the remainder exponent without first moving the Mertens exponent. The constant still moves, and does.

2. **The record step is the carrier of the remaining problem.** The innovation budget splits with no triangle inequality, because the physical row and the square-wall departure have disjoint support; a positive record forces a full endpoint power beyond naive localization; and the departure is bounded unconditionally by $p^2$ sparsity. What is left unbounded is one object: the record-conditioned outer physical row after inherited high transport has been removed.

3. **The q-square route reaches a terminal synthesis needing no spectral input.** With the sharp odd-owner budget $\sum_{q\ \mathrm{odd}}q^{-2}\le 17/72$ and the $36/35$ Young split for the endpoint transfer, a factor-four recurrence on the fully signed, fully reassembled physical daughters has coefficient $4\cdot(36/35)\cdot(17/72)=34/35<1$ and by itself gives linear Mertens energy and the Riemann hypothesis. Everything after the parent recurrence is now packaged, so the remaining hypothesis is irreducible.

4. **The frozen and far-wall carriers are fully reassembled, signed, before any norm.** The `q^2` parent reassembly leaves an exact formula for the existing historical matching transport with no hidden source scale left in it; the frozen cofactor top/bottom cancellation sharpens the endpoint identity to $D_R=U_R+F_R^{c=1}-T_R$; and the stable far wall descends by a strictly decreasing owner to terminal branches that are literally a prime count in a reciprocal interval.

5. **Two coordinate systems turn out to be one, again.** The zero-factor raw law and the reciprocal Euler law are the endpoint specializations at $s=0$ and $s=1$ of a single Mellin-weighted fresh-prime identity, so the memory factor is an endpoint difference and differentiating in $s$ produces the logarithmic prime weight. The signed boundary is transported between coordinates with the Euler factor rather than discarded.

The processed-seat layer still carries the one outstanding *construction*: the weight-preserving classifier at the no-liberty seam. Its Head, Partial, BornExit and RootEquality branches are built individually, with membership, injectivity and exact weight preservation proved for each; the product-wall branch of the source dichotomy is removed outright; and the target-side budget is $3R+21$. What is not yet assembled is the source-to-boundary classifier itself, and the `Partial` branch still rests on one named budget, stated so that no downstream file can discharge it by an arithmetic encoding of the seat index.
