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
  - is the synthesis-ledger revision-3 witness.

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

## Research boundary and export guards

- `RHLean.Analysis.MobiusSynthesisBoundary`
  - contains the protected quantitative boundary types.

- `boundary/frontier.json`
  - records the monotone quantitative frontier.

- `boundary/synthesis.json`
  - records exact cross-track synthesis advances; the refreshed export is at revision 4.

- `scripts/check_markdown_math.py`
  - rejects unsupported GitHub Markdown TeX delimiter forms outside code.

- `.github/workflows/markdown-math.yml`
  - runs that audit automatically after this canonical directory is mirrored to standalone repository root.

The quantitative frontier is unchanged: the missing theorem is still genuine RH-scale control of the signed Möbius field. The new modules sharpen the exact defect representation that must be bounded, make the residual gap to the square-prefix Mertens value explicit, and close three proposed routes with recorded obstructions.
