# Principal modules

The formal source lives under `RHLean/`.  The package is intentionally broad, but the modules below are the main entry points for the current Möbius-synthesis route.

## Three-slot degree-one layer

- `RHLean.Analysis.ThreeSlotMertensDegreeOneProjection`
  - encodes the 27 three-slot Möbius states;
  - defines the exact state counts `threeSlotStateCount`;
  - defines `chiA`, `chiB`, `chiC` and the direct sums `threeSlotWa`, `threeSlotWb`, `threeSlotWc`;
  - proves `W_j(K) = sum_i chi_j(i) C_i(K)`;
  - proves `M(4K) = W_a(K) + W_b(K) + W_c(K)`;
  - proves the coordinatewise and total equivalence with the physical signed `R - 2H` field.

- `RHLean.Analysis.ThreeSlotDegreeOneSynthesis`
  - packages the degree-one identity together with established square-prefix and zero-mode-centered square-wheel identities as a compact cross-track checkpoint.

- `RHLean.Arithmetic.PrimeWheelThreeSlotRecovery`
  - defines raw, smooth-core, and recovered slot prefixes;
  - proves square-root coverage recovers each active Möbius slot exactly;
  - proves the three recovered slots sum to the complete four-cell Möbius prefix.

## Canonical recovered-wheel criterion

- `RHLean.Analysis.PrimeWheelRecoveredMertensCriterion`
  - defines the canonical square-root recovered prefix;
  - proves it is exactly the ordinary Möbius prefix and the analytic Mertens summatory function;
  - defines `SqrtWheelRecoveredEnergyBoundedStatement`;
  - proves equivalence with the global Mertens-energy and square-prefix energy criteria;
  - proves the recovered-wheel energy criterion implies the formal Riemann hypothesis.

- `RHLean.Analysis.MertensEnergyRHForward`
  - carries the Mertens-energy estimate through reciprocal continuation, zero-freeness to the right of the critical line, and completed-zeta reflection.

## Canonical finite-difference layer

- `RHLean.Arithmetic.PrimeCombFiniteDifference`
  - defines the unordered Möbius divisor-difference operator `finiteDifferenceOperator`.

- `RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime`
  - proves the fresh-prime recurrence
    `D_(S ∪ {p}) f = D_S f - D_S (shift p f)`.

- `RHLean.Arithmetic.PrimeCombFiniteDifferenceRecovery`
  - proves square-root prime-wheel recovery through the finite-difference interface;
  - identifies the signed recovered prefix with the existing first-failure Möbius frontier.

## Prime-square collision layer

- `RHLean.Arithmetic.PrimeSquareCollisionKernel`
  - establishes the local collision structure used by the square-sensitive prime-wheel analysis.

- `RHLean.Arithmetic.PrimeSquareCollisionCRT`
  - realizes the distinct-prime square collisions as nine exact CRT residue classes.

- `RHLean.Arithmetic.PrimeSquareCollisionPrefix`
  - gives the exact complete-period plus finite-frontier ledger;
  - proves the remainder frontier for one distinct-prime pair has cardinality at most nine.

- `RHLean.Arithmetic.PrimeSquareCollisionInvolution`
  - separates local exponent states from physical collision-slot labels;
  - defines the exponent flip and the candidate nine-state slot involution;
  - proves the abstract local sign-reversal algebra.

- `RHLean.Arithmetic.PrimeSquareCollisionPairingFrontier`
  - partitions any finite collision frontier into pairable, fixed, and cutoff-defect parts;
  - proves exact cancellation of the pairable part for any separately established sign-reversing physical weight.

- `RHLean.Arithmetic.PrimeWheelCorrectedLocalFlip`
  - proves the actual corrected `R - 2H` site weight changes sign under a genuine single-prime exponent flip when all other local coordinates and smooth-core status are preserved;
  - specializes the finite-frontier decomposition to the corrected physical weight.

## Square-sensitive synthesis layer

The established square-prefix, transport, survivor, zero-mode, and square-wheel modules remain part of the same package.  In particular:

- `RHLean.Analysis.SquareRootTransportRealization`
  - realizes the original square-root transport identity and the positive-smooth plus matched decomposition.

- `RHLean.Analysis.PrimeSievePNTCentering`
  - identifies the canonical nonzero square-wheel response as the exact zero-mode centering of the Mertens summatory function.

- `RHLean.Analysis.MobiusRenewalTelescope`
  - proves the exact g-weighted renewal telescope `sum (g*1)(n) M(floor(X/n)) = sum g(a)`, the substrate for renewal-type reciprocal Mertens identities.

- `RHLean.Analysis.MobiusRenewalSquareWheelSynthesis`
  - realizes the far-upper survivor Mertens transform through the renewal telescope and substitutes it into the zero-mode-centered primorial wheel response (synthesis ledger revision 3).

- `RHLean.Analysis.SquarePrefixMertensBridge`
  - provides the square-prefix energy criterion used by the recovered-wheel equivalence.

## Research boundary

- `RHLean.Analysis.MobiusSynthesisBoundary`
  - contains the protected quantitative boundary types used to distinguish exact reductions from genuine power-saving progress.

- `boundary/frontier.json`
  - records the monotone quantitative frontier.

- `boundary/synthesis.json`
  - records exact cross-track synthesis advances.

The current quantitative frontier is unchanged by the three-slot projection work: the missing result is still a genuine RH-scale estimate for the signed degree-one field.
