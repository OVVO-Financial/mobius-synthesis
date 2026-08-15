# Exact seams between the proof layers

This document records the interfaces that should remain stable while the quantitative proof evolves.

## 1. Three-slot state seam

For each complete four-cell, define

\[
S_k=(\mu(4k+1),\mu(4k+2),\mu(4k+3)).
\]

The 27-state population is encoded by `threeSlotStateCount K i`.  The degree-one coordinate characters recover the direct Möbius sums exactly:

\[
W_j(K)=\sum_i\chi_j(i)C_i(K).
\]

This seam converts any state-population argument into the actual signed coordinate statistic without probabilistic assumptions.

**Formal module:** `RHLean.Analysis.ThreeSlotMertensDegreeOneProjection`.

## 2. Complete-cell Mertens seam

The fourth slot of every four-cell is killed by the square of 2, so

\[
M(4K)=W_a(K)+W_b(K)+W_c(K).
\]

This is the exact endpoint at which the three-slot state language becomes the ordinary Mertens function.

**Formal modules:** `RHLean.Arithmetic.PrimeWheelThreeSlotRecovery` and `RHLean.Analysis.ThreeSlotMertensDegreeOneProjection`.

## 3. Signed-field seam

For the canonical prime set through the physical square-root cutoff,

\[
W_j(K)=R_j(K)-2H_j(K).
\]

Therefore

\[
M(4K)=\sum_{j=1}^3(R_j(K)-2H_j(K)).
\]

The correction term must remain inside the signed field.  Separate absolute estimates for `R` and `H` are not interchangeable with an estimate for their difference.

**Formal modules:** `RHLean.Arithmetic.PrimeWheelThreeSlotRecovery`, `RHLean.Arithmetic.PrimeCombFiniteDifferenceRecovery`, and `RHLean.Analysis.ThreeSlotMertensDegreeOneProjection`.

## 4. Arbitrary-prefix recovery seam

At any physical cutoff \(X\), the canonical square-root-covered corrected wheel satisfies

\[
R(X)-2H(X)=M(X).
\]

After the integer-to-complex cast, the same object is exactly `mertensSummatory X`.

This is the preferred global object for quantitative work.

**Formal module:** `RHLean.Analysis.PrimeWheelRecoveredMertensCriterion`.

## 5. Energy seam

The squared recovered-wheel target

\[
|R(X)-2H(X)|^2\ll_\varepsilon (X+1)^{1+\varepsilon}
\]

is formally equivalent to the global Mertens-energy statement and to the existing square-prefix energy criterion.

The analytic continuation and completed-zeta reflection layer then turns this energy estimate into the formal Riemann hypothesis.

**Formal modules:** `RHLean.Analysis.PrimeWheelRecoveredMertensCriterion` and `RHLean.Analysis.MertensEnergyRHForward`.

## 6. Collision-pairing seam

For one distinct odd-prime pair, the physical square-collision prefix is represented by nine labelled CRT classes plus an exact incomplete-period frontier.

A finite frontier is partitioned into:

- pairable labels;
- fixed labels;
- labels whose involution mate lies outside the prefix.

If the physical weight satisfies sign reversal under the label involution, every pairable contribution cancels exactly.

The corrected field already has a local arithmetic sign theorem under a genuine single-prime exponent flip.  The unresolved seam is to prove that the chosen physical CRT site realization satisfies the hypotheses needed to invoke that theorem.

**Formal modules:** `RHLean.Arithmetic.PrimeSquareCollisionCRT`, `RHLean.Arithmetic.PrimeSquareCollisionPrefix`, `RHLean.Arithmetic.PrimeSquareCollisionInvolution`, `RHLean.Arithmetic.PrimeSquareCollisionPairingFrontier`, and `RHLean.Arithmetic.PrimeWheelCorrectedLocalFlip`.

## 7. Finite-difference seam

The canonical operator

\[
D_S f(x)=\sum_{d\mid\prod_{p\in S}p}\mu(d)f(\lfloor x/d\rfloor)
\]

satisfies the exact fresh-prime recurrence

\[
D_{S\cup\{p\}}f=D_Sf-D_S(\operatorname{shift}_pf).
\]

This seam is designed for the case where a physical residue pairing cannot preserve all other prime coordinates.  The finite-difference fiber holds those coordinates fixed algebraically.

**Formal modules:** `RHLean.Arithmetic.PrimeCombFiniteDifference` and `RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime`.

## 8. First-failure frontier seam

The signed recovered prefix is exactly the existing first-failure Möbius frontier at every admissible prime coordinate.  This supplies a canonical destination for globally charging physical cutoff defects.

The important requirement is bounded multiplicity: a local frontier error must not simply be summed independently over all prime pairs.

**Formal module:** `RHLean.Arithmetic.PrimeCombFiniteDifferenceRecovery`.

## 9. Square-sensitive seam

The square-prefix transport decomposition and the canonical zero-mode-centered square-wheel response are exact alternate representations of the same Mertens object.  They can be used to organize the global defect energy without changing the final signed target.

**Formal checkpoint:** `RHLean.Analysis.ThreeSlotDegreeOneSynthesis`.

## 10. Acceptance criterion for new estimates

A proposed quantitative theorem should satisfy both conditions:

1. it respects the physical square-block and prime-wheel architecture rather than replacing the signed object by an unrelated surrogate;
2. it contracts the proven bound toward the scale

\[
K^{1/2+\varepsilon}.
\]

A theorem that only refines the 27-state transition matrix, improves an unsigned population estimate, or introduces a constant defect for every prime pair does not by itself advance the RH-scale frontier.
