# Current proof route

## 1. What is already exact

The active architecture uses complete four-cells

\[
(4k+1,4k+2,4k+3,4k+4).
\]

The fourth slot vanishes because \(4\mid 4k+4\), so the signed problem is carried by the three active coordinates.

For

\[
S_k=(\mu(4k+1),\mu(4k+2),\mu(4k+3))\in\{-1,0,1\}^3,
\]

the formalization defines the 27 exact state counts \(C_i(K)\) and the three degree-one characters \(\chi_a,\chi_b,\chi_c\).  The finite-fiber regrouping theorem gives

\[
W_j(K)=\sum_i\chi_j(i)C_i(K)
\]

for each active coordinate.  These are not probabilistic statements; they are finite identities.

The three degree-one sums are

\[
W_a(K)=\sum_{k<K}\mu(4k+1),
\]

\[
W_b(K)=\sum_{k<K}\mu(4k+2),
\]

\[
W_c(K)=\sum_{k<K}\mu(4k+3).
\]

At complete-cell endpoints,

\[
M(4K)=W_a(K)+W_b(K)+W_c(K).
\]

For the canonical prime set through the physical square-root cutoff, each coordinate is also exactly

\[
W_j(K)=R_j(K)-2H_j(K).
\]

Consequently

\[
M(4K)=\sum_{j=1}^3\bigl(R_j(K)-2H_j(K)\bigr).
\]

The same recovered signed field is proved equal to the ordinary Möbius prefix for arbitrary physical cutoffs.  Its squared energy criterion is formally equivalent to the global Mertens-energy criterion and to the square-prefix energy criterion.  The Mertens-energy criterion already implies the formal Riemann hypothesis.

The exact bridge is therefore complete.  What remains is quantitative cancellation.

## 2. The theorem that matters

The primary target is

\[
M(4K)\ll_\varepsilon K^{1/2+\varepsilon}.
\]

A convenient formal form is a squared degree-one energy statement

\[
\left|W_a(K)+W_b(K)+W_c(K)\right|^2
\ll_\varepsilon (K+1)^{1+\varepsilon}.
\]

The corresponding recovered-wheel statement is already connected to the analytic RH route.

A first useful infrastructure theorem should transfer a complete-cell estimate to arbitrary \(X\).  Set

\[
K=\left\lfloor X/4\right\rfloor.
\]

Then \(0\le X-4K\le3\), hence

\[
|M(X)-M(4K)|\le3.
\]

Thus the complete-cell target and the global Mertens-energy target differ only by a bounded endpoint correction and harmless changes of constants.

## 3. Route A: physical prime-square sign-reversing pairing

The collision layer already provides the abstract and conditional pieces.

For distinct odd primes \(p,q\), the joint \(p^2q^2\) collision system has nine labelled current-to-next slot classes.  A finite physical prefix is decomposed exactly into complete periods plus a remainder frontier of at most nine residue classes for that one prime pair.

A chosen involution on the nine slot labels splits every finite frontier into:

1. pairable states whose mates are also inside the frontier;
2. fixed states;
3. a mate-crosses-cutoff defect.

For any weight that genuinely reverses sign under the involution, all pairable states cancel by a finite involution sum.

The corrected arithmetic field has the required local sign law under an actual exponent flip.  If one selected prime coordinate changes between exponent states 0 and 1, every other local prime-comb coordinate is unchanged, and smooth-core membership is preserved, then

\[
(R-2H)(m)=-(R-2H)(n).
\]

### Immediate arithmetic task

Construct the actual residue-level site realization for the physical collision labels and prove the hypotheses of the existing corrected-field sign theorem:

- the selected prime really performs the local exponent-state flip;
- every other active prime-comb coordinate is preserved;
- smooth-core membership is preserved;
- both paired sites lie inside the pinned physical cutoff.

The three collision-slot labels and the three local exponent states must not be identified merely because both are represented by `Fin 3`.  Their arithmetic meanings and residue multiplicities differ.

### Fixed points

The chosen slot involution has three fixed labels.  The preferred next result is stronger than a bound: show that the physically realized fixed-point weight is exactly zero whenever the fixed label forces a square-kill state.  If this holds, the entire finite-frontier contribution reduces to the mate-crosses-cutoff defect.

### Global charging problem

A bound of nine remainder classes for each prime pair is not enough.  Summing a constant error independently over all \((p,q)\) would destroy the desired square-root scale.

The surviving defects must instead be assigned to a unique or bounded-multiplicity structural event, such as a first-failure prime coordinate, a fresh-prime transition, or a controlled square-sensitive frontier.  The target should be an energy estimate for the total signed defect, not a termwise absolute-value estimate.

## 4. Route B: finite-difference fibers

If the literal physical pairing cannot preserve all other prime coordinates or smooth-core status, the exact finite-difference operator gives the preferred fallback.

For a finite prime set \(S\), define

\[
D_S f(x)=\sum_{d\mid\prod_{p\in S}p}\mu(d)f(\lfloor x/d\rfloor).
\]

For a fresh prime \(p\notin S\), the formalized recurrence is

\[
D_{S\cup\{p\}}f
=
D_Sf-D_S(\operatorname{shift}_pf).
\]

This representation freezes the remaining prime coordinates by construction.  It is therefore the natural place to move the sign flip if the residue-level pairing does not preserve the full wheel state.

The recovered `R - 2H` prefix is already identified with the ordinary Möbius prefix through this finite-difference interface.  A successful fiberwise contraction can feed the same degree-one target without introducing a new analytic bridge.

## 5. Route C: square-sensitive transport and defect estimates

The square-block side supplies a second exact coordinate system for the same Mertens quantity: positive smooth mass, matched transport, zero-mode centering, nonzero square response, and the established energy criterion.

Existing smooth-defect and cutoff estimates remain useful as a secondary route.  They should now be judged by a single acceptance test: do they contract the signed recovered field toward

\[
K^{1/2+\varepsilon}
\]

without splitting away the cancellation that is visible in \(R-2H\)?

The square-sensitive machinery is especially useful for organizing the global cutoff defects from Route A or the fiberwise remainder from Route B.

## 6. What is not the target

The 27-state transition matrix is a diagnostic, not the quantity to bound.  It is expected to be nonuniform because square divisibility creates a large zero sector.

Likewise, approximate uniformity of the eight all-nonzero sign states does not prove the required estimate.  It is finite numerical evidence about one conditional statistic.

No proof route should require:

- uniformity of all 27 states;
- a Markov assumption for successive three-slot states;
- independence of neighboring Möbius values;
- separate absolute bounds on `R` and `H` that discard their signed cancellation.

The exact target is the degree-one signed projection

\[
W_a+W_b+W_c=M(4K).
\]

## 7. Recommended order of work

1. Prove the bounded three-term endpoint transfer from \(M(4K)\) to arbitrary \(M(X)\).
2. Package the degree-one energy statement and prove it implies the existing recovered-wheel energy criterion.
3. Attempt the canonical physical collision realization and discharge the exponent-flip, other-coordinate, and smooth-status hypotheses.
4. Prove exact vanishing of physical fixed points if available.
5. Express the remaining cutoff defect in a globally chargeable first-failure or fresh-prime form.
6. If physical pairing cannot preserve the full wheel state, move immediately to the finite-difference fiber formulation rather than weakening the arithmetic hypotheses.
7. Prove an \(L^2\) or energy bound for the total signed defect at exponent \(1+\varepsilon\).
8. Feed that estimate through the already-formalized recovered-wheel and Mertens-energy bridge.

The mathematical bottleneck is therefore precise: **control the signed degree-one physical field at square-root scale.**
