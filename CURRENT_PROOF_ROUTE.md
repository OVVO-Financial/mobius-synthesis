# Current proof route

## 1. Exact architecture

The active arithmetic decomposition uses complete four-cells

$$
(4k+1,4k+2,4k+3,4k+4).
$$

The fourth slot is killed by the square of $2$, so the signed field is carried by the first three coordinates. For

$$
S_k=(\mu(4k+1),\mu(4k+2),\mu(4k+3))\in\{-1,0,1\}^3,
$$

the degree-one characters recover the three direct coordinate sums and hence

$$
M(4K)=W_a(K)+W_b(K)+W_c(K).
$$

At the canonical square-root prime cutoff each coordinate also equals the corresponding recovered prime-wheel field:

$$
W_j(K)=R_j(K)-2H_j(K).
$$

The bounded endpoint transfer is now proved. If $K=\lfloor X/4\rfloor$, then

$$
|M(X)-M(4K)|\le 3.
$$

Thus the complete-cell target and the global Mertens target are separated only by a fixed additive constant.

The squared recovered-wheel criterion is already equivalent to the global Mertens-energy and square-prefix energy criteria, and the formal forward analytic bridge carries the Mertens-energy criterion to the Riemann hypothesis statement.

## 2. Quantitative target

No RH-scale estimate is claimed by the current exact reductions. The target remains

$$
M(X)\ll_\varepsilon X^{1/2+\varepsilon},
$$

or, in the energy form used by the formal analytic bridge,

$$
|M(X)|^2\ll_\varepsilon (X+1)^{1+\varepsilon}.
$$

Every new quantitative theorem should preserve the square-block and prime-wheel architecture and contract the proven bound toward this scale.

## 3. Collision route: what is now exact

For one distinct odd-prime pair, the physical square-collision prefix is organized by nine exact CRT collision labels. The finite frontier is partitioned into pairable labels, fixed labels, and labels whose involution mate crosses the cutoff.

The exported collision layer now proves all of the following exact facts.

- Pairable labels cancel for any separately verified sign-reversing physical weight.
- A genuine selected-prime exponent flip reverses the actual corrected `R - 2H` field when the other prime-comb coordinates and smooth-core status are preserved.
- A selected-prime square hit kills the corrected field exactly.
- Consequently every fixed collision label forced into a square-hit state has zero corrected weight.
- After those fixed points vanish, the physical frontier reduces to the explicit mate-crosses-cutoff defect.
- That defect has at most three labels, not nine.

The local problem has therefore been compressed to a genuinely small signed defect.

## 4. The collision-defect chain is the sharp global target

`RHLean.Analysis.PrimeBoundaryDefectBridge` packages the remaining global arithmetic statement as `SquarePrefixCollisionDefectChain`.

A chain at square stage $n$ has at most $n+1$ charged steps, each step is a finite collision frontier, each frontier carries unit-bounded signed weights, and the total signed mass represents the exact square-prefix Mertens value. If such a chain exists, the three-label local defect theorem gives

$$
|M((n+1)^2-1)|\le 3(n+1),
$$

hence

$$
|M((n+1)^2-1)|^2\le 9(n+1)^2.
$$

This is already the critical square-prefix scale before any $\varepsilon$ loss. The same module proves that a chain for every $n$ implies the square-prefix energy criterion and then the global Mertens-energy criterion.

**The unresolved collision task is therefore precise:** construct the chain from the actual arithmetic frontier with bounded multiplicity. A constant local defect must not be summed independently over all prime pairs.

## 5. Boolean finite differences and survivor parity

The finite-difference fallback has also advanced beyond the one-prime recurrence.

For an arbitrary Boolean-supported predicate, exact first, second, and third coordinate differences are proved. The two-pivot stencil is the four-state derivative

$$
I(u)-I(a+u)-I(b+u)+I(a+b+u),
$$

and the three-pivot form is the corresponding eight-state third derivative.

These identities apply directly to the actual fixed-prime survivor fibre. For every prime $q\ge7$, the coordinates $2$, $3$, and $5$ give the exact representation

$$
\text{survivor mass}=-\sum_u (-1)^{|u|}\,\Delta_{2,3,5} I(u).
$$

Each local three-pivot stencil has integer magnitude at most $4$. The quantitative question is therefore the signed support and correlation of the nonzero stencils, not their individual size.

Inside parity residue fibres, the first-failure frontier admits a second residue-preserving toggle. Primes $3$ and $5$ reduce the actual parity-conditioned high survivor mass to six explicit codimension-two corner sums.

## 6. Dyadic signed channels

The dyadic survivor decomposition retains cancellation before norms. For odd upper prime $q$, parity residue $0$ is exactly the odd-cofactor channel and parity residue $1$ is exactly the even-cofactor channel.

The true survivor square is represented by the signed two-channel Gram, including its cross-channel term. Replacing that signed square by a positive two-channel energy can discard essentially all of the cancellation.

For an odd parent $d$ and $q>2$, canonical source admissibility is invariant under $d\mapsto 2d$. Therefore nonzero dyadic pair mass is supported only where the geometric survivor conditions change. The mismatch is classified into exactly three shells: one product-cutoff crossing and two height-band crossings.

This gives a second concrete quantitative target: prove square-root-scale signed energy for those three shell families, rather than taking absolute values before pairing.

## 7. Renewal and affine coordinates

The renewal layer is also exact. `RHLean.Analysis.MobiusRenewalTelescope` proves the weighted finite renewal telescope, and `RHLean.Analysis.MobiusRenewalSquareWheelSynthesis` realizes the far-upper survivor Mertens transform in those coordinates before substituting it into the primorial square-wheel zero-mode center.

The synthesis ledger recorded that step as revision 3; the ledger is now at revision 5. The affine-excursion and two-obligation prime-sieve modules expose further exact coordinates for a contraction argument, but they do not by themselves supply the missing power saving.

## 8. Orientation split and the combined signed residual

Write $X=R^2-1$, and for a source $m$ let $q=P^+(m)$ and $c=m/q$. The square-root smooth mass splits exactly by canonical orientation,

$$
A_R=A_R^{\mathrm{pos}}+A_R^{\mathrm{born}},
$$

with the positive orientation $c<q$ and the born orientation $q\le c$. The matched object is $A_R^{\mathrm{born}}-T_R$.

Centering the cofactor-first transport against the smooth logarithmic-integral main term gives the three-term split $T_R=T_R^{\mathrm{sm}}+Q_R+E_R$, with $Q_R$ the aggregate reciprocal-cutoff floor rounding and $E_R$ the aggregate prime-counting discrepancy. **Those two must not be separated.** $E_R$ carries the large prime-count drift, so a separate absolute bound on it is far weaker than the signed cancellation actually available against $Q_R$ and against the born-smooth mass.

`RHLean.Analysis.SquareRootCombinedSignedResidual` therefore defines the combined residual channel by channel,

$$
D_R=\sum_{1\le c<R}\mu(c)\Big[\big(\pi(\lfloor X/c\rfloor)-\pi(R)\big)-\big(\mathrm{Li}(X/c)-\mathrm{Li}(R)\big)\Big],
$$

before the cofactor sum is ever taken, so no later step can reach one summand without the other. It proves

- $D_R=Q_R+E_R$, so the combination is the existing pair rather than a new object;
- the two-term centering $T_R=T_R^{\mathrm{sm}}+D_R$;
- the matched form $A_R^{\mathrm{born}}-T_R=\big(A_R^{\mathrm{born}}-T_R^{\mathrm{sm}}\big)-D_R$;
- the Gram identity $\lVert \text{main}-D_R\rVert^2=\lVert A_R^{\mathrm{born}}-T_R\rVert^2$, so centering changes no norm;
- equivalence of the combined RH-scale statement with the square-prefix criterion.

The one-way triangle bound is recorded deliberately, to document what separating costs: the inequality runs from the separated norms to the matched norm and admits no converse.

## 9. The lower-scale Möbius/reciprocal form

Write $\mathrm{Rough}(q,B)=\sum_{c\le B,\;P^+(c)<q}\mu(c)$ for the Möbius prefix restricted to cofactors rough below $q$. `RHLean.Analysis.SquareRootBornSmoothReciprocalForm` puts the born-smooth mass into the same reciprocal form the transport already had.

Two structural facts make it clean. The smoothness cutoff is automatic on the born side: $q\le c$ together with $cq\le R^2-1$ already forces $q<R$. And the fibre of $q$ is a rough prefix over the window $[q,\lfloor X/q\rfloor]$, hence a difference of two lower-scale prefixes. The results are

$$
A_R^{\mathrm{born}}=1-\sum_{q\le R}\Big(\mathrm{Rough}(q,\lfloor X/q\rfloor)-M(q-1)\Big),
\qquad
T_R=\sum_{R<q\le X}\mathrm{Rough}(q,\lfloor X/q\rfloor),
$$

the second because $\lfloor X/q\rfloor<q$ above $R$ makes the roughness restriction vacuous and collapses $\mathrm{Rough}$ to $M$. Subtracting gives one signed sum over the whole prime range,

$$
A_R^{\mathrm{born}}-T_R=1-\sum_{q\le X}\mathrm{Rough}(q,\lfloor X/q\rfloor)+\sum_{q\le R}M(q-1),
$$

with no norm and no triangle inequality anywhere. The centered main-term difference $A_R^{\mathrm{born}}-T_R^{\mathrm{sm}}$ is the same object plus $D_R$, carried whole.

`RHLean.Analysis.SquareRootSmoothParityClasses` records the parity-class consequence. The sign of a smooth squarefree source is parity-determined, and adjoining a fresh top prime flips it, so the smooth population is mandatorily cancelling. Combining the two orientations, the prime-indexed Mertens prefix transform cancels exactly and leaves

$$
A_R=1-\sum_{q\le R}\mathrm{Rough}(q,\lfloor X/q\rfloor),
$$

each fibre the signed parity-class count of the $q$-rough pool truncated at the reciprocal cutoff.

The same module makes the residual gap explicit. Since

$$
M(X)=A_R^{\mathrm{pos}}+\big(A_R^{\mathrm{born}}-T_R\big),
$$

the matched criterion does **not** by itself bound the square-prefix Mertens value: the positive-orientation mass, which is exactly $-\sum_{q\le R}M(q-1)$, must be at the same scale. The module proves that the two RH-scale statements together bound the square-prefix Mertens Gram, as a hypothetical implication with both hypotheses named and unassumed.

## 10. Structural obstructions now proved

Three exact results constrain any future route. All are stated as ordinary theorems, not as estimates.

**The transport transform carries an exactly same-sign top block.** For a prime $q$ with $X/2<q\le X$ the reciprocal cutoff is $\lfloor X/q\rfloor=1$, so the only surviving cofactor is $c=1$ and the fibre contributes exactly $\mu(1)=1$. Every such prime contributes $+1$ and none contributes anything else, so

$$
\sum_{X/2<q\le X}\mathrm{Rough}(q,\lfloor X/q\rfloor)=\#\{q\ \text{prime}:X/2<q\le X\}.
$$

The block equals its own cardinality: no cancellation inside it at all. These are the sources $m=q$, a single prime, all carrying $\mu(m)=-1$; parity buys nothing because $\omega(m)$ is constant on the block. Bertrand makes it nonempty, and the splitting theorem places it inside $T_R$ as an exact summand. Any claim that the hyperbolic cutoff decomposes the transport population into complete cancelling orbits plus a bounded boundary must account for this block.

**Complete CRT periods do not fit the square clock.** The square-block transition window admits the injection $k\mapsto 4k+1$ into $\mathrm{Icc}(R^2,(R+1)^2)$, so it holds at most $2R+2$ cells, while an aligned CRT period holds exactly $\prod_{p\in P}p^2$. A complete period therefore sits inside the window only if

$$
\prod_{p\in P}p^2\le 2R+2 .
$$

When that fails the complete-period core is empty, the CRT interior mass is zero, and the entire physical mass is the square-clock boundary. Since strict Walsh contraction is only available for $p\ge11$, the threshold bites immediately: the three primes $\{11,13,17\}$ already give period $5{,}909{,}761$ and need $R\ge2{,}954{,}880$. The period is a product of squares, so it grows doubly exponentially in the number of selected primes while the window grows linearly in $R$.

**The middle/top count gap is a second-order prime-counting question.** At $X_R=R^2-1$ the prime-first transport splits into middle primes $R<q\le X_R/2$, whose reciprocal quotients lie in $[2,R)$, and inert top primes $X_R/2<q\le X_R$, whose reciprocal quotient is exactly $1$. The two populations satisfy $\text{middle}+\pi(R)=\pi(X_R/2)$ and $\text{top}+\pi(X_R/2)=\pi(X_R)$, so

$$
\text{middle}-\text{top}=2\pi(X_R/2)-\pi(X_R)-\pi(R).
$$

This identity is unconditional, but its sign is not decided by the qualitative $\pi(N)\log N/N\to1$: the leading $X/\log X$ terms cancel. Any proposal that cancels the same-sign top block one-for-one against the middle fibres must supply the stronger input, which is isolated in this package rather than inferred from first-order PNT.

A fourth, weaker constraint sits alongside them. Unrestricted fresh-prime equivariance between the prime-wheel mechanics and the canonical ancestry flow is false, because the ancestry parent strips the *largest* prime factor of the core while abstract insertion may adjoin a prime in any order. Equivariance is exact precisely on the ordered submove where the adjoined prime exceeds every prime already present in the parent core.

## 11. The shallow reciprocal crossing

The upper-middle reciprocal packet does not have to be processed to the end.

Let $x_n\to\infty$ be endpoints and $y_n$ cutoffs, and fix a reciprocal depth $K_0$ that eventually lies above the cutoff in the exact form $y_n\le x_n/(K_0+1)$. If the finite reciprocal coefficient at $K_0$ is negative, the intact packet eventually crosses at some depth $K\le K_0$, and for every $C>0$ that depth is eventually at most $C\log x_n$.

The mechanism is deliberately stated without the square parametrization; the square case is the instance $x_R=R^2-1$, $y_R=R$. One rational witness in the final step is checked by `native_decide`, and no decimal approximation or externally generated data enters the proof.

## 12. What the crossing leaves behind

Two objects must be kept apart. The **raw transport tail** is the increment from the partial packet to the completely processed post-root packet. The **coupled tail** adds the complete square-root-smooth population to that increment. The raw tail is not the terminal Mertens remainder; the exact terminal identity is

$$
M(R^2-1)=\text{partial crossing residual}+\text{coupled tail}.
$$

Once the partial residual is bounded by an absolute shallow depth, a critical root-scale estimate for the coupled tail is equivalent to the square-prefix Mertens energy criterion. The eventual crossing theorem supplies the shallow residual unconditionally. It does not supply the coupled-tail estimate, and that estimate is now the sharpest single open statement in this package.

The residual is then kept signed. For $1\le K<R$ there are three exact descriptions of the coupled tail: a direct remaining-layer cap, an Abel form in which the remaining transport is one signed Möbius/prime-prefix tail, and a lower-triangular renewal row obtained by subtracting the shallow crossing coefficients from the complete recursive replacement row *before* any norm. Under the replacement-fibre dictionary the packet layer is the negative cofactor-one prime face, so every fully admitted shallow layer cancels its prime diagonal exactly and the crossing layer retains precisely the negative number of unfilled seats. Both remaining orientations recombine as one signed Type-II cofactor-prime window mass and stay coupled to the strict descendants in a single signed double Gram.

Pushing that renewal back onto the cofactor coordinate gives the current form of the problem:

$$
\text{coupled tail}=\text{explicit packet baseline}-\sum_c\mu(c)\,\mathrm{Resp}(c),
$$

where each cofactor response carries its diagonal reciprocal-prime multiplicity together with every strict quotient descendant. So the entire remaining nonlocal cancellation is a literal finite correlation between the Möbius parity field and one intact rough-prime response field, with the centered mean/covariance form also recorded. No mean-zero assertion, norm split, probabilistic independence, or quantitative estimate is used anywhere on that path.

## 13. Transport without the prime-counting function

The high transport has been rewritten so that no irreducible prime-count coefficient remains. Each floor difference is the cardinality of a finite quotient interval, so the whole transport is a signed sum over triples $(c,t,k)$ with

- $1\le c<R$,
- $t$ a Boolean face of the primes through $R$,
- $R<P(t)\,k$,
- $c\,P(t)\,k\le R^2-1$,

and signed weight $\mu(c)(-1)^{|t|}$. Every arithmetic sign is a low-wheel sign; the high region survives only as the two hyperbolic inequalities.

The square-root geometry then removes the cofactor-face truncation entirely. Any active state satisfies $R<P(t)k$ and $P(u)P(t)k\le R^2-1$, which forces $P(u)<R$, so every face of product at least $R$ contributes zero automatically. Both coordinates therefore live on the *same* full low-prime Boolean cube, which is the symmetric carrier on which a prime can be toggled sequentially in either coordinate.

On that carrier the canonical least-prime cofactor/quotient involution cancels every interior state. The only fixed state is $(1,1)$, and summed over the Boolean face those fixed states are exactly the already-smooth squarefree population in $(R,R^2-1]$. Hence

$$
\text{transport}=\text{smooth}-M(R)+\mathrm{canonicalDefect},
\qquad
M(R^2-1)=M(R)-\mathrm{canonicalDefect},
$$

and the abstract missing-mate predicate can be removed completely: the defect is exactly the physical insertion state whose least-prime pivot is absent from the cofactor and whose pivot-removal quotient has crossed down through the root, an adjacent multiplicative shell state

$$
P(t)\,(k/p)\le R<P(t)\,p\,(k/p).
$$

The remaining fixed-amplification problem is therefore a signed estimate on one genuine first-failure frontier ledger, not on the full transport or a union of unrelated boundaries.

## 14. A fixed amplification constant is enough

The open square-root endpoint theorem is allowed an arbitrary fixed absolute amplification constant $A$:

$$
(M(R^2-1)-1)^2\le A\,R^2K_R,
$$

where $K_R$ controls the shifted critical energy on all lower arguments $y<R$. A subunit contraction is **not** required. For each $\varepsilon>0$, choose an onset at which $4A\le R^{\varepsilon}$; strong induction on the physical integer then closes the full shifted Mertens estimate, and the unfinished part of one square block contributes only $O(R^2)$ after squaring.

The cross-region reduction says where to aim that constant. The legal root/successor cancellation is overwhelmingly cross-region rather than fixed-prime fibrewise, and the exact decomposition already packages the relevant signed interactions into the positive-orientation smooth channel and the matched born-smooth/high-transport channel, with

$$
M(R^2-1)-1=\mathrm{positiveSmooth}(R)+\bigl(\mathrm{matched}(R)-1\bigr).
$$

Fixed critical-envelope amplification bounds for those two already-signed channels imply the full endpoint amplification theorem. Raw root or successor diagonals are not bounded, and the matched channel is not split by distinguished prime.

The endpoint sequence also carries the whole obligation. Inside a complete square block every integer lies within distance $R$ of one of the two completed-square endpoints, and the Mertens summatory function changes by at most the length of an integer interval, so arbitrary interior points contribute only an explicit $2R^2$ baseline beyond adjacent endpoint energy.

## 15. The quantitative analytic layer

Two analytic stacks are now present, and neither is a substitute for the arithmetic frontier above.

**The strong-Mertens corridor.** One shared corridor object reconciles the reciprocal-zeta estimate, the zero-free region, and the bounded-height zero-free box into a single positive constant $A$ and a single left boundary

$$
\sigma_A(T)=1-\frac{A}{(\log T)^{9}},
$$

so downstream contour code never destructs those existential theorems again, and no wide-strip reciprocal-zeta hypothesis is introduced. Above it sit the reciprocal-zeta kernel — where the removable value at the pole is handled by the residue limit rather than by pretending the literal function is continuous — the residue-free contour pull, the five-leg envelope, the boundary and small-height estimates, and the finite sharp-cutoff smoothing bridge, which uses no prime number theorem at all. Balancing at $r=(\log X)^{1/10}$, $T=e^{r}$, $\varepsilon=e^{-(A/4)r}$ turns all three envelopes into exponential decays in $r$ with only fixed polynomial factors, absorbed by weakening the exponential constant once.

**Centered K2 and the reciprocal moments.** The centered K2 argument consumes the reciprocal logarithmic Möbius moments

$$
A_m(N)=\sum_{n\le N}\frac{\mu(n)(\log n)^m}{n},
$$

not the summatory function directly. The finite Abel identity between them is exact for every $N$ and keeps its two analytic facts — summability of the Abel increments and vanishing of the endpoint term — as explicit hypotheses; a decay bound of the shape $|M(x)|\le Cx\exp(-c(\log x)^{1/10})$ discharges both. On the analytic side the zeta pole is removed with Mathlib's proved limit, the reciprocal germ is factored as $(s-1)q(s)$, and the second Taylor coefficient is read directly:

$$
\Bigl(\tfrac1\zeta\Bigr)''(1)=-2\gamma .
$$

On $\Re s>1$ that derivative is the logarithmic-square Möbius L-series, so one explicit Abel-boundary step remains. The factor-four corollary is independent of the unknown centered constant, which cancels between the two prefixes.

**Signed second-Selberg cancellation.** Separately and unconditionally, the exact signed kernel

$$
K_2(n)=(\Lambda*\Lambda)(n)-\Lambda(n)\log n
$$

has reciprocal mass $O(\log N)$, while the positive second von Mangoldt kernel has logarithmic-square reciprocal mass. This removes one full logarithm from the constant mode of the second Selberg operator before any wheel-frontier or error-profile estimate is applied. The tempting summatory shortcut is calibrated at the same time: the summatory signed kernel differs from $-2E(N)\log N$ by only $O(N)$, so a linear summatory bound would require precisely the logarithmic improvement of the physical PNT error that the current onset analysis does not provide.

The normalized recurrence layer explains why that improvement is not free. Dividing the exact signed first Selberg recurrence by the current endpoint leaves an absolute remainder rather than a term growing like $N$ or $N\log N$, and the reciprocal term becomes a nonnegative barycentric transform of the smaller normalized errors with total weight exactly $\log(N!)/N=\log N-1+O(\log N/N)$. The signed relation is therefore a scale-free near-averaging law, not an affine recurrence with a growing intercept.

## 16. The corrected-conductor Gram and its first uniform bound

The corrected-conductor sector must not be estimated packetwise. The decisive exact point is that the all-conductor raw boundary pairing can be split by its **boundary divisor** $d$ rather than by the original conductor $q$. Removing only the reindexed raw boundary divisors $d\le R$ leaves one collapsed signed core containing the conductor-one bulk, every large raw expansion layer, and the fully collapsed smooth term; the original high-conductor-plus-zero sector differs from that core only by the small reindexed raw boundary piece minus the already-controlled low corrected-conductor sector. No absolute value is placed on a high-conductor packet and the complete cross-conductor interaction stays inside one Gram quantity.

The first uniform quantitative consequence is elementary. A corrected conductor packet is $q$-periodic; reducing the endpoint to one incomplete period, bounding each divisor boundary by $2q^2$ and summing over at most $q$ divisors gives $2q^3$ for the complete boundary defect, and after the common torus normalization

$$
\lVert J_q(k,x)\rVert\le 6q^3 .
$$

Hence all nontrivial conductors $q\le R$ contribute at most $6(R+1)R^3$, that is $O(R^4)$, uniformly in the prefix length. Choosing a cutoff on the order of the eighth root of the arithmetic scale places that entire growing conductor sector at square-root size, restricting the remaining Gram problem to conductor one and conductors above the cutoff. No cancellation between distinct conductors is used to get there.

## 17. The processed-seat low-prime coordinate

The low-prime layer now sits on one finite object rather than on a sequence of ad hoc populations. `squareRootLowPrimeProcessedSeatCarrier` is the complete processed seat carrier: every state a fresh low prime can still act on, carrying its cofactor and its channel tag.

Two exact telescopes live on it, and neither is an estimate.

The running telescope evaluates the low-prime running state $T$ at every cutoff and proves that composite cutoffs contribute no change, so the state moves only at fresh primes. The global energy telescope then gives, for the ordered increments $\Delta_p$,

$$
\sum_{K<p\le U,\ p\ \text{prime}}\bigl(2\,T(p-1)\,\Delta_p-\Delta_p^{2}\bigr)=T(K)^{2}-T(U)^{2}.
$$

It is worth being explicit about what that identity does not do. A global energy decrement lower bound is *equivalent* to the terminal square bound, so a dissipation argument has to establish the decrement independently. Rewriting the telescope after assuming terminal control does not cross the quantitative gate.

The reciprocal crossing depth is also pinned exactly. The finite coefficient changes sign between the adjacent depths $18348$ and $18349$, and combined with the already-proved fixed-depth limit the square-root packet crosses at the single fixed depth $18349$ for every sufficiently large endpoint. Every fresh prime processed after the crossing is therefore strictly larger than $18349$.

## 18. Two Othello matchings on one carrier

The Othello principle used here is a finite parity statement, not a heuristic about local flips.

`RHLean.Proof.FiniteOthelloMatching` proves it in two forms. First, a matching involution on a finite signed region pairs every moving state with a state of opposite weight, so if at most one stable state remains the whole region has signed mass of absolute value at most one. Second — the form the canonical-liberty argument needs — if two different sign-reversing involutions act on the same signed region, the signed mass of the stable set of one equals the signed mass of the stable set of the other.

That second statement is what makes the move order a free choice. A large exposed frontier under one legal order may be replaced by the stable set of a quieter order without ever estimating the alternating paths between them.

Both matchings are then built on the processed-seat carrier.

The first plays the sequential fresh-prime edges in chronological order. `squareRootLowPrimeProcessedSeatMatchingInvolution` packages the entire chronology as a single involution: each state is paired at the first stage that removes it, and states never paired are fixed. Carrier preservation, involutivity, sign reversal on every moved state, and the identification of its fixed set with the iterated matching frontier are all proved.

The second plays the same legal edges in descending fresh-prime order. Its compiled legality layer proves carrier preservation, involutivity, sign reversal for every moved state, that the stable set is exactly the descending processed-seat frontier, and that the stable mass is `squareRootLowPrimeRunningImbalanceReal` by finite cancellation on the full carrier.

## 19. The no-liberty seam and the remaining rematching theorem

The two populations at the seam do not have the same element type. The true stable population of the descending matching is indexed by processed seats; the four-class endpoint boundary is indexed by tagged endpoints. Literal Finset equality between them is therefore not merely unproved, it is not the meaningful statement.

The correct closure object is a weight-preserving finite equivalence

$$
\mathrm{Stable}(\mathrm{match}_2)\;\simeq\;\texttt{squareRootLowPrimeProcessedSeatNoLibertyBoundary}\ R\ K\ j\ U,
$$

together with pointwise preservation of signed weight,

$$
\texttt{squareRootLowPrimeNoLibertyBoundaryWeight}(\varphi\,x)=\texttt{squareRootLowPrimeProcessedSeatWeightReal}(x).
$$

`RHLean.Proof.SquareRootLowPrimeNoLibertyFiniteEquiv` packages exactly that interface as `SquareRootLowPrimeNoLibertyWeightEquiv` and proves that any such equivalence transfers the entire signed sum. Combined with the compiled Othello cancellation theorem, that identifies tagged boundary mass with the running imbalance immediately.

So the arithmetic construction of $\varphi$ is the sole remaining carrier-specific obstruction at this seam. It has to classify every stable processed seat into exactly one of four endpoint coordinates — head, partial packet, born no-successor, and Go root equality — and prove inverse recovery together with native weight preservation.

No cardinality estimate is accepted as a substitute for that rematching theorem. Matching cardinalities on the two sides would not produce the signed identity, and the interface is deliberately written so that the missing step cannot be papered over by a counting argument.

## 20. The Go boundary layer

The hyperbolic Go recursion isolates a crossing population indexed by ordered primes $r<q$ and a squarefree parent $d$. At the square endpoint a strict crossing satisfies $R<rq$, while the proved first-contact geometry gives $q(rd)\le X_R$.

The strict part of that population needs no new estimate. The same incidence is already a literal state $(t,x)=(\{r\},(d,q))$ of the global low-wheel transport carrier, with transport weight exactly the Go source weight $\mu(qd)$, and it is not a canonical transport defect: the birth boundary forces $d>1$ and every prime factor of $d$ is strictly below $r<q$, so the canonical least-prime pivot of $dq$ lies in $d$. The canonical cofactor/quotient toggle removes that pivot, stays inside the physical transport carrier, and reverses the sign. Every strict Go crossing therefore already has its opposite-sign partner inside the global transport identity, before the canonical downcross frontier is formed.

What is left is the single arithmetic equality $rq=R$, where the transport root inequality is not strict. That is a root-boundary population rather than unfinished Euler recursion. It is packaged as one literal finite carrier and charged injectively to its parent coordinate $d<R$, so the resulting global boundary has cardinality at most $R$ with no remaining prime-owner multiplicity, and its signed Möbius mass is bounded by $R$ using only $\lvert\mu\rvert\le1$.

No estimate is made on the isolated Go crossing kernel. Strict crossings are returned to their transport partners first, and only the exact root-equality boundary is counted.

## 21. Recoupling to the smooth/transport residual

The low-prime sequential construction is a finite coordinate system for the historical signed interaction $S_R=A_R-T_R$. It must not introduce a new independent low-prime analytic obligation, and the recoupling layer proves that it does not.

At $P_R=R-\lfloor\sqrt R\rfloor$ the terminal state is exactly

$$
\text{terminal}=M(R^{2}-1)-A_R^{\mathrm{pos}}-\text{Packet}-\text{NearRoot},
$$

or, after the positive-orientation collapse,

$$
\text{terminal}=M(R^{2}-1)+\sum_{q\le R\ \text{prime}}M(q-1)-\text{Packet}-\text{NearRoot}.
$$

The two terminal boundary terms have total norm at most $R+K$. The only non-elementary amplitude left in the terminal state is therefore the old matched $A-T$ core.

The quantitative consequence is recorded conditionally. A bound

$$
\lVert\mathrm{Matched}_R\rVert\le 3R\sqrt{K}
$$

implies the exact endpoint estimate $T(P_R)^{2}\le 25R^{2}K$, and hence, through the proved global telescope, the desired signed response-child energy decrement. Those final theorems are hypothetical implications: they do not assert the matched-core bound, and this package does not claim the remaining arithmetic cancellation is solved. Their purpose is to make rigorous that the remaining quantitative input is the historical signed smooth/transport correlation rather than a separate low-prime frontier estimate.

One further reduction sharpens where a counting theorem would land. After every available fresh-prime matching has been played on the complete signed response-child carrier,

$$
\Bigl\lvert\sum_{K<p\le U}\Delta_p\Bigr\rvert\le\#\bigl(\mathrm{OwnedResponseMatchingFrontier}\ R\ K\ U\bigr),
$$

with no raw response weight and no number-of-fresh-primes factor left on the right. A cardinality theorem for that frontier at scale $R\sqrt K$ would give the deep processed-response estimate immediately.

## 22. The cumulative reduction: a prefix is two walls

The sitewise Othello laws say what one move does to one site. Applied term by term they describe the distribution of individual Möbius values, which is not the question a cumulative sum asks, and a term-by-term estimate discards the coherence the moment an absolute value is taken.

Playing the same two laws on a whole region at once removes that loss. For a prime $p$ the carrier toggle

$$
\tau_p(n)=\begin{cases} np & p\nmid n\\ n/p & p\mid n,\ p^2\nmid n\\ n & p^2\mid n\end{cases}
$$

is an involution of $\mathbb{N}$ whose moving states are exactly the $p^2$-free sites, where $\mu(\tau_p n)=-\mu n$, and whose frozen states are exactly the square hits, which carry no Möbius mass at all. Hence for any finite region

$$
\sum_{n\in S}\mu(n)=\sum_{n\in\partial_p S}\mu(n),
$$

where $\partial_p S$ is the escape part, the sites whose mate has left $S$. This is an equality: the whole interior has cancelled in mated pairs, and nothing is estimated.

For the region that actually carries a Mertens increment — the ordered prefix carrier $(L,x]$ — the escape part is completely explicit and consists of exactly two walls. The **anchor wall** is the set of sites carrying one factor $p$ whose quotient falls back past $L$, characterized by $n\le pL$; the **cutoff wall** is the set of $p$-free sites whose $p$-multiple overshoots $x$, characterized by $x<np$. Peeling a list of distinguished primes iterates the construction and preserves the equality on the iterated boundary.

The same transport applies to the pinned primorial-wheel residual and to a whole consecutive run of complete square blocks, where the known square telescope removes the block count and the fixed-prime pairing then reduces the resulting cumulative interval to its two walls. If some finite peel leaves an iterated boundary of RH-scale population, the Mertens energy criterion follows.

Two scope statements belong with this. First, for one fixed $p$ every orbit is a two cycle or a fixed point, so this is a global *pairing* of a cumulative region, not a statement about long alternating components, and it contains no birth-to-capture cancellation. Second, the single-prime wall cardinalities are honest but are not yet a saving: they are the quantity a later multiplicity theorem has to bound. The measured behaviour is unambiguous — the fixed-prime peel bottoms out at $2/\pi^2$ of $x$ in every prime order, and even a maximum state-dependent matching leaves a positive proportion exposed.

That measurement is now a theorem. On the raw prefix carrier every squarefree site has a legal prime move, so the true no-liberty boundary consists of square hits only and carries no mass; a liberty-exhausting mate would therefore force $M(x)=0$. And every prime $p$ with $x<2p$ has the single legal move $p\mapsto1$, so all top-half primes compete for one neighbour and any adaptive involution has a fixed set of at least $\pi(x)-\pi(x/2)-1$ states. The carrier, not the matching, is what has to change — which is exactly why the processed-seat carrier of section 17 records multiplicities instead of bare integers.

## 23. Lifetime cancellation across square time

A prime-toggle pairing has no trajectory in it; the Go statement does. An atom of the square-time process has a birth stage and a capture stage, and its activity indicator is the indicator of the half-open lifetime, so activity increments telescope over a run and an atom born after the run starts and captured before it ends contributes

$$
0-0=0
$$

whatever its lifetime was. A stone that lived one stage and a stone that lived ten thousand stages cost the run exactly the same: nothing. The length of the lifetime appears nowhere in the statement or in the proof, which is the property a cumulative run needs and which a fixed-prime pairing does not provide.

The model is proved faithful rather than assumed. For a nonnegative cutoff slope the moving-high threshold is nondecreasing, so an atom alive at $t$ and already born at $s\le t$ is alive at $s$: death is permanent, and there is no resurrection between birth and capture. What is established is interval structure plus endpoint telescope, and the aggregate run identity in the existing $\mathrm{Active}=\mathrm{Birth}-\mathrm{Death}$ coordinates; explicit birth and capture times are not constructed, and the package says so.

## 24. The frozen square run and the canonical downcross frontier

On a subdoubling run $[a^2,(b+1)^2)$ with $(b+1)^2\le 2a^2$, every proper divisor consulted by any new site lies strictly below $a^2$. So the signed frozen kernel

$$
K(a,b)=\sum_{1\le d<a^2}\mu(d)\,w_{a,b}(d),\qquad w_{a,b}(d)=\Bigl\lfloor\frac{(b+1)^2-1}{d}\Bigr\rfloor-\Bigl\lfloor\frac{a^2-1}{d}\Bigr\rfloor,
$$

is exactly the negative new Möbius mass, and no value of $\mu$ created inside the run appears in it. The energy premise squares the *whole signed divisor sum*, not any term of it.

The bridge to the wheel side is a single algebraic law. Admitting one fresh Euler prime $p$ to a finite old universe $S$ acts on a signed window by

$$
W_{S\cup\{p\}}(A,B)=W_S(A,B)-W_S(\lfloor A/p\rfloor,\lfloor B/p\rfloor),
$$

so a new prime leaves one compressed predecessor-cube window rather than another independent copy of an old parent. This is the finite replacement for the prime-gap lifetime picture. Combining it with the canonical low-wheel involution $M(R^2-1)=M(R)-D_R$ gives

$$
K(a,b)=(M(a)-M(b+1))+(D_{b+1}-D_a),
$$

whose Mertens gap costs at most the root interval length. Hence the energy of the *change* in the canonical downcross frontier is equivalent, with no loss, to the frozen-square-run criterion, the global Mertens-energy criterion, the maximal signed square-run criterion, and the synchronized primorial-wheel residual criterion.

After exact late-parent cancellation the downcross ledger *is* the canonically oriented Euler first-crossing ledger, and on one oriented state the Boolean faces that charge it are exactly the frozen faces of the old universe below its canonical pivot. Both run endpoints then extend to a common state carrier on which each state keeps the same owner and only its two window endpoints move with the root, which is the representation a run difference needs before it is squared.

The counting route stops here, provably. The faces charging one boundary state are carried injectively into a single state-dependent interval, at most $R$ of the $2^{\pi(R)}$ faces carry any downcross mass, and the resulting unconditional bound $\lVert D_R\rVert\le R^4$ is worse than the trivial $O(R^2)$. That is not a lossy step: the unsigned ledger mass already dominates $\pi(R^2-1)-\pi(R)$ at the empty face alone, since $k\mapsto(1,k)$ embeds every prime of $(R,R^2-1]$ with weight $+1$ and face sign $+1$. No bound of the shape $\lVert D_R\rVert\le CR$ is reachable by discarding signs.

A scope note belongs with the seam itself. The linear form $\lVert D_R\rVert\le CR$ would give $\lvert M(R^2-1)\rvert\le(C+1)R$ and hence $M(x)=O(\sqrt x)$, the strong Mertens bound, which is open and widely believed false. The energy bridge only ever consumes the square-prefix energy statement, so the correct seam is the $1+\varepsilon$ form, and the base of that statement is exactly the root $R$: no off-square interpolation is duplicated.

## 25. Squaring first: Green--Kubo on the physical line

The vertical-line layer squares the whole signed birth/death population before taking any absolute value. At each physical child integer $n$ define one real event variable: $0$ if the child has the same endpoint status, $-\mu(n)$ if it is born into the active set, $+\mu(n)$ if it dies out of it. Their sum is exactly the vertical-interval mass, so

$$
\lVert V(a,b)\rVert^2=D_{\text{line}}+2\,C_{\text{line}},
$$

with $C_{\text{line}}$ a masked Möbius pair sum, not a probabilistic covariance.

The diagonal is then bounded twice, and the second time exactly. Every event lies in $\{-1,0,1\}$ and every active child at root $R$ is below $R^2$, which already gives $D\le(b+1)^2$ and, under strict subdoubling, $D\le 2a^2$. Sharpening the pointwise envelope to $\mathrm{event}(n)^2\le\mu(n)^2$ replaces that by the exact finite squarefree population $K-1-Z(K-1)$. So the limiting $40/30/30$ law is used only in the safe direction — the zero population sharpens the diagonal — and no $30/30$ sign balance is asserted on the arithmetically selected birth/death set.

What remains is therefore one quantity and nothing else:

$$
\lVert V(a,b)\rVert^2\le 2a^2+2\max(0,C_{\text{line}}).
$$

The carrier underneath it is completely normalized. The active-child set is exactly the squarefree shell $\{n:\ R<n<R^2\}$, with a constructive converse; fresh-prime membership instability is exactly birth or top escape, so there is no residual mysterious population; and a completely stable prime family has exactly the lower-prefix covariance, so prime-stable covariance is recursive rather than new. Failure of that descent is owned by one of the two physical walls.

This layer also fixes the discipline for coordinate changes. The complex/Fermat strip, the ordered Euler cut, the oriented downcross ledger, the signed prefix lifetime residual, and the canonical defect ledger are proved to be one signed object, and each new energy proposition is stated as an open `Prop` and then proved *equal* to the pre-existing canonical oriented-run seam. Exact equality among coordinates removes duplicate seams and supplies no quantitative cancellation; the package records that explicitly rather than presenting a coordinate change as progress.

## 26. The Euler contraction on the critical reciprocal carrier

The native square-prefix argument does not delete a fresh-prime parent/child pair. It compresses the pair back onto the parent with the exact Euler factor $1-1/p$, and transporting that mechanism to the RH-critical rough covariance carrier gives

$$
v_R(c)+v_R(cp)=\Bigl(1-\frac1p\Bigr)v_R(c)+\frac{\mu(c)}{cp}\bigl(T+E-B\bigr),
$$

with $T$, $E$, $B$ the exact order-threshold, top-escape and lower-root birth cardinalities. No norm, independence assumption, or analytic estimate enters, and the factors accumulate exactly on the Boolean square, which is the finite model for a chronological descending compression.

Four things then sharpen it.

- **The zero mode is recoupled.** The protected object is the *uncentered* correlation $\mathrm{Corr}_R=M(R-1)-M(X_R)$, whose critical control is equivalent to the square-prefix energy criterion. The reciprocal parity zero mode obeys the same pure Euler factor with no defect, so adding back the response mean gives the uncentered coordinate with exactly the same defect law. The many-prime theorem is then iterated on the *actual* compressed parent carriers, with unpaired states retained in an explicit transported survivor ledger rather than pretending an arbitrary carrier is uniformly multiplied by the Euler product.
- **One channel is eliminated.** On a complete sub-root Euler cube — full wheel product through $p$ still below $R$ — the threshold-loss channel is literally empty, top escapes are forced strictly beyond the root, and births stay strictly below it. The critical signed boundary is exactly post-root top escape minus lower-root birth. Beyond the root a fresh prime supplies no new contraction at all, so useful contraction has to be earned on sub-root primes.
- **The defects telescope.** With its native $1/p$ restored, one physical defect shell is exactly $T_{P\cup\{p\}}(N)-(1-1/p)T_P(N)$: the discrepancy between the true next truncated Euler cube and the uniform contraction. Transporting these over a descending prime list is a telescope closing on the single boundary $T_L(N)-\prod_{q\in L}(1-1/q)$, which replaces the earlier majorant by a structural identity taken before absolute values.
- **The return is exact.** The reciprocal-weighted upper column telescopes to one terminal boundary, while the literal physical columns carry no $1/q$ and therefore produce a prime-weighted discrete boundary variation. Finite summation by parts closes that into the primitive $\sum_{n<K}B_n(X)-K\,B_K(X)$, so the RH-critical object attached to the physical columns is that combination and not the endpoint boundary alone. Returning from reciprocal prefixes to the unweighted numerator is likewise an exact Abel transform, costing only an absolute constant.

An adaptive variant of the same descent deletes only the paired child copy, so no survivor mass is frozen and every still-unpaired state stays available to later prime coordinates. There a descending schedule provably leaves no nontrivial squarefree survivor, the unweighted correlation annihilates with coefficient *zero* rather than an Euler factor, and the only obstruction to transporting an accumulated coefficient is a mismatch created when a commuting-square corner is missing from the physical carrier. Iterating gives a chronological formula with two explicit signed ledgers and nothing frozen.

One honest negative belongs here. Injecting the three channels into explicit reciprocal windows does give the development's first global estimate on $T$, $E$ and $B$, but the step from three window cardinalities to one ledger is a triangle inequality, and it discards precisely the sign structure the compression was built to keep. The package states that, declines the same step on the critical windows, and records the route in `boundary/dead_lanes.json`.

## 27. Block covariance, refinement, and family descent

The Green--Kubo expansion is an identity about *pairs*, so partitioning the index range partitions the pairs. For signed blocks,

$$
S_K^2=E_K+2X_K,\qquad\text{hence}\qquad 2X_K=S_K^2-E_K,
$$

which says cross-block coherence is not a free adversary: it is pinned by the total mass and the block energy. A route that replaces the signed blocks by magnitudes and only then squares is allowing every block to align independently, and the identity above measures exactly what that discards.

Instantiated at the literal square blocks this gives the partition of the global integer-order covariance into within-block and cross-block parts, on one carrier, with no domination hypothesis anywhere. Two exact consequences follow, and they pull in opposite directions.

The square-block energy exceeds the exact squarefree diagonal by *precisely* twice the aggregate within-block covariance, $E-Q=2\sum_j C_j$. So proving $E\ll N^{1+\varepsilon}$ *is* proving that aggregate is of RH scale; the linear behaviour that finite measurement shows must not be promoted to a theorem. The way forward is not to bound $E$ but to refine it: each refinement of the blocks into signed children moves energy into the children and leaves an explicit signed cross term, and iterating to singletons makes the leaf energy exactly the squarefree diagonal, which is linear with no conjecture at all. Every unordered Möbius pair is then charged to the unique node at which its two entries first separate — the Green--Kubo identity rewritten as an Euler covariance tree, with every signed cross term preserved on the way down.

The second consequence is a genuine descent. For a prime $p$ and cofactors below it, $\mu(pc)=-\mu(c)$ but $\mu(pc)\mu(pd)=\mu(c)\mu(d)$: multiplication by $p$ *reverses* family mass and *preserves* family pair covariance. A post-root prime family is therefore an isometric copy of a lower-scale prefix as far as covariance is concerned, and summing over post-root primes turns a supercritical scale into a sum of strictly lower-scale covariances. Stated as a descent on the signed aggregate covariance itself, this forbids a *minimal* supercritical excursion and hence any, which gives the one-sided frontier statement and the Mertens energy criterion.

The same section records what the support-only route still owes, and the answer is a full power. Keeping the lag-zero diagonal sharpens the frontier capacity to $(F^2-Q)/2$, but the minimising pivot is $\ell=2$, whose frontier is the squarefree part of $(X/2,X]$ with density $2/\pi^2$, so $F$ is linear and $F^2$ stays quadratic. Two thresholds must also not be conflated: crossing the literal $\sqrt x$ line is the threshold of the *false* Mertens conjecture, whereas the RH threshold is the strictly weaker $C(x)\le x^{1+o(1)}$, and an RH-violating excursion of exponent $\varepsilon$ needs $C$ of order $x^{1+2\varepsilon}$ — a fixed power above target, not a constant factor.

At run level the same algebra gives the seam its final form. The window identity splits the run covariance into a descended part and an escape remainder, *exactly*, for any proposed descended part; a nonpositive descended part together with RH-scale escape covariance gives the global criterion. What that escape must contain is stated rather than hidden: it holds the cross-square-block pairs any narrower descended part leaves behind. And the obvious candidate for the descended part is closed — on a subdoubling run, stripping a prime from a physical endpoint sends it below the run anchor, so the same-prime negative leaf is empty exactly where the frozen-prefix mechanism applies, the escape is literally the whole covariance, and the unique fresh-prime owner cube always straddles both run boundaries. Four-corner cancellation is genuinely nonlocal in square time.

## 28. The first-jump residual and its recombination

Ordered dense divisibility becomes quantitative at the root scale. With $s=\lfloor\sqrt R\rfloor$, a face of product at most $R$ that is triply predecessor-dense above $s$ has every prime coordinate at most $s$, since a coordinate $p>s$ would satisfy $p^4\le sR<(s+1)^4\le p^4$. So the dense part of every frozen predecessor window collapses *exactly* onto the smaller Boolean cube, leaving the complementary first-jump mass signed:

$$
F_{q^-}=F_{\sqrt R}+J_{q,\sqrt R}.
$$

The first jump is then one-dimensional: at the same physical cutoff, a jump $p>\sqrt R$ can have no later prime coordinate at all, because two primes above $\sqrt R$ already multiply past $R$. The residual is an exact high-prime ledger with a completed lower-scale Mertens gap at each prime, and no fixed-prime absolute value is taken.

Estimating that ledger one first-jump prime at a time does not work, and the reason is now compiled. For a post-root prime with $R/2<p$ the packing factor $R/p$ is $1$, yet the same prime stays live under every later oriented owner $p<k\le(R^2-1)/p$; once the owner window is below $2p$ the whole canonical $p$-slice is the singleton Boolean face $\{p\}$ with signed mass $-1$, so the fixed-$p$ aggregate is exactly the negative cardinality of that owner interval — prime-count size. Expanding instead on a common low-cofactor carrier and swapping to global cofactor columns gives a cleaner object but not a smaller one: the proposed column estimate $\lVert G_R(d)\rVert\le R/d$ fails on direct finite tests for the same reason, and is retained only as a diagnostic conditional.

The exact correction is recombination. The first-jump aggregate has to be joined with the square-root-dense piece *before* a critical norm is taken, and the recombined scalar is exactly the canonical defect ledger — through the vertical-line normalization, the signed squarefree shell between $R$ and $R^2$. On that object the canonical rough correlation differs by only the single root Möbius atom, and its reciprocal prefixes are precisely the coordinate on which the Euler factor $1-1/p$ of section 26 acts. A uniform reciprocal-prefix bound of size $(\log R+1)/R$ then gives the root-scale bound on the recombined defect, with no first-jump-prime or cofactor-column norm inserted anywhere in the argument.

The same bridge carries the post-root subtraction. Grouping post-root primes by reciprocal band gives a family covariance that is exactly a band cardinality times a lower-scale covariance, the total family covariance is an energy difference, and what is left over is exactly the Bessel defect — so "the post-root remainder is linear" and "the Bessel defect is linear" are one hypothesis, not two. That subtraction is a genuine partition rather than an inclusion--exclusion estimate: two distinct post-root primes cannot divide a common physical site below the endpoint, so the literal family pair carriers are pairwise disjoint.

Underneath both sits an exact signed descent on the quadratic carrier. Every nonzero physical pair has a unique first differing Euler prime; that owner strictly decreases under stripping, the parent’s fresh-prime set is the child’s with the owner erased, and the pair is one *mixed* corner of the owner’s fresh-prime square. Stripping the owner therefore reverses the pair weight exactly, which is what makes owner promotion a finite signed descent rather than a re-indexing.

## 29. The forward analytic consumer is unconditional

Two statements about conditionality have to be kept apart, and this section is the one that changed.

The reduction from the projected-renewal Gram form down to $\lVert M(x)\rVert^2\le C(x+1)^{1+\varepsilon}$ is proved outright: no criterion, realization, partition, or low-increment control is supplied by the caller, and the only hypothesis is nonnegativity of the slope. Above it, the classical Mertens criterion used to be accepted as an ordinary theorem argument — visible in the signature, absent from `#print axioms`, and never constructed here.

The direction the route actually consumes is now constructed. From $\sum\mu(n)n^{-s}=1/\zeta(s)$, partial summation gives convergence on $\mathrm{Re}\,s>1/2$; the limit is analytic there and agrees with $1/\zeta$ on $\mathrm{Re}\,s>1$; the identity theorem forces $\zeta\ne0$ on $\mathrm{Re}\,s>1/2$; and the functional equation reflects that to the left half. No contour shifting and no zero-free region is used. The reverse implication needs the harder contour argument, is not needed by this route, and is not asserted.

Consequently `RHLean.Proof.TerminalMertensForward.riemannHypothesis_of_squarePrefixEnergy` has the square-prefix energy estimate as its *only* hypothesis, and it is guarded by `#print axioms` with the same three standard axioms as the rest. The historical equivalence theorems still take the full classical criterion as an argument, and that conditionality remains visible in their signatures; the forward route no longer does.

## 30. What is not sufficient

The following do not advance the quantitative frontier by themselves:

- uniformity of the 27 three-slot states;
- a Markov model for successive cells;
- independence assumptions for neighboring Möbius values;
- separate absolute estimates for `R` and `H`;
- separate absolute estimates for $Q_R$ and $E_R$;
- a constant collision error charged independently to every prime pair;
- a positive residue-energy bound that discards the signed parity cross term;
- a local finite-difference bound without controlling the support or signed covariance of the nonzero stencils;
- a further exact coordinate change identifying the recombined state with the Mertens prefix in new notation.
- a bound on the raw transport tail in place of the coupled tail, which differs from it by the complete square-root-smooth population;
- a diagonal estimate or triangle inequality applied to the post-crossing renewal row, which is the object built to keep the cancellation;
- a reintroduction of prime-counting coefficients into the transport after they have been removed;
- a one-for-one cancellation of the inert top block against the middle prime fibres without deciding the sign of the exact count gap;
- a subunit contraction where a fixed amplification constant already suffices — sharpening the constant is not progress toward the missing inequality;
- a cardinality match between the stable processed-seat population and the tagged no-liberty boundary in place of the weight-preserving equivalence, since equal counts do not produce the signed identity;
- a fresh estimate on the isolated Go crossing kernel, when every strict crossing already has an opposite-sign partner inside the global transport identity and only the exact root-equality face remains;
- a global energy decrement asserted from terminal control, which the exact telescope makes equivalent to the conclusion rather than a route to it;
- a low-prime frontier estimate presented as new analytic content, when the recoupling identity shows the only non-elementary amplitude in the terminal state is the historical matched $A-T$ core;
- a bound on the square-block energy $E$ presented as an independent linear fact, when $E-Q=2\sum_j C_j$ makes it exactly the aggregate within-block covariance;
- an estimate on the surviving support of an Euler peel, or on the unsigned mass of the downcross ledger, since both are provably superlinear and leave a full power;
- a matching that restores state-dependent freedom on a raw interval carrier, which the top-half primes obstruct outright;
- a fixed first-jump-prime or fixed cofactor-column norm, in place of recombining the first-jump aggregate with the square-root-dense piece before any norm;
- a square-run split whose descended part is the fixed-prime leaf, which is empty on exactly the subdoubling windows where the mechanism applies;
- a linear seam $\lVert D_R\rVert\le CR$, which is strictly stronger than RH needs and would give the strong Mertens bound;
- a further coordinate identification of the vertical, ordered Euler, oriented, lifetime and canonical defect ledgers, which are already proved equal, with their energy statements proved equal too.

The target remains the signed object itself.

Three specific proposals are now closed, with reasons recorded in `boundary/dead_lanes.json`:

1. **Bounding the complete smooth mass $A_R$.** The complete smooth mass is not the RH residual. Because $X=R^2-1$, every source below $R^2$ has at most one prime factor above $R$, so $A_R=M(X)+T_R$ exactly, and $A_R$ carries the whole transport drift. Only the orientation-split object is at square-root scale.
2. **Transporting a CRT product law onto the physical square-prefix transport.** Blocked by both obstructions in section 10, and independently by a multiplier ceiling: the recombination terminates in the weight-one Walsh multiplier $\lambda_q=(q^2-2q-4)/(q^2-6)$, whose product over primes is a Mertens product of order $(\log y)^{-2}$. A product of local multipliers of the form $1-c/q$ cannot beat a power of a logarithm.
3. **Row-energy Cauchy–Schwarz on a lower-triangular endpoint operator.** Writing $E_R=\sum_{y<R}a_R(y)(M(y)-1)$ and asking for $\sum_{y<R}(y+1)\lvert a_R(y)\rvert^2\le AR$ is not a weaker statement. The least-norm solution of that single linear constraint has

$$
\min\sum_{y<R}(y+1)\lvert a_R(y)\rvert^2=\frac{\lvert E_R\rvert^2}{\sum_{y<R}\lvert M(y)-1\rvert^2/(y+1)},
$$

so the existence of any admissible coefficient vector is a statement at least as strong as the conclusion. Cauchy–Schwarz is an identity at the optimum: it loses nothing and therefore supplies nothing, and the optimal coefficients $a_y\propto (M(y)-1)/(y+1)$ require the data being bounded.

4. **The literal same-site collision-defect quotient.** The strongest literal realization of the section-4 chain weights every defect label by the corrected prime-wheel field on the same physical site that realizes its selected-prime square collision. Every such weight vanishes at the square hit, so every step mass and hence every finite bounded chain mass is zero, contradicting the first nontrivial square prefix $-1$; this is a kernel-checked contradiction, not an estimate. The adjacent-cell escape fails too: for $p\ge7$ a $p^2$ hit leaves only exponent states $0$ and $2$ across the current and next active cells, and the exponent flip exchanges $0$ and $1$ while fixing $2$, so any realized flip in those two cells is the trivial square state where both corrected weights vanish. A viable quotient must transport a collision label to a different arithmetic fibre before reading its corrected weight, and must then separately prove that the transport preserves square-block mass and has bounded global multiplicity.

5. **Unsigned support capacity.** Bounding the covariance by a count of surviving support fails by a full power, in three separate places. The minimising Euler pivot is $\ell=2$, whose first-failure frontier is the squarefree part of $(X/2,X]$ with density $2/\pi^2$, so $F$ is linear and even the sharpened capacity $(F^2-Q)/2$ stays quadratic against an $x^{1+\varepsilon}$ target. The triangle inequality $\lVert T+E-B\rVert\le T+E+B$ on the reciprocal defect ledger discards exactly the Euler sign structure the compression was built to preserve. And the canonical downcross ledger has superlinear unsigned mass, since $k\mapsto(1,k)$ embeds every prime of $(R,R^2-1]$ at the empty face with weight $+1$, so no bound of the shape $CR$ survives discarding signs there either. A capacity theorem has to be a signed identity or recurrence taken *before* absolute values.
6. **Adaptive matching on the raw prefix carrier.** Allowing the matching prime to depend on the state does not rescue $(0,x]$. Every squarefree site has a legal move, so the true no-liberty boundary is square hits only and carries no mass; a liberty-exhausting mate would force $M(x)=0$. Independently, every prime $p$ with $x<2p$ has the single legal move $p\mapsto1$, so all top-half primes compete for one neighbour and any adaptive involution has fixed set of size at least $\pi(x)-\pi(x/2)-1$. This is a negative control, and it is what makes the processed-seat multiplicity load-bearing rather than cosmetic.
7. **A fixed first-jump-prime seat bound.** For $R/2<p$ the numerical packing factor is $1$, yet the canonical $p$-slice stays live under every later oriented owner in $(p,(R^2-1)/p]$ and aggregates to the negative cardinality of that interval. The proposed global cofactor-column replacement $\lVert G_R(d)\rVert\le R/d$ fails on direct finite tests for the same reason. The correction is recombination with the square-root-dense piece, and the recombined scalar is the canonical defect ledger.
8. **The fixed-prime descended leaf on subdoubling runs.** Splitting a square-run covariance into a same-prime negative leaf and a top-escape remainder is circular where it applies: stripping any prime from a physical endpoint of a subdoubling run sends it strictly below the run anchor, so the leaf is empty and the escape is literally the whole covariance, whose RH-scale bound is equivalent to the global criterion. The unique fresh-prime owner cube always straddles both run boundaries, so four-corner cancellation is genuinely nonlocal in square time.

## 31. Recommended order of work

The exact layers above are complete, and further identities are not the bottleneck. What is missing is one genuine inequality on a single signed state. This revision changed which state that should be: five coordinate systems were proved to be one object, the pair sum is now squared before any absolute value on three different carriers, and an exact Euler contraction acts on the critical one. Ordered by whether the success mode can produce a power saving at all:

1. **The positive line covariance.** After the squarefree diagonal sharpening, the entire vertical-line energy is $\lVert V(a,b)\rVert^2\le 2a^2+2\max(0,C_{\text{line}})$ on strict subdoubling runs. The diagonal is already at the required scale, the carrier is exactly the squarefree shell $\{n:R<n<R^2\}$, and every failure of prime-family descent is one of two named physical walls. This is the sharpest statement of the remaining problem in the package, and it is a statement about a signed covariance, not about a population.
2. **A contractive recursion for that covariance.** The exact reciprocal Euler contraction $1-1/p$ of section 26 acts on the critical coordinate, with the threshold channel empty on a complete sub-root wheel and the defect shells telescoping to one truncated-wheel boundary. The open question is whether that contraction can be transported onto the now-identified vertical/canonical-defect increment while birth and top escape remain a signed physical defect, so that the positive covariance obeys a genuinely contractive recursion of the shape
   $$
   C_{\text{current}}=\text{contracted lower-prefix covariance}+\text{signed boundary defect}.
   $$
   Every stable prime family must be reindexed to a strictly lower prefix, the contraction coefficient must come from an exact Euler factor rather than an assumed density, every failure of descent must be explicitly a wall crossing, and no triangle inequality may be applied until all cross-family signed cancellation has been exposed. If such a recursion exists, iterate it before estimating the remaining boundary.
3. **Refinement rather than a bound on the block energy.** $E-Q=2\sum_j C_j$ makes bounding $E$ the same problem, but each refinement step moves energy into children plus an explicit signed cross term and terminates at the linear squarefree diagonal. Combined with the post-root family isometry, this is the descent formulation, and it is the one route in the package whose intermediate quantities are allowed to oscillate arbitrarily.
4. **Global bounded multiplicity on a peel boundary.** A cumulative prefix is exactly two walls, and the construction iterates. The single-prime wall cardinalities are honest but not yet a saving; the missing theorem is a multiplicity bound on the iterated boundary, which is a statement about a boundary rather than about individual Möbius seats.
5. **The canonical rough-prime correlation** of section 12, one finite correlation between the Möbius parity field and one intact rough-prime response field, with the packet baseline explicit and no norm taken on the way to it.
6. **The canonical transport defect** of section 13, a signed estimate on a single first-failure frontier ledger whose states are an explicit adjacent multiplicative shell.
7. **The collision-defect chain** of section 4, still the sharpest conditional route packaged in Lean, restricted by the refutation in section 30 to realizations that transport a label off its own square-hit site.
8. **The no-liberty rematching theorem** of section 19. This is a construction rather than an inequality, and its four branches are now built individually with membership, injectivity and exact weight preservation; what remains is the classifier that routes every source state to a branch, plus the one named `Partial` budget.
9. **The matched-core bound** of section 21, $\lVert\mathrm{Matched}_R\rVert\le 3R\sqrt K$, or the sharper Mertens tracking form. Because $M(R^2-1)-A_{\mathrm{pos}}(R)$ is *exactly* the matched channel, the tracking hypothesis is literally the matched-channel bound and reaches the terminal imbalance at $CR+R+K$ rather than $(C+8)R+K$. Bounding $M(R^2-1)$ and the middle population separately would not help: it would force $M(x)=O(\sqrt x)$, so the content is entirely in the correlation between them.
10. Transfer any resulting complete-cell or square-prefix estimate to arbitrary cutoffs using the proved additive-$3$ endpoint theorem and the nearest-square endpoint domination of section 14, then feed it through the recovered-wheel and Mertens-energy bridges into the forward analytic consumer, which now carries no criterion hypothesis of its own.

The bottleneck is no longer an unspecified local pairing theorem, no longer a missing coordinate identity, and no longer a choice of carrier. It is the **signed cancellation of a positive aggregate covariance on a carrier that is already normalized, already squared before absolute values, and already equipped with an exact Euler contraction**.

Any candidate closure must survive four checks the package can already apply to it.

1. **Support-only no-go.** Support and capacity control is a full power too weak, in every coordinate where it has been tried. A proof that ultimately bounds the critical signed defect by its cardinality is not the missing argument.
2. **Top-escape no-go.** On strict subdoubling runs the natural same-prime nonpositive leaf can be empty and its top escape can equal the whole square-run covariance. "Top escape is thin" is not by itself a gain.
3. **No selected-carrier sign balance.** The limiting $40/30/30$ Möbius density cannot be transferred to the birth/death/escape carrier without proof. The safe use of squarefree density is the diagonal sharpening already compiled.
4. **No hidden RH-strength input.** If an intermediate lemma would itself imply the terminal energy estimate by a trivial bridge, it is the hard theorem rather than an elementary auxiliary fact — and the linear downcross seam is exactly such a case, since it would give the strong Mertens bound.

Separately from those inequalities, one exact construction is outstanding: the weight-preserving classifier of section 19. It remains the only place in this package where a compiled cancellation theorem is waiting on a rematching map rather than on an estimate.
