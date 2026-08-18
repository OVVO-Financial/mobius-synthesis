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

The synthesis ledger records this as revision 3. The affine-excursion and two-obligation prime-sieve modules expose further exact coordinates for a contraction argument, but they do not by themselves supply the missing power saving.

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

Two exact results constrain any future route. Both are stated as ordinary theorems, not as estimates.

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

## 11. What is not sufficient

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

The target remains the signed object itself.

Three specific proposals are now closed, with reasons recorded in `boundary/dead_lanes.json`:

1. **Bounding the complete smooth mass $A_R$.** The complete smooth mass is not the RH residual. Because $X=R^2-1$, every source below $R^2$ has at most one prime factor above $R$, so $A_R=M(X)+T_R$ exactly, and $A_R$ carries the whole transport drift. Only the orientation-split object is at square-root scale.
2. **Transporting a CRT product law onto the physical square-prefix transport.** Blocked by both obstructions in section 10, and independently by a multiplier ceiling: the recombination terminates in the weight-one Walsh multiplier $\lambda_q=(q^2-2q-4)/(q^2-6)$, whose product over primes is a Mertens product of order $(\log y)^{-2}$. A product of local multipliers of the form $1-c/q$ cannot beat a power of a logarithm.
3. **Row-energy Cauchy–Schwarz on a lower-triangular endpoint operator.** Writing $E_R=\sum_{y<R}a_R(y)(M(y)-1)$ and asking for $\sum_{y<R}(y+1)\lvert a_R(y)\rvert^2\le AR$ is not a weaker statement. The least-norm solution of that single linear constraint has

$$
\min\sum_{y<R}(y+1)\lvert a_R(y)\rvert^2=\frac{\lvert E_R\rvert^2}{\sum_{y<R}\lvert M(y)-1\rvert^2/(y+1)},
$$

so the existence of any admissible coefficient vector is a statement at least as strong as the conclusion. Cauchy–Schwarz is an identity at the optimum: it loses nothing and therefore supplies nothing, and the optimal coefficients $a_y\propto (M(y)-1)/(y+1)$ require the data being bounded.

## 12. Recommended order of work

The exact layers above are complete, and further identities are not the bottleneck. What is missing is one genuine inequality on a single signed state. Ordered by whether the success mode can produce a power saving at all:

1. **Scale-descent contraction.** A fixed contraction factor $\rho<1$ per dyadic scale, iterated over $\log R/\log 2$ descents, yields $\rho^{\log R}=R^{-c}$ — a power. This is the only proposal on the table whose success mode is dimensionally capable of reaching the target, and it requires a contraction that is *not* the local Walsh multiplier, since that one is capped at $(\log y)^{-2}$.
2. **A global sign-reversing involution on factorization paths**, performed before absolute values, turning the observed anti-alignment of the born-smooth and transport populations into an exact combinatorial symmetry. The same-sign top block of section 10 is the sharp design constraint: it admits no internal pairing, so any such involution must move it wholesale against smooth partners and cannot be local in the prime coordinates.
3. **The collision-defect chain** of section 4, which remains the sharpest conditional route already packaged in Lean.
4. Transfer any resulting complete-cell or square-prefix estimate to arbitrary cutoffs using the proved additive-$3$ endpoint theorem, then feed it through the existing recovered-wheel, Mertens-energy, and completed-zeta bridge.

The bottleneck is no longer an unspecified local pairing theorem, and no longer a missing coordinate identity. It is the **global bounded-multiplicity control of the exact signed defects that remain after the proved local cancellations**.
