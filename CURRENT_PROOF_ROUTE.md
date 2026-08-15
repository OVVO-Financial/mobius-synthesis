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

## 8. What is not sufficient

The following do not advance the quantitative frontier by themselves:

- uniformity of the 27 three-slot states;
- a Markov model for successive cells;
- independence assumptions for neighboring Möbius values;
- separate absolute estimates for `R` and `H`;
- a constant collision error charged independently to every prime pair;
- a positive residue-energy bound that discards the signed parity cross term;
- a local finite-difference bound without controlling the support or signed covariance of the nonzero stencils.

The target remains the signed object itself.

## 9. Recommended order of work

1. Construct the actual square-prefix collision-defect chain, preferably through a canonical first-failure or fresh-prime charging rule with bounded multiplicity.
2. In parallel, exploit the exact `2-3-5` survivor stencil and the six parity corner sums to identify the support of nonzero third differences.
3. Use the dyadic three-shell classification and signed parity Gram to preserve cancellation through the residue layer.
4. Prove an $L^2$ bound for one of these exact signed defect representations at exponent $1+\varepsilon$.
5. Transfer the resulting complete-cell or square-prefix estimate to arbitrary cutoffs using the proved additive-$3$ endpoint theorem.
6. Feed the estimate through the existing recovered-wheel, Mertens-energy, and completed-zeta bridge.

The bottleneck is no longer an unspecified local pairing theorem. It is the **global bounded-multiplicity control of the exact signed defects that remain after the proved local cancellations**.
