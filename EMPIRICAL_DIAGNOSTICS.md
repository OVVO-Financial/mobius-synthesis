# Empirical diagnostics

This note records finite computations used to choose the formal target.  None of the observations below is used as a proof of an asymptotic statement.

A separate category, described in the last section, must not be confused with these: a handful of finite constants in the package are *certified* inside Lean rather than measured, and those do carry theorem status.

## Three-slot sample at $x=10^7$

Take

$$
K=2{,}500{,}000,
$$

so the complete three-slot cells cover the active positions through $10^7$.

The directly computed degree-one sums are

$$
W_a(K)=459,
\qquad
W_b(K)=468,
\qquad
W_c(K)=110.
$$

Therefore

$$
M(10^7)=W_a+W_b+W_c=1037.
$$

The same value is obtained by summing the Möbius function directly through $10^7$, giving an exact numerical check of the three-slot decomposition.

With

$$
\sqrt K\approx1581.13883,
$$

the endpoint ratios are approximately

$$
W_a/\sqrt K\approx0.2903,
\qquad
W_b/\sqrt K\approx0.2960,
\qquad
W_c/\sqrt K\approx0.06957,
$$

and

$$
M(4K)/\sqrt K\approx0.65586.
$$

On the conventional $x$-scale,

$$
M(10^7)/\sqrt{10^7}\approx0.32793.
$$

A dense prefix scan over the same range also kept the observed degree-one sums on a numerical square-root-like scale.  This is motivation for the target estimate, not evidence of a uniform asymptotic bound.

## The 27-state distribution is not uniform

For each cell define

$$
S_k=(\mu(4k+1),\mu(4k+2),\mu(4k+3)).
$$

There are $3^3=27$ possible states.  Their empirical frequencies at $x=10^7$ are strongly nonuniform, as they must be because square divisibility creates zero coordinates with a different density from the two signed values.

A useful correction is that these three slots do **not** sample all integers uniformly: they omit the residue class $0\pmod4$.  For each retained slot the appropriate limiting squarefree density is

$$
\Pr(\mu\ne0)=\frac{8}{\pi^2},
$$

so

$$
\Pr(\mu=0)=1-\frac{8}{\pi^2}\approx0.1894305,
$$

and the two signs each have density

$$
\Pr(\mu=1)\approx\Pr(\mu=-1)\approx\frac{4}{\pi^2}\approx0.4052847.
$$

The pooled empirical marginals at $x=10^7$ were approximately

$$
\Pr(\mu=-1)=0.4052169,
\qquad
\Pr(\mu=0)=0.1894279,
\qquad
\Pr(\mu=1)=0.4053552.
$$

This is why a uniform $1/27$ model for the full state distribution is inappropriate.

## Conditional eight-state sign diagnostic

If both the source and destination states are restricted to the eight states with all three coordinates nonzero, the row-normalized empirical transition matrix is close to uniform on those eight states.

At $x=10^7$, the largest observed absolute deviation from $1/8$ in that conditioned matrix was approximately

$$
0.003305.
$$

This is a useful diagnostic of the sign sector, but it does not imply independence, Markov behavior, or asymptotic mixing.

## Why the degree-one projection is the relevant statistic

The full 27-state counts $C_i(K)$ contain much more information than is needed for the Mertens sum.  The exact signed statistic is only the degree-one projection

$$
W_j(K)=\sum_i\chi_j(i)C_i(K),
$$

followed by

$$
M(4K)=W_a(K)+W_b(K)+W_c(K).
$$

The formal development proves these identities exactly and also identifies each $W_j$ with the corresponding corrected prime-wheel slot field $R_j-2H_j$.

Accordingly, future computation should be judged by how well it diagnoses cancellation in the signed degree-one field.  Uniformity of the complete 27-state transition matrix is neither expected nor required.

## Orientation scales at the square endpoint

With $X=R^2-1$, direct computation of the complete smooth mass, its two canonical orientations, and the high transport mass gives the following least-squares log-log exponents over $100\le R\le 2000$.

| object | measured exponent |
| --- | --- |
| complete smooth mass $A_R$ | $R^{1.71}$ |
| high transport mass $T_R$ | $R^{1.78}$ |
| positive orientation $A_R^{\mathrm{pos}}$ | $R^{0.87}$ |
| matched object $A_R^{\mathrm{born}}-T_R$ | $R^{0.55}$ |

Local slopes for $A_R$ over consecutive sample points run $1.83,\,1.58,\,1.75,\,1.70,\,1.71,\,1.71,\,1.61,\,1.79,\,1.72$, with no downward drift across a factor of $20$ in $R$.

The transport mass tracks $R^2/\log R$ rather than $R$: the ratio $|T_R|/(R^2/\log R)$ reads $0.047,\,0.048,\,0.047,\,0.044,\,0.042,\,0.041$ at $R=100,400,800,1200,1600,2000$.

Two readings, neither of them asymptotic evidence. First, the complete smooth mass and the transport mass are individually far above square-root scale, while the matched difference is far below it, so the orientation split is doing essentially all of the observed cancellation. Second, the positive orientation sits comfortably inside the exponent $1$ needed by the residual-gap theorem.

## Walsh multiplier product

The finite-prime recombination terminates in the weight-one Walsh multiplier

$$
\lambda_q=\frac{q^2-2q-4}{q^2-6}=1-\frac{2q-2}{q^2-6}.
$$

Its product over primes $11\le q\le y$ is a Mertens product:

| $y$ | primes | $\prod\lambda_q$ | $(\log y)^{-2}$ | ratio |
| --- | --- | --- | --- | --- |
| $10^2$ | 21 | 0.2795 | 0.0472 | 5.93 |
| $10^3$ | 164 | 0.1268 | 0.0210 | 6.05 |
| $10^4$ | 1225 | 0.0717 | 0.0118 | 6.08 |
| $10^5$ | 9588 | 0.0460 | 0.0075 | 6.09 |
| $10^6$ | 78494 | 0.0319 | 0.0052 | 6.10 |
| $10^7$ | 664575 | 0.0235 | 0.0038 | 6.10 |

The ratio stabilizes at about $6.10$, so the available contraction is of order $(\log y)^{-2}$. This is a diagnostic of the multiplier structure only; the classical statement behind it is Mertens' product theorem, which is not formalized in this package.

## Row energy of the canonical endpoint operator

Writing the endpoint as a lower-triangular combination of lower-scale Mertens values and scanning the normalized row energy

$$
Q_R=\frac1R\sum_{y<R}(y+1)\lvert a_R(y)\rvert^2
$$

for the canonical coefficients supplied by the prime-first transport transform gives $Q_R=8.5\times10^{3},\,3.1\times10^{5},\,6.0\times10^{6},\,7.3\times10^{7}$ at $R=100,400,1200,3000$, with log-log slopes $2.669,\,2.705,\,2.732$ rising toward $3$. The dominant contribution is the single fibre $\lfloor X/q\rfloor=1$, which is the same-sign top block proved to admit no internal cancellation.

For comparison, the least-norm coefficient vector satisfying the same identity has $Q_R$ between $0.015$ and $0.89$ over the same range. That column is bounded because the target is true, not as evidence for it; the least-norm coefficients are proportional to $(M(y)-1)/(y+1)$ and are not arithmetically constructible.

## Frontier capacity against the two thresholds

The support-only route bounds $\lvert M(X)\rvert$ by the first-failure frontier of an Euler pivot $\ell$,

$$
F(X,\ell)=\#\{n\le X:\ n\ \text{squarefree},\ \ell\nmid n,\ X<\ell n\},
$$

which yields a covariance capacity $F(F-1)/2$, sharpened to $(F^{2}-Q)/2$ once the exact squarefree diagonal $Q$ is restored. The measurement below is what closed that route.

| $x$ | $M(x)$ | actual $C(x+1)$ | $F(x,2)$ | $F/x$ | $F/\sqrt x$ | capacity $F(F-1)/2$ |
| --- | --- | --- | --- | --- | --- | --- |
| $2\cdot10^{3}$ | $5$ | $-595$ | $407$ | $0.2035$ | $9.1$ | $41.3\,x$ |
| $2\cdot10^{4}$ | $26$ | $-5742$ | $4048$ | $0.2024$ | $28.6$ | $409.6\,x$ |
| $2\cdot10^{5}$ | $-1$ | $-60\,790$ | $40\,527$ | $0.2026$ | $90.6$ | $4106.0\,x$ |

Three readings, and only the third is a conclusion about the route.

The minimising pivot is $\ell=2$, whose frontier is the squarefree part of the top-half window $(x/2,x]$ — the same set as the $\ell=2$ cutoff wall of the prefix carrier — so $F/x$ tends to $2/\pi^{2}=0.20264$ and the capacity is of order $x^{2}$. That is a full power above the RH target $x^{1+\varepsilon}$, and subtracting the linear diagonal does not change the exponent. The pivots $\ell=3$ and $\ell=5$ are worse, at densities $0.304$ and $0.405$.

$F/\sqrt x$ grows, so the exposed frontier is nowhere near square-root size. That is exactly the hypothesis the root-scale frontier statement asks for, and this measurement refutes it for the raw prime cube.

The two thresholds must not be conflated. Crossing the literal $\sqrt x$ line is $C(x+1)>Z(x)/2\approx0.196\,x$, which is the threshold of the *false* Mertens conjecture and therefore not a provable target. The RH threshold is the strictly weaker $C(x)\le x^{1+o(1)}$, and an RH-violating excursion of exponent $\varepsilon$ needs $C$ of order $x^{1+2\varepsilon}$ — a fixed power above target, not a constant factor. The actual covariance in the range above is strongly negative, far below every threshold; the problem is not its true value but that no theorem yet bounds it.

## What the fixed-prime peel leaves, in every order

The cumulative Othello layer proves that peeling a distinguished prime leaves the signed Möbius mass unchanged and reduces a prefix to two walls. The measurement asks what those walls actually cost.

| $x$ | $M(x)$ | ascending peel | descending peel | mixed order | maximum adaptive matching |
| --- | --- | --- | --- | --- | --- |
| $2\cdot10^{3}$ | $5$ | $407$ | $407$ | $407$ | $335$ |
| $2\cdot10^{4}$ | $26$ | $4048$ | $4048$ | $4048$ | $3314$ |

The signed mass never moves under any peel, at any scale, in any order: the exact layer holds. The surviving population bottoms out at $2/\pi^{2}$ of $x$ and is identical for ascending, descending and mixed prime orders, so the peel order is not the free parameter. Restoring full state-dependent freedom — allowing the matching prime to depend on the state — still leaves a positive proportion exposed, about $0.166\,x$.

That last row is now a theorem rather than a measurement. At $x=2\cdot10^{3}$ there are $135$ primes with $x<2p$, and at $x=2\cdot10^{4}$ there are $1033$; each has the single legal move $p\mapsto1$, so they all compete for one neighbour and an involution can serve at most one of them. The fixed set of *any* adaptive mate on $(0,x]$ therefore has at least $\pi(x)-\pi(x/2)-1$ states. The carrier, not the matching, is what has to change.

## Square-block covariance: the partition holds, the magnitude step does not

The block decomposition proves $S^{2}=E+2X$ and $C_{\text{global}}(R^{2})=\sum_j C_j+X$. Both identities were checked exactly before being relied on, and the same run measures what a magnitude-first bound would discard.

| $R$ | $N=R^{2}$ | $S=M(N-1)$ | block energy $E$ | cross $X$ | $\sum_j C_j$ | partition check | $\sum_j\lvert B_j\rvert$ | discarded |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $200$ | $40\,000$ | $-10$ | $24\,406$ | $-12\,153$ | $48$ | exact | $1706$ | $72.8\,N$ |
| $400$ | $160\,000$ | $-67$ | $99\,961$ | $-47\,736$ | $1347$ | exact | $4781$ | $142.8\,N$ |

Three readings.

The partition is exact at every scale, so the block decomposition is a refinement of the same pair sum rather than a second object needing a bridge.

The discarded quantity $\bigl(\sum_j\lvert B_j\rvert\bigr)^{2}-S^{2}$ grows like $N^{3/2}$, because $\sum_j\lvert B_j\rvert$ grows like $N^{3/4}$ while $\lvert S\rvert$ stays near $N^{1/2}$. Bounding blocks separately and only then squaring therefore loses a half power, not a constant factor.

The block energy $E$ *looks* linear here, close to the squarefree density $6N/\pi^{2}$. That reading must not be promoted. Exactly, $E-Q=2\sum_j C_j$, so proving $E\ll N^{1+\varepsilon}$ is proving the aggregate within-block covariance is of RH scale. The way out is refinement rather than a bound on $E$: each refinement step moves energy into the children and leaves an explicit signed cross term, and the leaf energy is exactly $Q$, which is linear with no conjecture at all.

## Certified finite constants are not diagnostics

Four finite quantities appear in the package with proof status rather than diagnostic status. They are listed here only so that they are not mistaken for the measurements above.

**The shallow-crossing coefficient at depth $18800$.** The weighted reciprocal coefficient

$$
\sum_{1\le d\le K}M(d)\Bigl(\frac1d-\frac1{d+1}\Bigr)
$$

is first identified by exact rational summation by parts with its Möbius-boundary form, and that rational value at $K=18800$ is proved negative by `native_decide`. No decimal approximation and no externally generated table enters the argument. The number then appears in exactly one place: as a witness for the general negative-coefficient hypothesis. The public crossing theorem is stated in the endpoint variable, holds for every positive logarithmic constant, and does not expose the certificate.

**The corrected-conductor packet bound $6q^3$.** Each ingredient is an elementary counting step: a divisor boundary on an interval shorter than the conductor is bounded by $2q^2$, at most $q$ divisors occur, the periodic raw spectrum is bounded by the torus modulus, and the smooth-site carrier has at most the same cardinality. Summing over $q\le R$ gives $6(R+1)R^3$. These constants are deliberately crude and use no cancellation between distinct conductors; they are proved, not fitted.

**The Mertens prefix at the fixed crossing depth $18349$.** The finite value $M(18349)=-21$ is proved, not measured, and it is the reason the fixed-depth boundary budget is a theorem rather than an observation. Because the first crossing prime advances the reciprocal packet in steps of exactly that size, and the crossing theorem already gives a nonnegative overshoot strictly smaller than one step, the compressed partial packet has fewer than $21$ unit cells — uniformly in $R$. Combined with the other endpoint budgets this gives a tagged no-liberty boundary of cardinality at most $3R+21$: head $1$, partial at most $20$, born-exit at most $2R$, root equality at most $R$. That is a target-side improvement only; it neither assumes nor supplies the still-open source-to-boundary classifier.

**The low-slope cubic step.** The proved affine-envelope contraction step is $\alpha-\alpha^3/178200000$. The denominator is a proof artifact of the elementary route taken, not a measured optimum. What remains open is the physical cutoff law required to iterate the step at RH-compatible scale, and no measurement in this note bears on that.

## What a future measurement should target

The two most concrete open statements in the package are both finite objects, so both admit direct finite probing.

The first is the canonical rough-prime correlation after the shallow crossing. Once the packet has stopped, the coupled tail is an explicit baseline minus

$$
\sum_c\mu(c)\,\mathrm{Resp}(c),
$$

where each cofactor response carries its diagonal reciprocal-prime multiplicity together with every strict quotient descendant. A useful diagnostic measures the *signed* correlation and its centered covariance directly, at fixed $R$, rather than the size of either field. Measuring $\lVert\mu\rVert$ and $\lVert\mathrm{Resp}\rVert$ separately answers a question the package has already closed.

The second is the canonical least-prime transport defect. Its states form an explicit adjacent multiplicative shell,

$$
P(t)\,(k/p)\le R<P(t)\,p\,(k/p),
$$

so its population and signed mass are directly enumerable at moderate $R$. The informative statistic is again the signed mass against $R$, not the raw shell cardinality.

A third object has joined them and is now the sharpest of the three. After the squarefree-diagonal sharpening, the whole vertical-line energy on a strict subdoubling run is

$$
\lVert V(a,b)\rVert^{2}\le 2a^{2}+2\max\bigl(0,C_{\text{line}}\bigr),
$$

and the carrier is exactly the squarefree shell $\{n:\ R<n<R^{2}\}$. So the informative measurement is the *positive part* of the aggregate line covariance against $a^{2}$, on that shell, with births and deaths kept signed. Because the shell is explicit and the event variable is $\mu(n)\chi(n)$, a candidate exact recursion can be tested directly: check equality over many roots and fresh primes, isolate each discrepancy by lower wall, upper square wall, stable family and cross-family term, and search for the smallest counterexample immediately.

In all three cases the same standard applies as to every table above: a finite trend is motivation for a formal target, never evidence for an asymptotic bound. Two specific traps are worth naming, because both have already cost a route. Measuring the size of two fields separately answers a question the package has closed; and a quantity that looks linear over a decade of scales — the block energy is the live example — may be exactly equivalent to the conjecture being tested.
