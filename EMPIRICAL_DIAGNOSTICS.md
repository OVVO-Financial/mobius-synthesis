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

## Certified finite constants are not diagnostics

Three finite quantities appear in the package with proof status rather than diagnostic status. They are listed here only so that they are not mistaken for the measurements above.

**The shallow-crossing coefficient at depth $18800$.** The weighted reciprocal coefficient

$$
\sum_{1\le d\le K}M(d)\Bigl(\frac1d-\frac1{d+1}\Bigr)
$$

is first identified by exact rational summation by parts with its Möbius-boundary form, and that rational value at $K=18800$ is proved negative by `native_decide`. No decimal approximation and no externally generated table enters the argument. The number then appears in exactly one place: as a witness for the general negative-coefficient hypothesis. The public crossing theorem is stated in the endpoint variable, holds for every positive logarithmic constant, and does not expose the certificate.

**The corrected-conductor packet bound $6q^3$.** Each ingredient is an elementary counting step: a divisor boundary on an interval shorter than the conductor is bounded by $2q^2$, at most $q$ divisors occur, the periodic raw spectrum is bounded by the torus modulus, and the smooth-site carrier has at most the same cardinality. Summing over $q\le R$ gives $6(R+1)R^3$. These constants are deliberately crude and use no cancellation between distinct conductors; they are proved, not fitted.

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

In both cases the same standard applies as to every table above: a finite trend is motivation for a formal target, never evidence for an asymptotic bound.
