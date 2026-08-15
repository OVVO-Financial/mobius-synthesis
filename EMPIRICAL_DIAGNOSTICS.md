# Empirical diagnostics

This note records finite computations used to choose the formal target.  None of the observations below is used as a proof of an asymptotic statement.

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
