# Möbius Synthesis

This is a standalone Lean 4 formalization of a square-sensitive, prime-wheel approach to cancellation in the Möbius summatory function.

The central quantity is the **joint signed field**

\[
R-2H,
\]

where `R` is the seeded prime-wheel mass and `H` is the smooth-core correction.  Under square-root prime coverage this field is proved exactly equal to the ordinary Möbius prefix.  The formal development keeps this signed object intact rather than bounding `R` and `H` separately.

## Current exact structure

For each complete four-cell, only three slots are active:

\[
4k+1,\qquad 4k+2,\qquad 4k+3,
\]

because the fourth position is divisible by \(4\) and has Möbius value zero.  The three-slot state

\[
S_k=(\mu(4k+1),\mu(4k+2),\mu(4k+3))\in\{-1,0,1\}^3
\]

therefore has exactly 27 possible values.

The formalization now proves the exact degree-one projection.  If \(C_i(K)\) is the number of occurrences of state \(i\) among the first \(K\) cells and \(\chi_a,\chi_b,\chi_c\) select its three signed coordinates, then

\[
W_j(K)=\sum_i \chi_j(i)C_i(K),
\]

with

\[
W_a(K)=\sum_{k<K}\mu(4k+1),\qquad
W_b(K)=\sum_{k<K}\mu(4k+2),\qquad
W_c(K)=\sum_{k<K}\mu(4k+3).
\]

At every complete four-cell endpoint,

\[
M(4K)=W_a(K)+W_b(K)+W_c(K).
\]

Each coordinate sum is also proved exactly equal to the corresponding canonical square-root-wheel signed slot field \(R_j(K)-2H_j(K)\).  Thus the empirical three-slot diagnostic and the arithmetic prime-wheel field meet at the same kernel-checked object.

## Quantitative target

The missing theorem is the signed degree-one estimate

\[
M(4K)\ll_\varepsilon K^{1/2+\varepsilon}.
\]

Equivalently, in the squared formulation used by the formal analytic bridge, the recovered square-root-wheel energy must satisfy a bound of size

\[
X^{1+\varepsilon}.
\]

The exact recovery layer proves that this recovered-wheel energy statement is equivalent to the Mertens-energy criterion already used by the square-prefix route, and that this criterion implies the formal Riemann hypothesis through the completed-zeta reflection argument.

No RH-scale cancellation theorem is claimed here.  The exact reductions are proved; the quantitative cancellation remains open.

## Current proof mechanisms

The package includes three complementary mechanisms aimed at the missing estimate.

**Physical collision pairing.** Prime-square collision classes are organized by exact CRT residue frontiers.  A local exponent-state flip is proved to reverse the actual corrected `R - 2H` weight whenever the other local coordinates and smooth-core status are preserved.  Finite frontiers then split exactly into pairable states, fixed states, and mate-crosses-cutoff defects.

**Canonical finite differences.** The multi-prime operator is defined as an unordered Möbius-weighted divisor sum.  For a fresh prime \(p\), it satisfies the exact recurrence

\[
D_{S\cup\{p\}}f=D_Sf-D_S(\operatorname{shift}_p f).
\]

This gives a fiberwise alternative when a literal physical pairing cannot freeze all other prime coordinates.

**Square-sensitive transport and centering.** The complete square-block development remains available as a second exact representation of the same Mertens object, including the square-prefix transport decomposition and the zero-mode-centered nonzero response.

See [CURRENT_PROOF_ROUTE.md](CURRENT_PROOF_ROUTE.md) for the active proof plan and [EMPIRICAL_DIAGNOSTICS.md](EMPIRICAL_DIAGNOSTICS.md) for finite computations that motivate, but do not prove, the target estimate.

## Main formal entry points

See [MODULES.md](MODULES.md) for the principal modules and [SEAMS.md](SEAMS.md) for the exact interfaces between the three-slot, prime-wheel, square-block, and analytic layers.

## Related public projects

The two companion public projects are:

- `prime-wheel-mobius`
- `square-block-mobius`

They develop the prime-wheel and square-block viewpoints separately.  This repository focuses on the exact synthesis and the remaining signed cancellation problem.
