# Current Möbius Synthesis proof route

**Status:** canonical internal wording for the active proof route.

This file is the source of truth for how the remaining Möbius Synthesis problem is to be described. In particular, it supersedes any wording that treats the PNT-corrected comb and the reciprocal PNT error as two independent analytic obligations to be bounded separately.

## 1. Reduce Möbius cancellation to complete-square samples inside synchronized prime-wheel blocks

For each synchronized primorial block `(L_k,U_k]`, sample at

```math
X_n=(n+1)^2-1.
```

The square-block machinery makes these the natural checkpoints. Interpolation from a square endpoint to an arbitrary `x` costs only one square gap, already `O(sqrt x)`.

## 2. Separate the wheel zero mode from the genuine nonzero response

At every complete-square sample,

```math
R_k(X_n)=H_{k,n}+\rho_{k,n}R_k(U_k),
\qquad
\rho_{k,n}=\frac{X_n-L_k}{Q_k}.
```

The terminal zero mode is eliminated exactly, the remaining endpoint tail is square-root scale, and the minimal modulus gives

```math
0\le \rho_{k,n}<\frac16.
```

Thus the self-coupling is contractive and **is not the RH obstruction**. The exact elimination is formalized independently of any analytic estimate on `H`.

## 3. Make `H_{k,n}` the canonical proof target

The quantitative goal is exactly

```math
|H_{k,n}|
\ll_\varepsilon
(X_n+1)^{1/2+\varepsilon}
```

uniformly over every synchronized block and complete-square sample. This is the repository predicate `NonzeroResponseRHScale`.

Merely rewriting `H` does not count as quantitative progress.

The repository also contains the explicit finite expansion-reindexed form. Writing

```math
N_k(x)=\operatorname{primorialExpansionReindexedNumerator}(k,x),
```

its content is

```math
H_{k,n}
=
\frac1{Q_k}
\left[
N_k(X_n)
-
\frac{X_n-L_k}{Q_k}N_k(U_k)
\right].
```

This is the canonical endpoint before introducing diagnostic coordinates.

## 4. Use the post-square-root prime sieve to expose arithmetic structure inside the same `H_{k,n}`

Above the square-root cutoff,

```math
M_y^+(x)-M(x)
=
2\sum_{\substack{y<q\le x\\q\ \mathrm{prime}}}
M(\lfloor x/q\rfloor).
```

This is exact finite algebra, not a prime-distribution estimate.

Reindex by the lower scale

```math
d=\lfloor x/q\rfloor.
```

Each fixed `d` corresponds exactly to the reciprocal interval

```math
\max\!\left(y,\left\lfloor\frac{x}{d+1}\right\rfloor\right)
<q\le
\left\lfloor\frac{x}{d}\right\rfloor.
```

The prime-distribution part thereby becomes a finite family of lower-scale Mertens weights `M(d)` against prime-count discrepancies on these explicit intervals. This reindexing is machine checked.

## 5. Use the PNT-centered form as a diagnostic coordinate system, not as two independent proof obligations

The exact checked identity is

```math
H_{k,n}
=
C_{k,n}^{\mathrm{PNT}}
-
2E_{k,n}^{\mathrm{rec}},
```

where `E^{rec}` is the centered, Mertens-weighted reciprocal-interval prime discrepancy.

The diagnostic update is decisive:

**Do not now try to prove**

```math
|C^{\mathrm{PNT}}|=O(\sqrt X)
\qquad\text{and}\qquad
|E^{\mathrm{rec}}|=O(\sqrt X)
```

independently and then combine them by triangle inequality.

Finite diagnostics show that this loses a large part of the actual cancellation. `C` and `E` usually have the same sign and are positively correlated; because the expression is `C-2E`, that same-sign correlation is favorable.

Therefore the actual open analytic theorem should attack the **signed combined object**

```math
\boxed{
C_{k,n}^{\mathrm{PNT}}
-
2E_{k,n}^{\mathrm{rec}}
}
```

directly.

Equivalently, the desired theorem is simply

```math
\boxed{
\left|
C_{k,n}^{\mathrm{PNT}}
-
2E_{k,n}^{\mathrm{rec}}
\right|
\ll_\varepsilon
X_n^{1/2+\varepsilon}.
}
```

## 6. Exploit the reciprocal-`d` family without destroying its signs

This is the active analytic research step.

The experiments rule out the most naive version of strong induction: inserting

```math
|M(d)|\le Kd^{1/2+\varepsilon}
```

and taking absolute values produces an operator far too large to close. Scale reduction alone is insufficient.

Likewise, the `d`-family is **not directly a Bombieri-Vinogradov family**. It averages over many disjoint short ordinary intervals, not residue classes modulo varying moduli.

The plausible proof mechanism must therefore be something like a **signed short-interval or dispersion estimate adapted to the reciprocal interval family**, or another exact transformation that preserves the observed `C-2E` cancellation.

Any proposed next theorem should answer

```text
Why does the combined signed operator save roughly X^(1/2)?
```

not merely

```text
How large are its two pieces separately?
```

## 7. Once the `H`-bound is proved, the rest of the route is already built

The `H` estimate plus exact zero-mode elimination controls the complete block residual. The square-gap estimate transports that to arbitrary `x`, yielding the RH-strength Mertens bound.

The existing formal chain then carries the result through Mertens transfer, Mellin continuation, zeta continuation, and the terminal RH bridge. The final implication no longer needs an external "Mertens implies RH" axiom: the repository constructs the forward criterion from Mellin continuation and completed-zeta reflection and proves that the required Mertens energy estimate implies RH.

## Compressed route

```text
square blocks + prime wheels
  -> H_{k,n}
  -> C_{k,n}^{PNT} - 2 E_{k,n}^{rec}
  -> OPEN: signed cancellation
  -> O(X_n^(1/2+epsilon))
  -> M(x)=O(x^(1/2+epsilon))
  -> 1/zeta(s) analytic for Re(s)>1/2
  -> zeta(s) != 0 for Re(s)>1/2
  -> functional equation
  -> RH
```

The **single live proof problem** is the signed-cancellation arrow.

The active analytic strategy is:

> **Prove signed cancellation in the combined reciprocal-interval representation of `H_{k,n}`, exploiting the many-`d`, short-interval structure without taking absolute values termwise.**
