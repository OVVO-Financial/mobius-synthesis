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
N_k(x)=\mathrm{primorialExpansionReindexedNumerator}(k,x),
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
2\sum_{y<q\le x,\ q\ \mathrm{prime}}
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

Finite diagnostics show that `C` and `E` usually have the same sign and are strongly positively correlated. The exact identity explains why such a correlation can appear whenever `H` is substantially smaller than the two individual terms: `C` must then track `2E` closely. The measured correlation coefficient is therefore a diagnostic of the signed cancellation, not independent evidence for a new theorem.

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

## 6. Record the exact positive-orientation collapse without promoting its numerics to a theorem

The square-root smooth/transport coordinates also admit the exact orientation split

```math
M(R^2-1)
=
P(R)+\operatorname{matched}(R),
```

where `P(R)` is the positive-orientation smooth mass `c<q=P^+(m)` and `matched` is the born-smooth minus transport term.

The positive orientation collapses exactly to

```math
\boxed{
P(R)
=
-\sum_{\substack{q\le R\\q\ \mathrm{prime}}} M(q-1).
}
```

This identity is finite algebra. It does **not** provide an asymptotic lower bound for `P(R)` and it does **not** make `matched(R)` a new canonical RH target.

Independent exact numerics through

```text
R = 536,870,912
```

show an envelope compatible with `R^(3/2+o(1))` for `|P(R)|`, and the normalized quantity `|P(R)| log R / R^(3/2)` remains roughly flat over the measured large-scale ranges. Those observations are diagnostic only.

The rigorous warning is conditional:

```math
P(R)=\Omega(R^{3/2-o(1)})
```

**if proved independently**, together with an RH-scale bound

```math
\operatorname{matched}(R)=O_\varepsilon(R^{1+\varepsilon}),
```

would force `M(R^2-1)` to have `R^(3/2-o(1)) = X^(3/4-o(1))` excursions and would therefore be incompatible with RH. The repository does not currently prove the required lower bound for `P(R)`, so this is not an asymptotic closure theorem.

The same caution applies to survivor pairing. Far-upper rigidity proves that a fixed prime fibre is exactly

```math
-M(\lfloor X/q\rfloor).
```

Thus a fixed-`q` prime-face toggle changes representation but does not make that fibre smaller. This rules out **fixed-`q` cancellation as the whole mechanism**. It does not rule out signed cancellation across `q`, nor cancellation between survivor and another signed frontier before norms are taken.

## 7. Exploit the reciprocal-`d` family without destroying its signs

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

## 8. Once the `H`-bound is proved, the rest of the route is already built

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

The positive-smooth collapse is a **diagnostic side coordinate**, not a replacement for this route.

The **single live proof problem** remains the signed-cancellation arrow.

The active analytic strategy is:

> **Prove signed cancellation in the combined reciprocal-interval representation of `H_{k,n}`, exploiting the many-`d`, short-interval structure without taking absolute values termwise.**
