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

where `E^rec` is the centered, Mertens-weighted reciprocal-interval prime discrepancy.

The diagnostic update is decisive:

**Do not now try to prove**

```math
|C^{\mathrm{PNT}}|=O(\sqrt X)
\qquad\text{and}\qquad
|E^{\mathrm{rec}}|=O(\sqrt X)
```

independently and then combine them by triangle inequality.

Finite diagnostics show that `C` and `E` usually have the same sign and are strongly positively correlated. The exact identity explains why such a correlation can appear whenever `H` is substantially smaller than the two individual terms: `C` must then track `2E` closely. The measured correlation coefficient is therefore a diagnostic of the signed cancellation, not independent evidence for a new theorem.

**However, the pair of obligations is strictly stronger than the target, and the correlation is forced.** The centering operator is linear and `M = (allPlus - 2 Bulk) - 2 Err`, so

```math
C_{k,n}^{\mathrm{PNT}}-2E_{k,n}^{\mathrm{rec}} = H_{k,n}
```

is an identity, not a reformulation, and therefore

```math
C_{k,n}^{\mathrm{PNT}} = H_{k,n}+2E_{k,n}^{\mathrm{rec}}.
```

Consequently `{|C| = O(s), |E| = O(s)}` is *equivalent* to `{|H| = O(s), |E| = O(s)}`, which is strictly stronger than the target `{|H| = O(s)}`. The PNT coordinate change cannot reduce the difficulty; it can only relocate it. The observed positive correlation of `C` with `E` (measured `+0.88`, against `corr(H,2E) = -0.95`) is a consequence of that identity rather than independent evidence.

By §3 — merely rewriting `H` is not quantitative progress — "attack `C-2E` directly" is therefore **not** an actionable next step: `C-2E` *is* `H`. See the lane `pnt-reciprocal-coordinate-change` in `boundary/dead_lanes.json`.

What survives from this section is the genuine content of §6: the reciprocal-interval *representation* of `E^rec`. The split becomes a real reduction only if the comb side `C = allPlus - 2*Bulk` is controlled by combinatorial means that do not route back through `M`.

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

### Measured answer to that question

Finite diagnostics now identify the mechanism. Writing `D = floor(x/y)`, which is about `sqrt(x)`, for the number of reciprocal fibres, measurements on a 240-point logarithmic grid to `x = 1e8` give:

- the termwise triangle bound `sum_d |E_d|` grows with exponent `0.678` (sub-range fits `0.635, 0.648, 0.706, 0.677`), robustly **above** the `1/2` target — so absolute values are indeed fatal, confirming the paragraph above;
- the signed `|E^rec|` fits exponent about `0.51` and tracks `sum_d |E_d| / sqrt(D)` with median ratio `1.43` and log-log correlation `0.78`.

So the saving is **square-root cancellation across the `d`-fibres**, and it is exactly sufficient with essentially no margin: the required saving over the triangle bound is about `x^0.18`, and the observed median saving is `24.9x` at these scales.

This is the mechanism a proof has to capture. It also sets the bar: any proposed estimate that yields less than full square-root cancellation over the `d`-family cannot close, and any estimate that passes through `|M(d)| <= K d^(1/2+eps)` termwise has already discarded it.


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

## 8. Routes that are closed

`boundary/dead_lanes.json` is the ledger. A proposal matching a closed lane must defeat the stated obstruction or be rejected before a Lean build is spent on it.

The two closures added most recently constrain the wording above directly.

### The canonical orientation split is off the table

Splitting the square-root smooth mass by canonical orientation — `c < q` against `q <= c`, with `q = P+(m)` and `c = m/q` — and then bounding

```math
\mathrm{matched}(R) = \mathrm{bornSmooth}(R) - \mathrm{transport}(R)
```

**cannot deliver the RH-scale bound, and pursuing it is self-defeating.** The split leaves exactly one region uncancelled, and that region has a closed form:

```math
\mathrm{positiveSmooth}(R)
= -\sum_{q\le R,\ q\ \mathrm{prime}} M(q-1)
= -\sum_{c<R}\mu(c)\bigl(\pi(R)-\pi(c)\bigr),
\qquad
M(R^2-1)=\mathrm{positiveSmooth}(R)+\mathrm{matched}(R).
```

Summation by parts turns it into an **integral of `M` against `dpi`**, and integration is a smoothing that removes exactly the sign oscillation the target relies on. Under RH the explicit formula gives every zero a contribution to `int_1^R M` of modulus exactly `R^(3/2) / |rho(rho+1)zeta'(rho)|`, so the integral is `R^(3/2-o(1))` and no cancellation among zeros lowers it.

Hence `matched(R)` is of order `R^(3/2)/log R = X^(3/4+o(1))` — a full quarter power of `X` above the target. The dichotomy is sharp: **either `|matched|` exceeds `R^(1+eps)` and the route fails, or `M(R^2-1) = Omega(X^(3/4-eps))` and RH is false.**

Measured to `R = 5.37e8`: `|positiveSmooth|/R` rises from `0.32` to `18.96`; the normalized `|positiveSmooth| * log R / R^(3/2)` is flat in `[0.0079, 0.0202]` across four decades; the fitted exponent `1.4440` matches the predicted `1.5 - 1/log R = 1.4502`; and `positiveSmooth(R) / (-int_2^R M(t) dt/log t)` tends to `1.005`.

This closes `RHLean/Analysis/SquareRootMatchedTransport.lean` as a *quantitative* lane, and with it the far-upper survivor localization of `RHLean/Proof/MatchedFarSurvivorBridge.lean`, which differs from `matched` only by the elementary `7R` root strip. Those modules remain correct exact algebra; they are simply not a route to the bound.

### Pairing before residues terminates here too

The reopener recorded for `survivor-residue-covariance-cauchy` — cancel matched `(c, c*l)` sources directly, before passing to residues — was carried out. `RHLean/Proof/SurvivorFarUpperRigidity.lean` proves the fixed-`q` fibre is then the **full** negative reciprocal Mertens prefix `-M(floor(X_t/q))`, with the unpaired-boundary set empty in the far range. The pairing cancels nothing there, and the resulting object is the closed lane above.
