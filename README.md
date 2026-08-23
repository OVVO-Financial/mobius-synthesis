# Möbius Synthesis

This is a self-contained Lake package. `RHLean.lean` imports every shipped module, so `lake build RHLean --wfail` builds the whole development.

The project is a Lean 4 formalization of square-sensitive and prime-wheel cancellation in the Möbius summatory function. Its central arithmetic object is the signed field

$$
R-2H,
$$

where `R` is the seeded prime-wheel mass and `H` is the smooth-core correction. Under square-root prime coverage this field is proved exactly equal to the ordinary Möbius prefix.

No unfinished proof and no project-local axiom is present. `scripts/audit_assumptions.sh` rejects `sorry`, `admit`, and any declared axiom or opaque constant, and because a text scan cannot see what a proof actually depends on, `RHLean.Proof.TerminalAxiomAudit` asks the kernel directly and pins the answer with `#guard_msgs`: each theorem carrying the reduction to the Riemann hypothesis statement depends on exactly

```text
[propext, Classical.choice, Quot.sound]
```

the three standard axioms of Lean's logic. Any added dependency changes the message and fails the build. The hosted baseline job additionally prints the axiom dependencies of the status declarations on every change.

Two scope notes belong with that. The guarded statements are equivalences and implications, not proofs of their left-hand sides, and the classical Mertens criterion is taken as an ordinary theorem argument rather than an axiom, so it does not appear in those lists. And results whose final step is a finite `native_decide` certificate carry `Lean.ofReduceBool` in their own axiom list, as the compiler-evaluation route requires; the guarded terminal theorems above do not.

## Exact structure now exported

For each complete four-cell, only the three positions

$$
4k+1,\qquad 4k+2,\qquad 4k+3
$$

are active. The degree-one state projection gives

$$
M(4K)=W_a(K)+W_b(K)+W_c(K)
$$

and each coordinate is the corresponding recovered prime-wheel field $R_j(K)-2H_j(K)$.

The endpoint transfer is now exact as well. With $K=\lfloor X/4\rfloor$,

$$
|M(X)-M(4K)|\le 3.
$$

So a complete-cell estimate transfers to every physical cutoff with only a bounded additive correction. The squared combined degree-one mode is now itself a named criterion, proved equivalent to the recovered-wheel, global Mertens-energy, and square-prefix energy criteria — so the three-slot route has a stated endpoint rather than only an exact decomposition.

The export also contains the merged collision, finite-difference, survivor-parity, dyadic, affine-excursion, and renewal layers:

- the corrected `R - 2H` field has the exact local sign law under a genuine selected-prime exponent flip;
- square-hit fixed points have exactly zero corrected weight;
- the mate-crosses-cutoff collision defect has at most three labels;
- arbitrary Boolean-supported alternating mass has exact one-, two-, and three-coordinate finite-difference formulas;
- for every prime survivor fibre $q\ge 7$, the actual survivor mass has an exact `2-3-5` eight-state third-difference representation;
- the parity residue channels retain their exact signed Gram, and nonzero dyadic pair mass is confined to three explicit geometric shells;
- the weighted renewal telescope is connected exactly to the far-upper survivor sector and the primorial square-wheel zero-mode center;
- inside a complete square block every interior point is within one root-scale term of an adjacent completed-square endpoint, so the square-prefix sequence carries the whole energy obligation.

The square-root orientation layer is unchanged in substance:

- the smooth mass splits exactly by canonical orientation into a positive and a born-smooth part, and the matched object is the born-smooth mass minus the high transport mass;
- the reciprocal-cutoff floor rounding and the prime-counting discrepancy are combined into a single signed residual $D_R$ *channel by channel*, before the cofactor sum, so neither is ever available alone;
- the born-smooth mass is put into the same lower-scale Möbius/reciprocal form the transport already had, giving one signed sum over the whole prime range;
- the smoothness cutoff is proved automatic on the born orientation;
- the parity-class form of the complete smooth mass is exact, and the residual gap between the matched criterion and the square-prefix Mertens value is made explicit.

## What is new in this revision

Five layers have been added since the previous publication, and they change where the remaining work sits.

### 1. The shallow crossing and the post-crossing tail

The reciprocal packet no longer has to be processed to the end. For endpoint and cutoff sequences with $x_n\to\infty$ and a fixed reciprocal depth $K_0$ eventually above the cutoff, a negative finite reciprocal coefficient at $K_0$ forces the intact upper-middle packet to cross at some depth $K\le K_0$; for every $C>0$ that depth is eventually at most $C\log x_n$. The square geometry is the instance $x_R=R^2-1$, $y_R=R$, and the one numeric witness in the final step is checked by `native_decide`.

What remains after the crossing is identified exactly:

$$
M(R^2-1)=\text{partial crossing residual}+\text{coupled tail},
$$

where the coupled tail is the raw transport increment *plus* the complete square-root-smooth population. These are two different objects and the raw increment alone is not the terminal remainder. Once the partial residual is bounded by an absolute shallow depth, a critical root-scale estimate for the coupled tail is equivalent to the standard square-prefix Mertens energy criterion.

The crossing residual is then kept signed rather than collapsed to a scalar. Three exact normal forms are proved — a remaining-layer cap, an Abel form, and a lower-triangular renewal row obtained by subtracting the shallow crossing coefficients from the complete recursive replacement row before any norm. Pushing that renewal back onto the cofactor coordinate leaves

$$
\text{coupled tail}=\text{explicit packet baseline}-\sum_c \mu(c)\,\mathrm{Resp}(c),
$$

so the entire remaining nonlocal cancellation is a literal finite correlation between the Möbius parity field and one intact rough-prime response field. No mean-zero assertion, norm split, or independence hypothesis is used to get there.

### 2. Prime-count-free transport on a double low-prime cube

The high transport has been rewritten with the prime-counting function removed entirely. Each floor difference is the cardinality of a finite quotient interval, so the transport becomes a signed sum over triples $(c,t,k)$ with $\mu(c)(-1)^{|t|}$ as the only weight and the high region surviving purely as two hyperbolic cutoff inequalities. The square-root geometry then forces every low face with product at least $R$ to contribute zero, so both coordinates live on the *same* full Boolean cube of primes up to $R$.

On that symmetric carrier the canonical least-prime cofactor/quotient involution cancels every interior state, and the endpoint identity becomes

$$
M(R^2-1)=M(R)-\mathrm{canonicalDefect},
$$

with every term of the defect on one first-failure frontier: the physical insertion states whose least-prime pivot is absent from the cofactor and whose pivot-removal quotient has crossed down through the root. The remaining amplification problem is a signed estimate on that single ledger, not on the full transport.

### 3. An unconditional strong-Mertens corridor

A quantitative Mertens decay route is now formalized end to end at the interface level. One shared corridor object reconciles the reciprocal-zeta estimate, the zero-free region, and the bounded-height zero-free box into a single positive constant $A$ and a single left boundary

$$
\sigma_A(T)=1-\frac{A}{(\log T)^{9}},
$$

so downstream contour code never destructs the underlying existential theorems again. On top of it sit the reciprocal-zeta kernel (with the pole at $1$ handled by the residue limit rather than by pretending the literal function is continuous), the residue-free contour pull, the five-leg envelope, the small-height control, and the finite sharp-cutoff smoothing bridge. Balancing at $r=(\log X)^{1/10}$, $T=e^{r}$, $\varepsilon=e^{-(A/4)r}$ turns all three envelopes into exponential decays in $r$ with only fixed polynomial factors.

A separate finite Abel bridge converts a Mertens decay bound of the shape

$$
|M(x)|\le Cx\exp\bigl(-c(\log x)^{1/10}\bigr)
$$

into convergence of the reciprocal logarithmic Möbius moments

$$
A_m(N)=\sum_{n\le N}\frac{\mu(n)(\log n)^m}{n},
$$

which is what the centered K2 argument actually consumes. The Abel identity itself is exact for every $N$ and takes its two analytic facts as hypotheses, so the bridge is unconditional on its own terms.

### 4. Centered K2 and signed second-Selberg cancellation

The analytic side of the centered K2 closure removes the zeta pole using Mathlib's proved limit, factors the reciprocal germ as $(s-1)q(s)$, and reads the second Taylor coefficient directly:

$$
\Bigl(\tfrac1\zeta\Bigr)''(1)=-2\gamma .
$$

On $\Re s>1$ that same derivative is the logarithmic-square Möbius L-series, so the remaining step is a single explicit Abel-boundary target. The factor-four corollary is independent of the unknown centered constant, which cancels between the two prefixes.

Alongside it, the exact signed second Selberg kernel

$$
K_2(n)=(\Lambda*\Lambda)(n)-\Lambda(n)\log n
$$

is proved to have only $O(\log N)$ reciprocal mass, against the logarithmic-square size of the positive second von Mangoldt kernel. This is an unconditional signed cancellation theorem: it removes one full logarithm from the constant mode of the second Selberg operator before any wheel-frontier or error-profile estimate is applied. The summatory shortcut is calibrated exactly at the same time — the summatory kernel differs from $-2E(N)\log N$ by only $O(N)$ — which shows precisely which logarithmic improvement of the physical PNT error a linear summatory bound would require.

### 5. A signed conductor Gram with its first uniform bound

The corrected-conductor sector is now handled without packetwise absolute values. The all-conductor raw boundary pairing is split by its *boundary divisor* rather than by the original conductor, so removing only the small reindexed boundary divisors leaves one collapsed signed core carrying the conductor-one bulk, every large raw expansion layer, and the fully collapsed smooth term. The complete cross-conductor interaction stays inside one Gram quantity.

The first uniform quantitative consequence is elementary and deliberately crude: a corrected conductor packet is $q$-periodic, one incomplete period gives $\lVert J_q(k,x)\rVert\le 6q^3$, and hence all nontrivial conductors $q\le R$ contribute $O(R^4)$ uniformly in the prefix length. Choosing a cutoff on the order of the eighth root of the arithmetic scale puts that entire growing sector at square-root size, restricting the remaining Gram problem to conductor one and conductors above the cutoff.

The synthesis ledger is therefore at revision 5. These are exact identities, reductions, obstructions, and one uniform elementary bound; they do **not** assert a new asymptotic estimate at the target scale.

## Quantitative target

The missing theorem remains square-root-scale cancellation, for example

$$
M(X)\ll_\varepsilon X^{1/2+\varepsilon},
$$

or equivalently the corresponding squared Mertens-energy bound at exponent $1+\varepsilon$.

The formal recovery layer identifies this target with the square-prefix energy criterion, and the existing forward analytic bridge carries that criterion to the formal Riemann hypothesis.

Two things about the target are now sharper than before.

First, no subunit contraction is needed. The square-root endpoint statement is allowed an arbitrary fixed absolute amplification constant $A$,

$$
(M(R^2-1)-1)^2\le A\,R^2K_R,
$$

and strong induction on the physical integer, with an onset chosen so that $4A\le R^{\varepsilon}$, already closes the full shifted Mertens estimate. The unfinished part of one square block costs only $O(R^2)$ after squaring. So the open input is a *fixed*-amplification endpoint theorem, not a contraction.

Second, the residual-gap caveat stays explicit. Because

$$
M(X)=A_R^{\mathrm{pos}}+\bigl(A_R^{\mathrm{born}}-T_R\bigr),
$$

a bound on the matched object alone does not reach the square-prefix Mertens value. It needs the positive-orientation mass at the same scale, and that mass is exactly $-\sum_{q\le R}M(q-1)$. Both statements are named propositions in this package, and the theorem combining them into a square-prefix Mertens Gram bound is proved as a hypothetical implication.

## Proved obstructions

Structural obstructions are stated as ordinary theorems, not as estimates, and they are what constrains the next route.

- The transport transform carries a top block equal to its own cardinality, admitting no internal cancellation.
- Complete CRT periods cannot fit the square clock unless the selected prime-square product stays below the block width.
- The exact signed count gap between the middle-prime and inert-top populations is $2\pi(X_R/2)-\pi(X_R)-\pi(R)$. Its sign is a genuinely second-order prime-counting question: the leading $X/\log X$ terms cancel, so first-order PNT does not decide it, and the required stronger input is isolated rather than inferred.
- The strongest literal realization of the bounded collision-defect chain is refuted outright. If every defect label is weighted by the corrected prime-wheel field on the same physical site that realizes its selected-prime square collision, every such weight vanishes at the square hit, so every bounded chain mass is zero — a kernel-checked contradiction against the first nontrivial square prefix $-1$. The adjacent-cell escape is unavailable too: for $p\ge7$ a $p^2$ hit leaves only exponent states $0$ and $2$ across the current and next active cells, and the exponent flip fixes state $2$. A viable quotient must therefore transport a collision label to a different arithmetic fibre before reading its corrected weight, and must separately prove that transport preserves square-block mass with bounded multiplicity.
- Unrestricted fresh-prime equivariance between the prime-wheel mechanics and the canonical ancestry flow is false. It becomes exact precisely on the ordered submove where the adjoined prime exceeds every prime already in the parent core — the chronological Eulerian extension rule.

## Documentation and GitHub math

See [CURRENT_PROOF_ROUTE.md](CURRENT_PROOF_ROUTE.md) for the active proof plan, [MODULES.md](MODULES.md) for principal entry points, [SEAMS.md](SEAMS.md) for the exact interfaces, and [EMPIRICAL_DIAGNOSTICS.md](EMPIRICAL_DIAGNOSTICS.md) for finite diagnostics that are not used as asymptotic evidence.

All Markdown mathematics in this package uses GitHub-supported `$...$` and `$$...$$` delimiters. `scripts/check_markdown_math.py` rejects the unsupported `\(`, `\)`, `\[`, and `\]` delimiter forms outside code, and `.github/workflows/markdown-math.yml` runs that audit on every push and pull request.

## Building

Use the mirror rather than a bare `lake build`:

```bash
bash scripts/local_ci.sh
```

It audits the sources, restores the Mathlib cache, applies the StrongPNT compatibility patch, prebuilds the external theorem boundary, builds the library, gates warnings on the sources this package owns, and prints the axiom dependencies of the six status declarations — including the post-crossing coupled-tail route and the fixed-amplification closure.

Two details make a bare `lake build RHLean --wfail` the wrong command here.

**The StrongPNT dependency needs a compatibility patch.** Besides Mathlib, the package requires `PrimeNumberTheoremAnd` and `StrongPNT`, because the strong-Mertens corridor consumes the completed StrongPNT theorem source. `StrongPNT` is pinned at its finished upstream revision, and that revision predates Mathlib 4.24: its own sources do not elaborate against the Mathlib this package builds on. `lakefile.lean` already overrides the transitive `PrimeNumberTheoremAnd` snapshot with the one bumped to 4.24, but the StrongPNT source itself also has to be adjusted. `scripts/strongpnt_424/` holds that adjustment as five exact-match patch scripts, applied to the restored dependency sources before the build:

```bash
python3 scripts/strongpnt_424/apply.py
python3 scripts/strongpnt_424/apply_post.py
python3 scripts/strongpnt_424/apply_pnt5_mid.py
python3 scripts/strongpnt_424/apply_pnt5_strong.py
python3 scripts/strongpnt_424/apply_lint.py
```

They are exact-match by design: if the pinned upstream source ever changes, they fail loudly instead of guessing at a repair. Reapplying them to already-patched sources is a no-op. Every module outside the strong-Mertens layer depends on Mathlib alone.

**Warning-as-error has to be scoped.** Lake re-emits dependency warnings while building `RHLean`, so a global `--wfail` turns upstream linter churn in Mathlib, PNT+, or StrongPNT into a failure of this package. The build therefore runs without `--wfail`, and two gates apply warning-as-error to the sources this package actually owns: any warning pointing into `RHLean/`, and any diagnostic pointing into the patched StrongPNT port, which `scripts/strongpnt_424/` makes ours to keep silent.

One upstream scope note. StrongPNT's own `PNT1_ComplexAnalysis` contains an unfinished proof, so declarations downstream of it carry `sorryAx`. Nothing in `RHLean/` does, and `scripts/audit_assumptions.sh` enforces that for this package's sources; the status audits additionally print the kernel's axiom list for each headline declaration and fail on `sorryAx`, so an inherited one is reported rather than hidden.

## Related public projects

The companion projects `prime-wheel-mobius` and `square-block-mobius` develop the two main coordinate systems separately. This package records their exact synthesis and the remaining signed cancellation frontier.
