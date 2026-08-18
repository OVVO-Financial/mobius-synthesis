# Möbius Synthesis

This is a self-contained Lake package. `RHLean.lean` imports every shipped module, so `lake build RHLean --wfail` builds the whole development.

The project is a Lean 4 formalization of square-sensitive and prime-wheel cancellation in the Möbius summatory function. Its central arithmetic object is the signed field

$$
R-2H,
$$

where `R` is the seeded prime-wheel mass and `H` is the smooth-core correction. Under square-root prime coverage this field is proved exactly equal to the ordinary Möbius prefix.

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

So a complete-cell estimate transfers to every physical cutoff with only a bounded additive correction.

The refreshed export also contains the merged collision, finite-difference, survivor-parity, dyadic, affine-excursion, and renewal layers:

- the corrected `R - 2H` field has the exact local sign law under a genuine selected-prime exponent flip;
- square-hit fixed points have exactly zero corrected weight;
- the mate-crosses-cutoff collision defect has at most three labels;
- arbitrary Boolean-supported alternating mass has exact one-, two-, and three-coordinate finite-difference formulas;
- for every prime survivor fibre $q\ge 7$, the actual survivor mass has an exact `2-3-5` eight-state third-difference representation;
- the parity residue channels retain their exact signed Gram, and nonzero dyadic pair mass is confined to three explicit geometric shells;
- the weighted renewal telescope is connected exactly to the far-upper survivor sector and the primorial square-wheel zero-mode center.

The export also carries the square-root orientation layer:

- the smooth mass splits exactly by canonical orientation into a positive and a born-smooth part, and the matched object is the born-smooth mass minus the high transport mass;
- the reciprocal-cutoff floor rounding and the prime-counting discrepancy are combined into a single signed residual $D_R$ *channel by channel*, before the cofactor sum, so neither is ever available alone;
- the born-smooth mass is put into the same lower-scale Möbius/reciprocal form the transport already had, giving one signed sum over the whole prime range;
- the smoothness cutoff is proved automatic on the born orientation;
- the parity-class form of the complete smooth mass is exact, and the residual gap between the matched criterion and the square-prefix Mertens value is made explicit.

Two structural obstructions are proved as ordinary theorems: the transport transform carries a top block equal to its own cardinality, admitting no internal cancellation, and complete CRT periods cannot fit the square clock unless the selected prime-square product stays below the block width.

The synthesis ledger is therefore at revision 4. These are exact identities, reductions, and obstructions; they do **not** assert a new asymptotic estimate.

## Quantitative target

The missing theorem remains square-root-scale cancellation, for example

$$
M(X)\ll_\varepsilon X^{1/2+\varepsilon},
$$

or equivalently the corresponding squared Mertens-energy bound at exponent $1+\varepsilon$.

The formal recovery layer identifies this target with the square-prefix energy criterion, and the existing forward analytic bridge carries that criterion to the formal Riemann hypothesis.

One caveat is now explicit rather than implicit. Because

$$
M(X)=A_R^{\mathrm{pos}}+\bigl(A_R^{\mathrm{born}}-T_R\bigr),
$$

a bound on the matched object alone does not reach the square-prefix Mertens value. It needs the positive-orientation mass at the same scale, and that mass is exactly $-\sum_{q\le R}M(q-1)$. Both statements are named propositions in the export, and the theorem combining them into a square-prefix Mertens Gram bound is proved as a hypothetical implication.

The strongest new collision reduction is conditional in exactly the right place: an exact bounded collision-defect chain for every square-prefix endpoint would give

$$
|M((n+1)^2-1)|\le 3(n+1)
$$

and hence critical square-prefix energy with constant $9$. Constructing that globally chargeable chain, or proving an equivalent signed survivor-corner or covariance power saving, is the remaining arithmetic problem.

## Documentation and GitHub math

See [CURRENT_PROOF_ROUTE.md](CURRENT_PROOF_ROUTE.md) for the active proof plan, [MODULES.md](MODULES.md) for principal entry points, [SEAMS.md](SEAMS.md) for the exact interfaces, and [EMPIRICAL_DIAGNOSTICS.md](EMPIRICAL_DIAGNOSTICS.md) for finite diagnostics that are not used as asymptotic evidence.

All Markdown mathematics in this export uses GitHub-supported `$...$` and `$$...$$` delimiters. `scripts/check_markdown_math.py` rejects the unsupported `\(`, `\)`, `\[`, and `\]` delimiter forms outside code, and `.github/workflows/markdown-math.yml` carries that audit into the standalone repository when this directory is mirrored to repository root.

## Related public projects

The companion projects `prime-wheel-mobius` and `square-block-mobius` develop the two main coordinate systems separately. This package records their exact synthesis and the remaining signed cancellation frontier.
