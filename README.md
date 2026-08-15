# Möbius Synthesis

This directory is the **canonical standalone export**. The public standalone repository is produced by mirroring the contents of `RH_Lean/export_mobius_synthesis` to repository root; mathematical or documentation updates should be made here first so the export remains the source of truth.

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

The synthesis ledger is therefore at revision 3. These are exact identities and reductions; they do **not** assert a new asymptotic estimate.

## Quantitative target

The missing theorem remains square-root-scale cancellation, for example

$$
M(X)\ll_\varepsilon X^{1/2+\varepsilon},
$$

or equivalently the corresponding squared Mertens-energy bound at exponent $1+\varepsilon$.

The formal recovery layer identifies this target with the square-prefix energy criterion, and the existing forward analytic bridge carries that criterion to the formal Riemann hypothesis.

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
