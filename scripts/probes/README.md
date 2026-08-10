# Numerical probes

Diagnostic scripts backing the closures recorded in `boundary/dead_lanes.json`.

Per the repository status convention, **numerical experiments and finite-range
checks are diagnostic evidence only**. Nothing here is machine checked and
nothing here is a proof. The scripts exist so that a closed lane can be
re-tested rather than re-argued.

Requires `numpy` only.

## What each script does

| script | purpose |
| --- | --- |
| `mobius.py` | shared sieve: `mu`, largest prime factor, `M(x)`, primes. Uses the small-prime / large-remainder factorization, so only primes up to `sqrt(N)` are iterated. |
| `verify_defs.py` | brute-force check that the Python objects reproduce the Lean ones, and that `positiveSmooth R = -sum_{q<=R prime} M(q-1)`. Verifies four identities for every `R = 2..300`. |
| `matched_growth.py` | growth of `squareRootMatchedBornSmoothTransport` and its pieces, computed directly. |
| `posSmooth_1e9.py` | blocked large-scale growth of `positiveSmooth(R)` to `R = 1e9`. |
| `mechanism.py` | confirms *why* the lane closes: that `positiveSmooth` is the smoothed integral of `M`, and that `sum_{n<=R} M(n)` carries the full `3/2` power. |
| `routeB.py` | the PNT-centered / reciprocal-interval objects `T`, `Bulk`, `E^rec`, `C^PNT` at selected `x`. |
| `routeB_dense.py` | dense-grid growth exponents and correlations for Route B. |

## Reproducing the recorded measurements

```bash
cd scripts/probes
python3 verify_defs.py                 # identities, R = 2..300      (~1 min)
python3 mechanism.py 1e8               # Route A mechanism           (~1 min)
python3 posSmooth_1e9.py 1e9           # Route A growth to R = 1e9   (~3 min, ~6 GB)
python3 matched_growth.py 1e8          # matched object directly     (~1 min)
python3 routeB_dense.py 1e8 240        # Route B statistics          (~1 min)
```

`posSmooth_1e9.py` is the memory-hungry one; pass a smaller bound (`1e8`) on a
small machine.

## The two objects being measured

**Route A** (lane `canonical-orientation-split`). Writing `q = P+(m)`,
`c = m/q`, `X = R^2-1`, the canonical orientation split of the square-root
smooth mass leaves exactly one region uncancelled, and it has a closed form:

```text
squareRootPositiveSmoothMass R = -sum_{q<=R prime} M(q-1)
                               = -sum_{c<R} mu(c) * (pi(R) - pi(c))
M(R^2-1) = positiveSmooth(R) + matched(R)
```

The condition `P+(m) <= R` is implied by `P+(m) <= c_m` on `[0,X]`, and for
`c < q <= R` the constraint `cq <= X` is automatic — which is why the region
collapses this far. Summation by parts turns it into an integral of `M`
against `dpi`, and integrating `M` cannot beat `R^(3/2)`.

**Route B** (lane `pnt-reciprocal-coordinate-change`, plus the still-open
reciprocal-`d` family). With `y = sqrt(x)+1`:

```text
T    = sum_{y<q<=x, q prime} M(x/q)
Bulk = sum_{y<q<=x} (Li(q)-Li(q-1)) * M(x/q)
E    = T - Bulk                      C = allPlus - 2*Bulk = M + 2E
E    = sum_{d<=x/y} M(d) * (pi(I_d) - LiMass(I_d)),  I_d = (max(y,x/(d+1)), x/d]
```

`Li` is evaluated by an `Ei` series in `routeB.py` and by cumulative midpoint
quadrature in `routeB_dense.py`; only differences `Li(hi)-Li(lo)` with
`lo >= sqrt(x)` are ever used, and the two agree to `5.5e-12` relative.
