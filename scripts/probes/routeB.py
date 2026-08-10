"""Route B: the signed reciprocal-interval family.

Mirrors RHLean.Analysis.PrimeSievePNTCentering / PrimeSieveQuotientPNTError,
uncentered (the zero-mode center Z is a fixed 3-term linear combination, so it
cannot change the growth exponent of what follows).

  y            = Nat.sqrt x + 1                    (the hypothesis sqrt x < y)
  T(y,x)       = sum_{y<q<=x, q prime} M(x//q)      prime tail
  density(q)   = Li(q) - Li(q-1)
  Bulk(y,x)    = sum_{y<q<=x} density(q) * M(x//q)
  Err(y,x)     = T - Bulk                           = E^rec
  allPlus      = M(x) + 2T                          (PrimeSievePostSqrtGap)
  C            = allPlus - 2*Bulk                   = C^PNT
  =>  C - 2E   = M(x)                               exactly

Reciprocal-quotient reindexing (PrimeSieveQuotientPNTError): the fibre of
d = x//q is exactly the interval  I_d = (max(y, x//(d+1)), x//d],  and the
singleton Li masses telescope on it, so

  E = sum_{d=1}^{x//y} M(d) * ( pi(I_d) - LiMass(I_d) ).

The open question of CURRENT_PROOF_ROUTE section 6 is whether this signed
d-family saves the ~x^(1/2) that the target needs.  This script measures the
actual saving against the termwise triangle bound.
"""

import sys, math, time, pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import numpy as np
from mobius import sieve_mu

EULER = 0.5772156649015328606


def Ei(z):
    """Exponential integral Ei(z) for z > 0 (series; z <= ~30 here)."""
    s = 0.0
    term = 1.0
    for k in range(1, 200):
        term *= z / k
        s += term / k
        if term / k < 1e-18 * abs(s) and k > z:
            break
    return EULER + math.log(z) + s


_li2 = None


def Li(t):
    """Li(t) = int_2^t du/log u."""
    global _li2
    if _li2 is None:
        _li2 = Ei(math.log(2.0))
    if t <= 2:
        return 0.0
    return Ei(math.log(t)) - _li2


def prime_counts_at(checkpoints, xmax, blk=1 << 24):
    """pi(t) for each t in sorted `checkpoints` (segmented sieve)."""
    cps = np.asarray(sorted(set(int(c) for c in checkpoints if c >= 0)), dtype=np.int64)
    out = {}
    base = int(math.isqrt(xmax)) + 1
    small = np.ones(base + 1, dtype=bool)
    small[:2] = False
    for p in range(2, int(math.isqrt(base)) + 1):
        if small[p]:
            small[p * p :: p] = False
    sp = np.flatnonzero(small).astype(np.int64)

    count = 0
    ci = 0
    lo = 0
    while lo <= xmax and ci < len(cps):
        hi = min(lo + blk, xmax + 1)
        seg = np.ones(hi - lo, dtype=bool)
        if lo == 0:
            seg[0] = False
            if hi > 1:
                seg[1] = False
        for p in sp:
            if p * p >= hi:
                break
            start = max(p * p, ((lo + p - 1) // p) * p)
            if start < hi:
                seg[start - lo :: p] = False
        csum = np.cumsum(seg)
        while ci < len(cps) and cps[ci] < hi:
            t = cps[ci]
            out[int(t)] = count + (int(csum[t - lo]) if t >= lo else 0)
            ci += 1
        count += int(csum[-1])
        lo = hi
    while ci < len(cps):
        out[int(cps[ci])] = count
        ci += 1
    return out


def run(x, M):
    y = math.isqrt(x) + 1
    D = x // y
    ds = np.arange(1, D + 1, dtype=np.int64)
    hi = x // ds
    lo = np.maximum(y, x // (ds + 1))
    keep = hi > lo
    ds, hi, lo = ds[keep], hi[keep], lo[keep]

    cps = prime_counts_at(np.concatenate([hi, lo]), x)
    pihi = np.array([cps[int(v)] for v in hi], dtype=np.int64)
    pilo = np.array([cps[int(v)] for v in lo], dtype=np.int64)
    cnt = pihi - pilo

    Lihi = np.array([Li(float(v)) for v in hi])
    Lilo = np.array([Li(float(v)) for v in lo])
    lim = Lihi - Lilo

    Md = M[ds].astype(np.float64)
    disc = cnt - lim                     # prime-count discrepancy on I_d
    terms = Md * disc

    E = float(terms.sum())
    absE = float(np.abs(terms).sum())
    T = float((Md * cnt).sum())
    Bulk = float((Md * lim).sum())
    MX = int(M[x])
    allPlus = MX + 2 * T
    C = allPlus - 2 * Bulk
    return dict(x=x, y=y, D=len(ds), M=MX, T=T, Bulk=Bulk, E=E, absE=absE,
                C=C, check=C - 2 * E, terms=terms, disc=disc, Md=Md, ds=ds)


if __name__ == "__main__":
    XMAX = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 8
    t0 = time.time()
    mu = sieve_mu(XMAX)
    M = np.cumsum(mu, dtype=np.int64)
    del mu
    print("sieve+M to %.1e: %.1fs" % (XMAX, time.time() - t0), flush=True)

    xs = [10 ** k for k in range(4, 13) if 10 ** k <= XMAX]
    xs += [3 * 10 ** k for k in range(4, 13) if 3 * 10 ** k <= XMAX]
    xs = sorted(set(xs))

    print()
    hdr = "%12s %8s %10s %14s %14s %14s %10s %9s %9s" % (
        "x", "D", "M(x)", "T", "Bulk", "E=T-Bulk", "sum|E_d|", "saving", "|E|/sqrtx")
    print(hdr); print("-" * len(hdr))
    res = []
    for x in xs:
        r = run(x, M)
        res.append(r)
        assert abs(r["check"] - r["M"]) < 1e-3 * max(1, abs(r["M"])), (r["check"], r["M"])
        print("%12d %8d %10d %14.1f %14.1f %14.2f %10.1f %9.2f %9.4f"
              % (x, r["D"], r["M"], r["T"], r["Bulk"], r["E"], r["absE"],
                 r["absE"] / abs(r["E"]) if r["E"] else float("inf"),
                 abs(r["E"]) / math.sqrt(x)))
    print()
    print("identity C - 2E = M(x) verified at every x above.")

    print()
    print("growth exponents (consecutive x):")
    print("%22s %9s %9s %9s %9s" % ("x range", "|E|", "sum|E_d|", "|C|", "|T|"))
    for a, b in zip(res, res[1:]):
        lr = math.log(b["x"] / a["x"])
        def ex(u, v):
            if not u or not v:
                return float("nan")
            return math.log(abs(v) / abs(u)) / lr
        print("%22s %9.3f %9.3f %9.3f %9.3f"
              % ("%.0e->%.0e" % (a["x"], b["x"]), ex(a["E"], b["E"]),
                 ex(a["absE"], b["absE"]), ex(a["C"], b["C"]), ex(a["T"], b["T"])))

    # where does the mass of E live?  small d (long intervals) or large d (short)?
    print()
    print("=== distribution of E over the d-family (largest x) ===")
    r = res[-1]
    ds, terms = r["ds"], r["terms"]
    print("%14s %12s %14s %14s" % ("d range", "#d", "sum terms", "sum |terms|"))
    edges = [1, 10, 100, 1000, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7]
    for a, b in zip(edges, edges[1:] + [r["D"] + 1]):
        m = (ds >= a) & (ds < b)
        if not m.any():
            continue
        print("%14s %12d %14.2f %14.2f"
              % ("[%d,%d)" % (a, b), int(m.sum()), float(terms[m].sum()),
                 float(np.abs(terms[m]).sum())))
