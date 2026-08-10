"""Large-scale growth of

    positiveSmooth(R) = - sum_{q <= R, q prime} M(q-1)
                      = - sum_{c < R} mu(c) * (pi(R) - pi(c))

This is the single region of the canonical orientation split that the
matched born-smooth / transport object leaves uncancelled:

    M(R^2-1) = positiveSmooth(R) + matched(R).

RH scale at X = R^2-1 is R^(1+eps).  Blockwise so 1e9 fits in memory.
"""

import sys, time, pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import numpy as np
from mobius import sieve_mu

N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 9
BLK = 5 * 10 ** 7

t0 = time.time()
mu = sieve_mu(N)
print("mu sieve to %.2e: %.1fs" % (N, time.time() - t0), flush=True)

t0 = time.time()
isp = np.ones(N + 1, dtype=bool)
isp[:2] = False
for p in range(2, int(N ** 0.5) + 1):
    if isp[p]:
        isp[p * p :: p] = False
print("prime sieve: %.1fs" % (time.time() - t0), flush=True)

grid = sorted(set([10 ** k for k in range(2, 11) if 10 ** k <= N]
                  + [3 * 10 ** k for k in range(2, 11) if 3 * 10 ** k <= N]))
grid_vals = {}

dyadic = [2 ** k for k in range(7, 41) if 2 ** k <= N]
dy_max = {}

t0 = time.time()
Moff = 0          # M(lo-1)
run = 0           # sum_{q < lo} M(q-1)
runmax = 0
gi, di = 0, 0
lo = 0
while lo <= N:
    hi = min(lo + BLK, N + 1)
    Mb = np.cumsum(mu[lo:hi], dtype=np.int64)
    Mb += Moff                        # Mb[i] = M(lo+i)
    qs = np.flatnonzero(isp[lo:hi]).astype(np.int64) + lo
    if qs.size:
        # M(q-1): index q-1-lo, except q == lo (then it is Moff)
        idx = qs - 1 - lo
        vals = np.where(idx >= 0, Mb[np.maximum(idx, 0)], Moff)
        cs = np.cumsum(vals) + run
        runmax = max(runmax, int(np.abs(cs).max()))
        # record grid points
        while gi < len(grid) and grid[gi] < hi:
            R = grid[gi]
            j = np.searchsorted(qs, R, side="right")
            grid_vals[R] = -(int(cs[j - 1]) if j > 0 else run)
            gi += 1
        while di < len(dyadic) and dyadic[di] < hi:
            R = dyadic[di]
            j = np.searchsorted(qs, R, side="right")
            sub = np.abs(cs[:j])
            m = int(sub.max()) if j > 0 else 0
            dy_max[R] = max(m, dy_max.get(R, 0),
                            max([v for k, v in dy_max.items() if k < R] or [0]))
            di += 1
        run = int(cs[-1])
    Moff = int(Mb[-1])
    lo = hi
print("blocked pass: %.1fs" % (time.time() - t0), flush=True)

print()
print("=== positiveSmooth(R) at grid points ===")
print("%12s %16s %10s %10s %12s" % ("R", "positiveSmooth", "/R", "/R^1.25", "*logR/R^1.5"))
for R in grid:
    v = grid_vals.get(R)
    if v is None:
        continue
    print("%12d %16d %10.3f %10.4f %12.5f"
          % (R, v, abs(v) / R, abs(v) / R ** 1.25,
             abs(v) * np.log(R) / R ** 1.5))

print()
print("=== running max |positiveSmooth| over R' <= R (dyadic) ===")
print("%12s %16s %10s %10s %12s %10s"
      % ("R", "max|posSm|", "/R", "/R^1.25", "*logR/R^1.5", "loc.exp"))
prev = None
for R in dyadic:
    m = dy_max.get(R)
    if m is None:
        continue
    e = "-" if prev is None or prev[1] == 0 or m == 0 else \
        "%.4f" % (np.log(m / prev[1]) / np.log(R / prev[0]))
    print("%12d %16d %10.3f %10.4f %12.5f %10s"
          % (R, m, m / R, m / R ** 1.25, m * np.log(R) / R ** 1.5, e))
    prev = (R, m)

xs = np.array([np.log(R) for R in dyadic if dy_max.get(R, 0) > 0])
ys = np.array([np.log(dy_max[R]) for R in dyadic if dy_max.get(R, 0) > 0])
for lbl, sl in (("all", slice(None)), ("upper half", slice(len(xs) // 2, None)),
                ("last 8", slice(-8, None))):
    A = np.vstack([xs[sl], np.ones(len(xs[sl]))]).T
    s, _ = np.linalg.lstsq(A, ys[sl], rcond=None)[0]
    print("least-squares exponent of running max (%s): %.4f" % (lbl, s))
