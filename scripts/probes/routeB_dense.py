"""Route B, dense grid.  Robust growth statistics for

    M(x) = C^PNT(x) - 2 E^rec(x),      C = M + 2E   (a theorem, not a definition)
    E^rec(x) = sum_{d<=x//y} M(d) * (pi(I_d) - LiMass(I_d))

Questions:
  1. Does the signed d-family really save what the target needs?
     -> compare |E| against the termwise bound sum_d |E_d| and against
        sum_d |E_d| / sqrt(D)  (square-root cancellation over D fibres).
  2. Is the PNT split a REDUCTION?  i.e. is |C| systematically below |M|?
"""

import sys, math, time, pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import numpy as np
from mobius import sieve_mu
from routeB import Li

XMAX = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 8
NGRID = int(sys.argv[2]) if len(sys.argv) > 2 else 240

t0 = time.time()
mu = sieve_mu(XMAX)
M = np.cumsum(mu, dtype=np.int64)
del mu
print("mu + M to %.1e: %.1fs" % (XMAX, time.time() - t0), flush=True)

t0 = time.time()
isp = np.ones(XMAX + 1, dtype=bool)
isp[:2] = False
for p in range(2, int(math.isqrt(XMAX)) + 1):
    if isp[p]:
        isp[p * p :: p] = False
PI = np.cumsum(isp, dtype=np.int64)
del isp
print("pi prefix: %.1fs" % (time.time() - t0), flush=True)

# Li on the integer grid, by cumulative midpoint quadrature (error per unit
# ~ 1/(24 t^2 log^2 t); total tail error far below 1e-6 over the used range).
t0 = time.time()
tt = np.arange(2, XMAX + 1, dtype=np.float64)
LIarr = np.empty(XMAX + 1, dtype=np.float64)
LIarr[:3] = 0.0
LIarr[2:] = np.concatenate(([0.0], np.cumsum(1.0 / np.log(tt[:-1] + 0.5))))
# Only DIFFERENCES Li(hi)-Li(lo) with lo >= sqrt(x) are ever used, so the
# quadrature error accumulated near t=2 cancels.  Check the differences.
worst = 0.0
for a, b in ((10 ** 4, 10 ** 5), (10 ** 4, XMAX), (10 ** 6, XMAX), (XMAX // 2, XMAX)):
    if b <= XMAX and a < b:
        ex = Li(float(b)) - Li(float(a))
        got = LIarr[b] - LIarr[a]
        worst = max(worst, abs(got - ex) / ex)
assert worst < 1e-10, worst
print("Li table: %.1fs (differences match series to %.1e rel)"
      % (time.time() - t0, worst), flush=True)


def measure(x):
    y = math.isqrt(x) + 1
    D = x // y
    ds = np.arange(1, D + 1, dtype=np.int64)
    hi = x // ds
    lo = np.maximum(y, x // (ds + 1))
    k = hi > lo
    ds, hi, lo = ds[k], hi[k], lo[k]
    disc = (PI[hi] - PI[lo]).astype(np.float64) - (LIarr[hi] - LIarr[lo])
    terms = M[ds].astype(np.float64) * disc
    E = float(terms.sum())
    absE = float(np.abs(terms).sum())
    return E, absE, len(ds), int(M[x])


xs = np.unique(np.round(np.logspace(4, math.log10(XMAX), NGRID)).astype(np.int64))
t0 = time.time()
rows = []
for x in xs:
    E, absE, D, MX = measure(int(x))
    rows.append((int(x), E, absE, D, MX, MX + 2 * E))
print("dense sweep over %d values of x: %.1fs" % (len(xs), time.time() - t0), flush=True)

arr = np.array([(r[0], r[1], r[2], r[3], r[4], r[5]) for r in rows], dtype=np.float64)
X, E, absE, D, MX, C = arr[:, 0], arr[:, 1], arr[:, 2], arr[:, 3], arr[:, 4], arr[:, 5]

print()
print("=== dyadic running maxima, normalised by sqrt(x) ===")
hd = "%12s %10s %10s %11s %11s %12s" % ("x<=", "max|M|/vx", "max|E|/vx", "max|C|/vx",
                                        "max S/vx", "max S/(vD vx)")
print(hd); print("-" * len(hd))
k = 14
while 2 ** k <= XMAX:
    m = X <= 2 ** k
    if m.sum() >= 3:
        print("%12.2e %10.4f %10.4f %11.4f %11.4f %12.4f"
              % (2 ** k,
                 np.abs(MX[m] / np.sqrt(X[m])).max(),
                 np.abs(E[m] / np.sqrt(X[m])).max(),
                 np.abs(C[m] / np.sqrt(X[m])).max(),
                 (absE[m] / np.sqrt(X[m])).max(),
                 (absE[m] / (np.sqrt(D[m]) * np.sqrt(X[m]))).max()))
    k += 1


def fit(v, lab, lo=None):
    m = (v != 0)
    if lo is not None:
        m &= X >= lo
    s = np.polyfit(np.log(X[m]), np.log(np.abs(v[m])), 1)[0]
    print("  %-28s exponent %.4f" % (lab, s))


print()
print("=== least-squares growth exponents (all x >= 1e5) ===")
fit(E, "|E^rec|", 1e5)
fit(absE, "sum_d |E_d|  (triangle bd)", 1e5)
fit(absE / np.sqrt(D), "sum_d|E_d| / sqrt(D)", 1e5)
fit(MX, "|M(x)|", 1e5)
fit(C, "|C^PNT|", 1e5)
print("  (target exponent is 0.5)")

print()
print("=== sub-range robustness of the exponents ===")
print("%18s %10s %10s %10s" % ("x range", "|E|", "sum|E_d|", "sum|E_d|/vD"))
for a, b in ((1e4, 1e6), (1e5, 1e7), (1e6, 1e8), (1e5, 1e8), (1e7, 1e8)):
    m = (X >= a) & (X <= b) & (E != 0)
    if m.sum() < 5:
        continue
    f = lambda v: np.polyfit(np.log(X[m]), np.log(np.abs(v[m])), 1)[0]
    print("%18s %10.4f %10.4f %10.4f"
          % ("%.0e-%.0e" % (a, b), f(E), f(absE), f(absE / np.sqrt(D))))

print()
print("=== does the d-family cancel like a square root? ===")
pred = absE / np.sqrt(D)
r = np.abs(E) / pred
print("  |E| / (sum|E_d|/sqrt(D)):  median %.3f  mean %.3f  [%.3f, %.3f]"
      % (np.median(r), r.mean(), r.min(), r.max()))
print("  correlation log|E| vs log(sum|E_d|/sqrt(D)): %.4f"
      % np.corrcoef(np.log(np.abs(E)), np.log(pred))[0, 1])
tri = np.abs(E) / absE
print("  |E| / sum|E_d| (saving factor 1/x): median %.5f -> saving %.1f x"
      % (np.median(tri), 1 / np.median(tri)))

print()
print("=== is the PNT split a REDUCTION?  (is |C| below |M|?) ===")
ratio = np.abs(C) / np.maximum(np.abs(MX), 1)
print("  |C|/|M|: median %.3f  mean %.3f  frac with |C|<|M|: %.3f"
      % (np.median(ratio), ratio.mean(), float((ratio < 1).mean())))
print("  max|C|/sqrt(x) over all x = %.4f   vs   max|M|/sqrt(x) = %.4f"
      % (np.abs(C / np.sqrt(X)).max(), np.abs(MX / np.sqrt(X)).max()))
print("  corr(C, M) = %.4f ;  corr(C, 2E) = %.4f ;  corr(M, 2E) = %.4f"
      % (np.corrcoef(C, MX)[0, 1], np.corrcoef(C, 2 * E)[0, 1],
         np.corrcoef(MX, 2 * E)[0, 1]))
