"""Native-Moebius matched atom population, and the proposed inequality
        |Matched_R|^2  <<_eps  R^eps * D_R,   D_R = #squarefree in U_R <= R^2.

Verified earlier this session (brute force, R = 2..300):
    matched(R) = bornSmooth(R) - transport(R)
               = sum over m <= X_R with [P+(m)^2 <= m] OR [P+(m) > R] of mu(m)
so U_R is exactly region1 (born-smooth, q<=c) union region3 (high, q>R).
"""
import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import numpy as np
from mobius import sieve_mu_lpf

XMAX = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 7
mu, lpf = sieve_mu_lpf(XMAX)
cof = np.arange(XMAX + 1, dtype=np.int64) // lpf
RMAX = int(XMAX ** 0.5)

print("%7s %12s %12s %12s %10s %10s"
      % ("R", "Matched_R", "D_R", "R^2", "|Mat|^2/D", "|Mat|/R"))
rows = []
Rs = [r for r in [100, 200, 400, 800, 1600, 2000, 2500, 3000, 3162] if r <= RMAX]
for R in Rs:
    X = R * R - 1
    lp = lpf[: X + 1]; c = cof[: X + 1]; w = mu[: X + 1].astype(np.int64)
    inU = (lp <= c) | (lp > R)          # region1 or region3
    matched = int(w[inU].sum())
    D = int((w[inU] != 0).sum())         # squarefree count in U_R
    rows.append((R, matched, D))
    print("%7d %12d %12d %12d %10.4f %10.4f"
          % (R, matched, D, R * R, matched ** 2 / max(D, 1), abs(matched) / R))

print()
print("dyadic max of |Matched_R|^2 / D_R  (their reported max was 2.80 for R<1600)")
for lo, hi in [(2, 100), (100, 400), (400, 800), (800, 1600), (1600, RMAX + 1)]:
    if lo >= RMAX:
        continue
    best = 0.0; arg = 0
    for R in range(lo, min(hi, RMAX + 1)):
        X = R * R - 1
        lp = lpf[: X + 1]; c = cof[: X + 1]; w = mu[: X + 1].astype(np.int64)
        inU = (lp <= c) | (lp > R)
        m = int(w[inU].sum()); D = int((w[inU] != 0).sum())
        r = m * m / max(D, 1)
        if r > best:
            best, arg = r, R
    print("  R in [%5d,%5d):  max |Mat|^2/D_R = %8.3f  at R = %d" % (lo, min(hi, RMAX + 1), best, arg))
