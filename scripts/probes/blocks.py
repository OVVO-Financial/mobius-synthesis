"""Completed square blocks: what the increments actually do.

Block j is [j^2, (j+1)^2), length 2j+1.  Its signed Moebius mass is
    Delta_j = M(X_j) - M(X_{j-1}),   X_j = (j+1)^2 - 1.
So M(X_N) = sum_{j<=N} Delta_j, and the RH target is |M(X_N)| << N^(1+eps).
"""
import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import numpy as np
from mobius import sieve_mu

X = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 8
N = int(X ** 0.5) - 1
mu = sieve_mu(X)
M = np.cumsum(mu, dtype=np.int64)

j = np.arange(1, N + 1, dtype=np.int64)
Xj = (j + 1) ** 2 - 1
D = (M[Xj] - M[Xj - (2 * j + 1)]).astype(np.float64)   # block [j^2,(j+1)^2)
L = (2 * j + 1).astype(np.float64)
SQFREE = 6 / np.pi ** 2                                 # squarefree density

print("blocks j = 1..%d   (X up to %.1e)" % (N, X))
print()
print("=== 1. against the trivial (squarefree-density) ceiling ~0.6079*L ===")
print("%10s %12s %12s %12s %12s" % ("j<=", "max|D_j|", "max L", "max |D|/L", "ceiling"))
for c in [10 ** k for k in range(1, 9) if 10 ** k <= N]:
    m = j <= c
    print("%10d %12.0f %12.0f %12.5f %12.5f"
          % (c, np.abs(D[m]).max(), L[m].max(),
             (np.abs(D[m]) / L[m]).max(), SQFREE))

print()
print("=== 2. is |Delta_j| ~ sqrt(j) ? ===")
print("%10s %12s %12s %12s %12s"
      % ("j<=", "rms|D_j|", "rms/sqrt(j)", "max|D|/sqrt(j)", "sqrt(2*.6079)"))
for c in [10 ** k for k in range(1, 9) if 10 ** k <= N]:
    m = j <= c
    rms = float(np.sqrt(np.mean(D[m] ** 2)))
    print("%10d %12.2f %12.4f %12.4f %12.4f"
          % (c, rms, rms / np.sqrt(c), (np.abs(D[m]) / np.sqrt(j[m])).max(),
             np.sqrt(2 * SQFREE)))

print()
print("=== 3. the triangle-sum loss:  sum|Delta_j|  against  |sum Delta_j| ===")
print("%10s %14s %14s %10s %10s"
      % ("N", "sum|D_j|", "|M(X_N)|", "loss", "sqrt(N)"))
for c in [10 ** k for k in range(1, 9) if 10 ** k <= N]:
    m = j <= c
    s1 = float(np.abs(D[m]).sum()); s2 = abs(float(D[m].sum()))
    print("%10d %14.4g %14.4g %10.1f %10.1f"
          % (c, s1, s2, s1 / max(s2, 1e-9), np.sqrt(c)))

print()
print("=== 4. fitted exponents (j >= 100) ===")
m = j >= 100
for lab, v in (("rms |Delta_j| in dyadic bins", None),):
    pass
edges = [2 ** k for k in range(7, 40) if 2 ** k <= N]
xs, ys = [], []
for a, b in zip(edges, edges[1:]):
    s = (j >= a) & (j < b)
    if s.sum() > 8:
        xs.append(np.log(np.sqrt(a * b))); ys.append(np.log(np.sqrt(np.mean(D[s] ** 2))))
if len(xs) > 2:
    print("  rms |Delta_j| local exponent: %.4f   (1/2 = square-root law)"
          % np.polyfit(xs, ys, 1)[0])
sm = j >= 100
print("  sum_{j<=N}|Delta_j| exponent:  %.4f   (3/2 expected if |D_j|~sqrt j)"
      % np.polyfit(np.log(j[sm]), np.log(np.cumsum(np.abs(D))[sm]), 1)[0])
print("  |M(X_N)| target exponent:      1.0   (RH scale at X=N^2)")
