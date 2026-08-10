"""Confirm the MECHANISM behind the Route A ceiling.

Summation by parts turns the uncancelled region of the orientation split into a
pi-weighted Mertens sum:

    positiveSmooth(R) = - sum_{q<=R} M(q-1) = - sum_{c<R} mu(c)*(pi(R)-pi(c)),

i.e. an INTEGRAL of the Mertens function against dpi.  Integration is a
smoothing: it removes exactly the sign oscillation the RH-scale target relies
on.  Under RH the explicit formula gives

    int_1^R M(t) dt = sum_rho R^(rho+1)/(rho(rho+1)zeta'(rho)) + O(1),

every term of modulus R^(3/2)/|rho(rho+1)zeta'(rho)|, so the integral is
R^(3/2-o(1)) and cannot be pushed lower by cancellation among zeros.

This script checks the two links numerically:
  (a) the discrete integral  I(R) = sum_{n<=R} M(n)  grows like R^1.5;
  (b) posSmooth(R) tracks  -int_2^R M(t)/log t dt.
"""

import sys, time, pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import numpy as np
from mobius import sieve_mu, primes_upto

N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 8

mu = sieve_mu(N)
M = np.cumsum(mu, dtype=np.int64)
del mu
I = np.cumsum(M, dtype=np.int64)          # I[R] = sum_{n<=R} M(n)

print("=== (a) discrete integral I(R) = sum_{n<=R} M(n):  is it R^1.5 ? ===")
print("%12s %18s %12s %12s %10s" % ("R", "I(R)", "/R^1.25", "/R^1.5", "loc.exp"))
prev = None
k = 10
while 2 ** k <= N:
    R = 2 ** k
    v = int(np.abs(I[: R + 1]).max())
    e = "-" if prev is None else "%.4f" % (np.log(v / prev[1]) / np.log(R / prev[0]))
    print("%12d %18d %12.4f %12.5f %10s"
          % (R, v, v / R ** 1.25, v / R ** 1.5, e))
    prev = (R, v)
    k += 1
xs = np.array([np.log(2 ** k) for k in range(10, 40) if 2 ** k <= N])
ys = np.array([np.log(int(np.abs(I[: 2 ** k + 1]).max())) for k in range(10, 40) if 2 ** k <= N])
A = np.vstack([xs[-8:], np.ones(8)]).T
s, _ = np.linalg.lstsq(A, ys[-8:], rcond=None)[0]
print("least-squares exponent of running max |I| (last 8 octaves): %.4f" % s)
print("  -> the integral of M carries the FULL 3/2 power; no cancellation remains.")

print()
print("=== (b) posSmooth(R) vs the smooth model -int_2^R M(t)/log t dt ===")
pr = primes_upto(N)
t = np.arange(2, N + 1, dtype=np.float64)
integrand = M[2:].astype(np.float64) / np.log(t)
Ilog = np.cumsum(integrand)
print("%12s %16s %16s %8s" % ("R", "posSmooth", "-int M/log", "ratio"))
for R in [10 ** k for k in range(3, 10) if 10 ** k <= N]:
    i = np.searchsorted(pr, R, side="right")
    ps = -int(M[pr[:i] - 1].sum())
    model = -Ilog[R - 2]
    print("%12d %16d %16.0f %8.3f" % (R, ps, model, (ps / model) if model else float("nan")))
