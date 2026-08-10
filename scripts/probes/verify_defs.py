"""Brute-force verification that the Python harness reproduces the Lean objects,
and of the claimed closed form

    squareRootPositiveSmoothMass R = - sum_{q <= R, q prime} M(q-1).
"""

import sys, pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import numpy as np
from mobius import sieve_mu_lpf, primes_upto, mertens

RMAX = 300
N = RMAX * RMAX  # need [0, R^2-1]
mu, lpf = sieve_mu_lpf(N)
M = mertens(mu)
cof = np.arange(N + 1, dtype=np.int64) // lpf

# --- sanity on the sieve itself -------------------------------------------
assert list(mu[:13]) == [0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0], list(mu[:13])
assert list(lpf[:13]) == [1, 1, 2, 3, 2, 5, 3, 7, 2, 3, 5, 11, 3], list(lpf[:13])
print("sieve spot checks OK")

pr = primes_upto(RMAX)

rows = []
for R in range(2, RMAX + 1):
    X = R * R - 1
    m = np.arange(X + 1)
    lp = lpf[: X + 1]
    c = cof[: X + 1]
    w = mu[: X + 1].astype(np.int64)

    smooth = int(w[lp <= R].sum())
    born = int(w[(lp <= R) & (lp <= c)].sum())
    pos = int(w[(lp <= R) & (c < lp)].sum())

    # transport, prime-first
    q = pr[pr > R] if R < RMAX else np.zeros(0, dtype=np.int64)
    qq = primes_upto(X)
    qq = qq[qq > R]
    transport = int(M[X // qq].sum())

    MX = int(M[X])
    matched = born - transport

    # closed form for the positive-orientation side
    qs = pr[pr <= R]
    closed = -int(M[qs - 1].sum())

    rows.append((R, MX, smooth, born, pos, transport, matched, closed))

    # identities
    assert smooth == born + pos, (R, smooth, born, pos)
    assert MX == smooth - transport, (R, MX, smooth, transport)
    assert MX == pos + matched, (R, MX, pos, matched)
    assert pos == closed, (R, pos, closed)

print("all identities verified for R = 2..%d:" % RMAX)
print("  smooth      = bornSmooth + positiveSmooth")
print("  M(R^2-1)    = smooth - transport")
print("  M(R^2-1)    = positiveSmooth + matched")
print("  positiveSmooth R = - sum_{q<=R prime} M(q-1)   <-- closed form CONFIRMED")
print()
print("%6s %10s %12s %12s %12s %12s" % ("R", "M(X)", "bornSmooth", "positive", "transport", "matched"))
for (R, MX, smooth, born, pos, transport, matched, closed) in rows:
    if R in (10, 20, 50, 100, 150, 200, 250, 300):
        print("%6d %10d %12d %12d %12d %12d" % (R, MX, born, pos, transport, matched))
