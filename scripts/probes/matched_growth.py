"""Direct growth measurement of the matched object

    squareRootMatchedBornSmoothTransport R = bornSmooth R - transport R

using the verified identities

    matched(R)     = M(R^2-1) - positiveSmooth(R)
    positiveSmooth = -sum_{q<=R prime} M(q-1)
    transport(R)   = sum_{R<q<=R^2-1 prime} M((R^2-1)//q)
    bornSmooth(R)  = matched(R) + transport(R)

RH scale at X = R^2-1 is X^(1/2+eps) = R^(1+eps).
"""

import sys, time, pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import numpy as np
from mobius import sieve_mu, primes_upto, mertens

N = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 8
RMAX = int(N ** 0.5)

t0 = time.time()
mu = sieve_mu(N)
print("mu sieve to %.2e: %.1fs" % (N, time.time() - t0), flush=True)
t0 = time.time()
M = np.cumsum(mu, dtype=np.int64)
del mu
print("M cumsum: %.1fs  (|M| max = %d)" % (time.time() - t0, np.abs(M).max()), flush=True)
t0 = time.time()
pr = primes_upto(N)
print("primes to %.2e: %d, %.1fs" % (N, len(pr), time.time() - t0), flush=True)

print()
print("RH target scale at X=R^2-1 is R^1.  Measuring |matched| / R.")
print()
hdr = ("%7s %12s %12s %12s %12s %12s %9s %9s"
       % ("R", "M(X)", "posSmooth", "transport", "bornSmooth", "matched",
          "|mtc|/R", "|mtc|/R^1.5"))
print(hdr)
print("-" * len(hdr))

rows = []
Rs = [r for r in [100, 200, 400, 700, 1000, 1500, 2000, 3000, 4000,
                  5000, 6000, 7000, 8000, 9000, 10000] if r <= RMAX]
for R in Rs:
    X = R * R - 1
    i = np.searchsorted(pr, R, side="right")
    posSmooth = -int(M[pr[:i] - 1].sum())
    qq = pr[i:]
    qq = qq[qq <= X]
    transport = int(M[X // qq].sum())
    MX = int(M[X])
    matched = MX - posSmooth
    born = matched + transport
    rows.append((R, MX, posSmooth, transport, born, matched))
    print("%7d %12d %12d %12d %12d %12d %9.3f %9.5f"
          % (R, MX, posSmooth, transport, born, matched,
             abs(matched) / R, abs(matched) / R ** 1.5))

# growth exponents between consecutive sampled R
print()
print("local log-log growth exponents (consecutive samples):")
print("%16s %10s %10s %10s %10s" % ("R range", "|matched|", "|posSm|", "|born|", "|transp|"))
for a, b in zip(rows, rows[1:]):
    lr = np.log(b[0] / a[0])
    def ex(x, y):
        if x == 0 or y == 0:
            return float("nan")
        return np.log(abs(y) / abs(x)) / lr
    print("%16s %10.3f %10.3f %10.3f %10.3f"
          % ("%d->%d" % (a[0], b[0]), ex(a[5], b[5]), ex(a[2], b[2]),
             ex(a[4], b[4]), ex(a[3], b[3])))

# summation-by-parts cross-check:
#   sum_{q<=R} M(q-1) = pi(R)*M(R-1) - sum_{c<R} mu(c)*pi(c)
print()
print("summation-by-parts identity check  posSmooth = -[pi(R)M(R-1) - sum_{c<R} mu(c)pi(c)]:")
muarr = np.diff(np.concatenate(([0], M)))  # mu recovered from M
picount = np.cumsum(np.isin(np.arange(N + 1), pr))
for R in Rs[:6]:
    i = np.searchsorted(pr, R, side="right")
    lhs = -int(M[pr[:i] - 1].sum())
    piR = int(picount[R])
    rhs = -(piR * int(M[R - 1]) - int((muarr[:R] * picount[:R]).sum()))
    print("   R=%-6d  posSmooth=%-12d  parts=%-12d  %s"
          % (R, lhs, rhs, "OK" if lhs == rhs else "MISMATCH"))
