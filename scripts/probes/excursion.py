"""Question 1: does every primorial block carry a genuine two-sided interior excursion?

Block k is (W_k, W_{k+1}] with W_{k+1} = W_k * p_k (primorials).  Inside it the
wheel residual is exactly the Mertens increment (PrimorialWheelPrefixIdentity):

    R_k(x) = sum_{W_k < n <= x} mu(n) = M(x) - M(W_k),     R_k(W_k) = 0.

    U_k = max_{W_k<=x<=W_{k+1}} R_k(x)      L_k = min ...

Two-sided excursion:      L_k < 0 < U_k
Interior overshoot:       U_k > max(0, R_k(W_{k+1}))  and  L_k < min(0, R_k(W_{k+1}))

The second says the path does not merely drift between endpoint levels: it
overshoots above BOTH endpoint levels and below BOTH, i.e. a genuine hump and
valley.  Also records where the extrema sit and which square block holds them.
"""
import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import numpy as np
from mobius import sieve_mu

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
W = [1]
for p in PRIMES:
    W.append(W[-1] * p)

NMAX = int(float(sys.argv[1])) if len(sys.argv) > 1 else 223092870
W = [w for w in W if w <= NMAX]
print("primorials available: %s" % W, flush=True)

mu = sieve_mu(NMAX)
CH = 2 * 10 ** 7
print()
hdr = ("%3s %12s %12s %10s %10s %10s %10s %8s %8s"
       % ("k", "W_k", "W_k+1", "R(end)", "U_k", "L_k", "over+", "over-", "peak1st"))
print(hdr); print("-" * len(hdr))

Mrun = int(np.sum(mu[:W[0] + 1]))     # M(W_0)=M(1)=1
rows = []
for k in range(len(W) - 1):
    lo, hi = W[k], W[k + 1]
    if hi > NMAX:
        break
    base = Mrun                        # M(W_k)
    U, L = 0, 0                        # R_k(W_k) = 0
    argU, argL = lo, lo
    cur = base
    x = lo + 1
    while x <= hi:
        end = min(x + CH - 1, hi)
        c = np.cumsum(mu[x:end + 1], dtype=np.int64) + cur
        i = int(np.argmax(c)); j = int(np.argmin(c))
        if int(c[i]) - base > U:
            U, argU = int(c[i]) - base, x + i
        if int(c[j]) - base < L:
            L, argL = int(c[j]) - base, x + j
        cur = int(c[-1])
        x = end + 1
    Rend = cur - base
    Mrun = cur
    op = U - max(0, Rend)
    om = min(0, Rend) - L
    rows.append((k, lo, hi, base, Rend, U, L, op, om, argU, argL))
    print("%3d %12d %12d %10d %10d %10d %10d %8d %8s"
          % (k, lo, hi, Rend, U, L, op, om, "yes" if argU < argL else "no"))

print()
print("=== the two claims ===")
two_sided = all(r[6] < 0 < r[5] for r in rows)
overshoot = all(r[7] > 0 and r[8] > 0 for r in rows)
print("  L_k < 0 < U_k for every computed block:            %s" % two_sided)
print("  interior overshoot (both) for every computed block: %s" % overshoot)
for r in rows:
    k, lo, hi, base, Rend, U, L, op, om, aU, aL = r
    print("   k=%d  two-sided=%-5s overshoot+=%-8d overshoot-=%-8d"
          % (k, str(L < 0 < U), op, om))

print()
print("=== M(x) sign at the extrema (the stronger visual claim) ===")
print("%3s %12s %12s %8s %8s %12s %12s" % ("k", "M at peak", "M at trough", "M>0?", "M<0?", "r+=isqrt", "r-=isqrt"))
for (k, lo, hi, base, Rend, U, L, op, om, aU, aL) in rows:
    Mp, Mt = base + U, base + L
    print("%3d %12d %12d %8s %8s %12d %12d"
          % (k, Mp, Mt, Mp > 0, Mt < 0, int(np.sqrt(aU)), int(np.sqrt(aL))))
