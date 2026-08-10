"""Does the added-prime lever give a power, or only the Euler density factor?

alpha_q = C_q / E_q  is the dilation regression coefficient of one Buchstab step
    Z(q-1,y) = Z(q,y) - Z(q,y/q).
Define      theta_q = log(1/alpha_q)/log q.

  theta_q -> 1/2  : alpha_q ~ q^(-1/2), sum alpha_q ~ Q^(1/2)  -> a POWER saving
  theta_q -> 1    : alpha_q ~ 1/q,      sum alpha_q ~ log log Q -> only 1/log^2
                    i.e. the pure Euler DENSITY factor, no arithmetic gain.

The test that matters is Y-dependence: if theta_q at FIXED q drifts upward as Y
grows, the lever is density-only asymptotically and the (p-1)/(p+1) ceiling is
the whole story.
"""
import sys, time
import numpy as np

QS = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 37, 47, 59, 73, 97, 149, 199, 293]
YS = [int(float(v)) for v in (sys.argv[1:] or ["5e4", "1e5", "2e5", "4e5"])]

def descent(Y):
    spf = np.zeros(Y + 1, dtype=np.int64)
    for p in range(2, Y + 1):
        if spf[p] == 0:
            spf[p::p] = np.where(spf[p::p] == 0, p, spf[p::p])
    primes = np.flatnonzero(spf == np.arange(Y + 1)).astype(np.int64)
    primes = primes[primes >= 2]
    Z = np.ones(Y + 1, dtype=np.float64); Z[0] = 0.0
    ar = np.arange(Y + 1)
    out = {}
    for q in primes[::-1]:
        Zd = Z[ar // q]
        E = float(np.mean(Z[1:] ** 2))
        C = float(np.mean(Z[1:] * Zd[1:]))
        Z = Z - Zd
        if int(q) in QS and E > 0 and C > 0:
            a = C / E
            out[int(q)] = (a, -np.log(a) / np.log(q))
    return out

res = {}
for Y in YS:
    t0 = time.time()
    res[Y] = descent(Y)
    print("Y = %-8d descent %.0fs" % (Y, time.time() - t0), flush=True)

print()
print("=== theta_q = log(1/alpha_q)/log q ===")
print("1/2 => power saving.   1 => pure Euler density, no arithmetic gain.")
hdr = "%6s" + " %10s" * len(YS) + " %10s"
print(hdr % tuple(["q"] + ["Y=%.0e" % Y for Y in YS] + ["drift"]))
print("-" * (7 + 11 * (len(YS) + 1)))
for q in QS:
    vals = [res[Y].get(q, (None, None))[1] for Y in YS]
    if any(v is None for v in vals):
        continue
    drift = vals[-1] - vals[0]
    print(("%6d" + " %10.4f" * len(YS) + " %+10.4f") % tuple([q] + vals + [drift]))

print()
print("=== alpha_q against the two candidate laws ===")
Y = YS[-1]
print("%6s %12s %12s %12s" % ("q", "alpha_q", "q^-1/2", "1/q"))
for q in QS:
    if q in res[Y]:
        a = res[Y][q][0]
        print("%6d %12.5f %12.5f %12.5f" % (q, a, q ** -0.5, 1.0 / q))

print()
print("=== accumulated budget  sum_q alpha_q  (needs ~log Y for a power) ===")
for Y in YS:
    s = sum(v[0] for v in res[Y].values())
    print("  Y=%.0e  sum over sampled q = %8.4f   log Y = %6.3f   loglog Y = %5.3f"
          % (Y, s, np.log(Y), np.log(np.log(Y))))
