"""The added-prime lever: where does the cancellation come from?

Repository theorem (RHLean/Arithmetic/SignedBuchstabRecursion.lean):

    Z(b,y) = sum_{1<=m<=y, all prime factors of m > b} mu(m)
    Z(q-1, y) = Z(q, y) - Z(q, floor(y/q))          for every prime q

So "adding a prime" is the operator  (T_q f)(y) = f(y) - f(y/q).  Starting from
Z(Y,.) = 1 and applying T_q for every prime q <= Y in DECREASING order lands on
Z(1,.) = M(.).  That is the single lever.

Energy budget of one step.  With E(b) = mean_y Z(b,y)^2 over y <= Y:

    E(q-1) = E(q) + D_q - 2 C_q
    D_q = mean_y Z(q, y/q)^2          <- pure density / dilation term
    C_q = mean_y Z(q,y) Z(q, y/q)     <- AUTOCORRELATION of the rough Moebius
                                         sum with its own q-dilate

D_q is the "no arithmetic gain" part already known to give only the density
factor.  Every bit of extra cancellation must therefore live in C_q.  This
script measures C_q, its correlation coefficient rho_q = C_q/sqrt(E(q) D_q),
and compares the realised energy against the zero-correlation (rho=0) model.
"""

import sys, time
import numpy as np

Y = int(float(sys.argv[1])) if len(sys.argv) > 1 else 200000

# least prime factor and mu
spf = np.zeros(Y + 1, dtype=np.int64)
for p in range(2, Y + 1):
    if spf[p] == 0:
        spf[p::p] = np.where(spf[p::p] == 0, p, spf[p::p])
mu = np.ones(Y + 1, dtype=np.int64)
mu[0] = 0
rem = np.arange(Y + 1, dtype=np.int64)
for p in range(2, int(Y ** 0.5) + 1):
    if spf[p] == p:
        mu[p::p] = -mu[p::p]
        if p * p <= Y:
            mu[p * p :: p * p] = 0
        pk = p
        while pk <= Y:
            rem[pk::pk] //= p
            pk *= p
big = rem > 1
mu[big] = -mu[big]

primes = np.flatnonzero(spf == np.arange(Y + 1)).astype(np.int64)
primes = primes[primes >= 2]
print("Y = %d, pi(Y) = %d" % (Y, len(primes)), flush=True)

# Z(b,.) for b = Y: only m = 1 survives
Z = np.ones(Y + 1, dtype=np.float64)
Z[0] = 0.0

# sanity: build Z(1,.) = M(.) by the recursion, primes in DECREASING order
t0 = time.time()
rows = []
for q in primes[::-1]:
    idx = np.arange(Y + 1) // q
    Zd = Z[idx]
    E = float(np.mean(Z[1:] ** 2))
    D = float(np.mean(Zd[1:] ** 2))
    C = float(np.mean(Z[1:] * Zd[1:]))
    Z = Z - Zd
    rows.append((int(q), E, D, C, float(np.mean(Z[1:] ** 2))))
print("descent over all primes: %.1fs" % (time.time() - t0), flush=True)

M = np.cumsum(mu).astype(np.float64)
err = float(np.abs(Z[1:] - M[1:]).max())
print("CHECK  Z(1,.) == M(.) after the full descent:  max|diff| = %g  %s"
      % (err, "OK" if err < 1e-6 else "FAIL"))

arr = np.array(rows)          # q, E_before, D, C, E_after
q, Eb, D, C, Ea = arr.T
rho = C / np.sqrt(np.maximum(Eb * D, 1e-300))

print()
print("=== per-prime energy budget,  E_after = E_before + D - 2C ===")
print("small primes are added LAST (they are the contraction phase)")
hdr = "%9s %14s %14s %14s %8s %10s %10s" % (
    "q added", "E_before", "D (density)", "C (corr)", "rho_q", "E_aft/E_bef", "rho=0 ratio")
print(hdr); print("-" * len(hdr))
for i in list(range(len(q) - 1, max(len(q) - 26, -1), -1)):
    print("%9d %14.4g %14.4g %14.4g %8.4f %10.5f %10.5f"
          % (q[i], Eb[i], D[i], C[i], rho[i], Ea[i] / Eb[i], (Eb[i] + D[i]) / Eb[i]))

print()
print("=== is the correlation systematically positive? ===")
for lab, m in (("all primes", np.ones(len(q), bool)),
               ("q <= 100", q <= 100),
               ("q <= sqrt(Y)", q <= Y ** 0.5),
               ("q > sqrt(Y)", q > Y ** 0.5)):
    if m.sum():
        print("  %-14s n=%-7d median rho = %+.4f   frac rho>0 = %.3f"
              % (lab, m.sum(), np.median(rho[m]), float((rho[m] > 0).mean())))

print()
print("=== how much of the total contraction is due to correlation? ===")
peak = int(np.argmax(Eb))
print("  energy peaks when adding q = %d   (E = %.4g)" % (q[peak], Eb[peak]))
print("  final energy  mean M(y)^2 = %.4g" % Ea[-1])
print("  contraction from peak to final: factor %.4g" % (Eb[peak] / Ea[-1]))
tail = slice(peak, None)
realised = np.log(Ea[tail] / Eb[tail]).sum()
nocorr = np.log((Eb[tail] + D[tail]) / Eb[tail]).sum()
print("  sum log(E_after/E_before) over the contraction phase: realised %+.3f"
      % realised)
print("  same sum with the correlation term deleted (rho=0):            %+.3f"
      % nocorr)
print("  => correlation supplies a factor exp(%.3f) = %.4g of contraction"
      % (realised - nocorr, np.exp(realised - nocorr)))
