"""Finite Abel reindexing of the divisor-band sum, with the boundary term explicit.

    S_D = sum_{d<=D} M(d)/(d(d+1))        (weighted band bulk)
    A_D = sum_{n<=D} mu(n)/n              (harmonic Moebius sum)

Finite summation, swapping the order over the telescoping 1/d - 1/(d+1):

    S_D = sum_{n<=D} mu(n) (1/n - 1/(D+1)) = A_D - M(D)/(D+1)

so the EXACT identity is   S_D = A_D - M(D)/(D+1).
The infinite calculation silently discards M(D)/(D+1); killing that boundary is
itself PNT-strength, and killing it at rate D^(-1/2+eps) is the Mertens bound.
"""
from fractions import Fraction
import sys, numpy as np

D_EXACT = 3000
DS = [10, 100, 1000, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7]
N = max(DS)

# mu by sieve
mu = np.ones(N + 1, dtype=np.int64); mu[0] = 0
rem = np.arange(N + 1, dtype=np.int64)
for p in range(2, int(N ** 0.5) + 1):
    if rem[p] == p:
        mu[p::p] = -mu[p::p]
        if p * p <= N:
            mu[p * p :: p * p] = 0
        pk = p
        while pk <= N:
            rem[pk::pk] //= p
            pk *= p
big = rem > 1
mu[big] = -mu[big]
M = np.cumsum(mu)

# --- exact rational check of the identity for EVERY D <= D_EXACT -------------
S = Fraction(0); A = Fraction(0); bad = 0
for d in range(1, D_EXACT + 1):
    S += Fraction(int(M[d]), d * (d + 1))
    A += Fraction(int(mu[d]), d)
    if S != A - Fraction(int(M[d]), d + 1):
        bad += 1
print("exact rational check, every D = 1..%d:  %s (%d mismatches)"
      % (D_EXACT, "IDENTITY HOLDS" if bad == 0 else "FAILED", bad))

# --- reproduce and extend the table -----------------------------------------
print()
print("%10s %8s %12s %12s %14s %14s"
      % ("D", "M(D)", "S_D", "A_D", "A_D - S_D", "M(D)/(D+1)"))
w = 1.0 / (np.arange(1, N + 1) * (np.arange(1, N + 1) + 1.0))
Sarr = np.cumsum(M[1:].astype(np.float64) * w)
Aarr = np.cumsum(mu[1:].astype(np.float64) / np.arange(1, N + 1))
for D in DS:
    s, a, m = Sarr[D - 1], Aarr[D - 1], float(M[D])
    print("%10d %8d %12.6f %12.6f %14.9f %14.9f"
          % (D, int(M[D]), s, a, a - s, m / (D + 1)))

print()
print("=== decay rates: does the boundary dominate? ===")
print("%10s %14s %14s %14s" % ("D", "|A_D|", "|S_D|", "|M(D)|/(D+1)"))
for D in DS:
    print("%10d %14.3e %14.3e %14.3e"
          % (D, abs(Aarr[D - 1]), abs(Sarr[D - 1]), abs(float(M[D])) / (D + 1)))
print()
print("At the RH rate A_D = O(D^(-1/2+eps)) the boundary M(D)/(D+1) must also be")
print("O(D^(-1/2+eps)), i.e. M(D) = O(D^(1/2+eps)) -- the original Mertens bound.")
