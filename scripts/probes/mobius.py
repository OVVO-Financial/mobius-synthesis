"""Exact-integer harness for the mobius-synthesis square-root/survivor objects.

Mirrors the Lean definitions:
  mertensSummatory x              = sum_{m=0}^{x} mu(m)
  squarePrefixEndpoint n          = (n+1)^2 - 1
  squareRootEndpoint R            = R^2 - 1
  cumulativeSquarePrefixSet N     = range((N+1)^2)          = [0, (N+1)^2-1]
  canonicalLargestPrimeFactor m   = P+(m), with P+(0)=P+(1)=1
  canonicalCofactor m             = m // P+(m)
  canonicalMoebiusWeight m        = mu(m)

  squareRootSmoothMass (R-1)      = sum_{m<=R^2-1, P+(m)<=R} mu(m)
  squareRootBornSmoothMass R      = sum_{m<=R^2-1, P+(m)<=R, P+(m)<=c_m} mu(m)
  squareRootPositiveSmoothMass R  = sum_{m<=R^2-1, P+(m)<=R, c_m<P+(m)} mu(m)
  squareRootTransportPrimeFirst R = sum_{R<q<=R^2-1, q prime} M(floor((R^2-1)/q))
  matched R                       = bornSmooth R - transport R
"""

import numpy as np


def sieve_mu_lpf(N):
    """Return (mu, lpf) arrays over [0, N].

    Uses the small-prime / large-remainder factorization so only primes up to
    sqrt(N) are iterated.  After dividing out every prime power p^a with
    p <= sqrt(N), the remainder is either 1 or a single prime > sqrt(N).
    """
    rem = np.arange(N + 1, dtype=np.int64)
    mu = np.ones(N + 1, dtype=np.int8)
    maxp = np.ones(N + 1, dtype=np.int64)

    S = int(N ** 0.5)
    while (S + 1) * (S + 1) <= N:
        S += 1
    is_comp = np.zeros(S + 1, dtype=bool)
    for p in range(2, S + 1):
        if is_comp[p]:
            continue
        is_comp[p * p :: p] = True
        mu[p::p] = -mu[p::p]
        if p * p <= N:
            mu[p * p :: p * p] = 0
        maxp[p::p] = p
        pk = p
        while pk <= N:
            rem[pk::pk] //= p
            pk *= p

    big = rem > 1
    mu[big] = -mu[big]
    lpf = np.where(big, rem, maxp)
    if N >= 0:
        mu[0] = 0
        lpf[0] = 1
    if N >= 1:
        lpf[1] = 1
    return mu, lpf


def sieve_mu(N):
    """mu over [0, N] only (cheaper: no largest-prime-factor array)."""
    rem = np.arange(N + 1, dtype=np.int32 if N < 2 ** 31 else np.int64)
    mu = np.ones(N + 1, dtype=np.int8)
    S = int(N ** 0.5)
    while (S + 1) * (S + 1) <= N:
        S += 1
    is_comp = np.zeros(S + 1, dtype=bool)
    for p in range(2, S + 1):
        if is_comp[p]:
            continue
        is_comp[p * p :: p] = True
        mu[p::p] = -mu[p::p]
        if p * p <= N:
            mu[p * p :: p * p] = 0
        pk = p
        while pk <= N:
            rem[pk::pk] //= p
            pk *= p
    big = rem > 1
    mu[big] = -mu[big]
    mu[0] = 0
    return mu


def primes_upto(N):
    if N < 2:
        return np.zeros(0, dtype=np.int64)
    sieve = np.ones(N + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(N ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    return np.flatnonzero(sieve).astype(np.int64)


def mertens(mu):
    """M[x] = sum_{m<=x} mu(m), as int64."""
    return np.cumsum(mu, dtype=np.int64)
