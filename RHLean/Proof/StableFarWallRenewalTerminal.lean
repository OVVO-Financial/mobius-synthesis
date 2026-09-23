import RHLean.Proof.StableFarWallRenewalDescent

/-!
# Terminal branches of the stable-far renewal

A renewal branch terminates at low cofactor one exactly when the stripped
triple has shape `(q,(1,p))`.  At that point the arithmetic is completely
explicit: `q` is a low prime, `p` is the unchanged far prime, the original
single-insertion state fits below `X_R`, and its second `q` insertion crosses
`X_R`.

Thus the incoming terminal branches at a fixed far prime `p` are not mysterious
stable-wall multiplicity.  They are the finite prime interval cut out by

  q * p <= X_R < q^2 * p.

This is the exact hyperbolic/square-root transition that the reciprocal-layer
and prime-wheel coordinates see.  The theorem below exposes it directly on the
same crossing carrier used by the q^2 renewal, before any norm.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

/-- Prime owners whose unit-cofactor branch reaches the stable-far terminal at
`p`. -/
def lowWheelFarPrimeUnitCrossingOwners (R p : ℕ) : Finset ℕ :=
  (primesUpTo (R - 1)).filter fun q =>
    q * p ≤ squareRootEndpoint R ∧
      squareRootEndpoint R < q * q * p

@[simp] theorem mem_lowWheelFarPrimeUnitCrossingOwners
    {R p q : ℕ} :
    q ∈ lowWheelFarPrimeUnitCrossingOwners R p ↔
      q.Prime ∧ q ≤ R - 1 ∧
      q * p ≤ squareRootEndpoint R ∧
      squareRootEndpoint R < q * q * p := by
  simp [lowWheelFarPrimeUnitCrossingOwners, mem_primesUpTo, and_assoc]

/-- **Exact unit-terminal crossing classification.**

For a genuine far prime `p`, the stripped unit triple `(q,(1,p))` is a strict
q^2 crossing exactly for the prime owners satisfying the explicit hyperbolic
window `q*p <= X_R < q^2*p`. -/
theorem unitTriple_mem_q2Crossing_iff_owner
    {R p q : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hpFar : R + 8 ≤ p) :
    (q,(1,p)) ∈ lowWheelFarPrimeQ2CrossingTriples R ↔
      q ∈ lowWheelFarPrimeUnitCrossingOwners R p := by
  constructor
  · intro hcross
    have ht : (q,(1,p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
      (Finset.mem_filter.mp hcross).1
    have hdata := lowWheelFarPrimeLowCofactorTriple_data ht
    have hqR : q ≤ R - 1 := Nat.le_pred_of_lt hdata.2.1
    exact mem_lowWheelFarPrimeUnitCrossingOwners.mpr
      ⟨hdata.1, hqR,
        by simpa using hdata.2.2.2.2.2.2.2,
        by simpa using (Finset.mem_filter.mp hcross).2⟩
  · intro hq
    rcases mem_lowWheelFarPrimeUnitCrossingOwners.mp hq with
      ⟨hqPrime, hqRpred, hqp, hq2p⟩
    have hRpos : 0 < R := by omega
    have hqR : q < R := Nat.lt_of_le_pred hRpos hqRpred
    have htriple : (q,(1,p)) ∈ lowWheelFarPrimeLowCofactorTriples R := by
      apply lowWheelFarPrimeLowCofactorTriple_mem_of_data
        hqPrime hqR (by norm_num) hp hpFar squarefree_one
      · simpa [canonicalLargestPrimeFactor] using hqPrime.one_lt
      · simpa using hqp
    exact Finset.mem_filter.mpr ⟨htriple, by simpa using hq2p⟩

/-- A unit terminal branch returns to the literal stable-wall state `(empty,1,p)`.
The returned state no longer depends on the incoming owner `q`; this isolates
precisely where crossing-owner multiplicity accumulates. -/
theorem unitCrossing_stableState_eq
    {R p q : ℕ} (_hR : 2 ≤ R) (hp : p.Prime) (_hpFar : R + 8 ≤ p)
    (_hq : q ∈ lowWheelFarPrimeUnitCrossingOwners R p) :
    lowWheelFarPrimeCrossingStableState (q,p) =
      ((∅ : Finset ℕ), (1,p)) := by
  -- The returned state reads the far-prime coordinate only, and a prime carries
  -- canonical cofactor `1` while being its own largest prime factor.  That the
  -- crossing hypotheses are never consumed is exactly the content of this
  -- theorem: the returned state does not depend on the incoming owner `q`.  They
  -- are retained so the statement stays pinned to the unit-owner terminal
  -- carrier instead of becoming a bare arithmetic identity about primes.
  have htop : canonicalLargestPrimeFactor p = p := by
    simpa using canonicalLargestPrimeFactor_mul_prime_eq
      (c := 1) (q := p) (by decide) hp.one_lt hp
  have hcore : canonicalCofactor p = 1 := by
    simpa using canonicalCofactor_mul_prime_eq
      (c := 1) (q := p) (by decide) hp.one_lt hp
  simp [lowWheelFarPrimeCrossingStableState, htop, hcore]

/-- Every incoming unit-terminal owner contributes the same returned physical
weight `+1`.  Hence this terminal is exactly the place where multiplicity, not
Möbius sign variation, must be reconciled with the terminal product census. -/
theorem unitCrossing_stableState_weight_eq_one
    {R p q : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpFar : R + 8 ≤ p)
    (hq : q ∈ lowWheelFarPrimeUnitCrossingOwners R p) :
    lowWheelFullTaggedPhysicalWeight
        (lowWheelFarPrimeCrossingStableState (q,p)) = 1 := by
  rw [unitCrossing_stableState_eq hR hp hpFar hq]
  simp [lowWheelFullTaggedPhysicalWeight, booleanCubeSign,
    canonicalMoebiusWeight]

end RHLean.Proof
