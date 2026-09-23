import RHLean.Analysis.DyadicTransportCompression
import RHLean.Proof.PrimeCombReciprocalBandCancellation
import RHLean.Analysis.SquareRootMatchedTransport

/-!
# Dyadic survivor fibres are exactly the negative upper-prime Mertens transform

The finite x=210 / x=317 experiments pair an odd high-prime state `c*p`
with its doubled child `2*c*p` whenever both lie below the endpoint.
After those exact Möbius cancellations, the surviving cofactors are precisely
the odd dyadic boundary

`W/(2p) < c <= W/p`.

This file identifies that physical survivor boundary with the repository's
already-formalized upper-prime Mertens transform.  No estimate occurs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Signed mass left on one post-root prime fibre after exact dyadic
`c*p <-> 2*c*p` cancellation. -/
def dyadicLargePrimeSurvivorMass (W p : ℕ) : ℂ :=
  ∑ c ∈ dyadicCofactorBoundary (W / p),
    canonicalMoebiusWeight (c * p)

/-- **Fibrewise survivor invariant.**

For every prime `p > sqrt W`, the exact dyadic survivor mass is the negative
Mertens prefix at the reciprocal cutoff.  This is the formal version of the
invariant observed in the x=210, x=317, and production-square diagnostics. -/
theorem dyadicLargePrimeSurvivorMass_eq_neg_mertens
    {W p : ℕ} (hp : p.Prime) (hpRoot : Nat.sqrt W < p) :
    dyadicLargePrimeSurvivorMass W p =
      -RHLean.Analysis.mertensSummatory (W / p) := by
  unfold dyadicLargePrimeSurvivorMass
  calc
    (∑ c ∈ dyadicCofactorBoundary (W / p),
        canonicalMoebiusWeight (c * p)) =
      ∑ c ∈ dyadicCofactorBoundary (W / p),
        -canonicalMoebiusWeight c := by
      apply Finset.sum_congr rfl
      intro c hc
      have hcData := mem_dyadicCofactorBoundary.mp hc
      have hcTop : c ≤ W / p := hcData.2.1
      have hcpW : c * p ≤ W :=
        (Nat.le_div_iff_mul_le hp.pos).1 hcTop
      exact canonicalMoebiusWeight_mul_largePrime_eq_neg_cofactor
        hp hpRoot (by omega) hcpW
    _ = -dyadicCofactorBoundaryMass (W / p) := by
      unfold dyadicCofactorBoundaryMass
      simp
    _ = -cofactorMobiusPrefixMass (W / p) := by
      rw [cofactorMobiusPrefixMass_eq_dyadicBoundaryMass]
    _ = -RHLean.Analysis.mertensSummatory (W / p) := by
      rw [cofactorMobiusPrefixMass_eq_mertensSummatory]

/-- The dyadic survivor fibre is exactly the already-defined complete
large-prime family mass.  Thus the x=210 physical pairing is not a new
analytic object; it is a concrete realization of the existing post-root
prime family. -/
theorem dyadicLargePrimeSurvivorMass_eq_primeCombLargePrimeFamilyMass
    {W p : ℕ} (hp : p.Prime) (hpRoot : Nat.sqrt W < p) :
    dyadicLargePrimeSurvivorMass W p =
      primeCombLargePrimeFamilyMass W p := by
  rw [dyadicLargePrimeSurvivorMass_eq_neg_mertens hp hpRoot,
    primeCombLargePrimeFamilyMass_eq_neg_mertens hp hpRoot]

/-- Aggregate physical survivor mass over every prime above the square-root
frontier. -/
def dyadicPostRootSurvivorMass (W : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc (Nat.sqrt W) W,
    if p.Prime then dyadicLargePrimeSurvivorMass W p else 0

/-- **Arbitrary-endpoint global survivor invariant.**

The complete physical dyadic survivor population is exactly the negative
Mertens-weighted upper-prime tail already used by the prime-comb coordinate. -/
theorem dyadicPostRootSurvivorMass_eq_neg_mertensPrimeTail
    (W : ℕ) :
    dyadicPostRootSurvivorMass W =
      -primeSieveMertensPrimeTail (Nat.sqrt W) W := by
  unfold dyadicPostRootSurvivorMass primeSieveMertensPrimeTail
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hpRange
  have hpRoot := (Finset.mem_Ioc.mp hpRange).1
  by_cases hpPrime : p.Prime
  · simp [hpPrime, dyadicLargePrimeSurvivorMass_eq_neg_mertens hpPrime hpRoot]
  · simp [hpPrime]

/-- Square-endpoint aggregate on the repository's native high-prime
schedule `R < p <= R^2-1`. -/
def squareRootDyadicSurvivorMass (R : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc R (squareRootEndpoint R),
    if p.Prime then
      dyadicLargePrimeSurvivorMass (squareRootEndpoint R) p
    else
      0

/-- **Physical survivor / transport identification.**

At the production endpoint `X_R = R^2 - 1`, the exact dyadic survivor mass is
the negative of the repository's original high-prime transport.  This is the
formal bridge supplied by the x=210 family of examples. -/
theorem squareRootDyadicSurvivorMass_eq_neg_transport
    (R : ℕ) (hR : 0 < R) :
    squareRootDyadicSurvivorMass R =
      -squareRootTransportPrimeFirst R := by
  unfold squareRootDyadicSurvivorMass squareRootTransportPrimeFirst
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hpRange
  have hpR : R < p := (Finset.mem_Ioc.mp hpRange).1
  have hpRoot : Nat.sqrt (squareRootEndpoint R) < p := by
    have hsq : Nat.sqrt (squareRootEndpoint R) < R := by
      apply (Nat.sqrt_lt').2
      unfold squareRootEndpoint
      have hpos : 0 < R ^ 2 := by positivity
      omega
    exact hsq.trans hpR
  by_cases hpPrime : p.Prime
  · simp only [hpPrime, if_true]
    rw [dyadicLargePrimeSurvivorMass_eq_neg_mertens hpPrime hpRoot,
      primeDilatedLowCofactorMass_eq_mertensSummatory
        R p hR hpR hpPrime.pos]
  · simp [hpPrime]

end RHLean.Proof
