import RHLean.Proof.DyadicSurvivorMertensInvariant
import RHLean.Proof.MatchedFarSurvivorBridge
import RHLean.Analysis.SquareRootPostCrossingTail
import RHLean.Analysis.SquareRootCanonicalRoughCovariance

/-!
# Dyadic survivor splice into the matched square-root channel

The x=210 autopsy and its formal survivor invariant identify the complete
post-root transport with the negative physical dyadic survivor mass.

This file removes the abstract transport symbol from the matched
born-smooth/transport channel.  Every statement here is an exact rewrite:
no norm, triangle inequality, or new estimate is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- **Physical form of the matched channel.**

The matched born-smooth/transport object is literally born-smooth plus the
signed physical dyadic survivor population. -/
theorem squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_dyadicSurvivor
    (R : ℕ) (hR : 0 < R) :
    squareRootMatchedBornSmoothTransport R =
      squareRootBornSmoothMass R + squareRootDyadicSurvivorMass R := by
  unfold squareRootMatchedBornSmoothTransport
  rw [squareRootDyadicSurvivorMass_eq_neg_transport R hR]
  ring

/-- Above the production threshold, the whole physical dyadic survivor
population is exactly the far-upper survivor minus the seven-coordinate
near-prime strip. -/
theorem squareRootDyadicSurvivorMass_eq_farSurvivor_sub_near
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootDyadicSurvivorMass R =
      survivorSixteenFarUpperPrimeMass (R - 1) -
        squareRootNearPrimeTransport R := by
  rw [squareRootDyadicSurvivorMass_eq_neg_transport R (by omega),
    squareRootTransportPrimeFirst_eq_near_sub_farSurvivor R hR]
  ring

/-- The matched channel in completely physical survivor coordinates. -/
theorem squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_farDyadicSurvivor_sub_near
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootMatchedBornSmoothTransport R =
      squareRootBornSmoothMass R +
        survivorSixteenFarUpperPrimeMass (R - 1) -
          squareRootNearPrimeTransport R := by
  rw [squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_dyadicSurvivor
      R (by omega),
    squareRootDyadicSurvivorMass_eq_farSurvivor_sub_near R hR]
  ring

/-- RH-scale boundedness statement written only in physical born-smooth and
dyadic-survivor coordinates. -/
def SquareRootBornDyadicSurvivorBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
        ‖squareRootBornSmoothMass R + squareRootDyadicSurvivorMass R‖ ^ 2 ≤
          C * Real.rpow (R : ℝ) (2 + ε)

/-- The physical survivor statement is exactly equivalent to the existing
matched-transport statement.  Thus replacing transport by its survivor
autopsy loses no cancellation and changes no analytic strength. -/
theorem squareRootBornDyadicSurvivorBoundedStatement_iff_matchedTransport
    :
    SquareRootBornDyadicSurvivorBoundedStatement ↔
      SquareRootMatchedTransportBoundedStatement := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R hR
    rw [squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_dyadicSurvivor
      R (by omega)]
    exact hbound R hR
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R hR
    rw [← squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_dyadicSurvivor
      R (by omega)]
    exact hbound R hR

/-- The only difference between the physical matched channel and the
born-smooth plus far-survivor core is the already-bounded seven-coordinate
near-prime strip. -/
theorem norm_bornSmooth_add_dyadicSurvivor_sub_bornSmooth_add_farSurvivor_le
    (R : ℕ) (hR : 56 ≤ R) :
    ‖(squareRootBornSmoothMass R + squareRootDyadicSurvivorMass R) -
        (squareRootBornSmoothMass R +
          survivorSixteenFarUpperPrimeMass (R - 1))‖ ≤
      7 * (R : ℝ) := by
  rw [squareRootDyadicSurvivorMass_eq_farSurvivor_sub_near R hR]
  have hnear := norm_squareRootNearPrimeTransport_le R hR
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnear


/-- The physical survivor mass from the x=210 autopsy is exactly the
canonical source-signed high side of the same top dyadic wall. -/
theorem squareRootDyadicSurvivorMass_eq_dyadicCanonicalHighSourceMass
    (R : ℕ) (hR : 0 < R) :
    squareRootDyadicSurvivorMass R =
      dyadicCanonicalHighSourceMass R := by
  rw [squareRootDyadicSurvivorMass_eq_neg_transport R hR]
  rw [← squareRootTransportCofactorFirst_eq_primeFirst R]
  rw [squareRootTransportCofactorFirst_eq_neg_dyadicCanonicalHighSourceMass R]
  ring

/-- The matched channel is therefore one signed packet on a common physical
dyadic carrier: born-smooth plus canonical high-source mass. -/
theorem squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_dyadicHigh
    (R : ℕ) (hR : 0 < R) :
    squareRootMatchedBornSmoothTransport R =
      squareRootBornSmoothMass R + dyadicCanonicalHighSourceMass R := by
  rw [squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_dyadicSurvivor
      R hR,
    squareRootDyadicSurvivorMass_eq_dyadicCanonicalHighSourceMass R hR]

/-- Adding the positive-orientation smooth side recovers the exact square-prefix
Mertens value.  This is the main-DAG version of the research joint-packet
identity, expressed without importing any research module. -/
theorem squareRootPositiveSmooth_add_bornSmooth_add_dyadicHigh_eq_squarePrefixMertens
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootPositiveSmoothMass R +
        squareRootBornSmoothMass R +
          dyadicCanonicalHighSourceMass R =
      RHLean.Analysis.squarePrefixMertens (R - 1) := by
  have hmatched :=
    squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_dyadicHigh
      R (by omega)
  have hsquare := squarePrefixMertens_eq_positiveSmooth_add_matched R hR
  rw [hmatched] at hsquare
  simpa [add_assoc] using hsquare.symm

/-- Equivalently, the hard matched channel is exactly the square-prefix value
minus the positive-orientation smooth packet. -/
theorem squareRootMatchedBornSmoothTransport_eq_squarePrefixMertens_sub_positiveSmooth
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootMatchedBornSmoothTransport R =
      RHLean.Analysis.squarePrefixMertens (R - 1) -
        squareRootPositiveSmoothMass R := by
  have h := squarePrefixMertens_eq_positiveSmooth_add_matched R hR
  linear_combination -h



/-- **Autopsy-to-covariance frontier.**

After replacing high transport by its exact physical dyadic survivors, the
whole signed top packet minus the admitted crossing packet is *exactly* the
canonical baseline minus one Möbius-weighted fresh-prime partner correlation.
All lower Mertens descendants have already telescoped before this identity is
read. -/
theorem squareRootPhysicalDyadicPacket_sub_partial_eq_baseline_sub_partnerMass
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    (squareRootPositiveSmoothMass R +
        squareRootBornSmoothMass R +
          dyadicCanonicalHighSourceMass R) -
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) =
      squareRootPostCrossingCanonicalBaseline R K j -
        ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          canonicalMoebiusWeight c *
            squareRootCanonicalRoughPrimePartnerCount R c := by
  rw [squareRootPositiveSmooth_add_bornSmooth_add_dyadicHigh_eq_squarePrefixMertens
      R (by omega)]
  have hclock :
      RHLean.Analysis.squarePrefixMertens (R - 1) =
        RHLean.Analysis.mertensSummatory (squareRootEndpoint R) := by
    unfold RHLean.Analysis.squarePrefixMertens
      RHLean.Analysis.squarePrefixEndpoint squareRootEndpoint
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R)]
  rw [hclock]
  rw [← postCrossingCoupledTail_eq_mertens_sub_partial R K j hR]
  rw [squareRootPostCrossingCoupledTail_eq_baseline_sub_correlation
      R K j hR hK hKR]
  rw [squareRootCanonicalRoughCorrelation_eq_weighted_primePartnerCount
      R (by omega)]

/-- Same frontier with the existing correlation object left named. -/
theorem squareRootPhysicalDyadicPacket_sub_partial_eq_baseline_sub_correlation
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    (squareRootPositiveSmoothMass R +
        squareRootBornSmoothMass R +
          dyadicCanonicalHighSourceMass R) -
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) =
      squareRootPostCrossingCanonicalBaseline R K j -
        squareRootCanonicalRoughCorrelation R := by
  rw [squareRootPositiveSmooth_add_bornSmooth_add_dyadicHigh_eq_squarePrefixMertens
      R (by omega)]
  have hclock :
      RHLean.Analysis.squarePrefixMertens (R - 1) =
        RHLean.Analysis.mertensSummatory (squareRootEndpoint R) := by
    unfold RHLean.Analysis.squarePrefixMertens
      RHLean.Analysis.squarePrefixEndpoint squareRootEndpoint
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R)]
  rw [hclock]
  rw [← postCrossingCoupledTail_eq_mertens_sub_partial R K j hR]
  exact squareRootPostCrossingCoupledTail_eq_baseline_sub_correlation
    R K j hR hK hKR


end RHLean.Proof
