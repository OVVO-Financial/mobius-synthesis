import RHLean.Proof.LowWheelFrozenSquareResidualQ2Reindex

/-!
# Global signed q^2 telescope of the frozen square residual

An earlier layer identifies every fixed-owner square-residual fibre exactly with the
negative Möbius mass of its interval-prime `q^2` daughter window.  This file
performs the remaining finite Fubini step over the represented source scales.

No absolute value is taken.  In particular the source-scale Möbius factor
`mu(A)` remains outside the daughter sum; this is essential because the primes
below the old source pivot are encoded by that outer factor and must not be
silently replaced by an ordinary Mertens daughter at fixed `A`.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Exact q^2 daughter expansion of the square-residual charge at one source
scale.  The leading minus sign is the stripped owner prime. -/
def lowWheelFrozenSecondContactSquareResidualQ2MassAtScale
    (R A : ℕ) : ℂ :=
  -(canonicalMoebiusWeight A *
    ∑ q ∈ lowWheelFrozenSourceSquareResidualOwners
        (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A),
      ∑ d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
          (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q,
        canonicalMoebiusWeight d)

/-- **Fixed-source signed SR-q^2 identity.**  The complete residual at scale
`A` is exactly its owner-partitioned q^2 daughter telescope. -/
theorem lowWheelFrozenSecondContactSquareResidualMassAtScale_eq_q2
    (R A : ℕ) :
    lowWheelFrozenSecondContactSquareResidualMassAtScale R A =
      lowWheelFrozenSecondContactSquareResidualQ2MassAtScale R A := by
  let p := canonicalLargestPrimeFactor A
  let B := squareRootEndpoint R / A
  let O := lowWheelFrozenSourceSquareResidualOwners p B
  unfold lowWheelFrozenSecondContactSquareResidualMassAtScale
    lowWheelFrozenSecondContactSquareResidualQ2MassAtScale
  change canonicalMoebiusWeight A *
      (∑ c ∈ lowWheelFrozenSourceSquareResidual p B,
        canonicalMoebiusWeight c) =
    -(canonicalMoebiusWeight A *
      ∑ q ∈ O,
        ∑ d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow p B q,
          canonicalMoebiusWeight d)
  rw [lowWheelFrozenSourceSquareResidual_sum_eq_sum_ownerFibers
    p B canonicalMoebiusWeight]
  change canonicalMoebiusWeight A *
      (∑ q ∈ O,
        ∑ c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q,
          canonicalMoebiusWeight c) = _
  have howners :
      (∑ q ∈ O,
        ∑ c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q,
          canonicalMoebiusWeight c) =
      ∑ q ∈ O,
        -(∑ d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow p B q,
          canonicalMoebiusWeight d) := by
    apply Finset.sum_congr rfl
    intro q hqO
    rcases Finset.mem_image.mp hqO with ⟨c, hcResidual, howner⟩
    have hcFiber : c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q :=
      mem_lowWheelFrozenSourceSquareResidualOwnerFiber.mpr
        ⟨hcResidual, howner⟩
    rcases lowWheelFrozenSourceSquareResidualOwnerFiber_data hcFiber with
      ⟨hqPrime, hpq, _hdSq, _hdRough, _hdLt, _hfactor, _hq2, _hweight⟩
    exact lowWheelFrozenSourceSquareResidualOwnerFiber_mass_eq_neg_daughterMass
      hqPrime hpq
  rw [howners, Finset.sum_neg_distrib]
  ring

/-- Global q^2 form of the frozen square residual, with the source-scale sum
still signed and intact. -/
def lowWheelFrozenSecondContactSquareResidualQ2Mass (R : ℕ) : ℂ :=
  ∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
    lowWheelFrozenSecondContactSquareResidualQ2MassAtScale R A

/-- **Global signed SR-q^2 telescope.**  After the historical high-transport
rough-prefix cancellation, the entire remaining square residual is already an
exact sum of strict q^2 daughters.  The theorem performs only finite reindexing;
there is no norm, frame estimate, or selected-prime/Möbius substitution. -/
theorem lowWheelFrozenSecondContactSquareResidualMass_eq_q2Telescope
    (R : ℕ) :
    lowWheelFrozenSecondContactSquareResidualMass R =
      lowWheelFrozenSecondContactSquareResidualQ2Mass R := by
  unfold lowWheelFrozenSecondContactSquareResidualMass
    lowWheelFrozenSecondContactSquareResidualQ2Mass
  apply Finset.sum_congr rfl
  intro A hA
  exact lowWheelFrozenSecondContactSquareResidualMassAtScale_eq_q2 R A

end RHLean.Proof
