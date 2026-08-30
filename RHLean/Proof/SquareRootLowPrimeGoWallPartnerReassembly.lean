import Mathlib
import RHLean.Proof.SquareRootLowPrimeFirstOwnerWallRecurrence
import RHLean.Proof.SquareRootLowPrimeGoWallStripTelescope
import RHLean.Proof.SquareRootLowPrimeGoSecondContactSources

/-!
# Reassemble the literal first-owner wall with its Go partner

The first-owner wall identity of `SquareRootLowPrimeFirstOwnerWallRecurrence`
contains the moving old-prime column

`F_{q^-}(X_R / q)`

and a common fixed column at `X_R / p`.  The Go strip recurrence later opens one
moving-column term as

`F_{q^-}(X_R / q) = B_q + S_q`,

where

`B_q = F_q(X_R / q)`

is the moving boundary state and

`S_q = F_{q^-}(X_R / q^2)`

is the square-dilated residual.

This file keeps those two pieces together over the *literal old-prime wall
schedule* `q <= K`.  The partner ledger is defined directly from the already
existing boundary states and the fixed column.  It is not defined as wall mass
minus residual mass.

This distinction matters: the generic fourth-power Go owner schedule used by
later finite diagnostics is a different schedule.  No theorem here identifies
that generic diagnostic with the literal first-owner wall residual.

No norm, asymptotic estimate, PNT input, lower-envelope hypothesis, or new
carrier is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- The literal square-residual mass obtained by opening the moving column on
exactly the old-prime wall schedule `q <= K`. -/
def squareRootLowPrimeLiteralWallSquareResidualMass
    (R K : ℕ) : ℤ :=
  ∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
    squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R)

/-- The independently constructed partner ledger on the same literal wall.
It consists of the moving boundary states left beside the square residual,
minus the common fixed column already present in the wall identity. -/
def squareRootLowPrimeLiteralWallPartnerLedgerMass
    (R K p : ℕ) : ℤ :=
  (∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
      squareRootLowPrimeGoWallBoundaryState q (squareRootEndpoint R)) -
    ∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
      frozenPrimeUniverseMass (primesUpTo (q - 1))
        (squareRootEndpoint R / p)

/-- Signed mass of the literal arithmetic wall-pair carrier. -/
def squareRootLowPrimeLiteralWallPairMass
    (R K p : ℕ) : ℤ :=
  ∑ z ∈ squareRootLowPrimeWallPairCarrierCofactorFirst R K p, μ z.1

/-- Source orientation of the actual first-owner wall fallout.  This is the
negative of the parent-pair Möbius mass because every inherited wall seat has
weight `-mu(c)`. -/
def squareRootLowPrimeLiteralWallFalloutMass
    (R K p : ℕ) : ℤ :=
  -squareRootLowPrimeLiteralWallPairMass R K p

/-- Square-residual contribution in the same fallout orientation. -/
def squareRootLowPrimeLiteralWallResidualFalloutMass
    (R K : ℕ) : ℤ :=
  -squareRootLowPrimeLiteralWallSquareResidualMass R K

/-- Partner ledger in the same fallout orientation. -/
def squareRootLowPrimeLiteralWallPartnerFalloutMass
    (R K p : ℕ) : ℤ :=
  -squareRootLowPrimeLiteralWallPartnerLedgerMass R K p

/-- One moving-column term is exactly its admitted boundary state plus its
square-dilated predecessor residual.  This is just the fresh-prime Euler
recurrence at the cutoff `X_R / q`. -/
theorem squareRootLowPrimeWallMovingTerm_eq_boundaryState_add_squareResidual
    {R q : ℕ} (hq : q.Prime) :
    frozenPrimeUniverseMass (primesUpTo (q - 1))
        (squareRootEndpoint R / q) =
      squareRootLowPrimeGoWallBoundaryState q (squareRootEndpoint R) +
        squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R) := by
  have hstep :=
    frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor
      q (squareRootEndpoint R / q) hq
  unfold predecessorPrimeMass at hstep
  unfold squareRootLowPrimeGoWallBoundaryState
    squareRootLowPrimeGoWallSquareResidual
  omega

/-- The complete moving column on the literal wall schedule is the sum of its
boundary ledger and square-residual ledger. -/
theorem squareRootLowPrimeWallUpperColumn_eq_boundaryStates_add_squareResiduals
    (R K : ℕ) :
    (∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
      frozenPrimeUniverseMass (primesUpTo (q - 1))
        (squareRootEndpoint R / q)) =
      (∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
        squareRootLowPrimeGoWallBoundaryState q (squareRootEndpoint R)) +
      squareRootLowPrimeLiteralWallSquareResidualMass R K := by
  unfold squareRootLowPrimeLiteralWallSquareResidualMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  exact squareRootLowPrimeWallMovingTerm_eq_boundaryState_add_squareResidual
    (mem_squareRootLowPrimeWallOldPrimeSet.mp hq).1

/-- **Literal wall reassembly.**  The wall pair mass is the square residual plus
its independently constructed partner ledger.  The partner is built from the
existing `B_q` boundary states and fixed column; it is not introduced as a
difference of the two sides of this equality. -/
theorem squareRootLowPrimeLiteralWallPairMass_eq_residual_add_partner
    {R K p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hKp : K < p) (hpR : p < R) :
    squareRootLowPrimeLiteralWallPairMass R K p =
      squareRootLowPrimeLiteralWallSquareResidualMass R K +
        squareRootLowPrimeLiteralWallPartnerLedgerMass R K p := by
  unfold squareRootLowPrimeLiteralWallPairMass
  rw [squareRootLowPrimeWallPairCarrierCofactorFirst_eq_oldPrimeFirst
      hR hp hKp hpR,
    squareRootLowPrimeWallPairCarrierOldPrimeFirst_moebiusSum]
  have hwindow :
      (∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
        squareRootLowPrimeOldPrimeWallWindowMass R p q) =
        (∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / q)) -
          ∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
            frozenPrimeUniverseMass (primesUpTo (q - 1))
              (squareRootEndpoint R / p) := by
    calc
      (∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
          squareRootLowPrimeOldPrimeWallWindowMass R p q) =
        ∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
          (frozenPrimeUniverseMass (primesUpTo (q - 1))
              (squareRootEndpoint R / q) -
            frozenPrimeUniverseMass (primesUpTo (q - 1))
              (squareRootEndpoint R / p)) := by
        apply Finset.sum_congr rfl
        intro q hq
        have hqData := mem_squareRootLowPrimeWallOldPrimeSet.mp hq
        exact squareRootLowPrimeOldPrimeWallWindowMass_eq_frozenDifference
          hqData.1 (by omega)
      _ =
        (∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / q)) -
          ∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
            frozenPrimeUniverseMass (primesUpTo (q - 1))
              (squareRootEndpoint R / p) := by
        rw [Finset.sum_sub_distrib]
  rw [hwindow,
    squareRootLowPrimeWallUpperColumn_eq_boundaryStates_add_squareResiduals]
  unfold squareRootLowPrimeLiteralWallPartnerLedgerMass
  ring

/-- The same theorem in the actual first-owner fallout orientation. -/
theorem squareRootLowPrimeLiteralWallFalloutMass_eq_residual_add_partner
    {R K p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hKp : K < p) (hpR : p < R) :
    squareRootLowPrimeLiteralWallFalloutMass R K p =
      squareRootLowPrimeLiteralWallResidualFalloutMass R K +
        squareRootLowPrimeLiteralWallPartnerFalloutMass R K p := by
  unfold squareRootLowPrimeLiteralWallFalloutMass
    squareRootLowPrimeLiteralWallResidualFalloutMass
    squareRootLowPrimeLiteralWallPartnerFalloutMass
  rw [squareRootLowPrimeLiteralWallPairMass_eq_residual_add_partner
    hR hp hKp hpR]
  ring

/-- The fixed-column part of the partner can be restricted to exactly the
unfinished old-prime owners; completed predecessor cubes contribute zero. -/
theorem squareRootLowPrimeLiteralWallPartnerLedgerMass_eq_unfinishedFixedColumn
    (R K p : ℕ) :
    squareRootLowPrimeLiteralWallPartnerLedgerMass R K p =
      (∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
        squareRootLowPrimeGoWallBoundaryState q (squareRootEndpoint R)) -
      ∑ q ∈ squareRootLowPrimeUnfinishedWallOldPrimeSet R K p,
        frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / p) := by
  unfold squareRootLowPrimeLiteralWallPartnerLedgerMass
  rw [squareRootLowPrimeWallFixedColumn_eq_unfinished]

/-- The independently defined boundary ledger also exposes the already-proved
moving-column endpoint.  This is a theorem about the boundary ledger, not
its definition. -/
theorem squareRootLowPrimeLiteralWallPartnerLedgerMass_eq_endpoint_sub_residual_sub_fixed
    {R K p : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeLiteralWallPartnerLedgerMass R K p =
      (1 - frozenPrimeUniverseMass (primesUpTo K) (squareRootEndpoint R)) -
        squareRootLowPrimeLiteralWallSquareResidualMass R K -
        ∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / p) := by
  have hupper := squareRootLowPrimeWallUpperColumn_telescope (R := R) (K := K) hR
  have hsplit :=
    squareRootLowPrimeWallUpperColumn_eq_boundaryStates_add_squareResiduals R K
  unfold squareRootLowPrimeLiteralWallPartnerLedgerMass
  rw [hsplit] at hupper
  omega

/-! ## Literal wall schedule as the Go second-contact schedule -/

/-- The literal first-owner wall residual is definitionally the Go square
residual total on the *same* old-prime owner schedule.  This is the exact
schedule bridge; no generic fourth-power owner schedule is substituted. -/
theorem squareRootLowPrimeLiteralWallSquareResidualMass_eq_goWallSquareResidualTotal
    (R K : ℕ) :
    squareRootLowPrimeLiteralWallSquareResidualMass R K =
      squareRootLowPrimeGoWallSquareResidualTotal
        (squareRootLowPrimeWallOldPrimeSet K) (squareRootEndpoint R) := by
  rfl

/-- **Literal wall-to-Go source reindexing.**  On the exact wall schedule, the
square residual recombines before any norm into one disjoint population of
actual arithmetic second-contact children.  Their owner multiplicity is stored
in the child itself through its canonical largest prime. -/
theorem squareRootLowPrimeLiteralWallSquareResidual_cast_eq_neg_goSecondContactSourceMass
    (R K : ℕ) :
    (((squareRootLowPrimeLiteralWallSquareResidualMass R K : ℤ) : ℂ)) =
      -∑ m ∈ squareRootLowPrimeGoSecondContactSources
          (squareRootLowPrimeWallOldPrimeSet K) (squareRootEndpoint R),
        canonicalMoebiusWeight m := by
  rw [squareRootLowPrimeLiteralWallSquareResidualMass_eq_goWallSquareResidualTotal]
  apply squareRootLowPrimeGoWallSquareResidualTotal_cast_eq_neg_sourceMass
  intro q hq
  exact (mem_squareRootLowPrimeWallOldPrimeSet.mp hq).1

/-- Every arithmetic source in the literal wall Go population recovers a unique
old-prime owner from its canonical largest prime, and records its second contact
below the square endpoint. -/
theorem squareRootLowPrimeLiteralWallGoSecondContactSource_owner
    {R K m : ℕ}
    (hm : m ∈ squareRootLowPrimeGoSecondContactSources
      (squareRootLowPrimeWallOldPrimeSet K) (squareRootEndpoint R)) :
    canonicalLargestPrimeFactor m ∈ squareRootLowPrimeWallOldPrimeSet K ∧
      canonicalLargestPrimeFactor m * m ≤ squareRootEndpoint R := by
  apply squareRootLowPrimeGoSecondContactSource_owner_exists
    (Q := squareRootLowPrimeWallOldPrimeSet K)
    (X := squareRootEndpoint R)
  · intro q hq
    exact (mem_squareRootLowPrimeWallOldPrimeSet.mp hq).1
  · exact hm

end RHLean.Proof
