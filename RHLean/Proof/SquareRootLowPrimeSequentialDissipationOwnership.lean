import Mathlib
import RHLean.Proof.SquareRootLowPrimeSequentialDissipation

/-!
# Global ownership and energy convention for low-prime dissipation

`SquareRootLowPrimeSequentialDissipation` writes every actual fresh-prime step
as

`Delta_p = -D_p + F_p`,

where `D_p` and `F_p` are nonnegative natural response masses and the support of
`F_p` is assigned by the cofactor's canonical largest prime.  This module
records the corresponding running-imbalance convention and the exact quadratic
energy identity used by the numerical scan.

It also sums the already-proved local decomposition over a prime interval.  The
sum does not create new local errors: it contains one natural deletion mass and
the one globally assigned bad mass from the local theorem.  The latter is
realized below as one sum over the literal disjoint union of its canonically
owned cofactor fibres.  No absolute value, analytic estimate, covariance
normalization, or endpoint reconstruction is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Actual fresh primes in an arithmetic interval. -/
def squareRootLowPrimeFreshPrimeSet (L U : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter Nat.Prime

/-- Total deletion mass over a prime interval. -/
def squareRootLowPrimeGlobalDeletionMass
    (R K j L U : ℕ) : ℕ :=
  ∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
    squareRootLowPrimeDeletionMass R K j p

/-- The literal union of all positive-orientation cofactors in the selected
fresh-prime interval.  The union is disjoint by the unique largest-prime owner
proved below. -/
def squareRootLowPrimeOwnedBadCofactors
    (R L U : ℕ) : Finset ℕ :=
  (squareRootLowPrimeFreshPrimeSet L U).biUnion
    (squareRootLowPrimeBadCofactors R)

/-- The bad cofactor fibres over actual fresh primes are pairwise disjoint. -/
theorem squareRootLowPrimeBadCofactors_pairwiseDisjoint
    (R L U : ℕ) :
    Set.PairwiseDisjoint (↑(squareRootLowPrimeFreshPrimeSet L U))
      (squareRootLowPrimeBadCofactors R) := by
  intro p _hp q _hq hpq
  exact squareRootLowPrimeBadCofactors_disjoint hpq

/-- **Literal global ownership.**  The global positive obstruction is one sum
on one disjoint support, not a collection of independently charged local
errors.  Every cofactor occurs in the union at its unique largest-prime owner. -/
theorem squareRootLowPrimeGlobalBadMass_eq_ownedCofactorSum
    (R K j L U : ℕ) :
    squareRootLowPrimeGlobalBadMass R K j L U =
      ∑ c ∈ squareRootLowPrimeOwnedBadCofactors R L U,
        squareRootLowPrimeCombinedFreshResponse R K j c := by
  unfold squareRootLowPrimeGlobalBadMass squareRootLowPrimeBadMass
    squareRootLowPrimeOwnedBadCofactors
  change
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
      ∑ c ∈ squareRootLowPrimeBadCofactors R p,
        squareRootLowPrimeCombinedFreshResponse R K j c) =
      ∑ c ∈ (squareRootLowPrimeFreshPrimeSet L U).biUnion
        (squareRootLowPrimeBadCofactors R),
          squareRootLowPrimeCombinedFreshResponse R K j c
  rw [← Finset.sum_biUnion
    (squareRootLowPrimeBadCofactors_pairwiseDisjoint R L U)]

/-- The accepted sign convention: the response increment is exactly
`T(p-1)-T(p)` for the running imbalance `T = 1-S`. -/
theorem squareRootLowPrimeRunningImbalance_step_eq_freshIncrement
    (R K j p : ℕ) (hp : p.Prime) :
    squareRootLowPrimeRunningImbalance R K j (p - 1) -
        squareRootLowPrimeRunningImbalance R K j p =
      squareRootLowPrimeFreshIncrement R K j p := by
  unfold squareRootLowPrimeRunningImbalance
  calc
    (1 - squareRootBornPostTailRunningLowPrimeResponse R K j (p - 1)) -
        (1 - squareRootBornPostTailRunningLowPrimeResponse R K j p) =
      squareRootBornPostTailRunningLowPrimeResponse R K j p -
        squareRootBornPostTailRunningLowPrimeResponse R K j (p - 1) := by
          ring
    _ = squareRootLowPrimeFreshIncrement R K j p :=
      squareRootBornPostTailRunningLowPrimeResponse_step_eq_lowPrimeFreshIncrement
        R K j p hp

/-- Exact quadratic energy identity in the running-state convention. -/
theorem squareRootLowPrimeRunningEnergy_step
    (R K j p : ℕ) (hp : p.Prime) :
    squareRootLowPrimeRunningImbalance R K j (p - 1) ^ 2 -
        squareRootLowPrimeRunningImbalance R K j p ^ 2 =
      2 * squareRootLowPrimeRunningImbalance R K j (p - 1) *
          squareRootLowPrimeFreshIncrement R K j p -
        squareRootLowPrimeFreshIncrement R K j p ^ 2 := by
  have hstep :=
    squareRootLowPrimeRunningImbalance_step_eq_freshIncrement R K j p hp
  calc
    squareRootLowPrimeRunningImbalance R K j (p - 1) ^ 2 -
        squareRootLowPrimeRunningImbalance R K j p ^ 2 =
      2 * squareRootLowPrimeRunningImbalance R K j (p - 1) *
          (squareRootLowPrimeRunningImbalance R K j (p - 1) -
            squareRootLowPrimeRunningImbalance R K j p) -
        (squareRootLowPrimeRunningImbalance R K j (p - 1) -
          squareRootLowPrimeRunningImbalance R K j p) ^ 2 := by
            ring
    _ = 2 * squareRootLowPrimeRunningImbalance R K j (p - 1) *
          squareRootLowPrimeFreshIncrement R K j p -
        squareRootLowPrimeFreshIncrement R K j p ^ 2 := by
          rw [hstep]

/-- The full one-sided decomposition in the running-imbalance convention. -/
theorem squareRootLowPrimeSequentialDissipation_runningImbalance
    {R K j p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpR : p < R) :
    (squareRootLowPrimeRunningImbalance R K j (p - 1) -
        squareRootLowPrimeRunningImbalance R K j p =
      -((squareRootLowPrimeDeletionMass R K j p : ℕ) : ℂ) +
        ((squareRootLowPrimeBadMass R K j p : ℕ) : ℂ)) ∧
      (0 : ℤ) ≤ (squareRootLowPrimeDeletionMass R K j p : ℤ) ∧
      (0 : ℤ) ≤ (squareRootLowPrimeBadMass R K j p : ℤ) := by
  simpa [squareRootLowPrimeRunningImbalance] using
    (squareRootLowPrimeSequentialDissipation
      (R := R) (K := K) (j := j) (p := p) hR hp hpR)

/-- **Global one-sided decomposition.**  Summing fresh-prime steps produces one
natural deletion mass and the globally assigned natural bad mass. -/
theorem squareRootLowPrimeFreshIncrement_sum_eq_neg_globalDeletion_add_badMass
    {R K j L U : ℕ} (hR : 2 ≤ R) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
        squareRootLowPrimeFreshIncrement R K j p) =
      -((squareRootLowPrimeGlobalDeletionMass R K j L U : ℕ) : ℂ) +
        ((squareRootLowPrimeGlobalBadMass R K j L U : ℕ) : ℂ) := by
  unfold squareRootLowPrimeGlobalDeletionMass
    squareRootLowPrimeGlobalBadMass
    squareRootLowPrimeFreshPrimeSet
  calc
    (∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
        squareRootLowPrimeFreshIncrement R K j p) =
      ∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
        (-((squareRootLowPrimeDeletionMass R K j p : ℕ) : ℂ) +
          ((squareRootLowPrimeBadMass R K j p : ℕ) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro p _hp
            exact squareRootLowPrimeFreshIncrement_eq_neg_deletionMass_add_badMass hR
    _ = (∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
          -((squareRootLowPrimeDeletionMass R K j p : ℕ) : ℂ)) +
        ∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
          ((squareRootLowPrimeBadMass R K j p : ℕ) : ℂ) := by
            rw [Finset.sum_add_distrib]
    _ = -(∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
          ((squareRootLowPrimeDeletionMass R K j p : ℕ) : ℂ)) +
        ∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
          ((squareRootLowPrimeBadMass R K j p : ℕ) : ℂ) := by
            rw [Finset.sum_neg_distrib]
    _ = -((∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
          squareRootLowPrimeDeletionMass R K j p : ℕ) : ℂ) +
        ((∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
          squareRootLowPrimeBadMass R K j p : ℕ) : ℂ) := by
            push_cast
            rfl

/-- The global decomposition with the obstruction exposed on its one literal
owned support. -/
theorem squareRootLowPrimeFreshIncrement_sum_eq_neg_globalDeletion_add_ownedBadMass
    {R K j L U : ℕ} (hR : 2 ≤ R) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
        squareRootLowPrimeFreshIncrement R K j p) =
      -((squareRootLowPrimeGlobalDeletionMass R K j L U : ℕ) : ℂ) +
        ((∑ c ∈ squareRootLowPrimeOwnedBadCofactors R L U,
          squareRootLowPrimeCombinedFreshResponse R K j c : ℕ) : ℂ) := by
  rw [squareRootLowPrimeFreshIncrement_sum_eq_neg_globalDeletion_add_badMass hR,
    squareRootLowPrimeGlobalBadMass_eq_ownedCofactorSum]

/-- The same global decomposition expressed as accepted running-imbalance
steps. -/
theorem squareRootLowPrimeRunningImbalance_step_sum_eq_neg_globalDeletion_add_badMass
    {R K j L U : ℕ} (hR : 2 ≤ R) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
        (squareRootLowPrimeRunningImbalance R K j (p - 1) -
          squareRootLowPrimeRunningImbalance R K j p)) =
      -((squareRootLowPrimeGlobalDeletionMass R K j L U : ℕ) : ℂ) +
        ((squareRootLowPrimeGlobalBadMass R K j L U : ℕ) : ℂ) := by
  calc
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
        (squareRootLowPrimeRunningImbalance R K j (p - 1) -
          squareRootLowPrimeRunningImbalance R K j p)) =
      ∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
        squareRootLowPrimeFreshIncrement R K j p := by
          apply Finset.sum_congr rfl
          intro p hp
          exact squareRootLowPrimeRunningImbalance_step_eq_freshIncrement
            R K j p (Finset.mem_filter.mp hp).2
    _ = -((squareRootLowPrimeGlobalDeletionMass R K j L U : ℕ) : ℂ) +
        ((squareRootLowPrimeGlobalBadMass R K j L U : ℕ) : ℂ) :=
      squareRootLowPrimeFreshIncrement_sum_eq_neg_globalDeletion_add_badMass hR

/-- Running-imbalance version with the bad term exposed on its one literal
owned support. -/
theorem squareRootLowPrimeRunningImbalance_step_sum_eq_neg_globalDeletion_add_ownedBadMass
    {R K j L U : ℕ} (hR : 2 ≤ R) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
        (squareRootLowPrimeRunningImbalance R K j (p - 1) -
          squareRootLowPrimeRunningImbalance R K j p)) =
      -((squareRootLowPrimeGlobalDeletionMass R K j L U : ℕ) : ℂ) +
        ((∑ c ∈ squareRootLowPrimeOwnedBadCofactors R L U,
          squareRootLowPrimeCombinedFreshResponse R K j c : ℕ) : ℂ) := by
  rw [squareRootLowPrimeRunningImbalance_step_sum_eq_neg_globalDeletion_add_badMass hR,
    squareRootLowPrimeGlobalBadMass_eq_ownedCofactorSum]

end RHLean.Proof
