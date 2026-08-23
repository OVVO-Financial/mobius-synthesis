import Mathlib
import RHLean.Analysis.NearestSquareEndpointDomination
import RHLean.Analysis.PrimeWheelRecoveredMertensCriterion

/-!
# Prime-wheel square-endpoint domination

The canonical recovered square-root prime-wheel state is exactly the Mertens
prefix at every physical cutoff. This module combines that exact recovery with
the nearest-square endpoint theorem.

Consequently, inside the complete square block between `R^2 - 1` and
`(R+1)^2 - 1`, the recovered prime-wheel state at an arbitrary physical point
is controlled by the larger of its two adjacent recovered-wheel endpoint
states plus exactly one root-scale term `R`.

The squared form has only the explicit `2 * R^2` interior baseline. Finally,
critical energy control of the recovered wheel sampled only at completed-square
endpoints is proved equivalent to both the square-prefix Mertens criterion and
the full all-cutoff recovered-wheel criterion. Thus arbitrary physical cutoffs
carry no independent analytic obligation once the completed-square recovered
wheel states are controlled.

No quantitative RH-scale estimate is introduced here: the module proves the
lossless reduction to the endpoint-only recovered prime-wheel state.
-/

noncomputable section

namespace RHLean.Analysis

/-- At every completed-square crossing, the fully recovered prime-wheel state is
literally the square-prefix Mertens value. -/
theorem sqrtWheelRecoveredPrefix_squarePrefixEndpoint_cast_eq_squarePrefixMertens
    (n : ℕ) :
    ((sqrtWheelRecoveredPrefix (squarePrefixEndpoint n) : ℤ) : ℂ) =
      squarePrefixMertens n := by
  calc
    ((sqrtWheelRecoveredPrefix (squarePrefixEndpoint n) : ℤ) : ℂ) =
        mertensSummatory (squarePrefixEndpoint n) :=
      sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory (squarePrefixEndpoint n)
    _ = squarePrefixMertens n := rfl

/-- Pure prime-wheel form of nearest-square endpoint domination. Every recovered
wheel excursion inside a complete square block is within one root-scale term of
the larger adjacent completed-square recovered-wheel state. -/
theorem norm_sqrtWheelRecoveredPrefix_le_max_nearestSquareEndpoint_add_root
    (R x : ℕ)
    (hR : 1 ≤ R)
    (hlower : squarePrefixEndpoint (R - 1) ≤ x)
    (hupper : x ≤ squarePrefixEndpoint R) :
    ‖((sqrtWheelRecoveredPrefix x : ℤ) : ℂ)‖ ≤
      max
          ‖((sqrtWheelRecoveredPrefix (squarePrefixEndpoint (R - 1)) : ℤ) : ℂ)‖
          ‖((sqrtWheelRecoveredPrefix (squarePrefixEndpoint R) : ℤ) : ℂ)‖ +
        (R : ℝ) := by
  have h :=
    norm_mertensSummatory_le_max_nearestSquareEndpoint_add_root
      R x hR hlower hupper
  simpa only [
    ← sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory x,
    ← sqrtWheelRecoveredPrefix_squarePrefixEndpoint_cast_eq_squarePrefixMertens
      (R - 1),
    ← sqrtWheelRecoveredPrefix_squarePrefixEndpoint_cast_eq_squarePrefixMertens R]
    using h

/-- Squared prime-wheel nearest-endpoint domination. The only extra interior
energy beyond the adjacent completed-square states is the explicit `2 * R^2`
root-scale baseline. -/
theorem norm_sqrtWheelRecoveredPrefix_sq_le_two_max_nearestSquareEndpoint_sq_add_root_sq
    (R x : ℕ)
    (hR : 1 ≤ R)
    (hlower : squarePrefixEndpoint (R - 1) ≤ x)
    (hupper : x ≤ squarePrefixEndpoint R) :
    ‖((sqrtWheelRecoveredPrefix x : ℤ) : ℂ)‖ ^ 2 ≤
      2 * max
          (‖((sqrtWheelRecoveredPrefix
              (squarePrefixEndpoint (R - 1)) : ℤ) : ℂ)‖ ^ 2)
          (‖((sqrtWheelRecoveredPrefix
              (squarePrefixEndpoint R) : ℤ) : ℂ)‖ ^ 2) +
        2 * (R : ℝ) ^ 2 := by
  have h :=
    norm_mertensSummatory_sq_le_two_max_nearestSquareEndpoint_sq_add_root_sq
      R x hR hlower hupper
  simpa only [
    ← sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory x,
    ← sqrtWheelRecoveredPrefix_squarePrefixEndpoint_cast_eq_squarePrefixMertens
      (R - 1),
    ← sqrtWheelRecoveredPrefix_squarePrefixEndpoint_cast_eq_squarePrefixMertens R]
    using h

/-- Critical energy control of the fully recovered prime-wheel state only at
completed-square crossings. -/
def SqrtWheelSquareEndpointEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ,
        ‖((sqrtWheelRecoveredPrefix (squarePrefixEndpoint n) : ℤ) : ℂ)‖ ^ 2 ≤
          C * Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε)

/-- Endpoint-only recovered-wheel energy is exactly the existing square-prefix
Mertens energy criterion. -/
theorem sqrtWheelSquareEndpointEnergyBounded_iff_squarePrefixEnergyBounded :
    SqrtWheelSquareEndpointEnergyBoundedStatement ↔
      SquarePrefixEnergyBoundedStatement := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro n
    simpa only [
      sqrtWheelRecoveredPrefix_squarePrefixEndpoint_cast_eq_squarePrefixMertens]
      using hbound n
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro n
    simpa only [
      sqrtWheelRecoveredPrefix_squarePrefixEndpoint_cast_eq_squarePrefixMertens]
      using hbound n

/-- Sampling the fully recovered wheel only at completed squares loses no
critical-energy information relative to the global Mertens criterion. -/
theorem sqrtWheelSquareEndpointEnergyBounded_iff_mertensEnergyBounded :
    SqrtWheelSquareEndpointEnergyBoundedStatement ↔
      MertensEnergyBoundedStatement := by
  exact sqrtWheelSquareEndpointEnergyBounded_iff_squarePrefixEnergyBounded.trans
    mertensEnergyBounded_iff_squarePrefixEnergyBounded.symm

/-- Endpoint-only recovered-wheel energy is equivalent to controlling the same
fully recombined wheel state at every physical cutoff. -/
theorem sqrtWheelSquareEndpointEnergyBounded_iff_sqrtWheelRecoveredEnergyBounded :
    SqrtWheelSquareEndpointEnergyBoundedStatement ↔
      SqrtWheelRecoveredEnergyBoundedStatement := by
  exact sqrtWheelSquareEndpointEnergyBounded_iff_mertensEnergyBounded.trans
    sqrtWheelRecoveredEnergyBounded_iff_mertensEnergyBounded.symm

/-- Endpoint-only recovered-wheel energy therefore closes the existing RH
route, with arbitrary physical cutoffs supplied deterministically by the
nearest-square endpoint theorem. -/
theorem riemannHypothesis_of_sqrtWheelSquareEndpointEnergy
    (h : SqrtWheelSquareEndpointEnergyBoundedStatement) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_sqrtWheelRecoveredEnergy
  exact
    sqrtWheelSquareEndpointEnergyBounded_iff_sqrtWheelRecoveredEnergyBounded.mp h

end RHLean.Analysis
