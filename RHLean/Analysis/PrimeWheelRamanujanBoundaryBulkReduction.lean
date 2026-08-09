import Mathlib
import RHLean.Analysis.RamanujanDivisorBoundaryBulk
import RHLean.Analysis.PrimeWheelRamanujanBoundaryReduction

/-!
# Prime-wheel Ramanujan boundary reduction with bulk retained

The existing prime-wheel reduction uses `q > 1` to cancel the common Ramanujan
bulk separately on every shifted interval.  Full-conductor recombination needs
the conductor-one contribution to remain visible instead.  This file pushes the
all-conductor boundary-plus-bulk identity through both the reduced-conductor
window and the smooth packet.

No estimate is used.  The raw, smooth, and conductor-one terms remain signed
finite arithmetic expressions.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Signed total mass of the squarefree smooth divisor sites.  This is the
coefficient multiplying the common conductor-one Ramanujan bulk. -/
def primeWheelSmoothBulkMass (W : PrimeWheelFiniteSystem) : ℤ :=
  ∑ a ∈ primeWheelSmoothDivisorSites W, -(μ a)

/-- The normalized reduced-conductor window is a divisor-boundary packet plus
an explicit conductor-one interval bulk, uniformly for every positive divisor
conductor. -/
theorem primeWheelReducedConductorRamanujanWindow_eq_divisorBoundary_add_bulk
    (W : PrimeWheelFiniteSystem) {x q : ℕ}
    (hx : x ≤ W.upper) (hq : 0 < q) (hqmod : q ∣ W.modulus) :
    primeWheelReducedConductorRamanujanWindow W x q =
      ((W.modulus : ℂ)⁻¹) *
        ((((∑ d ∈ q.divisors,
          μ (q / d) * divisorIntervalBoundary d 0 W.lower x) +
          ((Finset.Ioc W.lower x).card : ℤ) *
            (if q = 1 then 1 else 0) : ℤ) : ℂ)) := by
  rw [primeWheelReducedConductorRamanujanWindow_eq_divisorInterval
    W hx hq hqmod]
  rw [ramanujanDivisorInterval_eq_boundary_add_bulk]

/-- Every shifted smooth Ramanujan interval carries the same conductor-one
bulk.  Factoring it after summing over smooth sites leaves one signed smooth
bulk mass and the existing divisor-boundary packet. -/
theorem primeWheelSmoothRamanujanPacket_eq_boundary_add_bulk
    (W : PrimeWheelFiniteSystem) (x q : ℕ) :
    primeWheelSmoothRamanujanPacket W x q =
      primeWheelSmoothBoundaryPacket W x q +
        primeWheelSmoothBulkMass W *
          ((Finset.Ioc W.lower x).card : ℤ) *
          (if q = 1 then 1 else 0) := by
  classical
  unfold primeWheelSmoothRamanujanPacket primeWheelSmoothBoundaryPacket
    primeWheelSmoothBulkMass
  simp_rw [ramanujanDivisorInterval_eq_boundary_add_bulk, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ a ∈ primeWheelSmoothDivisorSites W,
        -(μ a) *
          (((Finset.Ioc W.lower x).card : ℤ) *
            (if q = 1 then 1 else 0))) =
      (∑ a ∈ primeWheelSmoothDivisorSites W, -(μ a)) *
        (((Finset.Ioc W.lower x).card : ℤ) *
          (if q = 1 then 1 else 0)) := by
            rw [Finset.sum_mul]
    _ =
      (∑ a ∈ primeWheelSmoothDivisorSites W, -(μ a)) *
        ((Finset.Ioc W.lower x).card : ℤ) *
        (if q = 1 then 1 else 0) := by
          ring

/-- The smooth Fourier response inherits the same exact boundary-plus-bulk
formula after the standard normalization by the torus modulus. -/
theorem primeWheelSmoothConductorResponse_eq_boundaryPacket_add_bulk
    (W : PrimeWheelFiniteSystem) {x q : ℕ}
    (hx : x ≤ W.upper) (hq : 0 < q) (hqmod : q ∣ W.modulus) :
    primeWheelSmoothConductorResponse W x q =
      ((W.modulus : ℂ)⁻¹) *
        (((primeWheelSmoothBoundaryPacket W x q +
          primeWheelSmoothBulkMass W *
            ((Finset.Ioc W.lower x).card : ℤ) *
            (if q = 1 then 1 else 0) : ℤ) : ℂ)) := by
  rw [primeWheelSmoothConductorResponse_eq_ramanujanPacket
    W hx hq hqmod]
  rw [primeWheelSmoothRamanujanPacket_eq_boundary_add_bulk]

end RHLean.Analysis
