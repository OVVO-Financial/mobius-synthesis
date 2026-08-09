import Mathlib
import RHLean.Analysis.PrimeWheelFullConductorRecombination
import RHLean.Analysis.PrimeWheelRamanujanBoundaryBulkReduction

/-!
# Uniform explicit packet for every primorial conductor

The full-conductor realignment restored conductor one as a separate zero-frequency
atom.  The boundary-plus-bulk identities now let us remove that final case split:
every positive divisor conductor, including `q = 1`, is represented by the same
signed arithmetic packet.  The conductor-one bulk survives through the raw and
smooth terms and is therefore still available for cancellation after the full
sum is recombined.

No estimate or norm inequality is used here.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Fully explicit arithmetic packet for any divisor conductor.  The Kronecker
bulk terms are nonzero only at conductor one. -/
def primorialPeriodicRawExplicitAllConductorPacket
    (k x q : ℕ) : ℂ :=
  primorialRawConductorArithmeticCoefficient k q *
      (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹ *
        (((∑ d ∈ q.divisors,
            μ (q / d) *
              divisorIntervalBoundary d 0
                (primorialMinimalWheelSystem k).lower x) +
          ((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ) *
            (if q = 1 then 1 else 0) : ℤ) : ℂ)) -
    2 *
      (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹ *
        ((primeWheelSmoothBoundaryPacket
              (primorialMinimalWheelSystem k) x q +
            primeWheelSmoothBulkMass (primorialMinimalWheelSystem k) *
              ((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ) *
              (if q = 1 then 1 else 0) : ℤ) : ℂ))

/-- Every actual divisor conductor, including conductor one, is exactly the
same explicit arithmetic boundary-plus-bulk packet. -/
theorem primorialPeriodicRawJointConductorResponse_eq_explicitAllConductor
    (k x q : ℕ)
    (hqmem : q ∈ (primorialMinimalWheelSystem k).modulus.divisors)
    (hx : x ≤ (primorialMinimalWheelSystem k).upper) :
    primorialPeriodicRawJointConductorResponse k x q =
      primorialPeriodicRawExplicitAllConductorPacket k x q := by
  have hqmod : q ∣ (primorialMinimalWheelSystem k).modulus :=
    Nat.dvd_of_mem_divisors hqmem
  have hqpos : 0 < q := Nat.pos_of_mem_divisors hqmem
  have hconst :
      ∀ r : ZMod (primorialMinimalWheelSystem k).modulus,
        q = reducedAdditiveConductor r →
          primorialPeriodicRawSpectrum k r =
            primorialRawConductorArithmeticCoefficient k q := by
    intro r hr
    rw [primorialPeriodicRawSpectrum_eq_rawConductorArithmeticCoefficient k r]
    rw [← hr]
  rw [primorialPeriodicRawJointConductorResponse_eq_raw_sub_two_smooth]
  rw [primorialPeriodicRawConductorResponse_eq_constant_mul_ramanujanWindow
    k x q (primorialRawConductorArithmeticCoefficient k q) hconst]
  change
    primorialRawConductorArithmeticCoefficient k q *
        primeWheelReducedConductorRamanujanWindow
          (primorialMinimalWheelSystem k) x q -
      2 * primeWheelSmoothConductorResponse
        (primorialMinimalWheelSystem k) x q = _
  rw [primeWheelReducedConductorRamanujanWindow_eq_divisorBoundary_add_bulk
    (primorialMinimalWheelSystem k) hx hqpos hqmod]
  rw [primeWheelSmoothConductorResponse_eq_boundaryPacket_add_bulk
    (primorialMinimalWheelSystem k) hx hqpos hqmod]
  rfl

/-- Full-conductor recombination with no distinguished zero shell.  The actual
historical residual is one finite sum of uniform explicit arithmetic packets
over the divisors of the minimal torus modulus. -/
theorem primorialPeriodicRawResidual_eq_sum_explicitAllConductorPackets
    (k : ℕ) {x : ℕ}
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    ((((primorialWheelSystem k).residual x : ℤ) : ℂ)) =
      ∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
        primorialPeriodicRawExplicitAllConductorPacket k x q := by
  rw [primorialPeriodicRawResidual_eq_sum_divisorConductorResponses
    k hlower hupper]
  apply Finset.sum_congr rfl
  intro q hqmem
  have hx : x ≤ (primorialMinimalWheelSystem k).upper := by
    simpa using hupper
  exact primorialPeriodicRawJointConductorResponse_eq_explicitAllConductor
    k x q hqmem hx

end RHLean.Analysis
