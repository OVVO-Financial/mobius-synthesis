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

/-- A modulus-one divisor boundary is identically zero. -/
theorem divisorIntervalBoundary_one_eq_zero
    (a lower upper : ℕ) :
    divisorIntervalBoundary 1 a lower upper = 0 := by
  have hmod : ∀ m : ℕ, Nat.ModEq 1 m a := by
    intro m
    change m % 1 = a % 1
    omega
  have hcount :
      divisorResidueCount (Finset.Ioc lower upper) 1 a =
        ((Finset.Ioc lower upper).card : ℤ) := by
    unfold divisorResidueCount
    simp [hmod]
  unfold divisorIntervalBoundary divisorResidueBoundary
  rw [hcount]
  ring

/-- The conductor-three Möbius divisor packet has only its mod-`3` boundary
term; the divisor-one term vanishes exactly. -/
theorem conductorThree_divisorBoundaryPacket_eq
    (a lower upper : ℕ) :
    (∑ d ∈ (3 : ℕ).divisors,
      μ (3 / d) * divisorIntervalBoundary d a lower upper) =
      divisorIntervalBoundary 3 a lower upper := by
  have hdiv : (3 : ℕ).divisors = ({1, 3} : Finset ℕ) := by
    native_decide
  rw [hdiv]
  norm_num [divisorIntervalBoundary_one_eq_zero]

/-- The smooth conductor-three packet is exactly the signed sum of mod-`3`
boundary defects over the actual smooth divisor sites. -/
theorem primeWheelSmoothBoundaryPacket_three
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    primeWheelSmoothBoundaryPacket W x 3 =
      ∑ a ∈ primeWheelSmoothDivisorSites W,
        -(μ a) * divisorIntervalBoundary 3 a W.lower x := by
  classical
  unfold primeWheelSmoothBoundaryPacket
  apply Finset.sum_congr rfl
  intro a ha
  rw [conductorThree_divisorBoundaryPacket_eq]

/-- **Exact full corrected conductor-three packet.**  Once conductor `3` is an
actual divisor of the primorial torus, the full `raw - 2 * smooth` response is
one common torus normalization multiplying only mod-`3` endpoint boundary
defects.  In particular no growing conductor-three bulk survives. -/
theorem primorialPeriodicRawJointConductorResponse_three_eq_boundary
    (k x : ℕ)
    (h3mem : 3 ∈ (primorialMinimalWheelSystem k).modulus.divisors)
    (hx : x ≤ (primorialMinimalWheelSystem k).upper) :
    primorialPeriodicRawJointConductorResponse k x 3 =
      (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        (primorialRawConductorArithmeticCoefficient k 3 *
            (((divisorIntervalBoundary 3 0
              (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ)) +
          2 * (((∑ a ∈ primeWheelSmoothDivisorSites
                (primorialMinimalWheelSystem k),
              μ a * divisorIntervalBoundary 3 a
                (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))) := by
  rw [primorialPeriodicRawJointConductorResponse_eq_explicitAllConductor
    k x 3 h3mem hx]
  unfold primorialPeriodicRawExplicitAllConductorPacket
  rw [conductorThree_divisorBoundaryPacket_eq]
  rw [primeWheelSmoothBoundaryPacket_three]
  norm_num
  ring

end RHLean.Analysis