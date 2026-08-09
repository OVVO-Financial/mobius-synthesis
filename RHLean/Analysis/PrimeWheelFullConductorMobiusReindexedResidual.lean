import Mathlib
import RHLean.Analysis.PrimeWheelFullConductorUniformPacket
import RHLean.Analysis.PrimeWheelRawBoundaryMobiusPairing
import RHLean.Analysis.PrimeWheelSmoothConductorMobiusReindex

/-!
# Full conductor recombination after Möbius reindexing

The exact all-conductor packet can now be reindexed before any norm is taken.
The raw divisor-boundary family pairs with the upper-divisor Möbius transform
of the actual raw conductor coefficient.  The smooth divisor-boundary family
collapses to the single top divisor of the ambient torus.  The conductor-one
bulk terms remain explicit and survive exactly once.

Thus the historical residual is expressed as one common torus normalization
multiplying a signed combination of three objects:

* the collapsed raw boundary pairing,
* the retained raw conductor-one bulk,
* the collapsed smooth top-boundary packet plus its retained bulk.

No estimate or triangle inequality is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Raw boundary pairing after exchanging the conductor and boundary-divisor
sums. -/
def primorialRawCollapsedBoundaryPairing (k x : ℕ) : ℂ :=
  ∑ d ∈ (primorialMinimalWheelSystem k).modulus.divisors,
    primeWheelRawUpperMobiusTransform
        (primorialWheelPrimes k)
        (primorialMinimalWheelSystem k).modulus d *
      (((divisorIntervalBoundary d 0
        (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))

/-- The conductor-one raw bulk retained after the all-conductor reindexing. -/
def primorialRawRetainedBulk (k x : ℕ) : ℂ :=
  primorialRawConductorArithmeticCoefficient k 1 *
    ((((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ) : ℂ))

/-- Smooth packet after the complete conductor sum: one top-divisor boundary
packet plus the conductor-one smooth bulk. -/
def primorialSmoothCollapsedBoundaryBulk (k x : ℕ) : ℤ :=
  (∑ a ∈ primeWheelSmoothDivisorSites (primorialMinimalWheelSystem k),
    -(μ a) *
      divisorIntervalBoundary (primorialMinimalWheelSystem k).modulus a
        (primorialMinimalWheelSystem k).lower x) +
  primeWheelSmoothBulkMass (primorialMinimalWheelSystem k) *
    ((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ)

/-- The complete raw divisor-boundary family is exactly the collapsed raw
upper-Möbius pairing. -/
theorem sum_primorialRawBoundaryPackets_eq_collapsed
    (k x : ℕ) :
    (∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
      primorialRawConductorArithmeticCoefficient k q *
        (((∑ d ∈ q.divisors,
          μ (q / d) *
            divisorIntervalBoundary d 0
              (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))) =
      primorialRawCollapsedBoundaryPairing k x := by
  unfold primorialRawCollapsedBoundaryPairing
    primorialRawConductorArithmeticCoefficient
  exact
    sum_rawConductorCoefficient_mul_intMobiusPacket_eq_upperMobiusPairing
      (primorialWheelPrimes k)
      (primorialMinimalWheelSystem k).modulus
      (Nat.ne_of_gt (primorialMinimalWheelSystem k).modulus_pos)
      (fun d => divisorIntervalBoundary d 0
        (primorialMinimalWheelSystem k).lower x)

/-- The conductor-one Kronecker bulk in the raw family appears exactly once in
the complete divisor-conductor sum. -/
theorem sum_primorialRawBulkPackets_eq_retained
    (k x : ℕ) :
    (∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
      primorialRawConductorArithmeticCoefficient k q *
        ((((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ) *
          (if q = 1 then 1 else 0) : ℤ) : ℂ)) =
      primorialRawRetainedBulk k x := by
  classical
  have hNne : (primorialMinimalWheelSystem k).modulus ≠ 0 :=
    Nat.ne_of_gt (primorialMinimalWheelSystem k).modulus_pos
  have h1mem : 1 ∈ (primorialMinimalWheelSystem k).modulus.divisors :=
    (Nat.one_mem_divisors).2 hNne
  unfold primorialRawRetainedBulk
  calc
    (∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
      primorialRawConductorArithmeticCoefficient k q *
        ((((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ) *
          (if q = 1 then 1 else 0) : ℤ) : ℂ)) =
      ∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
        if q = 1 then
          primorialRawConductorArithmeticCoefficient k q *
            ((((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ) : ℂ))
        else 0 := by
          apply Finset.sum_congr rfl
          intro q hq
          by_cases hq1 : q = 1 <;> simp [hq1]
    _ = primorialRawConductorArithmeticCoefficient k 1 *
        ((((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ) : ℂ)) := by
          simp [h1mem]

/-- The complete smooth arithmetic family is the collapsed top-boundary packet
plus the retained conductor-one smooth bulk. -/
theorem sum_primorialSmoothPackets_eq_collapsed
    (k x : ℕ) :
    (∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
      (primeWheelSmoothBoundaryPacket (primorialMinimalWheelSystem k) x q +
        primeWheelSmoothBulkMass (primorialMinimalWheelSystem k) *
          ((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ) *
          (if q = 1 then 1 else 0))) =
      primorialSmoothCollapsedBoundaryBulk k x := by
  unfold primorialSmoothCollapsedBoundaryBulk
  exact
    sum_primeWheelSmoothBoundary_add_bulk_divisors
      (primorialMinimalWheelSystem k) x

/-- Final exact reindexed residual identity.  All conductor sums have been
collapsed before any norm is taken. -/
theorem primorialPeriodicRawResidual_eq_mobiusReindexed
    (k : ℕ) {x : ℕ}
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    ((((primorialWheelSystem k).residual x : ℤ) : ℂ)) =
      (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        (primorialRawCollapsedBoundaryPairing k x +
          primorialRawRetainedBulk k x -
          2 * (((primorialSmoothCollapsedBoundaryBulk k x : ℤ) : ℂ))) := by
  rw [primorialPeriodicRawResidual_eq_sum_explicitAllConductorPackets
    k hlower hupper]
  unfold primorialPeriodicRawExplicitAllConductorPacket
  let Ninv : ℂ := (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹)
  let L : ℤ := ((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ)
  have hraw :
      (∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
        primorialRawConductorArithmeticCoefficient k q *
          (Ninv *
            ((((∑ d ∈ q.divisors,
              μ (q / d) *
                divisorIntervalBoundary d 0
                  (primorialMinimalWheelSystem k).lower x) +
              L * (if q = 1 then 1 else 0) : ℤ) : ℂ)))) =
        Ninv *
          (primorialRawCollapsedBoundaryPairing k x +
            primorialRawRetainedBulk k x) := by
    calc
      (∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
        primorialRawConductorArithmeticCoefficient k q *
          (Ninv *
            ((((∑ d ∈ q.divisors,
              μ (q / d) *
                divisorIntervalBoundary d 0
                  (primorialMinimalWheelSystem k).lower x) +
              L * (if q = 1 then 1 else 0) : ℤ) : ℂ)))) =
        Ninv *
          ∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
            primorialRawConductorArithmeticCoefficient k q *
              ((((∑ d ∈ q.divisors,
                μ (q / d) *
                  divisorIntervalBoundary d 0
                    (primorialMinimalWheelSystem k).lower x) +
                L * (if q = 1 then 1 else 0) : ℤ) : ℂ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring
      _ = Ninv *
          ((∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
            primorialRawConductorArithmeticCoefficient k q *
              (((∑ d ∈ q.divisors,
                μ (q / d) *
                  divisorIntervalBoundary d 0
                    (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))) +
          (∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
            primorialRawConductorArithmeticCoefficient k q *
              (((L * (if q = 1 then 1 else 0) : ℤ) : ℂ)))) := by
            congr 1
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro q hq
            push_cast
            ring
      _ = Ninv *
          (primorialRawCollapsedBoundaryPairing k x +
            primorialRawRetainedBulk k x) := by
            rw [sum_primorialRawBoundaryPackets_eq_collapsed]
            change
              Ninv *
                (primorialRawCollapsedBoundaryPairing k x +
                  (∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
                    primorialRawConductorArithmeticCoefficient k q *
                      (((((Finset.Ioc
                        (primorialMinimalWheelSystem k).lower x).card : ℤ) *
                        (if q = 1 then 1 else 0) : ℤ) : ℂ)))) = _
            rw [sum_primorialRawBulkPackets_eq_retained]
  have hsmoothInt :=
    sum_primorialSmoothPackets_eq_collapsed k x
  have hsmoothCast :
      (∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
        ((primeWheelSmoothBoundaryPacket
            (primorialMinimalWheelSystem k) x q +
          primeWheelSmoothBulkMass (primorialMinimalWheelSystem k) *
            ((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ) *
            (if q = 1 then 1 else 0) : ℤ) : ℂ)) =
        ((primorialSmoothCollapsedBoundaryBulk k x : ℤ) : ℂ) := by
    have h := congrArg (Int.castRingHom ℂ) hsmoothInt
    simpa only [map_sum] using h
  have hsmooth :
      (∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
        2 * (Ninv *
          ((primeWheelSmoothBoundaryPacket
              (primorialMinimalWheelSystem k) x q +
            primeWheelSmoothBulkMass (primorialMinimalWheelSystem k) *
              ((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ) *
              (if q = 1 then 1 else 0) : ℤ) : ℂ))) =
        Ninv *
          (2 * ((primorialSmoothCollapsedBoundaryBulk k x : ℤ) : ℂ)) := by
    calc
      (∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
        2 * (Ninv *
          ((primeWheelSmoothBoundaryPacket
              (primorialMinimalWheelSystem k) x q +
            primeWheelSmoothBulkMass (primorialMinimalWheelSystem k) *
              ((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ) *
              (if q = 1 then 1 else 0) : ℤ) : ℂ))) =
        (2 * Ninv) *
          (∑ q ∈ (primorialMinimalWheelSystem k).modulus.divisors,
            ((primeWheelSmoothBoundaryPacket
                (primorialMinimalWheelSystem k) x q +
              primeWheelSmoothBulkMass (primorialMinimalWheelSystem k) *
                ((Finset.Ioc (primorialMinimalWheelSystem k).lower x).card : ℤ) *
                (if q = 1 then 1 else 0) : ℤ) : ℂ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring
      _ = (2 * Ninv) *
          ((primorialSmoothCollapsedBoundaryBulk k x : ℤ) : ℂ) := by
            rw [hsmoothCast]
      _ = Ninv *
          (2 * ((primorialSmoothCollapsedBoundaryBulk k x : ℤ) : ℂ)) := by
            ring
  rw [Finset.sum_sub_distrib]
  calc
    _ = Ninv *
          (primorialRawCollapsedBoundaryPairing k x +
            primorialRawRetainedBulk k x) -
        Ninv *
          (2 * ((primorialSmoothCollapsedBoundaryBulk k x : ℤ) : ℂ)) :=
      congrArg₂ (· - ·) hraw hsmooth
    _ = Ninv *
        (primorialRawCollapsedBoundaryPairing k x +
          primorialRawRetainedBulk k x -
          2 * ((primorialSmoothCollapsedBoundaryBulk k x : ℤ) : ℂ)) := by
            ring
    _ = (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        (primorialRawCollapsedBoundaryPairing k x +
          primorialRawRetainedBulk k x -
          2 * ((primorialSmoothCollapsedBoundaryBulk k x : ℤ) : ℂ)) := by
            rfl

end RHLean.Analysis
