import Mathlib
import RHLean.Analysis.PhysicalDegreeOneHigherSquareRecurrences
import RHLean.Arithmetic.PrimeWheelThreeSlotRecovery

/-!
# Exceptional least-square local intertwining

This file begins the physical LOCAL-BLOCK theorem on the actual least-square
channels.  It keeps the finite CRT/blocker geometry separate from the full
square-root recovery wheel.

The `q=3` case collapses to one unrestricted recovered interval.  For `q=5`
and `q=7`, the least-owner masks are not contiguous after the smaller square
channels are removed, so the correct primitive form is an exact finite
incidence sum of recovered four-cell increments.  This distinction is important:
there is no assumption that a sparse higher-owner mask is one scalar Mertens
interval.

No selected CRT/blocker wheel appears in these recovery identities.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- One local four-cell increment of the full recovered three-slot prefix. -/
def recoveredThreeSlotCellIncrement
    (S : Finset ℕ) (upper K : ℕ) : ℤ :=
  primeWheelThreeSlotRecoveredPrefix S upper (K + 1) -
    primeWheelThreeSlotRecoveredPrefix S upper K

/-- **Recovered cell identity.**  Once the recovery wheel covers the physical
cutoff, every local recovered prefix increment is exactly the actual Möbius
four-cell value.  This is pointwise in the cell index and needs no CRT period. -/
theorem recoveredThreeSlotCellIncrement_eq_fourSlotCellSum
    (S : Finset ℕ) (upper K : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hupper : 4 * (K + 1) ≤ upper) :
    recoveredThreeSlotCellIncrement S upper K = fourSlotCellSum K := by
  have hlo : 4 * K ≤ upper := by omega
  have hhi := primeWheelThreeSlotRecoveredPrefix_eq_fourSlotCellSum
    S upper (K + 1) hprime hcover hupper
  have hlow := primeWheelThreeSlotRecoveredPrefix_eq_fourSlotCellSum
    S upper K hprime hcover hlo
  unfold recoveredThreeSlotCellIncrement
  rw [hhi, hlow, Finset.sum_range_succ]
  ring

/-- **Physical q=3 LOCAL-BLOCK.**  A complete least-`3^2` physical block is
exactly the difference of the full recovered three-slot field at its two local
endpoints.  The recovery wheel `S` is arbitrary subject only to its own prime
coverage hypotheses; it is not identified with a finite blocker wheel. -/
theorem physicalD9_nine_step_eq_recoveredThreeSlot_interval
    (S : Finset ℕ) (upper L : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hupper : 36 * L + 32 ≤ upper) :
    physicalD9 (9 * (L + 1)) - physicalD9 (9 * L) =
      primeWheelThreeSlotRecoveredPrefix S upper (9 * L + 8) -
        primeWheelThreeSlotRecoveredPrefix S upper (9 * L + 2) := by
  have hhi : 4 * (9 * L + 8) ≤ upper := by
    nlinarith
  have hlo : 4 * (9 * L + 2) ≤ upper := by
    omega
  have hrecHi :=
    primeWheelThreeSlotRecoveredPrefix_eq_fourSlotCellSum
      S upper (9 * L + 8) hprime hcover hhi
  have hrecLo :=
    primeWheelThreeSlotRecoveredPrefix_eq_fourSlotCellSum
      S upper (9 * L + 2) hprime hcover hlo
  have hmHi := moebiusPositivePrefix_four_mul_eq_fourSlotCellSum (9 * L + 8)
  have hmLo := moebiusPositivePrefix_four_mul_eq_fourSlotCellSum (9 * L + 2)
  rw [physicalD9_nine_step_recurrence]
  rw [show 36 * L + 32 = 4 * (9 * L + 8) by ring,
    show 36 * L + 8 = 4 * (9 * L + 2) by ring]
  rw [hmHi, hmLo, ← hrecHi, ← hrecLo]

/-- **Physical q=5 local incidence block.**  One complete least-`5^2`
super-period is exactly the fixed 18-residue incidence operator applied to the
full recovered cell increments.  The higher-prime arithmetic content remains
inside the recovered field; no global prefix state is consulted. -/
theorem physicalD25_225_step_eq_recoveredIncidence
    (S : Finset ℕ) (upper L : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hupper : 4 * (225 * (L + 1) + 1) ≤ upper) :
    physicalD25 (225 * (L + 1)) - physicalD25 (225 * L) =
      ∑ r ∈ physicalTwentyFiveChannelResidues,
        recoveredThreeSlotCellIncrement S upper (225 * L + r + 1) := by
  rw [physicalD25_225_step_fourSlot_recurrence]
  apply Finset.sum_congr rfl
  intro r hr
  have hrlt : r < 225 := by
    exact Finset.mem_range.mp (Finset.filter_subset _ _ hr)
  symm
  apply recoveredThreeSlotCellIncrement_eq_fourSlotCellSum
    S upper (225 * L + r + 1) hprime hcover
  have hindex : 225 * L + r + 2 ≤ 225 * (L + 1) + 1 := by omega
  exact (Nat.mul_le_mul_left 4 hindex).trans hupper

/-- **Physical q=7 local incidence block.**  One complete least-`7^2`
super-period is exactly the fixed 342-residue incidence operator applied to the
full recovered cell increments. -/
theorem physicalD49_11025_step_eq_recoveredIncidence
    (S : Finset ℕ) (upper L : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hupper : 4 * (11025 * (L + 1) + 1) ≤ upper) :
    physicalD49 (11025 * (L + 1)) - physicalD49 (11025 * L) =
      ∑ r ∈ physicalFortyNineChannelResidues,
        recoveredThreeSlotCellIncrement S upper (11025 * L + r + 1) := by
  rw [physicalD49_11025_step_fourSlot_recurrence]
  apply Finset.sum_congr rfl
  intro r hr
  have hrlt : r < 11025 := by
    exact Finset.mem_range.mp (Finset.filter_subset _ _ hr)
  symm
  apply recoveredThreeSlotCellIncrement_eq_fourSlotCellSum
    S upper (11025 * L + r + 1) hprime hcover
  have hindex : 11025 * L + r + 2 ≤ 11025 * (L + 1) + 1 := by omega
  exact (Nat.mul_le_mul_left 4 hindex).trans hupper

end RHLean.Analysis
