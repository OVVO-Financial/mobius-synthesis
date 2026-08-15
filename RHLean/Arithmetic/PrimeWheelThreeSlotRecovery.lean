import Mathlib
import RHLean.Arithmetic.FourSlotCell
import RHLean.Arithmetic.PrimeCombFiniteDifferenceRecovery

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-!
# Exact three-slot square-root prime-wheel recovery

The four-cell architecture has three active slots, since the fourth site is
always killed by the square of `2`.  This module packages the seeded raw and
smooth-core masses on one fixed slot and proves the exact signed
`raw - 2 * smooth` recovery on every complete physical prefix.

The final theorem is the literal three-slot quantity singled out by the research
note: the sum of the three corrected slot prefixes is exactly the sum of the
complete four-slot Möbius cells.  No complete CRT period and no probabilistic
Walsh statement enters the proof.
-/

/-- Seeded raw prime-wheel mass on slot `j` of the first `K` four-cells. -/
def primeWheelRawSlotPrefix
    (S : Finset ℕ) (j K : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K, seededPrimeComb S (4 * k + j)

/-- Smooth-core mass on slot `j` of the first `K` four-cells. -/
def primeWheelSmoothSlotPrefix
    (S : Finset ℕ) (upper j K : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K, primeWheelSmoothCoreSite S upper (4 * k + j)

/-- The signed recovered slot mass.  The smooth correction stays inside the
quantity to be estimated. -/
def primeWheelRecoveredSlotPrefix
    (S : Finset ℕ) (upper j K : ℕ) : ℤ :=
  primeWheelRawSlotPrefix S j K -
    2 * primeWheelSmoothSlotPrefix S upper j K

/-- Under square-root coverage, every active slot recovers its Möbius values
exactly throughout the physical prefix. -/
theorem primeWheelRecoveredSlotPrefix_eq_moebius
    (S : Finset ℕ) (upper j K : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hK : 4 * K ≤ upper)
    (hjpos : 1 ≤ j) (hjle : j ≤ 3) :
    primeWheelRecoveredSlotPrefix S upper j K =
      ∑ k ∈ Finset.range K, μ (4 * k + j) := by
  classical
  unfold primeWheelRecoveredSlotPrefix primeWheelRawSlotPrefix
    primeWheelSmoothSlotPrefix
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < K := Finset.mem_range.mp hk
  have hnpos : 0 < 4 * k + j := by omega
  have hnupper : 4 * k + j ≤ upper := by omega
  change correctedPrimeWheelSite S upper (4 * k + j) = μ (4 * k + j)
  exact correctedPrimeWheelSite_eq_moebius
    S hprime hcover hnpos hnupper

/-- The three active corrected coordinates of the first `K` four-cells. -/
def primeWheelThreeSlotRecoveredPrefix
    (S : Finset ℕ) (upper K : ℕ) : ℤ :=
  primeWheelRecoveredSlotPrefix S upper 1 K +
    primeWheelRecoveredSlotPrefix S upper 2 K +
    primeWheelRecoveredSlotPrefix S upper 3 K

/-- Exact three-slot recovery at complete four-cell prefixes.  This is the
formal `sum_j (R_j - 2 H_j)` identity in the square-block architecture. -/
theorem primeWheelThreeSlotRecoveredPrefix_eq_fourSlotCellSum
    (S : Finset ℕ) (upper K : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : PrimeWheelSqrtCoverage S upper)
    (hK : 4 * K ≤ upper) :
    primeWheelThreeSlotRecoveredPrefix S upper K =
      ∑ k ∈ Finset.range K, fourSlotCellSum k := by
  have h1 := primeWheelRecoveredSlotPrefix_eq_moebius
    S upper 1 K hprime hcover hK (by omega) (by omega)
  have h2 := primeWheelRecoveredSlotPrefix_eq_moebius
    S upper 2 K hprime hcover hK (by omega) (by omega)
  have h3 := primeWheelRecoveredSlotPrefix_eq_moebius
    S upper 3 K hprime hcover hK (by omega) (by omega)
  unfold primeWheelThreeSlotRecoveredPrefix
  rw [h1, h2, h3]
  calc
    (∑ k ∈ Finset.range K, μ (4 * k + 1)) +
          (∑ k ∈ Finset.range K, μ (4 * k + 2)) +
          (∑ k ∈ Finset.range K, μ (4 * k + 3)) =
        ∑ k ∈ Finset.range K,
          (μ (4 * k + 1) + μ (4 * k + 2) + μ (4 * k + 3)) := by
            simp only [Finset.sum_add_distrib]
    _ = ∑ k ∈ Finset.range K, fourSlotCellSum k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [fourSlotCellSum, moebius_four_mul_add_four]
      ring

/-- The ordinary positive Möbius prefix at a complete four-cell endpoint is
exactly the sum of the complete four-slot cells. -/
theorem moebiusPositivePrefix_four_mul_eq_fourSlotCellSum (K : ℕ) :
    moebiusPositivePrefix (4 * K) =
      ∑ k ∈ Finset.range K, fourSlotCellSum k := by
  induction K with
  | zero =>
      simp [moebiusPositivePrefix, positivePrefix]
  | succ K ih =>
      have ih' :
          (∑ n ∈ Finset.Icc 1 (4 * K), μ n) =
            ∑ k ∈ Finset.range K, fourSlotCellSum k := by
        simpa [moebiusPositivePrefix, positivePrefix] using ih
      unfold moebiusPositivePrefix positivePrefix
      rw [show 4 * (K + 1) = 4 * K + 4 by omega]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 4 * K + 4)]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 4 * K + 3)]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 4 * K + 2)]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 4 * K + 1)]
      rw [ih', Finset.sum_range_succ]
      unfold fourSlotCellSum
      ring

/-- Canonical minimal square-root wheel for a complete `K`-cell prefix. -/
def sqrtWheelThreeSlotRecoveredPrefix (K : ℕ) : ℤ :=
  primeWheelThreeSlotRecoveredPrefix
    (primesUpTo (Nat.sqrt (4 * K))) (4 * K) K

/-- The canonical square-root wheel realizes the exact three-slot Möbius cell
sum using only prime coordinates through the physical square-root cutoff. -/
theorem sqrtWheelThreeSlotRecoveredPrefix_eq_fourSlotCellSum (K : ℕ) :
    sqrtWheelThreeSlotRecoveredPrefix K =
      ∑ k ∈ Finset.range K, fourSlotCellSum k := by
  unfold sqrtWheelThreeSlotRecoveredPrefix
  apply primeWheelThreeSlotRecoveredPrefix_eq_fourSlotCellSum
  · intro p hp
    exact prime_of_mem_primesUpTo hp
  · intro p hp hple
    exact mem_primesUpTo.mpr ⟨hp, hple⟩
  · exact le_rfl

/-- At every complete four-cell endpoint the canonical square-root three-slot
quantity is exactly the ordinary Möbius prefix.  This is the direct formal
`sum_j (R_j - 2 H_j) = M(4K)` bridge. -/
theorem sqrtWheelThreeSlotRecoveredPrefix_eq_moebiusPositivePrefix (K : ℕ) :
    sqrtWheelThreeSlotRecoveredPrefix K =
      moebiusPositivePrefix (4 * K) := by
  rw [sqrtWheelThreeSlotRecoveredPrefix_eq_fourSlotCellSum,
    moebiusPositivePrefix_four_mul_eq_fourSlotCellSum]

end RHLean.Arithmetic
