import Mathlib
import RHLean.Arithmetic.PrimeWheelThreeSlotRecovery
import RHLean.Analysis.PrimeWheelRecoveredMertensCriterion

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-!
# Exact three-slot Mertens degree-one projection

This module turns the empirical three-slot state diagnostic into an exact finite
identity.  For each complete four-cell indexed by `k`, the active state is

```text
(mu(4k+1), mu(4k+2), mu(4k+3)) in {-1,0,1}^3.
```

The three coordinates are encoded by the mixed-radix index

```text
(a+1) * 9 + (b+1) * 3 + (c+1) in {0,...,26}.
```

For the first `K` cells, `threeSlotStateCount K i` is the exact population of
state `i`.  Regrouping the three degree-one Mobius sums by these finite fibers
gives the corresponding Walsh projections.  Their sum is exactly `M(4K)`.

The same degree-one object is then identified with the repository's physical
prime-wheel signed field `R - 2H`: raw seeded mass minus twice the smooth-core
correction.  No transition probability, asymptotic estimate, or probabilistic
independence statement is used here.
-/

/-- Code a Mobius value `-1, 0, 1` as the trit `0, 1, 2`. -/
def moebiusTrit (n : ℕ) : Fin 3 :=
  if μ n = -1 then 0 else if μ n = 0 then 1 else 2

/-- Decode a trit back to its signed value `-1, 0, 1`. -/
def tritSign (t : Fin 3) : ℤ :=
  (t.1 : ℤ) - 1

@[simp] theorem tritSign_moebiusTrit (n : ℕ) :
    tritSign (moebiusTrit n) = μ n := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [moebiusTrit, tritSign, h]

/-- Mixed-radix encoding of three trits into the `27 = 3^3` state space. -/
def encodeThreeTrits (a b c : Fin 3) : Fin 27 :=
  ⟨9 * a.1 + 3 * b.1 + c.1, by omega⟩

/-- The exact three-slot Mobius state of the `k`th complete four-cell. -/
def threeSlotState (k : ℕ) : Fin 27 :=
  encodeThreeTrits
    (moebiusTrit (4 * k + 1))
    (moebiusTrit (4 * k + 2))
    (moebiusTrit (4 * k + 3))

/-- Degree-one character selecting the first coordinate. -/
def chiA (i : Fin 27) : ℤ :=
  ((i.1 / 9 : ℕ) : ℤ) - 1

/-- Degree-one character selecting the second coordinate. -/
def chiB (i : Fin 27) : ℤ :=
  ((((i.1 / 3) % 3 : ℕ)) : ℤ) - 1

/-- Degree-one character selecting the third coordinate. -/
def chiC (i : Fin 27) : ℤ :=
  ((i.1 % 3 : ℕ) : ℤ) - 1

@[simp] theorem chiA_encodeThreeTrits (a b c : Fin 3) :
    chiA (encodeThreeTrits a b c) = tritSign a := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [chiA, encodeThreeTrits, tritSign]

@[simp] theorem chiB_encodeThreeTrits (a b c : Fin 3) :
    chiB (encodeThreeTrits a b c) = tritSign b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [chiB, encodeThreeTrits, tritSign]

@[simp] theorem chiC_encodeThreeTrits (a b c : Fin 3) :
    chiC (encodeThreeTrits a b c) = tritSign c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [chiC, encodeThreeTrits, tritSign]

@[simp] theorem chiA_threeSlotState (k : ℕ) :
    chiA (threeSlotState k) = μ (4 * k + 1) := by
  simp [threeSlotState]

@[simp] theorem chiB_threeSlotState (k : ℕ) :
    chiB (threeSlotState k) = μ (4 * k + 2) := by
  simp [threeSlotState]

@[simp] theorem chiC_threeSlotState (k : ℕ) :
    chiC (threeSlotState k) = μ (4 * k + 3) := by
  simp [threeSlotState]

/-- The exact empirical count `C_i(K)` of state `i` among the first `K` cells. -/
def threeSlotStateCount (K : ℕ) (i : Fin 27) : ℕ :=
  ((Finset.range K).filter fun k => threeSlotState k = i).card

/-- Generic finite-fiber regrouping identity behind every degree-one projection. -/
theorem degreeOneProjection_fiberwise
    (K : ℕ) (χ : Fin 27 → ℤ) :
    (∑ i : Fin 27, χ i * (threeSlotStateCount K i : ℤ)) =
      ∑ k ∈ Finset.range K, χ (threeSlotState k) := by
  classical
  have hmaps :
      ∀ k ∈ Finset.range K,
        threeSlotState k ∈ (Finset.univ : Finset (Fin 27)) := by
    intro k hk
    simp
  unfold threeSlotStateCount
  calc
    (∑ i : Fin 27,
        χ i *
          (((Finset.range K).filter fun k => threeSlotState k = i).card : ℤ)) =
      ∑ i ∈ (Finset.univ : Finset (Fin 27)),
        ∑ _k ∈ Finset.range K with threeSlotState _k = i, χ i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [mul_comm]
    _ = ∑ k ∈ Finset.range K, χ (threeSlotState k) := by
      simpa using
        (Finset.sum_fiberwise_of_maps_to'
          (s := Finset.range K)
          (t := (Finset.univ : Finset (Fin 27)))
          (g := threeSlotState)
          hmaps
          χ)

/-- First degree-one Walsh sum `W_a(K)`. -/
def threeSlotWa (K : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K, μ (4 * k + 1)

/-- Second degree-one Walsh sum `W_b(K)`. -/
def threeSlotWb (K : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K, μ (4 * k + 2)

/-- Third degree-one Walsh sum `W_c(K)`. -/
def threeSlotWc (K : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K, μ (4 * k + 3)

/-- Exact first-coordinate projection `W_a(K) = sum_i chi_a(i) C_i(K)`. -/
theorem threeSlotWa_eq_degreeOneProjection (K : ℕ) :
    threeSlotWa K =
      ∑ i : Fin 27, chiA i * (threeSlotStateCount K i : ℤ) := by
  rw [degreeOneProjection_fiberwise (K := K) (χ := chiA)]
  simp [threeSlotWa]

/-- Exact second-coordinate projection `W_b(K) = sum_i chi_b(i) C_i(K)`. -/
theorem threeSlotWb_eq_degreeOneProjection (K : ℕ) :
    threeSlotWb K =
      ∑ i : Fin 27, chiB i * (threeSlotStateCount K i : ℤ) := by
  rw [degreeOneProjection_fiberwise (K := K) (χ := chiB)]
  simp [threeSlotWb]

/-- Exact third-coordinate projection `W_c(K) = sum_i chi_c(i) C_i(K)`. -/
theorem threeSlotWc_eq_degreeOneProjection (K : ℕ) :
    threeSlotWc K =
      ∑ i : Fin 27, chiC i * (threeSlotStateCount K i : ℤ) := by
  rw [degreeOneProjection_fiberwise (K := K) (χ := chiC)]
  simp [threeSlotWc]

/-- At a complete four-cell endpoint, the integer Mertens prefix is exactly the
sum of the three degree-one coordinate sums. -/
theorem moebiusPositivePrefix_four_mul_eq_degreeOne (K : ℕ) :
    moebiusPositivePrefix (4 * K) =
      threeSlotWa K + threeSlotWb K + threeSlotWc K := by
  rw [moebiusPositivePrefix_four_mul_eq_fourSlotCellSum]
  unfold threeSlotWa threeSlotWb threeSlotWc
  calc
    (∑ k ∈ Finset.range K, fourSlotCellSum k) =
        ∑ k ∈ Finset.range K,
          (μ (4 * k + 1) + μ (4 * k + 2) + μ (4 * k + 3)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [fourSlotCellSum, moebius_four_mul_add_four]
            ring
    _ =
        (∑ k ∈ Finset.range K, μ (4 * k + 1)) +
          (∑ k ∈ Finset.range K, μ (4 * k + 2)) +
          (∑ k ∈ Finset.range K, μ (4 * k + 3)) := by
            simp only [Finset.sum_add_distrib]

/-- The same identity in the analytic complex-valued Mertens notation used by
the downstream RH bridge: `M(4K) = W_a(K) + W_b(K) + W_c(K)`. -/
theorem mertensSummatory_four_mul_eq_degreeOne (K : ℕ) :
    mertensSummatory (4 * K) =
      (((threeSlotWa K + threeSlotWb K + threeSlotWc K : ℤ)) : ℂ) := by
  rw [← sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory (4 * K),
    sqrtWheelRecoveredPrefix_eq_moebiusPositivePrefix,
    moebiusPositivePrefix_four_mul_eq_degreeOne]

/-! ## Equivalence with the physical `R - 2H` signed field -/

/-- Canonical raw slot prefix `R_j(K)` for the square-root wheel at cutoff `4K`. -/
def threeSlotR (j K : ℕ) : ℤ :=
  primeWheelRawSlotPrefix (primesUpTo (Nat.sqrt (4 * K))) j K

/-- Canonical smooth-core slot prefix `H_j(K)` for the same physical cutoff. -/
def threeSlotH (j K : ℕ) : ℤ :=
  primeWheelSmoothSlotPrefix
    (primesUpTo (Nat.sqrt (4 * K))) (4 * K) j K

/-- Physical signed field `R_j(K) - 2 H_j(K)`. -/
def threeSlotSignedFieldPrefix (j K : ℕ) : ℤ :=
  threeSlotR j K - 2 * threeSlotH j K

/-- On every active slot, the physical `R - 2H` field is exactly the corresponding
Mobius degree-one sum. -/
theorem threeSlotSignedFieldPrefix_eq_moebius
    (j K : ℕ) (hjpos : 1 ≤ j) (hjle : j ≤ 3) :
    threeSlotSignedFieldPrefix j K =
      ∑ k ∈ Finset.range K, μ (4 * k + j) := by
  have h := primeWheelRecoveredSlotPrefix_eq_moebius
    (primesUpTo (Nat.sqrt (4 * K))) (4 * K) j K
    (by
      intro p hp
      exact prime_of_mem_primesUpTo hp)
    (primesUpTo_sqrtCoverage (4 * K))
    le_rfl hjpos hjle
  simpa [threeSlotSignedFieldPrefix, threeSlotR, threeSlotH,
    primeWheelRecoveredSlotPrefix] using h

@[simp] theorem threeSlotSignedFieldPrefix_one_eq_Wa (K : ℕ) :
    threeSlotSignedFieldPrefix 1 K = threeSlotWa K := by
  simpa [threeSlotWa] using
    threeSlotSignedFieldPrefix_eq_moebius 1 K (by omega) (by omega)

@[simp] theorem threeSlotSignedFieldPrefix_two_eq_Wb (K : ℕ) :
    threeSlotSignedFieldPrefix 2 K = threeSlotWb K := by
  simpa [threeSlotWb] using
    threeSlotSignedFieldPrefix_eq_moebius 2 K (by omega) (by omega)

@[simp] theorem threeSlotSignedFieldPrefix_three_eq_Wc (K : ℕ) :
    threeSlotSignedFieldPrefix 3 K = threeSlotWc K := by
  simpa [threeSlotWc] using
    threeSlotSignedFieldPrefix_eq_moebius 3 K (by omega) (by omega)

/-- Coordinatewise degree-one Walsh mass and physical `R - 2H` mass are the
same exact finite object. -/
theorem degreeOne_eq_signedField (K : ℕ) :
    threeSlotWa K + threeSlotWb K + threeSlotWc K =
      threeSlotSignedFieldPrefix 1 K +
        threeSlotSignedFieldPrefix 2 K +
        threeSlotSignedFieldPrefix 3 K := by
  simp

/-- Final exact bridge: the full three-slot `R - 2H` signed field is the Mertens
value at the complete four-cell endpoint. -/
theorem mertensSummatory_four_mul_eq_signedField (K : ℕ) :
    mertensSummatory (4 * K) =
      (((threeSlotSignedFieldPrefix 1 K +
          threeSlotSignedFieldPrefix 2 K +
          threeSlotSignedFieldPrefix 3 K : ℤ)) : ℂ) := by
  rw [threeSlotSignedFieldPrefix_one_eq_Wa,
    threeSlotSignedFieldPrefix_two_eq_Wb,
    threeSlotSignedFieldPrefix_three_eq_Wc]
  exact mertensSummatory_four_mul_eq_degreeOne K

end RHLean.Analysis
