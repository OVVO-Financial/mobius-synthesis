import Mathlib
import RHLean.Analysis.NativePNTMertens
import RHLean.Arithmetic.PrimorialReciprocalMobiusFactorization

/-!
# Truncated primorial wheel boundary decomposition

This module keeps reciprocal Möbius cancellation finite and exact while
allowing an ordinary prefix cutoff to truncate the Boolean prime cube.

For a finite prime set `P`, the truncated wheel profile is

`T_P(X) = sum_{t subset P, prod(t) <= X} mu(prod(t)) / prod(t)`.

It has two key properties.

* Once `X` reaches the full wheel product, `T_P(X)` is the complete signed
  contraction factor `prod_{p in P} (1 - 1/p)`.
* Adjoining one fresh prime gives the exact recurrence
  `T_{insert p P}(X) = T_P(X) - (1/p) T_P(X/p)`.

No asymptotic prime distribution, infinite Euler product, or Mertens product
theorem is used.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Arithmetic

/-- Product of all prime coordinates in a finite wheel. -/
def primorialWheelProduct (P : Finset ℕ) : ℕ := P.prod id

/-- Truncated signed reciprocal Boolean-cube profile.  Writing the cutoff as an
`if` over the complete powerset makes fresh-prime insertion an exact powerset
splitting identity. -/
def primorialTruncatedSignedReciprocalCube (P : Finset ℕ) (X : ℕ) : ℝ :=
  ∑ t ∈ P.powerset,
    if primeFaceProduct t ≤ X then
      ((booleanCubeSign t : ℤ) : ℝ) / (primeFaceProduct t : ℝ)
    else 0

/-- Möbius form of the truncated signed reciprocal cube. -/
theorem primorialTruncatedSignedReciprocalCube_eq_moebius
    (P : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    primorialTruncatedSignedReciprocalCube P X =
      ∑ t ∈ P.powerset,
        if primeFaceProduct t ≤ X then
          (ArithmeticFunction.moebius (primeFaceProduct t) : ℝ) /
            (primeFaceProduct t : ℝ)
        else 0 := by
  unfold primorialTruncatedSignedReciprocalCube
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hcut : primeFaceProduct t ≤ X
  · simp only [hcut, if_true]
    rw [moebius_primeFaceProduct_eq_booleanCubeSign t]
    intro p hp
    exact hprime p ((Finset.mem_powerset.mp ht) hp)
  · simp [hcut]

/-- Every face product divides the full wheel product. -/
theorem primeFaceProduct_dvd_primorialWheelProduct
    {P t : Finset ℕ} (ht : t ⊆ P) :
    primeFaceProduct t ∣ primorialWheelProduct P := by
  classical
  unfold primeFaceProduct primorialWheelProduct
  exact Finset.prod_dvd_prod_of_subset t P id ht

/-- Every face product is at most the full wheel product when all wheel entries
are positive. -/
theorem primeFaceProduct_le_primorialWheelProduct
    {P t : Finset ℕ} (ht : t ⊆ P) (hpos : ∀ p ∈ P, 1 ≤ p) :
    primeFaceProduct t ≤ primorialWheelProduct P := by
  unfold primeFaceProduct primorialWheelProduct
  exact Finset.prod_le_prod_of_subset_of_one_le' ht (by
    intro p hpP _hpt
    exact hpos p hpP)

/-- Once the cutoff reaches the full wheel product, the truncated cube is the
complete signed reciprocal cube. -/
theorem primorialTruncatedSignedReciprocalCube_eq_complete
    (P : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hX : primorialWheelProduct P ≤ X) :
    primorialTruncatedSignedReciprocalCube P X =
      primorialSignedReciprocalCube P := by
  unfold primorialTruncatedSignedReciprocalCube primorialSignedReciprocalCube
  apply Finset.sum_congr rfl
  intro t ht
  have hsubset : t ⊆ P := Finset.mem_powerset.mp ht
  have hle : primeFaceProduct t ≤ X :=
    le_trans
      (primeFaceProduct_le_primorialWheelProduct hsubset
        (fun p hp => (hprime p hp).one_le)) hX
  simp [hle]

/-- Therefore the stabilized truncated profile is exactly the finite signed
contraction product. -/
theorem primorialTruncatedSignedReciprocalCube_eq_factor
    (P : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hX : primorialWheelProduct P ≤ X) :
    primorialTruncatedSignedReciprocalCube P X =
      primorialSignedContractionFactor P := by
  rw [primorialTruncatedSignedReciprocalCube_eq_complete P X hprime hX]
  exact primorialSignedReciprocalCube_eq_factor P hprime

/-- Exact fresh-prime recurrence for the truncated wheel profile. -/
theorem primorialTruncatedSignedReciprocalCube_insert
    {P : Finset ℕ} {p X : ℕ}
    (hp : p ∉ P) (hpPrime : p.Prime) :
    primorialTruncatedSignedReciprocalCube (insert p P) X =
      primorialTruncatedSignedReciprocalCube P X -
        (1 / (p : ℝ)) * primorialTruncatedSignedReciprocalCube P (X / p) := by
  classical
  unfold primorialTruncatedSignedReciprocalCube
  rw [Finset.sum_powerset_insert hp]
  have hpR0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
  have hsecond :
      (∑ t ∈ P.powerset,
        if primeFaceProduct (insert p t) ≤ X then
          ((booleanCubeSign (insert p t) : ℤ) : ℝ) /
            (primeFaceProduct (insert p t) : ℝ)
        else 0) =
        -(1 / (p : ℝ)) *
          ∑ t ∈ P.powerset,
            if primeFaceProduct t ≤ X / p then
              ((booleanCubeSign t : ℤ) : ℝ) / (primeFaceProduct t : ℝ)
            else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hpt : p ∉ t := Finset.notMem_of_mem_powerset_of_notMem ht hp
    have hprod : primeFaceProduct (insert p t) = p * primeFaceProduct t := by
      simp [primeFaceProduct, hpt]
    have hsign :
        ((booleanCubeSign (insert p t) : ℤ) : ℝ) =
          -((booleanCubeSign t : ℤ) : ℝ) := by
      unfold booleanCubeSign
      rw [Finset.card_insert_of_notMem hpt, pow_succ]
      push_cast
      ring
    have hcut :
        primeFaceProduct (insert p t) ≤ X ↔ primeFaceProduct t ≤ X / p := by
      rw [hprod]
      constructor
      · intro hle
        apply (Nat.le_div_iff_mul_le hpPrime.pos).2
        simpa [Nat.mul_comm] using hle
      · intro hle
        have hmul := (Nat.le_div_iff_mul_le hpPrime.pos).1 hle
        simpa [Nat.mul_comm] using hmul
    by_cases hle : primeFaceProduct t ≤ X / p
    · have hchild : primeFaceProduct (insert p t) ≤ X := hcut.mpr hle
      simp only [hle, hchild, if_true]
      rw [hprod, hsign]
      push_cast
      field_simp [hpR0]
    · have hchild : ¬ primeFaceProduct (insert p t) ≤ X := by
        intro h
        exact hle (hcut.mp h)
      simp [hle, hchild]
  rw [hsecond]
  ring

/-- Complete-plus-boundary decomposition of a truncated wheel profile. -/
theorem primorialTruncatedSignedReciprocalCube_complete_boundary
    (P : Finset ℕ) (X : ℕ) :
    primorialTruncatedSignedReciprocalCube P X =
      primorialSignedContractionFactor P +
        (primorialTruncatedSignedReciprocalCube P X -
          primorialSignedContractionFactor P) := by
  ring

/-- The empty wheel has one face, of product `1`; hence its truncated profile is
`1` for every positive cutoff. -/
theorem primorialTruncatedSignedReciprocalCube_empty
    (X : ℕ) (hX : 1 ≤ X) :
    primorialTruncatedSignedReciprocalCube ∅ X = 1 := by
  simp [primorialTruncatedSignedReciprocalCube, primeFaceProduct,
    booleanCubeSign, hX]

end RHLean.Arithmetic
