import Mathlib
import RHLean.Proof.FiniteOthelloMatching
import RHLean.Proof.LowWheelCanonicalPairingFrontier

/-!
# Least-prime / largest-prime Othello on the same physical transport carrier

The canonical low-wheel transport carrier supports two opposite Euler moves on
exactly the same `(c,k)` states at a fixed Boolean face `t`.

* The **least** mate uses `minFac(c*k)`, the already-proved canonical pairing.
* The **largest** mate uses `P+(c*k)`.

Both raw toggles preserve `c*k`, hence preserve their own state-dependent pivot.
Complete each raw toggle by a fixed point whenever it would leave the physical
carrier.  On squarefree cofactors these completed maps are genuine
sign-reversing involutions.

This puts the bottom and top first-crossing coordinates on one finite signed
region, so `FiniteOthelloMatching` can transfer stable mass between them without
tracing alternating paths.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Largest-prime pivot of the invariant cofactor/quotient product. -/
def lowWheelLargestCofactorQuotientPivot
    (x : LowWheelCofactorQuotientState) : ℕ :=
  canonicalLargestPrimeFactor (x.1 * x.2)

/-- Raw largest-prime cofactor/quotient toggle. -/
def lowWheelLargestCofactorQuotientToggle
    (x : LowWheelCofactorQuotientState) : LowWheelCofactorQuotientState :=
  lowWheelCofactorQuotientToggleAt
    (lowWheelLargestCofactorQuotientPivot x) x

/-- The largest-prime raw toggle preserves the product. -/
theorem lowWheelLargestCofactorQuotientToggle_product
    (x : LowWheelCofactorQuotientState) :
    (lowWheelLargestCofactorQuotientToggle x).1 *
        (lowWheelLargestCofactorQuotientToggle x).2 =
      x.1 * x.2 := by
  unfold lowWheelLargestCofactorQuotientToggle
  exact lowWheelCofactorQuotientToggleAt_product x

/-- Therefore the largest pivot is invariant under its own raw toggle. -/
theorem lowWheelLargestCofactorQuotientPivot_toggle
    (x : LowWheelCofactorQuotientState) :
    lowWheelLargestCofactorQuotientPivot
        (lowWheelLargestCofactorQuotientToggle x) =
      lowWheelLargestCofactorQuotientPivot x := by
  unfold lowWheelLargestCofactorQuotientPivot
  rw [lowWheelLargestCofactorQuotientToggle_product]

private theorem lowWheelPhysicalState_product_pos
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (_ht : t ∈ (primesUpTo R).powerset)
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t) :
    0 < x.1 * x.2 := by
  have hxData := mem_lowWheelCanonicalPhysicalStateSet.mp hx
  have hcPos : 0 < x.1 := by
    have hc1 := (Finset.mem_Ico.mp hxData.1).1
    omega
  have hkPos : 0 < x.2 := by
    have hk1 := (Finset.mem_Icc.mp hxData.2.1).1
    omega
  exact Nat.mul_pos hcPos hkPos

private theorem lowWheelPhysicalState_product_gt_one_of_ne
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (ht : t ∈ (primesUpTo R).powerset)
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t)
    (hne : x.1 * x.2 ≠ 1) :
    1 < x.1 * x.2 := by
  have hpos := lowWheelPhysicalState_product_pos ht hx
  omega

/-- Largest pivot is prime on a nontrivial physical state. -/
theorem lowWheelLargestCofactorQuotientPivot_prime
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (ht : t ∈ (primesUpTo R).powerset)
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t)
    (hne : x.1 * x.2 ≠ 1) :
    (lowWheelLargestCofactorQuotientPivot x).Prime := by
  have hgt := lowWheelPhysicalState_product_gt_one_of_ne ht hx hne
  simpa [lowWheelLargestCofactorQuotientPivot] using
    canonicalLargestPrimeFactor_prime hgt

/-- Largest pivot is active in either cofactor or quotient. -/
theorem lowWheelLargestCofactorQuotientPivot_active
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (ht : t ∈ (primesUpTo R).powerset)
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t)
    (hne : x.1 * x.2 ≠ 1) :
    lowWheelLargestCofactorQuotientPivot x ∣ x.1 ∨
      lowWheelLargestCofactorQuotientPivot x ∣ x.2 := by
  have hgt := lowWheelPhysicalState_product_gt_one_of_ne ht hx hne
  have hp := lowWheelLargestCofactorQuotientPivot_prime ht hx hne
  have hdvd : lowWheelLargestCofactorQuotientPivot x ∣ x.1 * x.2 := by
    simpa [lowWheelLargestCofactorQuotientPivot] using
      canonicalLargestPrimeFactor_dvd hgt
  exact hp.dvd_mul.mp hdvd

/-- Largest raw toggle reverses signed weight on every nontrivial physical state. -/
theorem lowWheelLargestCofactorQuotientToggle_weight_neg
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (ht : t ∈ (primesUpTo R).powerset)
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t)
    (hne : x.1 * x.2 ≠ 1) :
    canonicalMoebiusWeight (lowWheelLargestCofactorQuotientToggle x).1 *
        (booleanCubeSign t : ℂ) =
      -(canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) := by
  have hsq := lowWheelCanonicalPhysicalStateSet_squarefree x hx
  unfold lowWheelLargestCofactorQuotientToggle
  exact lowWheelCofactorQuotientToggleAt_weight_neg
    (lowWheelLargestCofactorQuotientPivot_prime ht hx hne)
    hsq (lowWheelLargestCofactorQuotientPivot_active ht hx hne)

/-- Largest raw toggle is involutive on every nontrivial physical state. -/
theorem lowWheelLargestCofactorQuotientToggle_involutive
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (ht : t ∈ (primesUpTo R).powerset)
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t)
    (hne : x.1 * x.2 ≠ 1) :
    lowWheelLargestCofactorQuotientToggle
        (lowWheelLargestCofactorQuotientToggle x) = x := by
  change lowWheelCofactorQuotientToggleAt
      (lowWheelLargestCofactorQuotientPivot
        (lowWheelLargestCofactorQuotientToggle x))
      (lowWheelLargestCofactorQuotientToggle x) = x
  rw [lowWheelLargestCofactorQuotientPivot_toggle]
  change lowWheelCofactorQuotientToggleAt
      (lowWheelLargestCofactorQuotientPivot x)
      (lowWheelCofactorQuotientToggleAt
        (lowWheelLargestCofactorQuotientPivot x) x) = x
  exact lowWheelCofactorQuotientToggleAt_involutive
    (lowWheelLargestCofactorQuotientPivot_prime ht hx hne)
    (lowWheelCanonicalPhysicalStateSet_squarefree x hx)
    (lowWheelLargestCofactorQuotientPivot_active ht hx hne)

/-- Complete the canonical least-prime raw toggle by fixing boundary defects. -/
def lowWheelLeastOthelloMate
    (R : ℕ) (t : Finset ℕ) (x : LowWheelCofactorQuotientState) :
    LowWheelCofactorQuotientState :=
  if _hprod : x.1 * x.2 = 1 then x
  else if lowWheelCanonicalCofactorQuotientToggle x ∈
      lowWheelCanonicalPhysicalStateSet R t then
    lowWheelCanonicalCofactorQuotientToggle x
  else x

/-- Complete the largest-prime raw toggle by fixing boundary defects. -/
def lowWheelLargestOthelloMate
    (R : ℕ) (t : Finset ℕ) (x : LowWheelCofactorQuotientState) :
    LowWheelCofactorQuotientState :=
  if _hprod : x.1 * x.2 = 1 then x
  else if lowWheelLargestCofactorQuotientToggle x ∈
      lowWheelCanonicalPhysicalStateSet R t then
    lowWheelLargestCofactorQuotientToggle x
  else x

/-- Completed least mate preserves the physical carrier. -/
theorem lowWheelLeastOthelloMate_mem
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t) :
    lowWheelLeastOthelloMate R t x ∈ lowWheelCanonicalPhysicalStateSet R t := by
  unfold lowWheelLeastOthelloMate
  split_ifs with hprod hmate
  · exact hx
  · exact hmate
  · exact hx

/-- Completed largest mate preserves the physical carrier. -/
theorem lowWheelLargestOthelloMate_mem
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t) :
    lowWheelLargestOthelloMate R t x ∈ lowWheelCanonicalPhysicalStateSet R t := by
  unfold lowWheelLargestOthelloMate
  split_ifs with hprod hmate
  · exact hx
  · exact hmate
  · exact hx

/-- Completed least mate is involutive on the physical carrier. -/
theorem lowWheelLeastOthelloMate_involutive
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t) :
    lowWheelLeastOthelloMate R t (lowWheelLeastOthelloMate R t x) = x := by
  classical
  by_cases hprod : x.1 * x.2 = 1
  · simp [lowWheelLeastOthelloMate, hprod]
  · by_cases hmate : lowWheelCanonicalCofactorQuotientToggle x ∈
        lowWheelCanonicalPhysicalStateSet R t
    · have hsq := lowWheelCanonicalPhysicalStateSet_squarefree x hx
      have hinv := lowWheelCanonicalCofactorQuotientToggle_involutive hsq hprod
      have hprodMate :
          (lowWheelCanonicalCofactorQuotientToggle x).1 *
              (lowWheelCanonicalCofactorQuotientToggle x).2 ≠ 1 := by
        rw [lowWheelCanonicalCofactorQuotientToggle_product]
        exact hprod
      simp [lowWheelLeastOthelloMate, hprod, hmate, hprodMate, hinv, hx]
    · simp [lowWheelLeastOthelloMate, hprod, hmate]

/-- Completed largest mate is involutive on the physical carrier. -/
theorem lowWheelLargestOthelloMate_involutive
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (ht : t ∈ (primesUpTo R).powerset)
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t) :
    lowWheelLargestOthelloMate R t (lowWheelLargestOthelloMate R t x) = x := by
  classical
  by_cases hprod : x.1 * x.2 = 1
  · simp [lowWheelLargestOthelloMate, hprod]
  · by_cases hmate : lowWheelLargestCofactorQuotientToggle x ∈
        lowWheelCanonicalPhysicalStateSet R t
    · have hinv := lowWheelLargestCofactorQuotientToggle_involutive ht hx hprod
      have hprodMate :
          (lowWheelLargestCofactorQuotientToggle x).1 *
              (lowWheelLargestCofactorQuotientToggle x).2 ≠ 1 := by
        rw [lowWheelLargestCofactorQuotientToggle_product]
        exact hprod
      simp [lowWheelLargestOthelloMate, hprod, hmate, hprodMate, hinv, hx]
    · simp [lowWheelLargestOthelloMate, hprod, hmate]

/-- Every moved completed least state reverses the signed weight. -/
theorem lowWheelLeastOthelloMate_weight_neg
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t)
    (hne : lowWheelLeastOthelloMate R t x ≠ x) :
    canonicalMoebiusWeight (lowWheelLeastOthelloMate R t x).1 *
        (booleanCubeSign t : ℂ) =
      -(canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) := by
  unfold lowWheelLeastOthelloMate at hne ⊢
  by_cases hprod : x.1 * x.2 = 1
  · simp [hprod] at hne
  · simp only [hprod] at hne ⊢
    by_cases hmate : lowWheelCanonicalCofactorQuotientToggle x ∈
        lowWheelCanonicalPhysicalStateSet R t
    · simp only [hmate, if_true]
      exact lowWheelCanonicalCofactorQuotientToggle_weight_neg
        (lowWheelCanonicalPhysicalStateSet_squarefree x hx) hprod
    · simp [hmate] at hne

/-- Every moved completed largest state reverses the signed weight. -/
theorem lowWheelLargestOthelloMate_weight_neg
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (ht : t ∈ (primesUpTo R).powerset)
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t)
    (hne : lowWheelLargestOthelloMate R t x ≠ x) :
    canonicalMoebiusWeight (lowWheelLargestOthelloMate R t x).1 *
        (booleanCubeSign t : ℂ) =
      -(canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) := by
  unfold lowWheelLargestOthelloMate at hne ⊢
  by_cases hprod : x.1 * x.2 = 1
  · simp [hprod] at hne
  · simp only [hprod] at hne ⊢
    by_cases hmate : lowWheelLargestCofactorQuotientToggle x ∈
        lowWheelCanonicalPhysicalStateSet R t
    · simp only [hmate, if_true]
      exact lowWheelLargestCofactorQuotientToggle_weight_neg ht hx hprod
    · simp [hmate] at hne

/-- **Two-direction Othello identity on one physical face.**  Least-prime and
largest-prime play orders have exactly the same signed stable mass. -/
theorem sum_lowWheelLeastStable_eq_largestStable
    {R : ℕ} {t : Finset ℕ}
    (ht : t ∈ (primesUpTo R).powerset) :
    (∑ x ∈ finiteOthelloStablePart
        (lowWheelCanonicalPhysicalStateSet R t)
        (lowWheelLeastOthelloMate R t),
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)) =
    ∑ x ∈ finiteOthelloStablePart
        (lowWheelCanonicalPhysicalStateSet R t)
        (lowWheelLargestOthelloMate R t),
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ) := by
  exact sum_finiteOthelloStablePart_eq_of_two_involutions
    (lowWheelCanonicalPhysicalStateSet R t)
    (lowWheelLeastOthelloMate R t)
    (lowWheelLargestOthelloMate R t)
    (fun x => canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ))
    (fun x hx => lowWheelLeastOthelloMate_mem hx)
    (fun x hx => lowWheelLeastOthelloMate_involutive hx)
    (fun x hx hne => lowWheelLeastOthelloMate_weight_neg hx hne)
    (fun x hx => lowWheelLargestOthelloMate_mem hx)
    (fun x hx => lowWheelLargestOthelloMate_involutive ht hx)
    (fun x hx hne => lowWheelLargestOthelloMate_weight_neg ht hx hne)

end RHLean.Proof
