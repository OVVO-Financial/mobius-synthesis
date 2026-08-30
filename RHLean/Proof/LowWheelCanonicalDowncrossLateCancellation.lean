import Mathlib
import RHLean.Proof.LowWheelCanonicalDowncrossLatePairing

/-!
# Exact cancellation of late-parent downcross multiplicity

The canonical late-parent mate from
`LowWheelCanonicalDowncrossLatePairing` moves the largest prime divisor of the
root-side parent between the Boolean face and the residual quotient.  This file
proves that the move preserves the parent itself.  Consequently it preserves
the canonical allocation prime and the full late-parent condition.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open LowWheelCanonicalDowncrossOwnership

attribute [local instance] Classical.propDecidable

/-- The original pivot divides the quotient coordinate after the late-parent
allocation move. -/
theorem lowWheelCanonicalDowncrossLateMate_pivot_dvd_quotient
    {R : ℕ} {t : Finset ℕ} {c k : ℕ}
    (hy : (t, (c, k)) ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    lowWheelCanonicalDowncrossPivot (c, k) ∣
      (lowWheelCanonicalDowncrossLateMate (t, (c, k))).2.2 := by
  let p := lowWheelCanonicalDowncrossPivot (c, k)
  let q := lowWheelCanonicalDowncrossLatePrime (t, (c, k))
  have hlate :=
    (mem_lowWheelCanonicalDowncrossLateTaggedCarrier.mp hy).2.2
  have hdown := (mem_lowWheelCanonicalDowncrossLateParentPart.mp hlate).1
  have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hdown
  dsimp only at hgeom
  have hpk : p ∣ k := by simpa [p] using hgeom.2.2.1
  unfold lowWheelCanonicalDowncrossLateMate
  dsimp only
  by_cases hqt : q ∈ t
  · rw [if_pos hqt]
    exact dvd_mul_of_dvd_right hpk q
  · rw [if_neg hqt]
    have hqu : q ∣ k / p := by
      simpa [p, q] using
        lowWheelCanonicalDowncrossLatePrime_dvd_quotient_of_not_mem_face
          hy (by simpa [q] using hqt)
    rcases hqu with ⟨u, hu⟩
    have hkEq : k = q * (p * u) := by
      calc
        k = p * (k / p) := (Nat.mul_div_cancel' hpk).symm
        _ = p * (q * u) := by rw [hu]
        _ = q * (p * u) := by ring
    have hkDivEq : k / q = p * u := by
      have hqPrime : q.Prime := by
        simpa [q] using lowWheelCanonicalDowncrossLatePrime_prime hy
      rw [hkEq]
      simp [hqPrime.ne_zero]
    exact ⟨u, hkDivEq⟩

/-- Multiplying the root-side parent by its pivot reconstructs the complete high
coordinate `P(t)*k`. -/
theorem lowWheelCanonicalDowncross_pivot_mul_parent_eq_highProduct
    {R c k : ℕ} {t : Finset ℕ}
    (hx : (c, k) ∈ lowWheelCanonicalDowncrossPart R t) :
    lowWheelCanonicalDowncrossPivot (c, k) *
        lowWheelCanonicalDowncrossParent t (c, k) =
      primeFaceProduct t * k := by
  have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hx
  dsimp only at hgeom
  have hpk := hgeom.2.2.1
  unfold lowWheelCanonicalDowncrossParent
  calc
    lowWheelCanonicalDowncrossPivot (c, k) *
        (primeFaceProduct t * (k / lowWheelCanonicalDowncrossPivot (c, k))) =
      primeFaceProduct t *
        (lowWheelCanonicalDowncrossPivot (c, k) *
          (k / lowWheelCanonicalDowncrossPivot (c, k))) := by ring
    _ = primeFaceProduct t * k := by rw [Nat.mul_div_cancel' hpk]

/-- The root-side parent is exactly invariant under the canonical late-parent
allocation move. -/
theorem lowWheelCanonicalDowncrossLateMate_parent_eq
    {R : ℕ} {t : Finset ℕ} {c k : ℕ}
    (hy : (t, (c, k)) ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    lowWheelCanonicalDowncrossTaggedParent
        (lowWheelCanonicalDowncrossLateMate (t, (c, k))) =
      lowWheelCanonicalDowncrossTaggedParent (t, (c, k)) := by
  let p := lowWheelCanonicalDowncrossPivot (c, k)
  have hp :=
    lowWheelCanonicalDowncrossLatePrime_prime hy
  have hpivotPrime : p.Prime := by
    have hlate :=
      (mem_lowWheelCanonicalDowncrossLateTaggedCarrier.mp hy).2.2
    have hdown := (mem_lowWheelCanonicalDowncrossLateParentPart.mp hlate).1
    have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hdown
    simpa [p] using hgeom.1
  have hpivotEq := lowWheelCanonicalDowncrossLateMate_pivot_eq hy
  have hpDvdMate := lowWheelCanonicalDowncrossLateMate_pivot_dvd_quotient hy
  have hlate :=
    (mem_lowWheelCanonicalDowncrossLateTaggedCarrier.mp hy).2.2
  have hdown := (mem_lowWheelCanonicalDowncrossLateParentPart.mp hlate).1
  have hold := lowWheelCanonicalDowncross_pivot_mul_parent_eq_highProduct hdown
  have hnew :
      p * lowWheelCanonicalDowncrossTaggedParent
          (lowWheelCanonicalDowncrossLateMate (t, (c, k))) =
        primeFaceProduct (lowWheelCanonicalDowncrossLateMate (t, (c, k))).1 *
          (lowWheelCanonicalDowncrossLateMate (t, (c, k))).2.2 := by
    unfold lowWheelCanonicalDowncrossTaggedParent
      lowWheelCanonicalDowncrossParent
    rw [hpivotEq]
    calc
      p * (primeFaceProduct (lowWheelCanonicalDowncrossLateMate (t, (c, k))).1 *
          ((lowWheelCanonicalDowncrossLateMate (t, (c, k))).2.2 / p)) =
        primeFaceProduct (lowWheelCanonicalDowncrossLateMate (t, (c, k))).1 *
          (p * ((lowWheelCanonicalDowncrossLateMate (t, (c, k))).2.2 / p)) := by ring
      _ = primeFaceProduct (lowWheelCanonicalDowncrossLateMate (t, (c, k))).1 *
          (lowWheelCanonicalDowncrossLateMate (t, (c, k))).2.2 := by
            rw [Nat.mul_div_cancel' hpDvdMate]
  have hhigh := lowWheelCanonicalDowncrossLateMate_highProduct hy
  have hmul :
      p * lowWheelCanonicalDowncrossTaggedParent
          (lowWheelCanonicalDowncrossLateMate (t, (c, k))) =
        p * lowWheelCanonicalDowncrossTaggedParent (t, (c, k)) := by
    calc
      p * lowWheelCanonicalDowncrossTaggedParent
          (lowWheelCanonicalDowncrossLateMate (t, (c, k))) =
        primeFaceProduct (lowWheelCanonicalDowncrossLateMate (t, (c, k))).1 *
          (lowWheelCanonicalDowncrossLateMate (t, (c, k))).2.2 := hnew
      _ = primeFaceProduct t * k := hhigh
      _ = p * lowWheelCanonicalDowncrossTaggedParent (t, (c, k)) := by
        simpa [p, lowWheelCanonicalDowncrossTaggedParent] using hold.symm
  exact Nat.eq_of_mul_eq_mul_left hpivotPrime.pos hmul

/-- Hence the canonical late-parent prime selected for the second move is the
same prime selected for the first move. -/
theorem lowWheelCanonicalDowncrossLateMate_prime_eq
    {R : ℕ} {t : Finset ℕ} {c k : ℕ}
    (hy : (t, (c, k)) ∈ lowWheelCanonicalDowncrossLateTaggedCarrier R) :
    lowWheelCanonicalDowncrossLatePrime
        (lowWheelCanonicalDowncrossLateMate (t, (c, k))) =
      lowWheelCanonicalDowncrossLatePrime (t, (c, k)) := by
  unfold lowWheelCanonicalDowncrossLatePrime
  rw [lowWheelCanonicalDowncrossLateMate_parent_eq hy]

end RHLean.Proof