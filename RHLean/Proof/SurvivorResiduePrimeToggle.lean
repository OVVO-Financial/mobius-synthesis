import Mathlib
import RHLean.Arithmetic.PrimeFaceMoebius
import RHLean.Proof.SurvivorPrimeFaceFrontier
import RHLean.Proof.SurvivorResidueCovariance

/-!
# Survivor residue transport under prime-face toggles

This module records the exact local mechanism linking the prime-face Möbius
cancellation to the residue-fibre covariance.

If a fresh prime coordinate `ell` is inserted into a cofactor face, the
cofactor is multiplied by `ell`, its Boolean/Möbius sign reverses, and its
signed height residue transforms affinely by

```text
u |-> ell^2 * u + (1-ell^2) * q^2.
```

In particular, whenever `ell^2 = 1` in `ZMod s`, the height residue is preserved
exactly while the sign flips.  Therefore matched parent/child sources along such
a coordinate cancel inside the same residue fibre, not merely after summing all
residues.

No activity estimate or power saving is claimed here.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Exact affine transport law for the signed survivor height residue under
cofactor dilation. -/
theorem survivorHeightResidue_mul_left_affine
    (s ell c q : ℕ) :
    survivorHeightResidue s (ell * c) q =
      ((ell : ZMod s) ^ 2) * survivorHeightResidue s c q +
        (1 - (ell : ZMod s) ^ 2) * (q : ZMod s) ^ 2 := by
  unfold survivorHeightResidue survivorHeightDifference
  push_cast
  ring

/-- A square-one cofactor multiplier preserves the signed height residue. -/
theorem survivorHeightResidue_mul_left_eq_of_sq_eq_one
    (s ell c q : ℕ)
    (hell : (ell : ZMod s) ^ 2 = 1) :
    survivorHeightResidue s (ell * c) q =
      survivorHeightResidue s c q := by
  rw [survivorHeightResidue_mul_left_affine, hell]
  ring

/-- Inserting a fresh prime-face coordinate multiplies the represented cofactor
by that prime. -/
theorem primeFaceProduct_insert_fresh
    (ell : ℕ) (u : Finset ℕ) (hell : ell ∉ u) :
    primeFaceProduct (insert ell u) = ell * primeFaceProduct u := by
  unfold primeFaceProduct
  simp [Finset.prod_insert, hell]

/-- The Boolean/Möbius face sign reverses when a fresh prime coordinate is
inserted. -/
theorem booleanCubeSign_insert_fresh
    (ell : ℕ) (u : Finset ℕ) (hell : ell ∉ u) :
    booleanCubeSign (insert ell u) = - booleanCubeSign u := by
  unfold booleanCubeSign
  rw [Finset.card_insert_of_notMem hell, pow_succ]
  ring

/-- Exact affine residue transport directly on prime faces. -/
theorem survivorHeightResidue_primeFace_insert_affine
    (s ell q : ℕ) (u : Finset ℕ) (hell : ell ∉ u) :
    survivorHeightResidue s (primeFaceProduct (insert ell u)) q =
      ((ell : ZMod s) ^ 2) *
          survivorHeightResidue s (primeFaceProduct u) q +
        (1 - (ell : ZMod s) ^ 2) * (q : ZMod s) ^ 2 := by
  rw [primeFaceProduct_insert_fresh ell u hell]
  exact survivorHeightResidue_mul_left_affine s ell (primeFaceProduct u) q

/-- **Residue-preserving sign toggle.**  A fresh face coordinate whose square is
one modulo `s` leaves the survivor height residue unchanged while reversing the
Boolean sign. -/
theorem survivor_primeFace_toggle_preserves_residue_and_flips_sign
    (s ell q : ℕ) (u : Finset ℕ) (hfresh : ell ∉ u)
    (hsq : (ell : ZMod s) ^ 2 = 1) :
    survivorHeightResidue s (primeFaceProduct (insert ell u)) q =
        survivorHeightResidue s (primeFaceProduct u) q ∧
      booleanCubeSign (insert ell u) = - booleanCubeSign u := by
  constructor
  · rw [primeFaceProduct_insert_fresh ell u hfresh]
    exact survivorHeightResidue_mul_left_eq_of_sq_eq_one
      s ell (primeFaceProduct u) q hsq
  · exact booleanCubeSign_insert_fresh ell u hfresh

/-- Consequently a residue test is invariant under a square-one fresh prime
coordinate.  This is the exact predicate-level fact needed to pair terms inside
a fixed residue fibre. -/
theorem survivor_primeFace_residue_iff_insert_of_sq_eq_one
    (s ell q : ℕ) (u : Finset ℕ) (r : ZMod s)
    (hfresh : ell ∉ u) (hsq : (ell : ZMod s) ^ 2 = 1) :
    survivorHeightResidue s (primeFaceProduct (insert ell u)) q = r ↔
      survivorHeightResidue s (primeFaceProduct u) q = r := by
  rw [(survivor_primeFace_toggle_preserves_residue_and_flips_sign
    s ell q u hfresh hsq).1]

end RHLean.Proof
