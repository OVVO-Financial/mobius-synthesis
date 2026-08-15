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

The second half of this module upgrades that local toggle to a complete
one-coordinate truncated-cube cancellation inside each residue class.  Thus a
square-one pivot collapses the residue-conditioned survivor cube to explicit
first-failure frontiers.  At modulus `2`, the single pivot prime `3` works for
every upper-prime face with `q >= 5`.

No activity estimate or power saving is claimed here.
-/

noncomputable section

open scoped BigOperators

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

/-- Alternating mass of an admissible prime-face population after restricting to
one signed-height residue class. -/
noncomputable def residueConditionedCubeAlternatingSum
    (modulus q : ℕ) (r : ZMod modulus)
    (ambient : Finset ℕ) (admissible : Finset ℕ → Prop) : ℤ := by
  classical
  exact ∑ u ∈ ambient.powerset,
    if admissible u ∧
        survivorHeightResidue modulus (primeFaceProduct u) q = r then
      booleanCubeSign u
    else 0

/-- Residue-conditioned alternating mass on one first-failure boundary. -/
noncomputable def residueConditionedFirstFailureBoundaryAlternatingSum
    (modulus q : ℕ) (r : ZMod modulus)
    (ambient : Finset ℕ) (ell : ℕ)
    (admissible : Finset ℕ → Prop) : ℤ := by
  classical
  exact ∑ u ∈ firstFailureBoundary ambient ell admissible,
    if survivorHeightResidue modulus (primeFaceProduct u) q = r then
      booleanCubeSign u
    else 0

/-- One-coordinate truncated-cube cancellation remains exact after conditioning
on a survivor height residue, provided the selected coordinate is square-one
modulo the residue modulus. -/
theorem residueConditionedCubeAlternatingSum_eq_firstFailureBoundary
    (modulus q : ℕ) (r : ZMod modulus)
    {ambient : Finset ℕ} {ell : ℕ} {admissible : Finset ℕ → Prop}
    (hell : ell ∈ ambient)
    (hdown : CubeDownwardClosed admissible)
    (hsq : (ell : ZMod modulus) ^ 2 = 1) :
    residueConditionedCubeAlternatingSum modulus q r ambient admissible =
      residueConditionedFirstFailureBoundaryAlternatingSum
        modulus q r ambient ell admissible := by
  classical
  have hdecomp : ambient = insert ell (ambient.erase ell) := by
    exact (Finset.insert_erase hell).symm
  unfold residueConditionedCubeAlternatingSum
  calc
    (∑ u ∈ ambient.powerset,
        if admissible u ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0) =
      ∑ u ∈ (insert ell (ambient.erase ell)).powerset,
        if admissible u ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0 := by
          rw [← hdecomp]
    _ =
      (∑ u ∈ (ambient.erase ell).powerset,
        if admissible u ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0) +
      ∑ u ∈ (ambient.erase ell).powerset,
        if admissible (insert ell u) ∧
            survivorHeightResidue modulus
              (primeFaceProduct (insert ell u)) q = r then
          booleanCubeSign (insert ell u)
        else 0 := by
          rw [Finset.sum_powerset_insert (Finset.notMem_erase ell ambient)]
    _ =
      ∑ u ∈ (ambient.erase ell).powerset,
        ((if admissible u ∧
              survivorHeightResidue modulus (primeFaceProduct u) q = r then
            booleanCubeSign u
          else 0) +
        (if admissible (insert ell u) ∧
              survivorHeightResidue modulus
                (primeFaceProduct (insert ell u)) q = r then
            booleanCubeSign (insert ell u)
          else 0)) := by
            rw [Finset.sum_add_distrib]
    _ =
      ∑ u ∈ (ambient.erase ell).powerset,
        if admissible u ∧ ¬ admissible (insert ell u) ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0 := by
          apply Finset.sum_congr rfl
          intro u hu
          have hfresh : ell ∉ u :=
            Finset.notMem_of_mem_powerset_of_notMem
              hu (Finset.notMem_erase ell ambient)
          have hres :=
            survivor_primeFace_residue_iff_insert_of_sq_eq_one
              modulus ell q u r hfresh hsq
          by_cases hchild : admissible (insert ell u)
          · have hparent : admissible u :=
              hdown u (insert ell u) (Finset.subset_insert ell u) hchild
            by_cases hr :
                survivorHeightResidue modulus (primeFaceProduct u) q = r
            · have hrChild :
                  survivorHeightResidue modulus
                    (primeFaceProduct (insert ell u)) q = r := hres.mpr hr
              simp [hchild, hparent, hr, hrChild, booleanCubeSign,
                Finset.card_insert_of_notMem, hfresh, pow_succ]
            · have hrChild :
                  survivorHeightResidue modulus
                    (primeFaceProduct (insert ell u)) q ≠ r := by
                intro h
                exact hr (hres.mp h)
              simp [hchild, hparent, hr, hrChild]
          · by_cases hparent : admissible u
            · by_cases hr :
                  survivorHeightResidue modulus (primeFaceProduct u) q = r
              · simp [hchild, hparent, hr]
              · simp [hchild, hparent, hr]
            · simp [hchild, hparent]
    _ = residueConditionedFirstFailureBoundaryAlternatingSum
          modulus q r ambient ell admissible := by
      unfold residueConditionedFirstFailureBoundaryAlternatingSum
        firstFailureBoundary
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _hu
      by_cases hparent : admissible u
      · by_cases hchild : admissible (insert ell u)
        · simp [hparent, hchild]
        · by_cases hr :
            survivorHeightResidue modulus (primeFaceProduct u) q = r
          · simp [hparent, hchild, hr]
          · simp [hparent, hchild, hr]
      · simp [hparent]

/-- Residue-conditioned alternating mass of the complete survivor high selector
in one distinguished-prime face cube. -/
noncomputable def survivorPrimeFaceResidueHighAlternatingMass
    (Λ : ℝ) (t q modulus : ℕ) (r : ZMod modulus) : ℤ :=
  residueConditionedCubeAlternatingSum modulus q r
    (survivorPrimeFaceAmbient q) (survivorPrimeFaceHigh Λ t q)

/-- The V-shaped survivor selector decomposes inside each residue fibre into the
same transport, product, and below-smooth pieces as in the unconditioned cube. -/
theorem survivorPrimeFaceResidueHigh_alternatingMass_decomposition
    (Λ : ℝ) (t q modulus : ℕ) (r : ZMod modulus) (hΛ : 0 ≤ Λ) :
    survivorPrimeFaceResidueHighAlternatingMass Λ t q modulus r =
      residueConditionedCubeAlternatingSum modulus q r
        (survivorPrimeFaceAmbient q) (survivorPrimeFaceTransportPrefix Λ t q) +
      residueConditionedCubeAlternatingSum modulus q r
        (survivorPrimeFaceAmbient q) (survivorPrimeFaceProductPrefix t q) -
      residueConditionedCubeAlternatingSum modulus q r
        (survivorPrimeFaceAmbient q) (survivorPrimeFaceBelowSmoothPrefix Λ t q) := by
  classical
  unfold survivorPrimeFaceResidueHighAlternatingMass
    residueConditionedCubeAlternatingSum
  calc
    (∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        if survivorPrimeFaceHigh Λ t q u ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0) =
      ∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        ((if survivorPrimeFaceTransportPrefix Λ t q u ∧
              survivorHeightResidue modulus (primeFaceProduct u) q = r then
            booleanCubeSign u
          else 0) +
        (if survivorPrimeFaceProductPrefix t q u ∧
              survivorHeightResidue modulus (primeFaceProduct u) q = r then
            booleanCubeSign u
          else 0) -
        (if survivorPrimeFaceBelowSmoothPrefix Λ t q u ∧
              survivorHeightResidue modulus (primeFaceProduct u) q = r then
            booleanCubeSign u
          else 0)) := by
            apply Finset.sum_congr rfl
            intro u _hu
            by_cases hr :
                survivorHeightResidue modulus (primeFaceProduct u) q = r
            · have hind :=
                survivorPrimeFaceHigh_indicator_decomposition Λ t q u hΛ
              unfold survivorPrimeFaceIndicator at hind
              have hscaled := congrArg (fun z : ℤ => z * booleanCubeSign u) hind
              simpa [hr, add_mul, sub_mul] using hscaled
            · simp [hr]
    _ =
      (∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        if survivorPrimeFaceTransportPrefix Λ t q u ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0) +
      (∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        if survivorPrimeFaceProductPrefix t q u ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0) -
      (∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        if survivorPrimeFaceBelowSmoothPrefix Λ t q u ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- **Residue-fibre three-frontier cancellation.**  A square-one selected prime
coordinate cancels every interior parent/child pair inside the same survivor
height residue. -/
theorem survivorPrimeFaceResidueHigh_alternatingMass_eq_threeFrontiers
    (Λ : ℝ) (t q modulus ell : ℕ) (r : ZMod modulus)
    (hΛ : 0 ≤ Λ)
    (hell : ell ∈ survivorPrimeFaceAmbient q)
    (hsq : (ell : ZMod modulus) ^ 2 = 1) :
    survivorPrimeFaceResidueHighAlternatingMass Λ t q modulus r =
      residueConditionedFirstFailureBoundaryAlternatingSum modulus q r
        (survivorPrimeFaceAmbient q) ell
        (survivorPrimeFaceTransportPrefix Λ t q) +
      residueConditionedFirstFailureBoundaryAlternatingSum modulus q r
        (survivorPrimeFaceAmbient q) ell
        (survivorPrimeFaceProductPrefix t q) -
      residueConditionedFirstFailureBoundaryAlternatingSum modulus q r
        (survivorPrimeFaceAmbient q) ell
        (survivorPrimeFaceBelowSmoothPrefix Λ t q) := by
  rw [survivorPrimeFaceResidueHigh_alternatingMass_decomposition
    Λ t q modulus r hΛ]
  rw [residueConditionedCubeAlternatingSum_eq_firstFailureBoundary
      modulus q r hell (survivorPrimeFaceTransportPrefix_downward Λ t q) hsq,
    residueConditionedCubeAlternatingSum_eq_firstFailureBoundary
      modulus q r hell (survivorPrimeFaceProductPrefix_downward t q) hsq,
    residueConditionedCubeAlternatingSum_eq_firstFailureBoundary
      modulus q r hell (survivorPrimeFaceBelowSmoothPrefix_downward Λ t q) hsq]

/-- At parity modulus `2`, the single pivot prime `3` works in every face with
upper coordinate at least `5`.  Thus all such residue fibres collapse to three
first-failure frontiers at one common coordinate. -/
theorem survivorPrimeFaceParityHigh_alternatingMass_eq_threeFrontiers_at_three
    (Λ : ℝ) (t q : ℕ) (r : ZMod 2)
    (hΛ : 0 ≤ Λ) (hq : 5 ≤ q) :
    survivorPrimeFaceResidueHighAlternatingMass Λ t q 2 r =
      residueConditionedFirstFailureBoundaryAlternatingSum 2 q r
        (survivorPrimeFaceAmbient q) 3
        (survivorPrimeFaceTransportPrefix Λ t q) +
      residueConditionedFirstFailureBoundaryAlternatingSum 2 q r
        (survivorPrimeFaceAmbient q) 3
        (survivorPrimeFaceProductPrefix t q) -
      residueConditionedFirstFailureBoundaryAlternatingSum 2 q r
        (survivorPrimeFaceAmbient q) 3
        (survivorPrimeFaceBelowSmoothPrefix Λ t q) := by
  apply survivorPrimeFaceResidueHigh_alternatingMass_eq_threeFrontiers
    Λ t q 2 3 r hΛ
  · unfold survivorPrimeFaceAmbient
    exact mem_primesUpTo.mpr ⟨by norm_num, by omega⟩
  · native_decide

end RHLean.Proof
