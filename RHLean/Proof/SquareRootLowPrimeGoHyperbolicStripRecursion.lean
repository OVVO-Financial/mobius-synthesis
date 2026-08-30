import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoRecursiveDescent

/-!
# Hyperbolic recursion of the signed Go liberty strips

The weighted-liberty handoff leaves one signed predecessor strip at every
prime pair `r < q`:

`-(F_{r^-}(q-1) - F_{r^-}(L(q,X,r)))`,

where

`L(q,X,r) = min (q-1) (X/(q^2*r))`.

There is an exact arithmetic split.  The lower endpoint is still unfinished at
owner `r` precisely when

`(q*r)^2 <= X`.

On that side, subtracting the recursive Go laws at the two strip endpoints
cancels the common completed anchor `M(r-1)` and descends the whole strip to
strictly smaller owners `s < r`.

Across the complementary hyperbolic wall `(q*r)^2 > X`, the lower endpoint is
already complete.  The strip is therefore one ordinary Mertens gap plus the
same signed descent through strictly smaller owners.

No norm, support bound, prime-count estimate, or asymptotic estimate is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- A frozen predecessor cube below its owner is already the complete ordinary
Mertens prefix. -/
theorem frozenPrimeUniverseMass_eq_mertensSummatoryInt_of_lt_owner
    {r Y : ℕ} (hr : r.Prime) (hY : Y < r) :
    frozenPrimeUniverseMass (primesUpTo (r - 1)) Y =
      mertensSummatoryInt Y := by
  have hrrPos : 0 < r * r := Nat.mul_pos hr.pos hr.pos
  have hcut : r * r * Y / (r * r) = Y :=
    Nat.mul_div_cancel_left Y hrrPos
  have hcomplete : r * r * Y / (r * r) < r := by
    rw [hcut]
    exact hY
  have h :=
    squareRootLowPrimeGoWallSquareResidual_eq_mertensSummatoryInt
      (q := r) (X := (r * r) * Y) hr hcomplete
  rw [squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff, hcut] at h
  exact h

/-- **Exact hyperbolic split.**  For a genuine liberty prime `r < q`, the lower
endpoint of the frozen `r`-strip is itself unfinished exactly when the physical
square `(q*r)^2` still fits below `X`. -/
theorem squareRootLowPrimeGoDefectSliceLowerCutoff_owner_le_iff_squareProduct_le
    {q X r : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q) :
    r ≤ squareRootLowPrimeGoDefectSliceLowerCutoff q X r ↔
      (q * r) ^ 2 ≤ X := by
  have hq2Pos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  constructor
  · intro hLower
    have hdiv : r ≤ X / (q * q) / r :=
      hLower.trans (by
        unfold squareRootLowPrimeGoDefectSliceLowerCutoff
        exact min_le_right _ _)
    have hrrDiv : r * r ≤ X / (q * q) :=
      (Nat.le_div_iff_mul_le hr.pos).1 hdiv
    have hmul : (r * r) * (q * q) ≤ X :=
      (Nat.le_div_iff_mul_le hq2Pos).1 hrrDiv
    calc
      (q * r) ^ 2 = (r * r) * (q * q) := by ring
      _ ≤ X := hmul
  · intro hsquare
    have hmul : (r * r) * (q * q) ≤ X := by
      calc
        (r * r) * (q * q) = (q * r) ^ 2 := by ring
        _ ≤ X := hsquare
    have hrrDiv : r * r ≤ X / (q * q) :=
      (Nat.le_div_iff_mul_le hq2Pos).2 hmul
    have hdiv : r ≤ X / (q * q) / r :=
      (Nat.le_div_iff_mul_le hr.pos).2 hrrDiv
    unfold squareRootLowPrimeGoDefectSliceLowerCutoff
    exact le_min (by omega) hdiv

/-- Subtract two unfinished states belonging to the same owner `r`.  The common
`M(r-1)` anchor and the common lower anchors cancel identically, leaving only a
signed sum of strips with strictly smaller owner `s < r`. -/
theorem frozenPrimeUniverseMass_sub_eq_neg_smallerOwnerStripSum
    {r U L : ℕ} (hr : r.Prime) (hU : r ≤ U) (hL : r ≤ L) :
    frozenPrimeUniverseMass (primesUpTo (r - 1)) U -
        frozenPrimeUniverseMass (primesUpTo (r - 1)) L =
      -∑ s ∈ primesUpTo (r - 1),
        (frozenPrimeUniverseMass (primesUpTo (s - 1)) (U / s) -
          frozenPrimeUniverseMass (primesUpTo (s - 1)) (L / s)) := by
  rw [frozenPrimeUniverseMass_eq_mertensPred_sub_smallerOwnerStrips hr hU,
    frozenPrimeUniverseMass_eq_mertensPred_sub_smallerOwnerStrips hr hL]
  simp only [Finset.sum_sub_distrib]
  ring

/-- If the lower endpoint has crossed below owner `r`, it is already an ordinary
Mertens prefix.  The remaining unfinished upper state still descends only
through strictly smaller owners. -/
theorem frozenPrimeUniverseMass_sub_eq_mertensGap_sub_smallerOwnerStrips
    {r U L : ℕ} (hr : r.Prime) (hU : r ≤ U) (hL : L < r) :
    frozenPrimeUniverseMass (primesUpTo (r - 1)) U -
        frozenPrimeUniverseMass (primesUpTo (r - 1)) L =
      (mertensSummatoryInt (r - 1) - mertensSummatoryInt L) -
        ∑ s ∈ primesUpTo (r - 1),
          (frozenPrimeUniverseMass (primesUpTo (s - 1)) (U / s) -
            frozenPrimeUniverseMass (primesUpTo (s - 1)) ((r - 1) / s)) := by
  rw [frozenPrimeUniverseMass_eq_mertensPred_sub_smallerOwnerStrips hr hU,
    frozenPrimeUniverseMass_eq_mertensSummatoryInt_of_lt_owner hr hL]
  ring

/-- **Interior liberty recursion.**  Below the hyperbolic wall `(q*r)^2 <= X`,
one whole fixed-`r` source strip descends with its sign intact to a sum of
strictly smaller-owner strips.  No absolute value is introduced. -/
theorem squareRootLowPrimeGoFrozenLibertyStripContribution_eq_smallerOwnerStrips_of_squareProduct_le
    {q X r : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hsquare : (q * r) ^ 2 ≤ X) :
    squareRootLowPrimeGoFrozenLibertyStripContribution q X r =
      ∑ s ∈ primesUpTo (r - 1),
        (frozenPrimeUniverseMass (primesUpTo (s - 1)) ((q - 1) / s) -
          frozenPrimeUniverseMass (primesUpTo (s - 1))
            (squareRootLowPrimeGoDefectSliceLowerCutoff q X r / s)) := by
  have hUpper : r ≤ q - 1 := by omega
  have hLower : r ≤ squareRootLowPrimeGoDefectSliceLowerCutoff q X r :=
    (squareRootLowPrimeGoDefectSliceLowerCutoff_owner_le_iff_squareProduct_le
      hq hr hrq).2 hsquare
  have hrec :=
    frozenPrimeUniverseMass_sub_eq_neg_smallerOwnerStripSum hr hUpper hLower
  unfold squareRootLowPrimeGoFrozenLibertyStripContribution
  rw [hrec]
  ring

/-- **Crossing liberty recursion.**  Above the hyperbolic wall `(q*r)^2 > X`,
the lower endpoint has completed.  The source strip is exactly a completed
Mertens gap plus one signed sum of strips with owner `s < r`. -/
theorem squareRootLowPrimeGoFrozenLibertyStripContribution_eq_neg_mertensGap_add_smallerOwnerStrips_of_crossing
    {q X r : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcross : X < (q * r) ^ 2) :
    squareRootLowPrimeGoFrozenLibertyStripContribution q X r =
      -(mertensSummatoryInt (r - 1) -
          mertensSummatoryInt
            (squareRootLowPrimeGoDefectSliceLowerCutoff q X r)) +
        ∑ s ∈ primesUpTo (r - 1),
          (frozenPrimeUniverseMass (primesUpTo (s - 1)) ((q - 1) / s) -
            frozenPrimeUniverseMass (primesUpTo (s - 1)) ((r - 1) / s)) := by
  have hUpper : r ≤ q - 1 := by omega
  have hLower : squareRootLowPrimeGoDefectSliceLowerCutoff q X r < r := by
    have hnotSquare : ¬ (q * r) ^ 2 ≤ X := Nat.not_le_of_gt hcross
    have hnotLower : ¬ r ≤ squareRootLowPrimeGoDefectSliceLowerCutoff q X r := by
      intro hLower
      exact hnotSquare
        ((squareRootLowPrimeGoDefectSliceLowerCutoff_owner_le_iff_squareProduct_le
          hq hr hrq).1 hLower)
    omega
  have hrec :=
    frozenPrimeUniverseMass_sub_eq_mertensGap_sub_smallerOwnerStrips
      hr hUpper hLower
  unfold squareRootLowPrimeGoFrozenLibertyStripContribution
  rw [hrec]
  ring

end RHLean.Proof
