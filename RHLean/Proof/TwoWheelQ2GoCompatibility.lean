import Mathlib
import RHLean.Analysis.TwoWheelQ2Compensation
import RHLean.Proof.SquareRootLowPrimeGoRecursiveDescent
import RHLean.Proof.PrimeWheelProperSubwheelDepthTwo

/-!
# Go / recovered q-square compatibility

The algebraic recovered packet really is q-square self-similar, but the literal
Go daughter at owner `q` is a different object: the frozen predecessor-prime
cube `F_{q^-}(X/q^2)`.  This module records the exact compatibility defect.

There are two regimes.

* If `X/q^2 < q`, the predecessor cube is already complete at the daughter
  cutoff and the Go daughter is ordinary Mertens exactly.
* If `q <= X/q^2`, the difference from ordinary Mertens is an explicit Mertens
  increment plus the already-compiled smaller-owner Go strips.  Equivalently,
  and more usefully for the two-wheel bookkeeping, it is exactly the negative
  high-prime transport column above `q-1` at the daughter scale.

Thus the compatibility term predicted at the boundary between the CRT blocker
wheel and the full recovery wheel is not a new probabilistic or analytic error:
it is the existing signed high-transport coordinate.  It must stay attached to
the local block before a norm is taken.

This is finite exact bookkeeping; no estimate is introduced.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- Difference between the full recovered/Mertens q-square daughter and the
literal Go predecessor-cube daughter. -/
def q2GoRecoveredCompatibilityDefect (q X : ℕ) : ℤ :=
  mertensSummatoryInt (X / (q * q)) -
    squareRootLowPrimeGoWallSquareResidual q X

/-- **Completed daughter compatibility.**  Once the q-square cutoff is below
its owner, the two daughter notions agree identically. -/
theorem q2GoRecoveredCompatibilityDefect_eq_zero_of_complete
    {q X : ℕ} (hq : q.Prime) (hcomplete : X / (q * q) < q) :
    q2GoRecoveredCompatibilityDefect q X = 0 := by
  unfold q2GoRecoveredCompatibilityDefect
  rw [squareRootLowPrimeGoWallSquareResidual_eq_mertensSummatoryInt
    hq hcomplete]
  ring

/-- **Unfinished daughter compatibility formula.**  When the daughter cutoff
has not yet fallen below `q`, the exact obstruction to replacing the literal Go
daughter by full Mertens is a Mertens increment plus the smaller-owner frozen
strips.  Nothing is discarded or renamed as endpoint error. -/
theorem q2GoRecoveredCompatibilityDefect_eq_increment_add_smallerOwnerStrips
    {q X : ℕ} (hq : q.Prime) (hunfinished : q ≤ X / (q * q)) :
    q2GoRecoveredCompatibilityDefect q X =
      (mertensSummatoryInt (X / (q * q)) - mertensSummatoryInt (q - 1)) +
        ∑ r ∈ primesUpTo (q - 1),
          (frozenPrimeUniverseMass (primesUpTo (r - 1))
              ((X / (q * q)) / r) -
            frozenPrimeUniverseMass (primesUpTo (r - 1)) ((q - 1) / r)) := by
  unfold q2GoRecoveredCompatibilityDefect
  rw [squareRootLowPrimeGoWallSquareResidual_eq_mertensPred_sub_smallerOwnerStrips
    hq hunfinished]
  ring

/-- **The predicted two-wheel compatibility term is exactly high transport.**
At daughter scale `Y=X/q^2`, the proper-subwheel identity stopped at `q-1`
says

`M(Y) = F_{q^-}(Y) - highTransport_{q..Y}(Y)`.

Since the literal Go square residual is precisely `F_{q^-}(Y)`, their difference
is the negative high-prime column.  This is the daughter-scale `S = A - T`
identity in the exact coordinates already present in the repository. -/
theorem q2GoRecoveredCompatibilityDefect_eq_neg_highOwnerColumn
    {q X : ℕ} (hcut : q - 1 ≤ X / (q * q)) :
    q2GoRecoveredCompatibilityDefect q X =
      -∑ p ∈ frozenPrimeUniverseHighPrimeSet (q - 1) (X / (q * q)),
        frozenPrimeUniverseMass (primesUpTo (p - 1))
          ((X / (q * q)) / p) := by
  let Y := X / (q * q)
  have hproper :=
    mertensSummatoryInt_eq_properSubwheel_sub_highOwnerColumn Y (q - 1) hcut
  unfold q2GoRecoveredCompatibilityDefect
  rw [squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff]
  change
    mertensSummatoryInt Y -
        frozenPrimeUniverseMass (primesUpTo (q - 1)) Y = _
  rw [hproper]
  ring

/-- Rearranged local form: a literal Go daughter becomes the full recovered
Mertens daughter only after its high-prime transport is retained with the same
sign.  This is the exact compatibility lemma needed by LOCAL-BLOCK. -/
theorem mertensDaughter_eq_goDaughter_sub_highOwnerColumn
    {q X : ℕ} (hcut : q - 1 ≤ X / (q * q)) :
    mertensSummatoryInt (X / (q * q)) =
      squareRootLowPrimeGoWallSquareResidual q X -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet (q - 1) (X / (q * q)),
          frozenPrimeUniverseMass (primesUpTo (p - 1))
            ((X / (q * q)) / p) := by
  have h := q2GoRecoveredCompatibilityDefect_eq_neg_highOwnerColumn
    (q := q) (X := X) hcut
  unfold q2GoRecoveredCompatibilityDefect at h
  linarith

/-- For owner 3 the predecessor cube is already a complete nonempty Boolean
cube as soon as the q-square daughter cutoff is at least 2, hence the literal
Go residual vanishes exactly. -/
theorem squareRootLowPrimeGoWallSquareResidual_three_eq_zero
    {X : ℕ} (hcut : 2 ≤ X / (3 * 3)) :
    squareRootLowPrimeGoWallSquareResidual 3 X = 0 := by
  rw [squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff]
  apply frozenPrimeUniverseMass_eq_zero_of_complete_old_cube
  · refine ⟨2, ?_⟩
    exact mem_primesUpTo.mpr ⟨Nat.prime_two, by norm_num⟩
  · intro p hp
    exact prime_of_mem_primesUpTo hp
  · have hprod : primeFaceProduct (primesUpTo (3 - 1)) = 2 := by
      native_decide
    rw [hprod]
    exact hcut

/-- Therefore, in the long q=3 regime the entire compatibility defect is the
full lower-scale Mertens value.  In particular it is not an `O(1)` CRT endpoint
artifact generated by the local 3^2 coordinate. -/
theorem q2GoRecoveredCompatibilityDefect_three_eq_mertens
    {X : ℕ} (hcut : 2 ≤ X / (3 * 3)) :
    q2GoRecoveredCompatibilityDefect 3 X =
      mertensSummatoryInt (X / (3 * 3)) := by
  unfold q2GoRecoveredCompatibilityDefect
  rw [squareRootLowPrimeGoWallSquareResidual_three_eq_zero hcut]
  ring

/-- **Prime-three stress test.**  Once `Y=X/9` is at least two, the entire full
Mertens daughter is the negative high-prime transport above the predecessor
cutoff `2`.  Thus a correct q=3 LOCAL-BLOCK must carry this whole transport
inside its compensation; the square-contact Go residual itself contributes
zero. -/
theorem q2HighOwnerColumn_three_eq_neg_mertens
    {X : ℕ} (hcut : 2 ≤ X / (3 * 3)) :
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet 2 (X / (3 * 3)),
        frozenPrimeUniverseMass (primesUpTo (p - 1))
          ((X / (3 * 3)) / p)) =
      -mertensSummatoryInt (X / (3 * 3)) := by
  have hcompat :=
    q2GoRecoveredCompatibilityDefect_eq_neg_highOwnerColumn
      (q := 3) (X := X) hcut
  have hmertens := q2GoRecoveredCompatibilityDefect_three_eq_mertens hcut
  rw [hmertens] at hcompat
  linarith

/-- Concrete certificate at the first square stage where this distinction is
visible: at `X = 35 = 6^2-1`, the literal q=3 Go daughter is zero while the full
Mertens daughter at cutoff 3 is `-1`. -/
theorem q2GoRecoveredCompatibilityDefect_three_thirtyFive :
    q2GoRecoveredCompatibilityDefect 3 35 = -1 := by
  rw [q2GoRecoveredCompatibilityDefect_three_eq_mertens (by norm_num)]
  native_decide

end RHLean.Proof
