import Mathlib
import RHLean.Proof.SquareRootPredecessorPrimeCells

/-!
# Go-wall strip descent

The first-owner wall is already a no-liberty boundary: there is no internal
prime-extension corner left to cancel there.  This module keeps one adjacent
old-prime strip intact and applies the fresh-prime recurrence before taking any
norm.

For consecutive old primes `ell < q`, encoded by the exact predecessor-universe
identity

`primesUpTo (q - 1) = primesUpTo ell`,

the strip

`F_{q^-}(X/q) - F_{q^-}(X/ell)`

is the difference of the two adjacent diagonal states, plus one genuinely
lower-scale residual

`F_{q^-}((X/q)/q)`.

Thus one lost fresh-prime liberty descends by a second factor of the same prime.
The residual is also realized literally as the signed Boolean mass of the old
faces whose `q^2`-dilate still lies below the endpoint.  No estimate, PNT input,
unrestricted Mertens replacement, or absolute value is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- One adjacent Go boundary strip on the predecessor cube. -/
def squareRootGoWallStripMass (X ell q : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo (q - 1)) (X / q) -
    frozenPrimeUniverseMass (primesUpTo (q - 1)) (X / ell)

/-- The diagonal frozen state after the prime `q` itself has been processed. -/
def squareRootGoDiagonalState (X q : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo q) (X / q)

/-- The square-dilated residual left after the adjacent boundary states are
peeled. -/
def squareRootGoSquareResidual (X q : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo (q - 1)) ((X / q) / q)

/-- **One-liberty Go descent.**

If `ell` is the immediate predecessor prime universe of `q`, the adjacent wall
strip is one telescoping diagonal increment plus the square-dilated residual.
This is just the genuine fresh-`q` Euler recurrence evaluated at `X/q`; no
support is duplicated. -/
theorem squareRootGoWallStripMass_eq_diagonal_sub_add_squareResidual
    {X ell q : ℕ} (hq : q.Prime)
    (hpred : primesUpTo (q - 1) = primesUpTo ell) :
    squareRootGoWallStripMass X ell q =
      squareRootGoDiagonalState X q -
        frozenPrimeUniverseMass (primesUpTo ell) (X / ell) +
          squareRootGoSquareResidual X q := by
  have hstep :=
    frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor
      q (X / q) hq
  unfold predecessorPrimeMass at hstep
  unfold squareRootGoWallStripMass squareRootGoDiagonalState
    squareRootGoSquareResidual
  rw [hpred]
  rw [hpred] at hstep
  omega

/-- Literal old faces contributing to the square-dilated residual. -/
def squareRootGoSquareKillFaces (X q : ℕ) : Finset (Finset ℕ) :=
  ((primesUpTo (q - 1)).powerset).filter fun t =>
    primeFaceProduct t ≤ (X / q) / q

/-- Signed mass of the literal square-kill face carrier. -/
def squareRootGoSquareKillFaceMass (X q : ℕ) : ℤ :=
  ∑ t ∈ squareRootGoSquareKillFaces X q, booleanCubeSign t

/-- The square-dilated frozen state is exactly the mass of the literal
`q^2`-admissible old-face carrier. -/
theorem squareRootGoSquareKillFaceMass_eq_squareResidual
    (X q : ℕ) :
    squareRootGoSquareKillFaceMass X q = squareRootGoSquareResidual X q := by
  unfold squareRootGoSquareKillFaceMass squareRootGoSquareKillFaces
    squareRootGoSquareResidual
  rw [Finset.sum_filter]
  exact (frozenPrimeUniverseMass_eq_cutoffSum
    (primesUpTo (q - 1)) ((X / q) / q)).symm

/-- Every literal square-kill face really has its `q^2`-dilate below `X`. -/
theorem squareRootGoSquareKillFace_product_le
    {X q : ℕ} (hq : q.Prime) {t : Finset ℕ}
    (ht : t ∈ squareRootGoSquareKillFaces X q) :
    q * q * primeFaceProduct t ≤ X := by
  have htCut : primeFaceProduct t ≤ (X / q) / q :=
    (Finset.mem_filter.mp ht).2
  have hOne : primeFaceProduct t * q ≤ X / q :=
    (Nat.le_div_iff_mul_le hq.pos).1 htCut
  have hTwo : (primeFaceProduct t * q) * q ≤ X :=
    (Nat.le_div_iff_mul_le hq.pos).1 hOne
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hTwo

end RHLean.Proof
