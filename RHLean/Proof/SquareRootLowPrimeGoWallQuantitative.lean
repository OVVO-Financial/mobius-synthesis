import Mathlib
import RHLean.Proof.SquareRootLegalAncestryGramReduction
import RHLean.Proof.SquareRootLowPrimeGoWallStripTelescope

/-!
# Quantitative control of completed Go-wall positions

The exact Go strip telescope leaves the square-dilated predecessor state

`F_{q^-}(X/q^2)`.

When `X/q^2 < q`, the predecessor cube is already complete at its physical
cutoff and the preceding module identifies this state exactly with the ordinary
integer Mertens prefix.  This file transfers the repository's lower critical
Mertens envelope to that completed Go territory.

The elementary cube condition `X < q^3` implies `X/q^2 < q`, so at the square
endpoint the only genuinely unfinished Go positions satisfy `q^3 <= R^2-1`.
No PNT input, prime-distribution estimate, or new Mertens hypothesis is used.
-/

noncomputable section

namespace RHLean.Proof

/-- A cubic owner threshold makes the square-dilated Go cutoff strictly smaller
than the owner. -/
theorem squareRootLowPrimeGo_squareCutoff_lt_owner_of_lt_cube
    {X q : ℕ} (hq : q.Prime) (hXq : X < q ^ 3) :
    X / (q * q) < q := by
  have hqqPos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  apply (Nat.div_lt_iff_lt_mul hqqPos).2
  simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hXq

/-- Square-endpoint specialization of the cubic completion criterion. -/
theorem squareRootLowPrimeGo_squareEndpointCutoff_lt_owner_of_lt_cube
    {R q : ℕ} (hq : q.Prime)
    (hRq : squareRootEndpoint R < q ^ 3) :
    squareRootEndpoint R / (q * q) < q :=
  squareRootLowPrimeGo_squareCutoff_lt_owner_of_lt_cube hq hRq

/-- **Completed Go positions inherit the lower critical Mertens energy.**
Once `q^3` lies beyond the square endpoint, the square-dilated wall residual is
not a new frozen state: it is exactly a lower-scale Mertens value, hence is
controlled by the existing lower critical envelope. -/
theorem squareRootLowPrimeGo_completedSquareResidual_energy_le
    {R q : ℕ} {K : ℝ}
    (hK : LowerMertensCriticalEnvelope R K)
    (hq : q.Prime) (hqR : q ≤ R)
    (hRq : squareRootEndpoint R < q ^ 3) :
    ((((squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R) - 1 : ℤ) : ℝ)) ^ 2) ≤
      K * (((squareRootEndpoint R / (q * q) + 1 : ℕ) : ℝ)) := by
  have hcomplete : squareRootEndpoint R / (q * q) < q :=
    squareRootLowPrimeGo_squareEndpointCutoff_lt_owner_of_lt_cube hq hRq
  have hyR : squareRootEndpoint R / (q * q) < R :=
    hcomplete.trans_le hqR
  rw [squareRootLowPrimeGoWallSquareResidual_eq_mertensSummatoryInt hq hcomplete]
  exact hK.2 _ hyR

/-- Contrapositive support statement: any Go position which has not yet become
a lower-scale Mertens state must still lie below the cubic owner threshold. -/
theorem squareRootLowPrimeGo_unfinished_forces_owner_cube_le
    {R q : ℕ} (hq : q.Prime)
    (hun : ¬ squareRootEndpoint R / (q * q) < q) :
    q ^ 3 ≤ squareRootEndpoint R := by
  by_contra hnot
  have hlt : squareRootEndpoint R < q ^ 3 := Nat.lt_of_not_ge hnot
  exact hun (squareRootLowPrimeGo_squareEndpointCutoff_lt_owner_of_lt_cube hq hlt)

end RHLean.Proof
