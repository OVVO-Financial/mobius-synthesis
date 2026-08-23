import Mathlib
import RHLean.Proof.SurvivorFarUpperRigidity
import RHLean.Proof.SurvivorPrimeFaceFiniteDifference

/-!
# Far survivor renewal is lower-scale Mertens

In the rigid far-upper sector, the exact `2,3,5` Boolean third-difference
stencil is not an autonomous cancellation term.  The prime-face realization
identifies it with the full fixed-prime survivor fibre, while far-upper
rigidity identifies that same fibre with the negative lower-scale Mertens
prefix.  Cancelling the common minus sign gives an exact renewal identity.

No estimate, asymptotic input, Markov approximation, or independence
hypothesis is used.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- **Far survivor renewal is exactly lower-scale Mertens.**  For `t >= 55`
and a prime coordinate `q >= t + 9`, the exact signed eight-state Boolean
third difference in the prime coordinates `2,3,5` is the lower-scale Mertens
value at `floor(X_t / q)`, where `X_t = (t+1)^2 - 1`.

This is the kernel-checked composition of
`survivorFixedPrimeCofactorMass_eq_neg_two_three_five_difference` and
`survivorFixedPrimeCofactorMass_sixteen_eq_neg_mertensSummatory`. -/
theorem farSurvivorRenewal_is_LowerMertens
    (t q : ℕ) (ht : 55 ≤ t) (hqPrime : q.Prime)
    (hqFar : t + 9 ≤ q) :
    (((∑ u ∈
        ((((survivorPrimeFaceAmbient q).erase 2).erase 3).erase 5).powerset,
        booleanCubeSign u *
          booleanThreePivotDifference 2 3 5
            (survivorPrimeFaceHigh 16 t q) u : ℤ)) : ℂ) =
      RHLean.Analysis.mertensSummatory
        (RHLean.Analysis.squarePrefixEndpoint t / q) := by
  have hq : 7 ≤ q := by omega
  have hstencil :=
    survivorFixedPrimeCofactorMass_eq_neg_two_three_five_difference
      16 t hqPrime hq
  have hfar :=
    survivorFixedPrimeCofactorMass_sixteen_eq_neg_mertensSummatory
      t q ht hqPrime hqFar
  have hneg :
      -(((∑ u ∈
          ((((survivorPrimeFaceAmbient q).erase 2).erase 3).erase 5).powerset,
          booleanCubeSign u *
            booleanThreePivotDifference 2 3 5
              (survivorPrimeFaceHigh 16 t q) u : ℤ)) : ℂ) =
        -RHLean.Analysis.mertensSummatory
          (RHLean.Analysis.squarePrefixEndpoint t / q) := by
    calc
      -(((∑ u ∈
          ((((survivorPrimeFaceAmbient q).erase 2).erase 3).erase 5).powerset,
          booleanCubeSign u *
            booleanThreePivotDifference 2 3 5
              (survivorPrimeFaceHigh 16 t q) u : ℤ)) : ℂ) =
          survivorFixedPrimeCofactorMass 16 t q := hstencil.symm
      _ = -RHLean.Analysis.mertensSummatory
          (RHLean.Analysis.squarePrefixEndpoint t / q) := hfar
  exact neg_inj.mp hneg

end RHLean.Proof
