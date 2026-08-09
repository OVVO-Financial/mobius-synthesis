import Mathlib
import RHLean.Arithmetic.PrimorialWheelPrefixIdentity
import RHLean.Analysis.CanonicalHighSectorCore

/-!
# Exact nesting of square blocks inside primorial-wheel residuals

The square-block and prime-wheel architectures are not independent. Whenever
complete square blocks lie inside one synchronized primorial block, their signed
Mobius mass is exactly an increment of the same pinned prime-wheel residual.

For the square endpoint

`X_j = (j+1)^2 - 1`,

the complete square block `j` is the integer interval `(X_{j-1}, X_j]`. Thus,
inside one primorial block,

`Delta_j = R_k(X_j) - R_k(X_{j-1})`.

More generally every consecutive run of complete square blocks telescopes to
one difference of wheel-residual values. Therefore a uniform wheel-residual
bound controls all such block runs with only the sharp triangle-inequality
factor two. Conversely, any route from individual block estimates back to the
wheel residual must retain cancellation in these consecutive signed sums; an
absolute-value sum over the blocks loses a full square-root factor.

This file contains only exact finite identities and deterministic norm transfers;
it asserts no new analytic estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- The primorial residual/Mertens difference identity also holds at the lower
wheel anchor, where both sides are zero. -/
theorem primorialWheel_residual_cast_eq_mertens_sub_le
    (k : ℕ) {x : ℕ}
    (hlower : primorialBlockLower k ≤ x)
    (hupper : x ≤ primorialBlockUpper k) :
    (((primorialWheelSystem k).residual x : ℤ) : ℂ) =
      RHLean.Analysis.mertensSummatory x -
        RHLean.Analysis.mertensSummatory (primorialBlockLower k) := by
  rw [primorialWheel_residual_eq_moebiusInterval k hupper]
  push_cast
  exact moebius_Ioc_cast_eq_mertens_sub hlower

/-- One complete square-block increment is the discrete derivative of the
square-prefix Mertens sequence. -/
theorem canonicalTotalIncrement_eq_squarePrefix_sub
    (j : ℕ) (hj : 1 ≤ j) :
    canonicalTotalIncrement j =
      RHLean.Analysis.squarePrefixMertens j -
        RHLean.Analysis.squarePrefixMertens (j - 1) := by
  rw [← canonicalTotalPrefix_eq_squarePrefixMertens j,
    ← canonicalTotalPrefix_eq_squarePrefixMertens (j - 1)]
  unfold canonicalTotalPrefix
  have hpred : j - 1 + 1 = j := Nat.sub_add_cancel hj
  rw [hpred, Finset.sum_range_succ]
  ring

/-- A consecutive run of complete square blocks telescopes exactly to the
difference of its two square-prefix endpoint values. The index interval is
`[a,b]`, written as `Ico a (b+1)`. -/
theorem sum_canonicalTotalIncrement_Ico_eq_squarePrefix_sub
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    (∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j) =
      RHLean.Analysis.squarePrefixMertens b -
        RHLean.Analysis.squarePrefixMertens (a - 1) := by
  rw [← canonicalTotalPrefix_eq_squarePrefixMertens b,
    ← canonicalTotalPrefix_eq_squarePrefixMertens (a - 1)]
  unfold canonicalTotalPrefix
  have hpred : a - 1 + 1 = a := Nat.sub_add_cancel ha
  rw [hpred]
  have hsplit :=
    Finset.sum_range_add_sum_Ico
      (fun j : ℕ => canonicalTotalIncrement j) hab
  rw [← hsplit]
  ring

/-- Exact nesting theorem. If the two square-prefix endpoints bounding a run
of complete square blocks lie in the closed primorial interval
`[W_k,W_{k+1}]`, then the run is exactly the difference of the two pinned
primorial-wheel residual values. Allowing the left endpoint to equal `W_k`
includes a complete block that begins at `W_k+1`; the pinned residual there is
exactly zero. -/
theorem sum_canonicalTotalIncrement_Ico_eq_primorialResidual_sub
    (k a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b + 1)
    (hleftLower :
      primorialBlockLower k ≤ RHLean.Analysis.squarePrefixEndpoint (a - 1))
    (hleftUpper :
      RHLean.Analysis.squarePrefixEndpoint (a - 1) ≤ primorialBlockUpper k)
    (hrightLower :
      primorialBlockLower k ≤ RHLean.Analysis.squarePrefixEndpoint b)
    (hrightUpper :
      RHLean.Analysis.squarePrefixEndpoint b ≤ primorialBlockUpper k) :
    (∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j) =
      ((((primorialWheelSystem k).residual
        (RHLean.Analysis.squarePrefixEndpoint b) : ℤ) : ℂ)) -
      ((((primorialWheelSystem k).residual
        (RHLean.Analysis.squarePrefixEndpoint (a - 1)) : ℤ) : ℂ)) := by
  rw [sum_canonicalTotalIncrement_Ico_eq_squarePrefix_sub a b ha hab]
  rw [primorialWheel_residual_cast_eq_mertens_sub_le
      k hrightLower hrightUpper,
    primorialWheel_residual_cast_eq_mertens_sub_le
      k hleftLower hleftUpper]
  simp only [RHLean.Analysis.squarePrefixMertens]
  ring

/-- Single-block specialization of the exact nesting theorem. -/
theorem canonicalTotalIncrement_eq_primorialResidual_sub
    (k j : ℕ) (hj : 1 ≤ j)
    (hleftLower :
      primorialBlockLower k ≤ RHLean.Analysis.squarePrefixEndpoint (j - 1))
    (hleftUpper :
      RHLean.Analysis.squarePrefixEndpoint (j - 1) ≤ primorialBlockUpper k)
    (hrightLower :
      primorialBlockLower k ≤ RHLean.Analysis.squarePrefixEndpoint j)
    (hrightUpper :
      RHLean.Analysis.squarePrefixEndpoint j ≤ primorialBlockUpper k) :
    canonicalTotalIncrement j =
      ((((primorialWheelSystem k).residual
        (RHLean.Analysis.squarePrefixEndpoint j) : ℤ) : ℂ)) -
      ((((primorialWheelSystem k).residual
        (RHLean.Analysis.squarePrefixEndpoint (j - 1)) : ℤ) : ℂ)) := by
  simpa using
    (sum_canonicalTotalIncrement_Ico_eq_primorialResidual_sub
      k j j hj (by omega) hleftLower hleftUpper hrightLower hrightUpper)

/-- Deterministic norm transfer: a bound `B` for every pinned wheel residual in
one primorial block bounds the net contribution of every consecutive run of
complete square blocks by `2B`. No exponent or block-count loss occurs. -/
theorem norm_sum_canonicalTotalIncrement_Ico_le_two_mul_of_wheelResidual_bound
    (k a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b + 1)
    (hleftLower :
      primorialBlockLower k ≤ RHLean.Analysis.squarePrefixEndpoint (a - 1))
    (hleftUpper :
      RHLean.Analysis.squarePrefixEndpoint (a - 1) ≤ primorialBlockUpper k)
    (hrightLower :
      primorialBlockLower k ≤ RHLean.Analysis.squarePrefixEndpoint b)
    (hrightUpper :
      RHLean.Analysis.squarePrefixEndpoint b ≤ primorialBlockUpper k)
    (B : ℝ)
    (hresidual : ∀ x : ℕ,
      primorialBlockLower k ≤ x → x ≤ primorialBlockUpper k →
      ‖((((primorialWheelSystem k).residual x : ℤ) : ℂ))‖ ≤ B) :
    ‖∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j‖ ≤ 2 * B := by
  rw [sum_canonicalTotalIncrement_Ico_eq_primorialResidual_sub
    k a b ha hab hleftLower hleftUpper hrightLower hrightUpper]
  calc
    ‖((((primorialWheelSystem k).residual
          (RHLean.Analysis.squarePrefixEndpoint b) : ℤ) : ℂ)) -
        ((((primorialWheelSystem k).residual
          (RHLean.Analysis.squarePrefixEndpoint (a - 1)) : ℤ) : ℂ))‖ ≤
      ‖((((primorialWheelSystem k).residual
          (RHLean.Analysis.squarePrefixEndpoint b) : ℤ) : ℂ))‖ +
        ‖((((primorialWheelSystem k).residual
          (RHLean.Analysis.squarePrefixEndpoint (a - 1)) : ℤ) : ℂ))‖ :=
      norm_sub_le _ _
    _ ≤ B + B :=
      add_le_add
        (hresidual _ hrightLower hrightUpper)
        (hresidual _ hleftLower hleftUpper)
    _ = 2 * B := by ring

/-- In particular, one complete square block is bounded by twice the ambient
wheel-residual oscillation. -/
theorem norm_canonicalTotalIncrement_le_two_mul_of_wheelResidual_bound
    (k j : ℕ) (hj : 1 ≤ j)
    (hleftLower :
      primorialBlockLower k ≤ RHLean.Analysis.squarePrefixEndpoint (j - 1))
    (hleftUpper :
      RHLean.Analysis.squarePrefixEndpoint (j - 1) ≤ primorialBlockUpper k)
    (hrightLower :
      primorialBlockLower k ≤ RHLean.Analysis.squarePrefixEndpoint j)
    (hrightUpper :
      RHLean.Analysis.squarePrefixEndpoint j ≤ primorialBlockUpper k)
    (B : ℝ)
    (hresidual : ∀ x : ℕ,
      primorialBlockLower k ≤ x → x ≤ primorialBlockUpper k →
      ‖((((primorialWheelSystem k).residual x : ℤ) : ℂ))‖ ≤ B) :
    ‖canonicalTotalIncrement j‖ ≤ 2 * B := by
  simpa using
    (norm_sum_canonicalTotalIncrement_Ico_le_two_mul_of_wheelResidual_bound
      k j j hj (by omega) hleftLower hleftUpper hrightLower hrightUpper
      B hresidual)

end RHLean.Proof
