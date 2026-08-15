import Mathlib
import RHLean.Arithmetic.BooleanCubeFiniteDifference
import RHLean.Proof.SurvivorPrimeFaceRealization

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic

/-!
# Actual survivor fibres as finite Boolean derivatives

The prime-face realization identifies the actual fixed-`q` survivor cofactor
mass with an alternating Boolean-supported sum. Generic Boolean finite
differences therefore apply directly to the real survivor selector, without
decomposing its V-shaped support into monotone pieces.

The distinguished coordinates `2`, `3`, and `5` are available in every prime
fibre `q >= 7`. They give one exact eight-state third-difference stencil that
simultaneously records the dyadic parity flip and the two odd-prime sign flips.
No Markov, residue-uniformity, or independence hypothesis is used.
-/

/-- Any two distinct prime-face coordinates below `q` put the actual fixed-`q`
survivor mass on an exact four-point Boolean stencil. -/
theorem survivorFixedPrimeCofactorMass_eq_neg_twoPivotDifference
    (Λ : ℝ) (t : ℕ) {q a b : ℕ}
    (hq : q.Prime)
    (ha : a ∈ survivorPrimeFaceAmbient q)
    (hb : b ∈ survivorPrimeFaceAmbient q)
    (hab : a ≠ b) :
    survivorFixedPrimeCofactorMass Λ t q =
      -(((∑ u ∈
          (((survivorPrimeFaceAmbient q).erase a).erase b).powerset,
          booleanCubeSign u *
            booleanTwoPivotDifference a b
              (survivorPrimeFaceHigh Λ t q) u : ℤ)) : ℂ) := by
  rw [survivorFixedPrimeCofactorMass_eq_neg_faceAlternating Λ t hq]
  rw [truncatedCubeAlternatingSum_eq_twoPivotDifference
    (survivorPrimeFaceHigh Λ t q) ha hb hab]

/-- Any three distinct prime-face coordinates below `q` put the actual fixed-`q`
survivor mass on an exact eight-state third-difference stencil. -/
theorem survivorFixedPrimeCofactorMass_eq_neg_threePivotDifference
    (Λ : ℝ) (t : ℕ) {q a b c : ℕ}
    (hq : q.Prime)
    (ha : a ∈ survivorPrimeFaceAmbient q)
    (hb : b ∈ survivorPrimeFaceAmbient q)
    (hc : c ∈ survivorPrimeFaceAmbient q)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    survivorFixedPrimeCofactorMass Λ t q =
      -(((∑ u ∈
          ((((survivorPrimeFaceAmbient q).erase a).erase b).erase c).powerset,
          booleanCubeSign u *
            booleanThreePivotDifference a b c
              (survivorPrimeFaceHigh Λ t q) u : ℤ)) : ℂ) := by
  rw [survivorFixedPrimeCofactorMass_eq_neg_faceAlternating Λ t hq]
  rw [truncatedCubeAlternatingSum_eq_threePivotDifference
    (survivorPrimeFaceHigh Λ t q) ha hb hc hab hac hbc]

/-- For every prime `q >= 7`, primes `3` and `5` give a universal exact
four-point survivor stencil. No residue or monotonicity hypothesis is needed. -/
theorem survivorFixedPrimeCofactorMass_eq_neg_three_five_difference
    (Λ : ℝ) (t : ℕ) {q : ℕ}
    (hqPrime : q.Prime) (hq : 7 ≤ q) :
    survivorFixedPrimeCofactorMass Λ t q =
      -(((∑ u ∈
          (((survivorPrimeFaceAmbient q).erase 3).erase 5).powerset,
          booleanCubeSign u *
            booleanTwoPivotDifference 3 5
              (survivorPrimeFaceHigh Λ t q) u : ℤ)) : ℂ) := by
  apply survivorFixedPrimeCofactorMass_eq_neg_twoPivotDifference Λ t hqPrime
  · unfold survivorPrimeFaceAmbient
    exact mem_primesUpTo.mpr ⟨by norm_num, by omega⟩
  · unfold survivorPrimeFaceAmbient
    exact mem_primesUpTo.mpr ⟨by norm_num, by omega⟩
  · norm_num

/-- **Exact `2-3-5` parity stencil.** For every prime `q >= 7`, the complete
actual survivor fibre is the signed eight-state third finite difference in the
three smallest prime coordinates. This is the finite Boolean cube on which all
three sign reversals are simultaneously visible. -/
theorem survivorFixedPrimeCofactorMass_eq_neg_two_three_five_difference
    (Λ : ℝ) (t : ℕ) {q : ℕ}
    (hqPrime : q.Prime) (hq : 7 ≤ q) :
    survivorFixedPrimeCofactorMass Λ t q =
      -(((∑ u ∈
          ((((survivorPrimeFaceAmbient q).erase 2).erase 3).erase 5).powerset,
          booleanCubeSign u *
            booleanThreePivotDifference 2 3 5
              (survivorPrimeFaceHigh Λ t q) u : ℤ)) : ℂ) := by
  apply survivorFixedPrimeCofactorMass_eq_neg_threePivotDifference Λ t hqPrime
  · unfold survivorPrimeFaceAmbient
    exact mem_primesUpTo.mpr ⟨by norm_num, by omega⟩
  · unfold survivorPrimeFaceAmbient
    exact mem_primesUpTo.mpr ⟨by norm_num, by omega⟩
  · unfold survivorPrimeFaceAmbient
    exact mem_primesUpTo.mpr ⟨by norm_num, by omega⟩
  · norm_num
  · norm_num
  · norm_num

/-- The four-point Boolean stencil has universal integer magnitude at most two. -/
theorem abs_booleanTwoPivotDifference_le_two
    {α : Type*} [DecidableEq α]
    (a b : α) (P : Finset α → Prop) (u : Finset α) :
    |booleanTwoPivotDifference a b P u| ≤ 2 := by
  unfold booleanTwoPivotDifference booleanPredicateIndicator
  by_cases h0 : P u <;>
    by_cases ha : P (insert a u) <;>
    by_cases hb : P (insert b u) <;>
    by_cases hab : P (insert a (insert b u)) <;>
    simp [h0, ha, hb, hab]

/-- The eight-point Boolean stencil has universal integer magnitude at most
four. The quantitative problem is therefore its support, not the size of one
local stencil value. -/
theorem abs_booleanThreePivotDifference_le_four
    {α : Type*} [DecidableEq α]
    (a b c : α) (P : Finset α → Prop) (u : Finset α) :
    |booleanThreePivotDifference a b c P u| ≤ 4 := by
  unfold booleanThreePivotDifference
  calc
    |booleanTwoPivotDifference a b P u -
        booleanTwoPivotDifference a b P (insert c u)| ≤
      |booleanTwoPivotDifference a b P u| +
        |booleanTwoPivotDifference a b P (insert c u)| := by
          exact abs_sub _ _
    _ ≤ 2 + 2 := by
      exact add_le_add
        (abs_booleanTwoPivotDifference_le_two a b P u)
        (abs_booleanTwoPivotDifference_le_two a b P (insert c u))
    _ = 4 := by norm_num

end RHLean.Proof
