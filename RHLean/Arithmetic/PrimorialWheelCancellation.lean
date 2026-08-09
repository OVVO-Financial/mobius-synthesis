import Mathlib

/-!
# General primorial-wheel cancellation

The arithmetic mechanism behind the `2,3,5,7` wheel does not depend on the
particular odd primes.  Let `Q` be the product of any finite collection of odd
prime moduli.  After the prime-`2` coordinate is added, the full wheel has
period `2Q`.  Its second `Q`-cell is the sign-reversed copy of its first
`Q`-cell.  Consequently every complete `2Q`-cell has exact signed mass zero.

The statements below isolate this mechanism abstractly.  A later bridge may
instantiate `f` with the actual progressive first-cover sign assignment.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Arithmetic

def HasWheelHalfReversal (Q : ℕ) (f : ℕ → ℤ) : Prop :=
  ∀ r < Q, f (Q + r) = -f r

theorem sum_two_mul_cell_eq_zero_of_halfReversal
    (Q : ℕ) (f : ℕ → ℤ)
    (hrev : HasWheelHalfReversal Q f) :
    ∑ r ∈ Finset.range (2 * Q), f r = 0 := by
  have htwo : 2 * Q = Q + Q := by omega
  rw [htwo, Finset.sum_range_add]
  have hsecond :
      (∑ r ∈ Finset.range Q, f (Q + r)) =
        -(∑ r ∈ Finset.range Q, f r) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    exact hrev r (Finset.mem_range.mp hr)
  rw [hsecond]
  ring

def HasWheelPeriod (P : ℕ) (f : ℕ → ℤ) : Prop :=
  ∀ n, f (n + P) = f n

theorem wheel_period_mul
    {P : ℕ} {f : ℕ → ℤ}
    (hperiod : HasWheelPeriod P f) :
    ∀ q n : ℕ, f (q * P + n) = f n := by
  intro q
  induction q with
  | zero =>
      intro n
      simp
  | succ q ih =>
      intro n
      have hstep := hperiod (q * P + n)
      calc
        f ((q + 1) * P + n) = f ((q * P + n) + P) := by
          congr 1
          ring
        _ = f (q * P + n) := hstep
        _ = f n := ih n

theorem translated_two_mul_cell_eq_zero
    (Q q : ℕ) (f : ℕ → ℤ)
    (hperiod : HasWheelPeriod (2 * Q) f)
    (hrev : HasWheelHalfReversal Q f) :
    ∑ r ∈ Finset.range (2 * Q), f (q * (2 * Q) + r) = 0 := by
  have htranslate : ∀ r : ℕ,
      f (q * (2 * Q) + r) = f r := wheel_period_mul hperiod q
  calc
    ∑ r ∈ Finset.range (2 * Q), f (q * (2 * Q) + r) =
        ∑ r ∈ Finset.range (2 * Q), f r := by
          apply Finset.sum_congr rfl
          intro r hr
          exact htranslate r
    _ = 0 := sum_two_mul_cell_eq_zero_of_halfReversal Q f hrev

def IsUnitWheelSign (f : ℕ → ℤ) : Prop :=
  ∀ n, |f n| ≤ 1

theorem abs_wheel_fragment_le_length
    (f : ℕ → ℤ) (hunit : IsUnitWheelSign f)
    (a L : ℕ) :
    |∑ r ∈ Finset.range L, f (a + r)| ≤ (L : ℤ) := by
  calc
    |∑ r ∈ Finset.range L, f (a + r)|
        ≤ ∑ r ∈ Finset.range L, |f (a + r)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ Finset.range L, (1 : ℤ) := by
          apply Finset.sum_le_sum
          intro r hr
          exact hunit (a + r)
    _ = (L : ℤ) := by simp

theorem wheel_discrepancy_carried_by_boundary
    (f : ℕ → ℤ) (hunit : IsUnitWheelSign f)
    (boundaryStart boundaryLength : ℕ) :
    |∑ r ∈ Finset.range boundaryLength, f (boundaryStart + r)| ≤
      (boundaryLength : ℤ) :=
  abs_wheel_fragment_le_length f hunit boundaryStart boundaryLength

end RHLean.Arithmetic
