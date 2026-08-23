import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelbergDepthFourWheelSplit
import RHLean.Arithmetic.PrimeWheelFiniteDepthSemiprime

/-!
# Exact depth-four frontier classification

At depth four, every nonzero partial-wheel error has a resolved cofactor in
`{1,2,3}`, two unresolved prime factors above the wheel cutoff, and reciprocal
quotient in `{1,2,3}`.  This is the finite arithmetic support on which the
signed interval estimate must close.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Full depth-four support classification of a nonzero partial-wheel error. -/
theorem partialPrimeWheel_nonzero_error_depth_four_classification
    (y N d : ℕ)
    (hy : 4 ≤ y)
    (hscale : N < 4 * y ^ 2)
    (hd : d ∈ Finset.Icc 1 N)
    (herr : μ d - partialPrimeWheelSite y N d ≠ 0) :
    ∃ a q r : ℕ,
      (a = 1 ∨ a = 2 ∨ a = 3) ∧
      q.Prime ∧ r.Prime ∧ y < q ∧ y < r ∧
      d = a * q * r ∧
      (N / d = 1 ∨ N / d = 2 ∨ N / d = 3) := by
  have hdI := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := by omega
  rcases partialPrimeWheel_nonzero_error_smallCofactor_semiprime
      4 y N (by omega) hy hscale hdpos hdI.2 herr with
    ⟨a, q, r, ha4, hq, hr, hyq, hyr, hdFactor, hquot4⟩
  have ha0 : 0 < a := by
    by_contra ha
    have haz : a = 0 := Nat.eq_zero_of_not_pos ha
    have hd0 : d = 0 := by simpa [haz] using hdFactor
    exact (Nat.ne_of_gt hdpos) hd0
  have haCases : a = 1 ∨ a = 2 ∨ a = 3 := by omega
  have hquot1 : 1 ≤ N / d :=
    (Nat.one_le_div_iff hdpos).2 hdI.2
  have hquotCases : N / d = 1 ∨ N / d = 2 ∨ N / d = 3 := by omega
  exact ⟨a, q, r, haCases, hq, hr, hyq, hyr, hdFactor, hquotCases⟩

/-- Every large prime occurring in a depth-four frontier point is below
`4*y`.  Thus all frontier prime coordinates lie in one fixed multiplicative
annulus. -/
theorem partialPrimeWheel_depth_four_frontier_prime_lt_four_mul
    (y N d a q r : ℕ)
    (hy : 1 ≤ y)
    (hscale : N < 4 * y ^ 2)
    (hdN : d ≤ N)
    (ha : 1 ≤ a)
    (hyq : y < q) (hyr : y < r)
    (hd : d = a * q * r) :
    q < 4 * y ∧ r < 4 * y := by
  have hypos : 0 < y := by omega
  have h4ypos : 0 < 4 * y := Nat.mul_pos (by omega) hypos
  have hdlt : d < 4 * y ^ 2 := hdN.trans_lt hscale
  have hqrlt : q * r < 4 * y ^ 2 := by
    have hle : q * r ≤ a * q * r := by
      calc
        q * r = 1 * (q * r) := by simp
        _ ≤ a * (q * r) := Nat.mul_le_mul_right (q * r) ha
        _ = a * q * r := by ring_nf
    have hadlt : a * q * r < 4 * y ^ 2 := by
      simpa [hd] using hdlt
    exact hle.trans_lt hadlt
  constructor
  · by_contra hnot
    have h4yq : 4 * y ≤ q := Nat.le_of_not_gt hnot
    have hbig : 4 * y ^ 2 < q * r := by
      calc
        4 * y ^ 2 = (4 * y) * y := by ring_nf
        _ < (4 * y) * r := Nat.mul_lt_mul_of_pos_left hyr h4ypos
        _ ≤ q * r := Nat.mul_le_mul_right r h4yq
    exact Nat.lt_asymm hbig hqrlt
  · by_contra hnot
    have h4yr : 4 * y ≤ r := Nat.le_of_not_gt hnot
    have hbig : 4 * y ^ 2 < q * r := by
      calc
        4 * y ^ 2 = y * (4 * y) := by ring_nf
        _ < q * (4 * y) := Nat.mul_lt_mul_of_pos_right hyq h4ypos
        _ ≤ q * r := Nat.mul_le_mul_left q h4yr
    exact Nat.lt_asymm hbig hqrlt

end RHLean.Analysis
