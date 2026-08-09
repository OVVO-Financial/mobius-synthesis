import Mathlib
import RHLean.Arithmetic.PrimorialWheelScale

noncomputable section

namespace RHLean.Arithmetic

/-- The zero-indexed `k`th prime is at least `k + 2`. -/
theorem wheelPrime_add_two_le (k : ℕ) : k + 2 ≤ wheelPrime k := by
  exact Nat.add_two_le_nth_prime k

/-- Every primorial step grows by at least a factor of two. -/
theorem two_mul_primorialEndpoint_le_succ (k : ℕ) :
    2 * primorialEndpoint k ≤ primorialEndpoint (k + 1) := by
  rw [primorialEndpoint_succ]
  simpa [Nat.mul_comm] using
    Nat.mul_le_mul_left (primorialEndpoint k) (wheelPrime_prime k).two_le

/-- After the first prime, every primorial step grows by at least a factor of three. -/
theorem three_mul_primorialEndpoint_le_succ
    {k : ℕ} (hk : 1 ≤ k) :
    3 * primorialEndpoint k ≤ primorialEndpoint (k + 1) := by
  rw [primorialEndpoint_succ]
  have hp : 3 ≤ wheelPrime k := by
    exact le_trans (by omega) (wheelPrime_add_two_le k)
  simpa [Nat.mul_comm] using Nat.mul_le_mul_left (primorialEndpoint k) hp

/-- In the shifted scale used by the Mertens-energy statement, every primorial
step after the first expands by at least a factor of two. -/
theorem two_mul_primorialEndpoint_add_one_le_succ
    {k : ℕ} (hk : 1 ≤ k) :
    2 * (primorialEndpoint k + 1) ≤ primorialEndpoint (k + 1) + 1 := by
  have hthree := three_mul_primorialEndpoint_le_succ hk
  have hpos := primorialEndpoint_pos k
  omega

/-- The primorial endpoints eventually dominate the identity function, in the
explicit form needed to locate every natural number in a synchronized block. -/
theorem succ_le_primorialEndpoint_succ (n : ℕ) :
    n + 1 ≤ primorialEndpoint (n + 1) := by
  induction n with
  | zero =>
      exact primorialEndpoint_pos 1
  | succ n ih =>
      have hdouble := two_mul_primorialEndpoint_le_succ (n + 1)
      omega

/-- A simple explicit witness that every natural number lies below some
primorial block endpoint. -/
theorem nat_le_primorialBlockUpper (x : ℕ) :
    x ≤ primorialBlockUpper x := by
  unfold primorialBlockUpper
  exact (Nat.le_succ x).trans (succ_le_primorialEndpoint_succ x)

private theorem primorialBlock_exists (x : ℕ) :
    ∃ k : ℕ, x ≤ primorialBlockUpper k :=
  ⟨x, nat_le_primorialBlockUpper x⟩

/-- Least synchronized primorial block whose right endpoint contains `x`. -/
def primorialBlockIndex (x : ℕ) : ℕ :=
  Nat.find (primorialBlock_exists x)

/-- The least selected block always contains `x` at its right endpoint. -/
theorem le_primorialBlockUpper_blockIndex (x : ℕ) :
    x ≤ primorialBlockUpper (primorialBlockIndex x) := by
  exact Nat.find_spec (primorialBlock_exists x)

/-- Every `x ≥ 2` lies strictly beyond the left endpoint of its least selected
primorial block. -/
theorem primorialBlockLower_blockIndex_lt
    {x : ℕ} (hx : 2 ≤ x) :
    primorialBlockLower (primorialBlockIndex x) < x := by
  unfold primorialBlockIndex
  cases hfind : Nat.find (primorialBlock_exists x) with
  | zero =>
      simpa [primorialBlockLower, primorialEndpoint_zero] using hx
  | succ j =>
      have hjlt : j < Nat.find (primorialBlock_exists x) := by
        rw [hfind]
        omega
      have hnot : ¬ x ≤ primorialBlockUpper j :=
        Nat.find_min (primorialBlock_exists x) hjlt
      unfold primorialBlockLower
      unfold primorialBlockUpper at hnot
      omega

end RHLean.Arithmetic
