import Mathlib
import RHLean.Proof.BalancedCanonicalGap

namespace RHLean.Proof

namespace CanonicalExtremeHeight

open BalancedCanonicalGap

/-!
# Extreme canonical pairs are intrinsically high

The balanced/extreme scanner showed that growing low-height cutoffs change the
balanced sector but leave the extreme sector unchanged.  This file records the exact
reason: in the extreme regime `u ≤ d`, doubled canonical height is already comparable
to the full product and hence to the square-block scale.
-/

/-- In the extreme regime, doubled height is at least three halves of the represented
product.  The division-free form is used over `ℕ`. -/
theorem three_mul_product_le_two_mul_doubledHeight
    {u d : ℕ} (hext : u ≤ d) :
    3 * (u * (u + d)) ≤ 2 * doubledHeight u d := by
  have hud : u * u ≤ u * d := Nat.mul_le_mul_left u hext
  have hdd : u * u ≤ d * d := Nat.mul_le_mul hext hext
  dsimp [doubledHeight]
  nlinarith

/-- Every extreme pair in `B_n` has doubled height at least `3 n² / 2`. -/
theorem three_mul_block_sq_le_two_mul_doubledHeight
    {n u d : ℕ} (hblock : InSquareBlock n u d) (hext : u ≤ d) :
    3 * n ^ 2 ≤ 2 * doubledHeight u d := by
  calc
    3 * n ^ 2 ≤ 3 * (u * (u + d)) := Nat.mul_le_mul_left 3 hblock.1
    _ ≤ 2 * doubledHeight u d :=
      three_mul_product_le_two_mul_doubledHeight hext

/-- Any threshold strictly below `3 n² / 2` automatically retains every extreme
pair in the block. -/
theorem extreme_above_subquadratic_threshold
    {n u d K : ℕ} (hblock : InSquareBlock n u d) (hext : u ≤ d)
    (hK : 2 * K < 3 * n ^ 2) :
    K < doubledHeight u d := by
  have hheight := three_mul_block_sq_le_two_mul_doubledHeight hblock hext
  nlinarith

end CanonicalExtremeHeight

end RHLean.Proof
