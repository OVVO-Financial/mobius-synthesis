import Mathlib

namespace RHLean.Arithmetic

/-- The sixteen residue classes modulo `40` that are coprime to `10`. -/
def IsUnitResidueMod40 (r : ℕ) : Prop :=
  r = 1 ∨ r = 3 ∨ r = 7 ∨ r = 9 ∨
  r = 11 ∨ r = 13 ∨ r = 17 ∨ r = 19 ∨
  r = 21 ∨ r = 23 ∨ r = 27 ∨ r = 29 ∨
  r = 31 ∨ r = 33 ∨ r = 37 ∨ r = 39

/-- Odd integers not divisible by `5` lie in one of the unit classes modulo `40`. -/
theorem mod_forty_unit_residue
    (n : ℕ)
    (h2 : n % 2 = 1)
    (h5 : n % 5 ≠ 0) :
    IsUnitResidueMod40 (n % 40) := by
  unfold IsUnitResidueMod40
  omega

/-- Every unit residue modulo `40` has square congruent to `1` or `9`. -/
theorem unit_residue_sq_modEq_one_or_nine_40
    {r : ℕ}
    (hr : IsUnitResidueMod40 r) :
    Nat.ModEq 40 (r ^ 2) 1 ∨ Nat.ModEq 40 (r ^ 2) 9 := by
  rcases hr with
    rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    norm_num [Nat.ModEq]

/-- An odd integer not divisible by `5` has square congruent to `1` or `9` modulo `40`. -/
theorem sq_modEq_one_or_nine_40_of_mod_two_five
    {n : ℕ}
    (h2 : n % 2 = 1)
    (h5 : n % 5 ≠ 0) :
    Nat.ModEq 40 (n ^ 2) 1 ∨ Nat.ModEq 40 (n ^ 2) 9 := by
  have hclass := mod_forty_unit_residue n h2 h5
  have hn : Nat.ModEq 40 n (n % 40) := by
    simp [Nat.ModEq]
  rcases unit_residue_sq_modEq_one_or_nine_40 hclass with h1 | h9
  · exact Or.inl ((hn.pow 2).trans h1)
  · exact Or.inr ((hn.pow 2).trans h9)

/-- Every prime other than `2` and `5` has square congruent to `1` or `9` modulo `40`. -/
theorem prime_sq_modEq_one_or_nine_40
    {q : ℕ}
    (hq : q.Prime)
    (hq2 : q ≠ 2)
    (hq5 : q ≠ 5) :
    Nat.ModEq 40 (q ^ 2) 1 ∨ Nat.ModEq 40 (q ^ 2) 9 := by
  have h2 : q % 2 = 1 := (hq.eq_two_or_odd).resolve_left hq2
  have h5 : q % 5 ≠ 0 := by
    intro hmod
    have hdiv : 5 ∣ q := Nat.dvd_iff_mod_eq_zero.mpr hmod
    have hcases : 5 = 1 ∨ 5 = q := (Nat.dvd_prime hq).mp hdiv
    rcases hcases with hfalse | hqeq
    · omega
    · exact hq5 hqeq.symm
  exact sq_modEq_one_or_nine_40_of_mod_two_five h2 h5

end RHLean.Arithmetic
