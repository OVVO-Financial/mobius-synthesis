import Mathlib

namespace RHLean.Arithmetic

/-- The eight residue classes modulo `24` that are coprime to `6`. -/
def IsUnitResidueMod24 (r : ℕ) : Prop :=
  r = 1 ∨ r = 5 ∨ r = 7 ∨ r = 11 ∨
  r = 13 ∨ r = 17 ∨ r = 19 ∨ r = 23

/-- Odd integers not divisible by `3` lie in one of the eight unit classes modulo `24`. -/
theorem mod_twenty_four_unit_residue
    (n : ℕ)
    (h2 : n % 2 = 1)
    (h3 : n % 3 ≠ 0) :
    IsUnitResidueMod24 (n % 24) := by
  unfold IsUnitResidueMod24
  omega

/-- Every unit residue modulo `24` has square congruent to `1`. -/
theorem unit_residue_sq_modEq_one_24
    {r : ℕ}
    (hr : IsUnitResidueMod24 r) :
    Nat.ModEq 24 (r ^ 2) 1 := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [Nat.ModEq]

/-- An odd integer not divisible by `3` has square congruent to `1` modulo `24`. -/
theorem sq_modEq_one_24_of_mod_two_three
    {n : ℕ}
    (h2 : n % 2 = 1)
    (h3 : n % 3 ≠ 0) :
    Nat.ModEq 24 (n ^ 2) 1 := by
  have hclass := mod_twenty_four_unit_residue n h2 h3
  have hn : Nat.ModEq 24 n (n % 24) := by
    simp [Nat.ModEq]
  exact (hn.pow 2).trans (unit_residue_sq_modEq_one_24 hclass)

/-- Every prime other than `2` and `3` has square congruent to `1` modulo `24`. -/
theorem prime_sq_modEq_one_24
    {q : ℕ}
    (hq : q.Prime)
    (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) :
    Nat.ModEq 24 (q ^ 2) 1 := by
  have h2 : q % 2 = 1 := (hq.eq_two_or_odd).resolve_left hq2
  have h3 : q % 3 ≠ 0 := by
    intro hmod
    have hdiv : 3 ∣ q := Nat.dvd_iff_mod_eq_zero.mpr hmod
    have hcases : 3 = 1 ∨ 3 = q := (Nat.dvd_prime hq).mp hdiv
    rcases hcases with hfalse | hqeq
    · omega
    · exact hq3 hqeq.symm
  exact sq_modEq_one_24_of_mod_two_three h2 h3

end RHLean.Arithmetic
