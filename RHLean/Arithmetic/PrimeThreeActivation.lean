import RHLean.Arithmetic.FourSlotCell

namespace RHLean.Arithmetic

/-- Exactly one of three propositions holds. -/
def ExactlyOneOfThree (P Q R : Prop) : Prop :=
  (P ∧ ¬Q ∧ ¬R) ∨ (¬P ∧ Q ∧ ¬R) ∨ (¬P ∧ ¬Q ∧ R)

/-- The active multiple of `3` follows the deterministic cycle indexed by `k % 3`. -/
theorem prime_three_active_slot_cycle (k : ℕ) :
    (k % 3 = 0 →
      ¬3 ∣ 4 * k + 1 ∧ ¬3 ∣ 4 * k + 2 ∧ 3 ∣ 4 * k + 3) ∧
    (k % 3 = 1 →
      ¬3 ∣ 4 * k + 1 ∧ 3 ∣ 4 * k + 2 ∧ ¬3 ∣ 4 * k + 3) ∧
    (k % 3 = 2 →
      3 ∣ 4 * k + 1 ∧ ¬3 ∣ 4 * k + 2 ∧ ¬3 ∣ 4 * k + 3) := by
  simp only [Nat.dvd_iff_mod_eq_zero]
  omega

/-- Every complete four-slot cell has exactly one active slot divisible by `3`. -/
theorem prime_three_exactly_one_active_slot (k : ℕ) :
    ExactlyOneOfThree
      (3 ∣ 4 * k + 1)
      (3 ∣ 4 * k + 2)
      (3 ∣ 4 * k + 3) := by
  have hcycle := prime_three_active_slot_cycle k
  have hlt : k % 3 < 3 := Nat.mod_lt k (by decide)
  unfold ExactlyOneOfThree
  by_cases h0 : k % 3 = 0
  · exact Or.inr (Or.inr (hcycle.1 h0))
  by_cases h1 : k % 3 = 1
  · exact Or.inr (Or.inl (hcycle.2.1 h1))
  · have h2 : k % 3 = 2 := by omega
    exact Or.inl (hcycle.2.2 h2)

end RHLean.Arithmetic
