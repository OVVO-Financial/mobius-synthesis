import Mathlib
import RHLean.Proof.OneBlockInvariant

/-!
# Exact prefix population identity

Every squarefree entry of a target square block is populated from its unique
canonical frozen-prefix parent.  The child has the opposite Mobius sign, and
that parent lies below the old-prefix cutoff.

This is the exact arithmetic content of the empty-block comb population
mechanism.  It also isolates the remaining cancellation question: cancellation
of a populated block is equivalent to cancellation of the weighted canonical
parent fibers; it does not follow from coverage alone.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

def canonicalPrefixAssignedSign (x : ℕ) : ℤ :=
  if Squarefree x then -μ (canonicalCofactor x) else 0

theorem canonicalPrefixAssignedSign_eq_moebius
    {x : ℕ} (hx : 1 < x) :
    canonicalPrefixAssignedSign x = μ x := by
  by_cases hsq : Squarefree x
  · simp only [canonicalPrefixAssignedSign, if_pos hsq]
    exact (canonicalSignedParent_moebius hsq hx).symm
  · simp only [canonicalPrefixAssignedSign, if_neg hsq]
    have hzero : μ x = 0 := by
      by_contra hne
      exact hsq (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hne)
    exact hzero.symm

theorem exact_prefix_population_pointwise
    {a x : ℕ} (ha : 3 ≤ a)
    (hxBlock : x ∈ squareBlockInterval a) :
    canonicalPrefixAssignedSign x = μ x ∧
      (Squarefree x → canonicalCofactor x ≤ oldParentCutoff a) := by
  have hxBounds : a ^ 2 ≤ x ∧ x < (a + 1) ^ 2 := by
    simpa [squareBlockInterval, Finset.mem_Ico] using hxBlock
  have hx1 : 1 < x := by
    have : 9 ≤ a ^ 2 := by nlinarith
    omega
  constructor
  · exact canonicalPrefixAssignedSign_eq_moebius hx1
  · intro hsq
    exact canonicalCofactor_le_oldParentCutoff ha hxBlock hsq hx1

def canonicalPrefixPopulationMass (a : ℕ) : ℤ :=
  ∑ x ∈ squareBlockInterval a, canonicalPrefixAssignedSign x

theorem canonicalPrefixPopulationMass_eq_squareBlockMoebius
    {a : ℕ} (ha : 3 ≤ a) :
    canonicalPrefixPopulationMass a = squareBlockMoebius a := by
  unfold canonicalPrefixPopulationMass squareBlockMoebius
  apply Finset.sum_congr rfl
  intro x hx
  exact (exact_prefix_population_pointwise ha hx).1

def canonicalParentFiber (a c : ℕ) : Finset ℕ :=
  (squareBlockInterval a).filter fun x =>
    Squarefree x ∧ canonicalCofactor x = c

def canonicalParentFiberMass (a c : ℕ) : ℤ :=
  ∑ x ∈ canonicalParentFiber a c, μ x

theorem canonicalParentFiberMass_eq
    {a c : ℕ} (ha : 3 ≤ a) :
    canonicalParentFiberMass a c =
      -μ c * ((canonicalParentFiber a c).card : ℤ) := by
  unfold canonicalParentFiberMass
  calc
    ∑ x ∈ canonicalParentFiber a c, μ x =
        ∑ _x ∈ canonicalParentFiber a c, -μ c := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [canonicalParentFiber, Finset.mem_filter] at hx
          have hxBlock := hx.1
          have hsq := hx.2.1
          have hparent := hx.2.2
          have hxBounds : a ^ 2 ≤ x ∧ x < (a + 1) ^ 2 := by
            simpa [squareBlockInterval, Finset.mem_Ico] using hxBlock
          have hx1 : 1 < x := by
            have : 9 ≤ a ^ 2 := by nlinarith
            omega
          rw [canonicalSignedParent_moebius hsq hx1, hparent]
    _ = -μ c * ((canonicalParentFiber a c).card : ℤ) := by
      simp [mul_comm]

theorem canonicalParentFiberMass_eq_zero_iff
    {a c : ℕ} (ha : 3 ≤ a) :
    canonicalParentFiberMass a c = 0 ↔
      μ c = 0 ∨ canonicalParentFiber a c = ∅ := by
  rw [canonicalParentFiberMass_eq ha]
  constructor
  · intro h
    have hmul : μ c = 0 ∨ ((canonicalParentFiber a c).card : ℤ) = 0 := by
      exact mul_eq_zero.mp (by simpa using h)
    rcases hmul with hmu | hcard
    · exact Or.inl hmu
    · right
      rw [Int.ofNat_eq_zero, Finset.card_eq_zero] at hcard
      exact hcard
  · intro h
    rcases h with hmu | hfiber
    · simp [hmu]
    · simp [hfiber]

end RHLean.Proof
