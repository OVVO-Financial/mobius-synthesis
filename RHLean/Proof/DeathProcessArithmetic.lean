import Mathlib
import RHLean.Proof.LifetimeEndpointDecomposition

/-!
# Death-process arithmetic

This module exposes the exact discrete derivative of the lifetime death process
and the arithmetic shell cut out by the moving doubled-height boundary.  It
also rewrites the canonical doubled height as the prime-cofactor difference of
squares and as its factorized form.

No cancellation or asymptotic estimate is asserted.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- Discrete increment of the death-ordered Möbius mass. -/
def lifetimeDeathIncrement (Λ : ℝ) (t : ℕ) : ℂ :=
  lifetimeDeathMass Λ (t + 1) - lifetimeDeathMass Λ t

/-- A source lies in the height shell crossed between stages `t` and `t+1`. -/
def IsDeathHeightShell (Λ : ℝ) (t m : ℕ) : Prop :=
  IsMovingCanonicalHigh Λ t m ∧ ¬ IsMovingCanonicalHigh Λ (t + 1) m

/-- The canonical crossing set is the finite population attached to the death
height shell at stage `t`. -/
def deathHeightShellSet (Λ : ℝ) (t : ℕ) : Finset ℕ :=
  movingCanonicalCrossingSet Λ t

/-- Möbius mass of the canonical death height shell. -/
def deathHeightShellMass (Λ : ℝ) (t : ℕ) : ℂ :=
  movingCanonicalCrossingMass Λ t

/-- Membership in the canonical crossing set implies the exact shell predicate. -/
theorem mem_deathHeightShellSet_implies_shell
    (Λ : ℝ) (t m : ℕ)
    (hm : m ∈ deathHeightShellSet Λ t) :
    IsDeathHeightShell Λ t m := by
  classical
  rcases Finset.mem_sdiff.mp hm with ⟨hmOld, hmNotNew⟩
  have hmHigh : IsMovingCanonicalHigh Λ t m :=
    (Finset.mem_filter.mp hmOld).2
  have hmNotHigh : ¬ IsMovingCanonicalHigh Λ (t + 1) m := by
    intro hHigh
    apply hmNotNew
    apply Finset.mem_filter.mpr
    refine ⟨?_, hHigh⟩
    have hmRange : m < (t + 1) ^ 2 :=
      Finset.mem_range.mp (Finset.mem_filter.mp hmOld).1
    apply Finset.mem_range.mpr
    have hsquares : (t + 1) ^ 2 ≤ (t + 2) ^ 2 := by
      exact Nat.pow_le_pow_left (by omega) 2
    exact lt_of_lt_of_le hmRange hsquares
  exact ⟨hmHigh, hmNotHigh⟩

/-- The strict activity convention gives an exact half-open shell inequality. -/
theorem isDeathHeightShell_iff_height_window
    (Λ : ℝ) (t m : ℕ) :
    IsDeathHeightShell Λ t m ↔
      2 * Λ * (t : ℝ) < abs (canonicalHeightTwice m) ∧
        abs (canonicalHeightTwice m) ≤ 2 * Λ * ((t + 1 : ℕ) : ℝ) := by
  simp [IsDeathHeightShell, IsMovingCanonicalHigh, not_lt]

/-- The canonical doubled height is a difference of the squared largest prime
factor and squared canonical cofactor. -/
theorem canonicalHeightTwice_eq_prime_sq_sub_cofactor_sq
    (m : ℕ) :
    canonicalHeightTwice m =
      (canonicalLargestPrimeFactor m : ℝ) ^ 2 -
        (canonicalCofactor m : ℝ) ^ 2 := by
  rfl

/-- Difference-of-squares factorization of the canonical doubled height. -/
theorem canonicalHeightTwice_eq_prime_sub_cofactor_mul_sum
    (m : ℕ) :
    canonicalHeightTwice m =
      ((canonicalLargestPrimeFactor m : ℝ) - (canonicalCofactor m : ℝ)) *
        ((canonicalLargestPrimeFactor m : ℝ) + (canonicalCofactor m : ℝ)) := by
  unfold canonicalHeightTwice
  ring

/-- Factorized form of the exact death-shell window. -/
theorem isDeathHeightShell_iff_factorized_window
    (Λ : ℝ) (t m : ℕ) :
    IsDeathHeightShell Λ t m ↔
      2 * Λ * (t : ℝ) <
          abs (((canonicalLargestPrimeFactor m : ℝ) -
              (canonicalCofactor m : ℝ)) *
            ((canonicalLargestPrimeFactor m : ℝ) +
              (canonicalCofactor m : ℝ))) ∧
        abs (((canonicalLargestPrimeFactor m : ℝ) -
              (canonicalCofactor m : ℝ)) *
            ((canonicalLargestPrimeFactor m : ℝ) +
              (canonicalCofactor m : ℝ))) ≤
          2 * Λ * ((t + 1 : ℕ) : ℝ) := by
  rw [isDeathHeightShell_iff_height_window]
  rw [canonicalHeightTwice_eq_prime_sub_cofactor_mul_sum]

/-- The death process is reconstructed exactly from its initial value and all
previous discrete death increments. -/
theorem lifetimeDeathMass_eq_zero_add_sum_increments
    (Λ : ℝ) (n : ℕ) :
    lifetimeDeathMass Λ n =
      lifetimeDeathMass Λ 0 +
        ∑ t ∈ Finset.range n, lifetimeDeathIncrement Λ t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        lifetimeDeathMass Λ (n + 1) =
            lifetimeDeathMass Λ n + lifetimeDeathIncrement Λ n := by
          unfold lifetimeDeathIncrement
          ring
        _ = (lifetimeDeathMass Λ 0 +
              ∑ t ∈ Finset.range n, lifetimeDeathIncrement Λ t) +
              lifetimeDeathIncrement Λ n := by rw [ih]
        _ = lifetimeDeathMass Λ 0 +
              ((∑ t ∈ Finset.range n, lifetimeDeathIncrement Λ t) +
                lifetimeDeathIncrement Λ n) := by ring

/-- The shell mass is exactly the existing moving-boundary crossing mass. -/
theorem deathHeightShellMass_eq_crossingMass
    (Λ : ℝ) (t : ℕ) :
    deathHeightShellMass Λ t = movingCanonicalCrossingMass Λ t := by
  rfl

end RHLean.Proof
