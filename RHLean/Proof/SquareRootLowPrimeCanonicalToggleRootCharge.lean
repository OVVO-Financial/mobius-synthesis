import Mathlib
import RHLean.Proof.SquareRootLowPrimeSecondToggleCharge

/-!
# One root interval for canonical no-toggle and instability residuals

The first-failure and second-toggle populations are not two independent error
budgets.

For one root state `n <= B`, let `a(n)` be the least fresh prime whose extension
leaves the multiplicative cutoff.  There are only two chronological cases:

* **no-toggle / first failure:** every prime factor already present in `n` is
  earlier than `a(n)`, so `P+(n) < a(n)`;
* **instability / double toggle:** `n = b*m` is the still-admissible state
  created by a later pivot `b`, so `a(n) < b = P+(n)`.

The root state determines `a(n)`.  In the second case it also recovers
`b = P+(n)` and `m = canonicalCofactor(n)`.  The two cases are disjoint because
their strict inequalities point in opposite directions.  Consequently their
tagged union injects into the *same* root interval `{1,...,B}`, with no factor
for the number of prime coordinates and no separate instability budget.

This is a direct cardinality theorem.  The remaining repository-specific step
is to show that the actual tagged residual carrier produced by the sequential
matching algorithm satisfies these canonical data predicates.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- One canonical first-failure state, before adjoining its failing prime. -/
structure SquareRootLowPrimeFirstFailureState where
  base : ℕ
  deriving DecidableEq

/-- Arithmetic data required of a canonical first-failure root. -/
def SquareRootLowPrimeCanonicalFirstFailureData
    (K U B : ℕ) (z : SquareRootLowPrimeFirstFailureState) : Prop :=
  0 < z.base ∧
    (squareRootLowPrimeCanonicalFailurePrime K U B z.base).Prime ∧
    K < squareRootLowPrimeCanonicalFailurePrime K U B z.base ∧
    squareRootLowPrimeCanonicalFailurePrime K U B z.base ≤ U ∧
    ¬ squareRootLowPrimeCanonicalFailurePrime K U B z.base ∣ z.base ∧
    canonicalLargestPrimeFactor z.base <
      squareRootLowPrimeCanonicalFailurePrime K U B z.base ∧
    z.base ≤ B ∧
    B < squareRootLowPrimeCanonicalFailurePrime K U B z.base * z.base

/-- The two genuinely distinct chronological residual types. -/
inductive SquareRootLowPrimeCanonicalToggleState where
  | noToggle (z : SquareRootLowPrimeFirstFailureState)
  | unstable (z : SquareRootLowPrimeDoubleToggleState)
  deriving DecidableEq

/-- Canonical arithmetic data on the tagged residual union. -/
def SquareRootLowPrimeCanonicalToggleData
    (K U B : ℕ) : SquareRootLowPrimeCanonicalToggleState → Prop
  | .noToggle z => SquareRootLowPrimeCanonicalFirstFailureData K U B z
  | .unstable z => SquareRootLowPrimeCanonicalDoubleToggleData K U B z

/-- Both residual types charge to their last still-admissible root state. -/
def squareRootLowPrimeCanonicalToggleRootCharge :
    SquareRootLowPrimeCanonicalToggleState → ℕ
  | .noToggle z => z.base
  | .unstable z => squareRootLowPrimeSecondToggleRootCharge z

/-- A canonical first-failure charge lies in the root interval. -/
theorem squareRootLowPrimeFirstFailureRootCharge_mem_Icc
    {K U B : ℕ} {z : SquareRootLowPrimeFirstFailureState}
    (hz : SquareRootLowPrimeCanonicalFirstFailureData K U B z) :
    z.base ∈ Finset.Icc 1 B := by
  exact Finset.mem_Icc.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hz.1), hz.2.2.2.2.2.2.1⟩

/-- Every canonical toggle residual charges into the same root interval. -/
theorem squareRootLowPrimeCanonicalToggleRootCharge_mem_Icc
    {K U B : ℕ} {z : SquareRootLowPrimeCanonicalToggleState}
    (hz : SquareRootLowPrimeCanonicalToggleData K U B z) :
    squareRootLowPrimeCanonicalToggleRootCharge z ∈ Finset.Icc 1 B := by
  rcases z with z | z
  · exact squareRootLowPrimeFirstFailureRootCharge_mem_Icc hz
  · exact squareRootLowPrimeSecondToggleRootCharge_mem_Icc hz

/-- The no-toggle and instability tags cannot share a root charge: the
canonical failing prime lies above the largest prime in the first case and
below it in the second. -/
theorem squareRootLowPrimeCanonicalToggleRootCharge_injective
    {K U B : ℕ} {x y : SquareRootLowPrimeCanonicalToggleState}
    (hx : SquareRootLowPrimeCanonicalToggleData K U B x)
    (hy : SquareRootLowPrimeCanonicalToggleData K U B y)
    (hcharge : squareRootLowPrimeCanonicalToggleRootCharge x =
      squareRootLowPrimeCanonicalToggleRootCharge y) :
    x = y := by
  rcases x with x | x
  · rcases y with y | y
    · change x.base = y.base at hcharge
      rcases x with ⟨xbase⟩
      rcases y with ⟨ybase⟩
      simp only at hcharge
      subst ybase
      rfl
    · have hxrough :
          canonicalLargestPrimeFactor x.base <
            squareRootLowPrimeCanonicalFailurePrime K U B x.base :=
        hx.2.2.2.2.2.1
      have hycoord := squareRootLowPrimeSecondToggleRootCharge_coordinates hy
      have hypivots : y.firstPivot < y.secondPivot := hy.2.2.2.2.1
      have hycanonical :
          y.firstPivot = squareRootLowPrimeCanonicalFailurePrime K U B
            (squareRootLowPrimeSecondToggleRootCharge y) :=
        hy.2.2.2.2.2.1
      change x.base = squareRootLowPrimeSecondToggleRootCharge y at hcharge
      rw [hcharge, hycoord.1, ← hycanonical] at hxrough
      omega
  · rcases y with y | y
    · have hyrough :
          canonicalLargestPrimeFactor y.base <
            squareRootLowPrimeCanonicalFailurePrime K U B y.base :=
        hy.2.2.2.2.2.1
      have hxcoord := squareRootLowPrimeSecondToggleRootCharge_coordinates hx
      have hxpivots : x.firstPivot < x.secondPivot := hx.2.2.2.2.1
      have hxcanonical :
          x.firstPivot = squareRootLowPrimeCanonicalFailurePrime K U B
            (squareRootLowPrimeSecondToggleRootCharge x) :=
        hx.2.2.2.2.2.1
      change squareRootLowPrimeSecondToggleRootCharge x = y.base at hcharge
      rw [← hcharge, hxcoord.1, ← hxcanonical] at hyrough
      omega
    · exact congrArg SquareRootLowPrimeCanonicalToggleState.unstable
        (squareRootLowPrimeSecondToggleRootCharge_injective hx hy hcharge)

/-- **Combined cardinality theorem.**  Canonical no-toggle and canonical
instability residuals together occupy at most `B` root states. -/
theorem squareRootLowPrimeCanonicalToggleStates_card_le_bound
    {K U B : ℕ} (S : Finset SquareRootLowPrimeCanonicalToggleState)
    (hdata : ∀ z ∈ S, SquareRootLowPrimeCanonicalToggleData K U B z) :
    S.card ≤ B := by
  have hinj : Set.InjOn squareRootLowPrimeCanonicalToggleRootCharge (↑S) := by
    intro x hx y hy hxy
    exact squareRootLowPrimeCanonicalToggleRootCharge_injective
      (hdata x hx) (hdata y hy) hxy
  have hsubset :
      S.image squareRootLowPrimeCanonicalToggleRootCharge ⊆ Finset.Icc 1 B := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
    exact squareRootLowPrimeCanonicalToggleRootCharge_mem_Icc (hdata z hz)
  calc
    S.card = (S.image squareRootLowPrimeCanonicalToggleRootCharge).card := by
      symm
      exact Finset.card_image_iff.mpr hinj
    _ ≤ (Finset.Icc 1 B).card := Finset.card_le_card hsubset
    _ = B := by simp

end RHLean.Proof
