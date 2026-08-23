import Mathlib
import RHLean.Arithmetic.PrimeSquareCollisionPhysicalFibreNoGo
import RHLean.Analysis.SquarePrefixMertensBridge

open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-!
# No-go theorem for a literal bounded collision-defect quotient

The local collision involution has at most three stranded labels per frontier.
The natural global proposal is therefore a chain of at most `n+1` such defects
representing the square-prefix value `M((n+1)^2-1)`.

This file tests the strongest literal realization of that proposal: every defect
label is weighted by the corrected prime-wheel field on the same physical site
that realizes its selected-prime square collision.

That realization is impossible for a nonzero target.  Every such corrected-site
weight vanishes at the square hit, so every step mass and hence every finite
bounded chain mass is zero.  The first nontrivial square prefix is `-1`, giving a
concrete kernel-checked contradiction to a global literal quotient statement.

The conclusion is intentionally narrow but decisive: a viable collision quotient
must transport a collision label to a different arithmetic fibre before reading
its corrected-field weight.  Such a transport must then be separately proved to
preserve the square-block mass and to have bounded global multiplicity.
-/

/-- Literal realization of the existing bounded collision-defect architecture.
There are at most `n+1` steps, and each step uses the already-defined defect part
of one nine-label collision frontier.  The new physical-faithfulness condition
is that the represented corrected-field site is the selected-prime square-hit
site named by the collision coordinate. -/
structure LiteralSquarePrefixCollisionDefectQuotient (n : ℕ) where
  steps : Finset ℕ
  steps_bounded : steps ⊆ Finset.range (n + 1)
  frontier : ℕ → Finset TwoPrimeCollisionState
  S : ℕ → Finset ℕ
  upper : ℕ → ℕ
  p : ℕ → ℕ
  site : ℕ → TwoPrimeCollisionState → ℕ
  selected : ∀ t ∈ steps, p t ∈ S t
  literal_square_hit : ∀ t ∈ steps,
    ∀ s ∈ collisionInvolutionDefectPart (frontier t),
      (p t) ^ 2 ∣ site t s
  represents :
    squarePrefixMertens n =
      ((∑ t ∈ steps,
          ∑ s ∈ collisionInvolutionDefectPart (frontier t),
            correctedCollisionSiteWeight (S t) (upper t) (site t) s : ℤ) : ℂ)

namespace LiteralSquarePrefixCollisionDefectQuotient

/-- One literal physical collision step has zero corrected-field mass. -/
theorem step_mass_eq_zero
    {n : ℕ} (Q : LiteralSquarePrefixCollisionDefectQuotient n)
    {t : ℕ} (ht : t ∈ Q.steps) :
    (∑ s ∈ collisionInvolutionDefectPart (Q.frontier t),
      correctedCollisionSiteWeight (Q.S t) (Q.upper t) (Q.site t) s) = 0 := by
  exact sum_correctedCollisionSiteWeight_eq_zero_of_literal_square_hit
    (Q.S t) (Q.upper t) (Q.p t) (Q.site t)
    (Q.selected t ht)
    (collisionInvolutionDefectPart (Q.frontier t))
    (Q.literal_square_hit t ht)

/-- Consequently the complete bounded chain mass is zero. -/
theorem total_mass_eq_zero
    {n : ℕ} (Q : LiteralSquarePrefixCollisionDefectQuotient n) :
    (∑ t ∈ Q.steps,
      ∑ s ∈ collisionInvolutionDefectPart (Q.frontier t),
        correctedCollisionSiteWeight (Q.S t) (Q.upper t) (Q.site t) s) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t ht
  exact Q.step_mass_eq_zero ht

/-- Any literal bounded collision-defect quotient therefore forces its target
square-prefix Mertens value to vanish. -/
theorem target_eq_zero
    {n : ℕ} (Q : LiteralSquarePrefixCollisionDefectQuotient n) :
    squarePrefixMertens n = 0 := by
  rw [Q.represents, Q.total_mass_eq_zero]
  norm_num

end LiteralSquarePrefixCollisionDefectQuotient

/-- Any nonzero square-prefix value excludes a literal collision-site quotient
at that endpoint. -/
theorem no_literalSquarePrefixCollisionDefectQuotient_of_ne_zero
    {n : ℕ} (hn : squarePrefixMertens n ≠ 0) :
    ¬ Nonempty (LiteralSquarePrefixCollisionDefectQuotient n) := by
  rintro ⟨Q⟩
  exact hn Q.target_eq_zero

/-- The first nontrivial square prefix is already nonzero. -/
theorem squarePrefixMertens_one_eq_neg_one :
    squarePrefixMertens 1 = -1 := by
  change mertensSummatory 3 = -1
  rw [mertensSummatory_succ 2, mertensSummatory_succ 1,
    mertensSummatory_succ 0, mertensSummatory_zero]
  have hmu2 : μ 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hmu3 : μ 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  norm_num [hmu2, hmu3]

/-- Concrete no-go witness for the current literal collision-site coordinates. -/
theorem no_literalSquarePrefixCollisionDefectQuotient_at_one :
    ¬ Nonempty (LiteralSquarePrefixCollisionDefectQuotient 1) := by
  apply no_literalSquarePrefixCollisionDefectQuotient_of_ne_zero
  rw [squarePrefixMertens_one_eq_neg_one]
  norm_num

/-- Global proposal: construct one literal bounded collision-defect quotient at
every square-prefix endpoint. -/
def LiteralSquarePrefixCollisionDefectQuotientStatement : Prop :=
  ∀ n : ℕ, Nonempty (LiteralSquarePrefixCollisionDefectQuotient n)

/-- **Current-coordinate no-go.**  The global literal quotient proposal is
false.  Any successful bounded-multiplicity quotient must leave the literal
square-hit site fibre and supply a separately justified transport map. -/
theorem not_literalSquarePrefixCollisionDefectQuotientStatement :
    ¬ LiteralSquarePrefixCollisionDefectQuotientStatement := by
  intro h
  exact no_literalSquarePrefixCollisionDefectQuotient_at_one (h 1)

end RHLean.Analysis
