import Mathlib
import RHLean.Proof.ExactPrefixPopulationIdentity
import RHLean.Proof.OneBlockInvariant

/-!
# Seeded exact-population induction

Start from completed seed blocks `1` and `2`, then invoke the existing one-block
extension constructor.  At every stage, retain the exact statement that each
square block already reached by the induction is populated from the frozen
prefix with precisely its actual Mobius mass.

This proves the seed-to-all-block propagation of the population mechanism.  It
does not insert a quantitative cancellation estimate into the extension data;
that remains the arithmetic estimate to be supplied.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- One-block extension law needed only from the completed seed stage onward. -/
def SeededOneBlockExtensionLaw : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ hN : OneBlockInvariant N,
    Nonempty (OneBlockExtensionData N hN)

/-- The one-block invariant together with exact prefix population for every
block reached through the next inherited block. -/
structure SeededPopulationInvariant (N : ℕ) where
  oneBlock : OneBlockInvariant N
  exactPopulationThrough :
    ∀ a : ℕ, 3 ≤ a → a ≤ N + 1 →
      canonicalPrefixPopulationMass a = squareBlockMoebius a

/-- The completed seed stage initializes exact population at the first generated
block, block `3`. -/
def seededPopulationInvariant_two
    (hseed : OneBlockInvariant 2) :
    SeededPopulationInvariant 2 where
  oneBlock := hseed
  exactPopulationThrough := by
    intro a ha hupper
    have ha3 : a = 3 := by omega
    subst a
    exact canonicalPrefixPopulationMass_eq_squareBlockMoebius (by omega)

/-- One exact extension step.  The old exact population identities are retained,
and the newly inherited block is populated exactly by the canonical prefix
mechanism. -/
def seededPopulationInvariant_succ
    {N : ℕ} (hN : SeededPopulationInvariant N)
    (hstep : OneBlockExtensionData N hN.oneBlock) :
    SeededPopulationInvariant (N + 1) where
  oneBlock := oneBlockInvariant_succ hN.oneBlock hstep
  exactPopulationThrough := by
    intro a ha hupper
    by_cases hold : a ≤ N + 1
    · exact hN.exactPopulationThrough a ha hold
    · have hnew : a = N + 2 := by omega
      subst a
      exact canonicalPrefixPopulationMass_eq_squareBlockMoebius (by omega)

/-- Starting from the completed seed and repeatedly invoking one-block
extension yields the exact population mechanism at every finite stage. -/
theorem seededPopulationInvariant_all
    (hseed : OneBlockInvariant 2)
    (hlaw : SeededOneBlockExtensionLaw) :
    ∀ k : ℕ, Nonempty (SeededPopulationInvariant (2 + k)) := by
  intro k
  induction k with
  | zero =>
      exact ⟨seededPopulationInvariant_two hseed⟩
  | succ k ih =>
      obtain ⟨hN⟩ := ih
      have hNge : 2 ≤ 2 + k := by omega
      obtain ⟨hstep⟩ := hlaw (2 + k) hNge hN.oneBlock
      have hs := seededPopulationInvariant_succ hN hstep
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (show Nonempty (SeededPopulationInvariant ((2 + k) + 1)) from ⟨hs⟩)

/-- Direct seed-to-block formulation: every target block `a ≥ 3` appears in a
finite seeded stage and therefore satisfies the exact population identity. -/
theorem exact_population_from_seed_and_oneBlockExtension
    (hseed : OneBlockInvariant 2)
    (hlaw : SeededOneBlockExtensionLaw)
    {a : ℕ} (ha : 3 ≤ a) :
    canonicalPrefixPopulationMass a = squareBlockMoebius a := by
  let k := a - 3
  obtain ⟨hstage⟩ := seededPopulationInvariant_all hseed hlaw k
  apply hstage.exactPopulationThrough a ha
  dsimp [k]
  omega

end RHLean.Proof
