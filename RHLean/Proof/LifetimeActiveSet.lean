import Mathlib
import RHLean.Proof.LifetimeOverlapKernel

/-!
# Exact lifetime active-set bridge

This module identifies the stage-`t` lifetime-active atoms with the existing
birth-high survivors and their Möbius amplitude.  It is entirely exact and
introduces no analytic premise.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- Birth-high atoms through stage `t` that are alive at stage `t`. -/
noncomputable def lifetimeActiveAtomSet (Λ : ℝ) (t : ℕ) : Finset CanonicalSourceAtom := by
  classical
  exact (birthCanonicalHighAtomSet Λ t).filter fun p => IsLifetimeActive Λ p t

/-- Every atom in the birth-high universe through `t` has already been born. -/
theorem birthCanonicalHighAtom_birth_le
    (Λ : ℝ) (t : ℕ) {p : CanonicalSourceAtom}
    (hp : p ∈ birthCanonicalHighAtomSet Λ t) : p.1 ≤ t := by
  classical
  rcases Finset.mem_sigma.mp hp with ⟨hpRange, hpBlock⟩
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hpRange)

/-- Lifetime activity on the stage-`t` birth universe is equivalent to current
moving-high membership. -/
theorem lifetimeActive_iff_movingHigh_of_birthHigh
    (Λ : ℝ) (t : ℕ) {p : CanonicalSourceAtom}
    (hp : p ∈ birthCanonicalHighAtomSet Λ t) :
    IsLifetimeActive Λ p t ↔ IsMovingCanonicalHigh Λ t p.2 := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨birthCanonicalHighAtom_birth_le Λ t hp, h⟩

/-- The lifetime-active set is exactly the existing birth-high survivor set. -/
theorem lifetimeActiveAtomSet_eq_stillHigh
    (Λ : ℝ) (t : ℕ) :
    lifetimeActiveAtomSet Λ t = birthCanonicalStillHighAtomSet Λ t := by
  classical
  ext p
  simp only [lifetimeActiveAtomSet, birthCanonicalStillHighAtomSet,
    Finset.mem_filter]
  constructor
  · rintro ⟨hpBirth, hpActive⟩
    exact ⟨hpBirth, hpActive.2⟩
  · rintro ⟨hpBirth, hpMoving⟩
    exact ⟨hpBirth, (lifetimeActive_iff_movingHigh_of_birthHigh Λ t hpBirth).2 hpMoving⟩

/-- Möbius amplitude of the exact lifetime-active population. -/
def lifetimeActiveAtomMass (Λ : ℝ) (t : ℕ) : ℂ :=
  canonicalAtomMass (lifetimeActiveAtomSet Λ t)

/-- The active-set mass is exactly the existing survivor mass. -/
theorem lifetimeActiveAtomMass_eq_stillHighMass
    (Λ : ℝ) (t : ℕ) :
    lifetimeActiveAtomMass Λ t = birthCanonicalStillHighAtomMass Λ t := by
  unfold lifetimeActiveAtomMass birthCanonicalStillHighAtomMass
  rw [lifetimeActiveAtomSet_eq_stillHigh]

/-- The canonical lifetime amplitude with terminal stage equal to the observation
stage is exactly the active-set mass. -/
theorem canonicalLifetimeAmplitude_self_eq_activeMass
    (Λ : ℝ) (t : ℕ) :
    canonicalLifetimeAmplitude Λ t t = lifetimeActiveAtomMass Λ t := by
  classical
  unfold canonicalLifetimeAmplitude canonicalLifetimeUniverse lifetimeAmplitude
    lifetimeActiveAtomMass canonicalAtomMass lifetimeActiveAtomSet
  simp [canonicalHighAtomWeight, Finset.sum_filter]

/-- Exact decomposition of the existing canonical high prefix into the
lifetime-active mass and absorbed mass. -/
theorem canonicalHighPrefix_eq_lifetimeActive_add_absorbed
    (Λ : ℝ) (t : ℕ) :
    canonicalHighPrefix Λ t =
      lifetimeActiveAtomMass Λ t + absorbedCanonicalHighAtomMass Λ t := by
  rw [lifetimeActiveAtomMass_eq_stillHighMass]
  exact canonicalHighPrefix_eq_still_add_absorbed Λ t

end RHLean.Proof
