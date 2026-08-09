import Mathlib
import RHLean.Analysis.CanonicalHighSectorCore
import RHLean.Proof.CumulativeHeightFlow

/-!
# Birth-scale high mass, current survivors, and absorption

The existing `canonicalHighPrefix` classifies each source using the threshold of
its birth block.  The cumulative moving-boundary flow reclassifies the entire
prefix using the current threshold.  This Proof-side module keeps the block
index attached to every source and proves the exact decomposition of the
birth-high population into

* birth-high atoms still high at the current cutoff; and
* birth-high atoms already absorbed by the moving boundary.

No asymptotic or cancellation premise is introduced.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- A canonical source atom retains both its birth block and its integer. -/
abbrev CanonicalSourceAtom := Sigma fun _ : ℕ => ℕ

/-- All birth-scale high atoms through block `N`. -/
noncomputable def birthCanonicalHighAtomSet
    (Λ : ℝ) (N : ℕ) : Finset CanonicalSourceAtom := by
  classical
  exact (Finset.range (N + 1)).sigma fun j =>
    (canonicalSquareBlock j).filter fun m => IsCanonicalHighHeight Λ j m

/-- Birth-high atoms that remain high under the current stage-`N` threshold. -/
noncomputable def birthCanonicalStillHighAtomSet
    (Λ : ℝ) (N : ℕ) : Finset CanonicalSourceAtom := by
  classical
  exact (birthCanonicalHighAtomSet Λ N).filter fun p =>
    IsMovingCanonicalHigh Λ N p.2

/-- Birth-high atoms already absorbed by the moving stage-`N` boundary. -/
noncomputable def absorbedCanonicalHighAtomSet
    (Λ : ℝ) (N : ℕ) : Finset CanonicalSourceAtom := by
  classical
  exact birthCanonicalHighAtomSet Λ N \ birthCanonicalStillHighAtomSet Λ N

/-- Möbius mass of a finite atom population. -/
def canonicalAtomMass (s : Finset CanonicalSourceAtom) : ℂ :=
  ∑ p ∈ s, canonicalMoebiusWeight p.2

/-- Birth-scale high mass written as an atom sum. -/
def birthCanonicalHighAtomMass (Λ : ℝ) (N : ℕ) : ℂ :=
  canonicalAtomMass (birthCanonicalHighAtomSet Λ N)

/-- Current survivors among the birth-high atoms. -/
def birthCanonicalStillHighAtomMass (Λ : ℝ) (N : ℕ) : ℂ :=
  canonicalAtomMass (birthCanonicalStillHighAtomSet Λ N)

/-- Signed absorbed birth-high mass. -/
def absorbedCanonicalHighAtomMass (Λ : ℝ) (N : ℕ) : ℂ :=
  canonicalAtomMass (absorbedCanonicalHighAtomSet Λ N)

/-- The still-high atom population is a subset of the birth-high population. -/
theorem birthCanonicalStillHighAtomSet_subset
    (Λ : ℝ) (N : ℕ) :
    birthCanonicalStillHighAtomSet Λ N ⊆ birthCanonicalHighAtomSet Λ N := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

/-- Exact birth-high population decomposition. -/
theorem birthCanonicalHighAtomSet_eq_still_union_absorbed
    (Λ : ℝ) (N : ℕ) :
    birthCanonicalHighAtomSet Λ N =
      birthCanonicalStillHighAtomSet Λ N ∪ absorbedCanonicalHighAtomSet Λ N := by
  classical
  unfold absorbedCanonicalHighAtomSet
  ext p
  by_cases hbirth : p ∈ birthCanonicalHighAtomSet Λ N
  · by_cases hstill : p ∈ birthCanonicalStillHighAtomSet Λ N
    · simp [hbirth, hstill]
    · simp [hbirth, hstill]
  · have hnotstill : p ∉ birthCanonicalStillHighAtomSet Λ N := by
      intro hp
      exact hbirth (birthCanonicalStillHighAtomSet_subset Λ N hp)
    simp [hbirth, hnotstill]

/-- The survivor and absorbed populations are disjoint. -/
theorem birthCanonicalStillHigh_disjoint_absorbed
    (Λ : ℝ) (N : ℕ) :
    Disjoint
      (birthCanonicalStillHighAtomSet Λ N)
      (absorbedCanonicalHighAtomSet Λ N) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpStill hpAbsorbed
  have hpNotStill : p ∉ birthCanonicalStillHighAtomSet Λ N := by
    exact (Finset.mem_sdiff.mp hpAbsorbed).2
  exact hpNotStill hpStill

/-- Exact signed decomposition of birth-high mass. -/
theorem birthCanonicalHighAtomMass_eq_still_add_absorbed
    (Λ : ℝ) (N : ℕ) :
    birthCanonicalHighAtomMass Λ N =
      birthCanonicalStillHighAtomMass Λ N +
        absorbedCanonicalHighAtomMass Λ N := by
  classical
  unfold birthCanonicalHighAtomMass birthCanonicalStillHighAtomMass
    absorbedCanonicalHighAtomMass canonicalAtomMass
  rw [birthCanonicalHighAtomSet_eq_still_union_absorbed]
  exact Finset.sum_union (birthCanonicalStillHigh_disjoint_absorbed Λ N)

/-- The atom formulation is exactly the repository's existing birth-scale
`canonicalHighPrefix`. -/
theorem birthCanonicalHighAtomMass_eq_canonicalHighPrefix
    (Λ : ℝ) (N : ℕ) :
    birthCanonicalHighAtomMass Λ N = canonicalHighPrefix Λ N := by
  classical
  unfold birthCanonicalHighAtomMass canonicalAtomMass birthCanonicalHighAtomSet
  rw [Finset.sum_sigma]
  simp [canonicalHighPrefix, canonicalHighIncrement, Finset.sum_filter]

/-- Exact bridge from the existing canonical high prefix to current survivors
plus absorbed birth-high mass. -/
theorem canonicalHighPrefix_eq_still_add_absorbed
    (Λ : ℝ) (N : ℕ) :
    canonicalHighPrefix Λ N =
      birthCanonicalStillHighAtomMass Λ N +
        absorbedCanonicalHighAtomMass Λ N := by
  rw [← birthCanonicalHighAtomMass_eq_canonicalHighPrefix]
  exact birthCanonicalHighAtomMass_eq_still_add_absorbed Λ N

/-- Membership in the absorbed population means birth-high membership together
with failure of current-cutoff high membership. -/
theorem mem_absorbedCanonicalHighAtomSet_iff
    (Λ : ℝ) (N : ℕ) (p : CanonicalSourceAtom) :
    p ∈ absorbedCanonicalHighAtomSet Λ N ↔
      p ∈ birthCanonicalHighAtomSet Λ N ∧
        ¬ IsMovingCanonicalHigh Λ N p.2 := by
  classical
  constructor
  · intro hp
    rcases Finset.mem_sdiff.mp hp with ⟨hpBirth, hpNotStill⟩
    refine ⟨hpBirth, ?_⟩
    intro hpMoving
    apply hpNotStill
    exact Finset.mem_filter.mpr ⟨hpBirth, hpMoving⟩
  · rintro ⟨hpBirth, hpNotMoving⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hpBirth, ?_⟩
    intro hpStill
    exact hpNotMoving (Finset.mem_filter.mp hpStill).2

end RHLean.Proof
