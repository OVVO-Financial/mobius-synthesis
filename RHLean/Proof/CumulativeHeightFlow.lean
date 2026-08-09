import Mathlib
import RHLean.Analysis.CanonicalHighSectorCore

/-!
# Cumulative moving-boundary height flow

This Proof-side module introduces the genuinely cumulative high sector at stage
`N`: every source in the square prefix through `(N+1)^2-1` is reclassified
against the current threshold `Λ N`.

It then defines the exact exit and entry sets between consecutive stages and
proves the set-level and Möbius-sum recurrences.  No occupancy, cancellation,
or asymptotic premise is used.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- The complete source population through the square-prefix endpoint
`(N+1)^2-1`, represented as the half-open range `[0,(N+1)^2)`. -/
def cumulativeSquarePrefixSet (N : ℕ) : Finset ℕ :=
  Finset.range ((N + 1) ^ 2)

/-- Current-cutoff high membership.  The repository stores doubled height, so
`|Y_m| > Λ N` is written as `|2Y_m| > 2 Λ N`. -/
def IsMovingCanonicalHigh (Λ : ℝ) (N m : ℕ) : Prop :=
  2 * Λ * (N : ℝ) < abs (canonicalHeightTwice m)

/-- The cumulative population still high at the current cutoff `N`. -/
noncomputable def movingCanonicalHighSet (Λ : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (cumulativeSquarePrefixSet N).filter (IsMovingCanonicalHigh Λ N)

/-- Sources that were high at `N` but are no longer high at `N+1`. -/
noncomputable def movingCanonicalCrossingSet (Λ : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact movingCanonicalHighSet Λ N \ movingCanonicalHighSet Λ (N + 1)

/-- Sources high at `N+1` that were not in the high population at `N`.
This definition automatically includes the genuinely new square-strip entrants
and excludes all sources already resident in the old high population. -/
noncomputable def movingCanonicalEntrySet (Λ : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact movingCanonicalHighSet Λ (N + 1) \ movingCanonicalHighSet Λ N

/-- Möbius mass of a finite source population. -/
def canonicalMoebiusMass (s : Finset ℕ) : ℂ :=
  ∑ m ∈ s, canonicalMoebiusWeight m

/-- Cumulative moving-boundary high-sector sum. -/
def movingCanonicalHighSum (Λ : ℝ) (N : ℕ) : ℂ :=
  canonicalMoebiusMass (movingCanonicalHighSet Λ N)

/-- Signed mass leaving the moving high population at the next reset. -/
def movingCanonicalCrossingMass (Λ : ℝ) (N : ℕ) : ℂ :=
  canonicalMoebiusMass (movingCanonicalCrossingSet Λ N)

/-- Signed mass entering the moving high population at the next reset. -/
def movingCanonicalEntryMass (Λ : ℝ) (N : ℕ) : ℂ :=
  canonicalMoebiusMass (movingCanonicalEntrySet Λ N)

/-- Exact population recurrence for an arbitrary pair of finite sets. -/
theorem finset_eq_sdiff_union_sdiff
    {α : Type*} [DecidableEq α] (A B : Finset α) :
    B = (A \ (A \ B)) ∪ (B \ A) := by
  ext x
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [hxA, hxB]

/-- Exact cumulative moving-boundary population recurrence. -/
theorem movingCanonicalHighSet_succ
    (Λ : ℝ) (N : ℕ) :
    movingCanonicalHighSet Λ (N + 1) =
      (movingCanonicalHighSet Λ N \ movingCanonicalCrossingSet Λ N) ∪
        movingCanonicalEntrySet Λ N := by
  classical
  unfold movingCanonicalCrossingSet movingCanonicalEntrySet
  exact finset_eq_sdiff_union_sdiff
    (movingCanonicalHighSet Λ N) (movingCanonicalHighSet Λ (N + 1))

/-- The retained old population and the new entry population are disjoint. -/
theorem movingCanonicalRetained_disjoint_entry
    (Λ : ℝ) (N : ℕ) :
    Disjoint
      (movingCanonicalHighSet Λ N \ movingCanonicalCrossingSet Λ N)
      (movingCanonicalEntrySet Λ N) := by
  classical
  rw [Finset.disjoint_left]
  intro m hmRetained hmEntry
  have hmOld : m ∈ movingCanonicalHighSet Λ N := by
    exact (Finset.mem_sdiff.mp hmRetained).1
  have hmNotOld : m ∉ movingCanonicalHighSet Λ N := by
    exact (Finset.mem_sdiff.mp hmEntry).2
  exact hmNotOld hmOld

/-- The crossing population is a subset of the old high population. -/
theorem movingCanonicalCrossingSet_subset
    (Λ : ℝ) (N : ℕ) :
    movingCanonicalCrossingSet Λ N ⊆ movingCanonicalHighSet Λ N := by
  classical
  intro m hm
  exact (Finset.mem_sdiff.mp hm).1

/-- Exact signed recurrence:

`new high = old high + entries - crossings`.
-/
theorem movingCanonicalHighSum_succ
    (Λ : ℝ) (N : ℕ) :
    movingCanonicalHighSum Λ (N + 1) =
      movingCanonicalHighSum Λ N + movingCanonicalEntryMass Λ N -
        movingCanonicalCrossingMass Λ N := by
  classical
  unfold movingCanonicalHighSum movingCanonicalEntryMass
    movingCanonicalCrossingMass canonicalMoebiusMass
  rw [movingCanonicalHighSet_succ]
  rw [Finset.sum_union (movingCanonicalRetained_disjoint_entry Λ N)]
  have hcross := movingCanonicalCrossingSet_subset Λ N
  have hpartition :
      (∑ m ∈ movingCanonicalHighSet Λ N \ movingCanonicalCrossingSet Λ N,
          canonicalMoebiusWeight m) +
        ∑ m ∈ movingCanonicalCrossingSet Λ N, canonicalMoebiusWeight m =
          ∑ m ∈ movingCanonicalHighSet Λ N, canonicalMoebiusWeight m := by
    exact Finset.sum_sdiff hcross
  rw [← hpartition]
  ring

/-- Entry membership is exactly membership at the new stage without membership
at the old stage. -/
theorem mem_movingCanonicalEntrySet_iff
    (Λ : ℝ) (N m : ℕ) :
    m ∈ movingCanonicalEntrySet Λ N ↔
      m ∈ movingCanonicalHighSet Λ (N + 1) ∧
        m ∉ movingCanonicalHighSet Λ N := by
  classical
  simp [movingCanonicalEntrySet]

/-- Crossing membership is exactly old-stage membership without new-stage
membership. -/
theorem mem_movingCanonicalCrossingSet_iff
    (Λ : ℝ) (N m : ℕ) :
    m ∈ movingCanonicalCrossingSet Λ N ↔
      m ∈ movingCanonicalHighSet Λ N ∧
        m ∉ movingCanonicalHighSet Λ (N + 1) := by
  classical
  simp [movingCanonicalCrossingSet]

end RHLean.Proof
