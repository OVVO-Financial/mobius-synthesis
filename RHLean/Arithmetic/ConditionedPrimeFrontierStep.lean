import Mathlib
import RHLean.Arithmetic.PrimeProductFrontierExhaustion

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- Prime-product admissibility after a selected extension set `A` has already
been inserted.  The remaining Boolean cube lives on coordinates outside `A`. -/
def conditionedPrimeProductAdmissible
    (S : Finset ℕ) (X : ℕ) (A : Finset ℕ) (t : Finset ℕ) : Prop :=
  primeProductAdmissible S X (A ∪ t)

/-- The alternating mass of the remaining free cube after inserting `A`. -/
def conditionedPrimeCubeAlternatingSum
    (S : Finset ℕ) (X : ℕ) (A : Finset ℕ) : ℤ :=
  truncatedCubeAlternatingSum (S \ A)
    (conditionedPrimeProductAdmissible S X A)

/-- Conditioned prime-product admissibility remains downward closed on the
free coordinates. -/
theorem conditionedPrimeProductAdmissible_downward
    {S A : Finset ℕ} {X : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    CubeDownwardClosed (conditionedPrimeProductAdmissible S X A) := by
  intro u v huv hv
  have hunion : A ∪ u ⊆ A ∪ v := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpA | hpu
    · exact Finset.mem_union_left _ hpA
    · exact Finset.mem_union_right _ (huv hpu)
  exact primeProductAdmissible_downward hprime
    (A ∪ u) (A ∪ v) hunion hv

/-- The generic first-failure boundary of the conditioned cube is exactly the
ordered prime-product frontier introduced in the exhaustion layer. -/
theorem firstFailureBoundary_conditioned_eq_ordered
    {S A : Finset ℕ} {X ell : ℕ} :
    firstFailureBoundary (S \ A) ell
        (conditionedPrimeProductAdmissible S X A) =
      orderedPrimeProductFrontier S X A ell := by
  classical
  ext t
  simp only [mem_firstFailureBoundary, mem_orderedPrimeProductFrontier]
  constructor
  · intro ht
    refine ⟨?_, ht.2.1, ?_⟩
    · intro p hp
      have hpDiff : p ∈ (S \ A).erase ell := ht.1 hp
      have hpBase := Finset.mem_erase.mp hpDiff
      have hpS : p ∈ S := (Finset.mem_sdiff.mp hpBase.2).1
      have hpA : p ∉ A := (Finset.mem_sdiff.mp hpBase.2).2
      have hpEll : p ≠ ell := hpBase.1
      exact Finset.mem_sdiff.mpr ⟨hpS, by
        intro hpInsert
        rcases Finset.mem_insert.mp hpInsert with hpeq | hpInA
        · exact hpEll hpeq
        · exact hpA hpInA⟩
    · simpa [conditionedPrimeProductAdmissible,
        Finset.union_assoc, Finset.union_left_comm,
        Finset.union_comm] using ht.2.2
  · intro ht
    refine ⟨?_, ht.2.1, ?_⟩
    · intro p hp
      have hpDiff := ht.1 hp
      have hpS : p ∈ S := (Finset.mem_sdiff.mp hpDiff).1
      have hpNotInsert : p ∉ insert ell A :=
        (Finset.mem_sdiff.mp hpDiff).2
      have hpEll : p ≠ ell := by
        intro hpeq
        exact hpNotInsert (by simp [hpeq])
      have hpA : p ∉ A := by
        intro hpInA
        exact hpNotInsert (Finset.mem_insert_of_mem hpInA)
      exact Finset.mem_erase.mpr ⟨hpEll,
        Finset.mem_sdiff.mpr ⟨hpS, hpA⟩⟩
    · simpa [conditionedPrimeProductAdmissible,
        Finset.union_assoc, Finset.union_left_comm,
        Finset.union_comm] using ht.2.2

/-- Exact one-step ordered frontier identity.

After a selected set `A` has been inserted, choose a fresh coordinate `ell`.
All complete parent/child pairs in the remaining free cube cancel, and the
entire conditioned alternating mass is carried by the ordered first-failure
frontier at `ell`. -/
theorem conditionedPrimeCubeAlternatingSum_eq_orderedFrontier
    {S A : Finset ℕ} {X ell : ℕ}
    (hell : ell ∈ S \ A)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    conditionedPrimeCubeAlternatingSum S X A =
      ∑ t ∈ orderedPrimeProductFrontier S X A ell,
        booleanCubeSign t := by
  unfold conditionedPrimeCubeAlternatingSum
  rw [truncatedCubeAlternatingSum_eq_firstFailureBoundary hell
    (conditionedPrimeProductAdmissible_downward hprime)]
  unfold firstFailureBoundaryAlternatingSum
  rw [firstFailureBoundary_conditioned_eq_ordered]

end RHLean.Arithmetic
