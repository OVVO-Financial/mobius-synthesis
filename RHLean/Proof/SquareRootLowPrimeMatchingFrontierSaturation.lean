import Mathlib
import RHLean.Proof.SquareRootLowPrimeSignedResponseMatching

/-!
# Fresh-prime saturation of the complete response matching frontier

The sequential matching frontier is not merely a smaller carrier with the same
Möbius mass.  After a coordinate `ell` has been processed, the surviving set
contains no full edge

`n <-> ell*n`

with `ell ∤ n`.  Later matching steps only remove states, so this property
persists.  Consequently the terminal response frontier is independent in every
fresh-prime direction.

This is the structural input needed to charge the remaining states through an
existing cofactor-to-root map: a complete fresh-prime fibre cannot survive.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- One matching step only removes states. -/
theorem squareRootLowPrimeResponseFrontierStep_subset
    (S : Finset ℕ) (ell : ℕ) :
    squareRootLowPrimeResponseFrontierStep S ell ⊆ S := by
  intro n hn
  exact (Finset.mem_sdiff.mp hn).1

/-- Iterated matching only removes states from the initial carrier. -/
theorem squareRootLowPrimeResponseMatchingFrontier_subset
    (ells : List ℕ) (S : Finset ℕ) :
    squareRootLowPrimeResponseMatchingFrontier ells S ⊆ S := by
  induction ells generalizing S with
  | nil =>
      intro n hn
      simpa [squareRootLowPrimeResponseMatchingFrontier] using hn
  | cons ell ells ih =>
      exact (ih (squareRootLowPrimeResponseFrontierStep S ell)).trans
        (squareRootLowPrimeResponseFrontierStep_subset S ell)

/-- After processing `ell`, no complete `ell`-edge remains. -/
theorem squareRootLowPrimeResponseFrontierStep_pair_free
    {S : Finset ℕ} {ell n : ℕ}
    (hn : n ∈ squareRootLowPrimeResponseFrontierStep S ell)
    (hnot : ¬ ell ∣ n) :
    ell * n ∉ squareRootLowPrimeResponseFrontierStep S ell := by
  rcases Finset.mem_sdiff.mp hn with ⟨hnS, hnNotPaired⟩
  intro hm
  have hmS : ell * n ∈ S :=
    (squareRootLowPrimeResponseFrontierStep_subset S ell) hm
  have hnLower : n ∈ squareRootLowPrimeResponsePairLower S ell :=
    mem_squareRootLowPrimeResponsePairLower.mpr ⟨hnS, hnot, hmS⟩
  apply hnNotPaired
  exact Finset.mem_union.mpr (Or.inl hnLower)

/-- Pair-freeness in any already-processed direction persists through all later
matching steps. -/
theorem squareRootLowPrimeResponseMatchingFrontier_pair_free
    (ells : List ℕ) (S : Finset ℕ) {ell n : ℕ}
    (hell : ell ∈ ells)
    (hn : n ∈ squareRootLowPrimeResponseMatchingFrontier ells S)
    (hnot : ¬ ell ∣ n) :
    ell * n ∉ squareRootLowPrimeResponseMatchingFrontier ells S := by
  induction ells generalizing S with
  | nil => simp at hell
  | cons q qs ih =>
      rcases List.mem_cons.mp hell with hEq | hTail
      · subst q
        have hsub :=
          squareRootLowPrimeResponseMatchingFrontier_subset qs
            (squareRootLowPrimeResponseFrontierStep S ell)
        have hnStep :
            n ∈ squareRootLowPrimeResponseFrontierStep S ell := hsub hn
        intro hmFinal
        have hmStep :
            ell * n ∈ squareRootLowPrimeResponseFrontierStep S ell :=
          hsub hmFinal
        exact
          (squareRootLowPrimeResponseFrontierStep_pair_free hnStep hnot)
            hmStep
      · exact ih (squareRootLowPrimeResponseFrontierStep S q)
          hTail hn

/-- The complete owned matching frontier is pair-free in every actual fresh
prime direction. -/
theorem squareRootLowPrimeOwnedResponseMatchingFrontier_pair_free
    {R K U ell n : ℕ}
    (hell : ell ∈ squareRootLowPrimeFreshPrimeList K U)
    (hn : n ∈ squareRootLowPrimeOwnedResponseMatchingFrontier R K U)
    (hnot : ¬ ell ∣ n) :
    ell * n ∉ squareRootLowPrimeOwnedResponseMatchingFrontier R K U := by
  unfold squareRootLowPrimeOwnedResponseMatchingFrontier at hn ⊢
  exact squareRootLowPrimeResponseMatchingFrontier_pair_free
    (squareRootLowPrimeFreshPrimeList K U)
    (squareRootLowPrimeOwnedResponseChildren R K U)
    hell hn hnot

/-- Every matched frontier state still lies in the exact arithmetic response
child carrier. -/
theorem squareRootLowPrimeOwnedResponseMatchingFrontier_subset_children
    (R K U : ℕ) :
    squareRootLowPrimeOwnedResponseMatchingFrontier R K U ⊆
      squareRootLowPrimeOwnedResponseChildren R K U := by
  unfold squareRootLowPrimeOwnedResponseMatchingFrontier
  exact squareRootLowPrimeResponseMatchingFrontier_subset _ _

/-- Hence every matched frontier state remains below the square endpoint. -/
theorem squareRootLowPrimeOwnedResponseMatchingFrontier_subset_Icc
    (R K U : ℕ) :
    squareRootLowPrimeOwnedResponseMatchingFrontier R K U ⊆
      Finset.Icc 1 (squareRootEndpoint R) := by
  exact
    (squareRootLowPrimeOwnedResponseMatchingFrontier_subset_children R K U).trans
      squareRootLowPrimeOwnedResponseChildren_subset_Icc

end RHLean.Proof
