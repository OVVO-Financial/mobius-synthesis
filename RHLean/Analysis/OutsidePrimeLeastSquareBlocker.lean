import Mathlib
import RHLean.Analysis.PhysicalSquareCRTPeriodNoGo
import RHLean.Analysis.OutsidePrimeLeastSquareEndpoint

/-!
# Local least-square ownership and complete-super-orbit blocker

This module isolates two facts needed by the compensated q-square daughter
intertwining.

First, least-square ownership is genuinely local: `q` owns a physical edge
exactly when `q^2` hits one of the six active affine forms and no smaller prime
square does. No ambient prefix occurs in the statement.

Second, if a q-owned deletion cell belongs to the complete least-owner interior
of one square block, then the exact least-owner super-orbit period is at most the
square-block length bound `2*R+2`. Consequently any owner whose super-orbit
period is larger is forced into the aggregate incomplete endpoint.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-- **Local ownership characterization.** A prime `q` is the least square
owner of edge `k` iff it actually hits one active form and every smaller prime
fails to hit every active form. The criterion contains no prefix parameter. -/
theorem physicalLeastOddSquarePrime_eq_some_iff_local
    {k q : ℕ} (_hq : q.Prime) :
    physicalLeastOddSquarePrime k = some q ↔
      physicalSquarePrimeAtEdge k q ∧
        ∀ p : ℕ, p.Prime → p < q → ¬ physicalSquarePrimeAtEdge k p := by
  constructor
  · intro hleast
    refine ⟨physicalLeastOddSquarePrime_some_spec hleast, ?_⟩
    intro p hp hlt hpHit
    have hle := physicalLeastOddSquarePrime_le hleast hpHit
    omega
  · rintro ⟨hqHit, hsmall⟩
    classical
    have hex : ∃ p, physicalSquarePrimeAtEdge k p := ⟨q, hqHit⟩
    have hspec : physicalSquarePrimeAtEdge k (Nat.find hex) := Nat.find_spec hex
    have hle : Nat.find hex ≤ q := Nat.find_min' hex hqHit
    have hnotlt : ¬ Nat.find hex < q := by
      intro hlt
      exact hsmall (Nat.find hex) hspec.1 hlt hspec
    have heq : Nat.find hex = q := by omega
    simp [physicalLeastOddSquarePrime, hex, heq]

/-- **Complete-owner period bound.** Any cell retained in the complete
least-owner interior with owner `q` carries its entire exact super-orbit inside
the physical square block. Hence that super-orbit period is at most `2*R+2`. -/
theorem outsidePrimeLeastComplete_owner_period_le
    {P : Finset ℕ} {R q k : ℕ}
    (hk : k ∈ squareBlockOutsidePrimeLeastCompleteCells P R)
    (howner : physicalLeastOddSquarePrime k = some q) :
    finitePrimeCRTPeriod (outsidePrimeLeastSuperPrimeSet P q) ≤ 2 * R + 2 := by
  have hsub := (Finset.mem_filter.mp hk).2
  have hget : (physicalLeastOddSquarePrime k).getD 0 = q := by
    simp [howner]
  rw [hget] at hsub
  have hcard := Finset.card_le_card hsub
  unfold outsidePrimeLeastSuperOrbit at hcard
  rw [card_finitePrimeCRTOrbit] at hcard
  exact hcard.trans (card_threeSlotSquareBlockTransitionCells_le R)

/-- **Blocker interface.** If the exact least-owner super-orbit period exceeds
one square block, owner `q` cannot occur in the complete interior. -/
theorem outsidePrimeLeastComplete_no_owner_of_period_gt
    {P : Finset ℕ} {R q k : ℕ}
    (hperiod : 2 * R + 2 <
      finitePrimeCRTPeriod (outsidePrimeLeastSuperPrimeSet P q))
    (hk : k ∈ squareBlockOutsidePrimeLeastCompleteCells P R) :
    physicalLeastOddSquarePrime k ≠ some q := by
  intro howner
  have hle := outsidePrimeLeastComplete_owner_period_le hk howner
  omega

end RHLean.Analysis
