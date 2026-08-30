import Mathlib
import RHLean.Proof.SquareRootLowPrimeResponseSeatCarrier
import RHLean.Proof.SquareRootLowPrimeDeepResponseAtoms

/-!
# Response seats are literal prime partners

Beyond the shallow cutoff, `CombinedFreshResponse(R,K,j,c)` is exactly the
cardinality of `DeepPartnerSet(R,c)`. Hence the abstract unit-seat coordinate
used by the canonical creation-response map is merely an enumeration of the
literal born/post-root prime partners already used by the response forest.

This file records a noncomputable fibrewise equivalence. No estimate or
analytic input is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Natural seat indices over one deep response cofactor. -/
def squareRootLowPrimeResponseSeatIndexSet
    (R K j c : ℕ) : Finset ℕ :=
  Finset.range (squareRootLowPrimeCombinedFreshResponse R K j c)

@[simp] theorem mem_squareRootLowPrimeResponseSeatIndexSet
    {R K j c s : ℕ} :
    s ∈ squareRootLowPrimeResponseSeatIndexSet R K j c ↔
      s < squareRootLowPrimeCombinedFreshResponse R K j c := by
  simp [squareRootLowPrimeResponseSeatIndexSet]

/-- **Seat/partner equivalence on one deep cofactor fibre.** -/
noncomputable def squareRootLowPrimeResponseSeatPartnerEquiv
    (R K j c : ℕ) (hR : 1 ≤ R) (hc : 0 < c) (hKc : K < c) :
    ↥(squareRootLowPrimeResponseSeatIndexSet R K j c) ≃
      ↥(squareRootLowPrimeDeepPartnerSet R c) := by
  apply Finset.equivOfCardEq
  show (Finset.range (squareRootLowPrimeCombinedFreshResponse R K j c)).card =
    (squareRootLowPrimeDeepPartnerSet R c).card
  rw [Finset.card_range]
  exact (card_squareRootLowPrimeDeepPartnerSet_eq_combinedFreshResponse
    hR hc hKc).symm

/-- The chosen partner of a valid seat is genuinely in the deep partner set. -/
theorem squareRootLowPrimeResponseSeatPartnerEquiv_mem
    (R K j c : ℕ) (hR : 1 ≤ R) (hc : 0 < c) (hKc : K < c)
    (s : ↥(squareRootLowPrimeResponseSeatIndexSet R K j c)) :
    (squareRootLowPrimeResponseSeatPartnerEquiv R K j c hR hc hKc s : ℕ) ∈
      squareRootLowPrimeDeepPartnerSet R c :=
  (squareRootLowPrimeResponseSeatPartnerEquiv R K j c hR hc hKc s).property

/-- Every literal deep partner is represented by exactly one response seat. -/
theorem squareRootLowPrimeResponseSeatPartnerEquiv_surjective
    (R K j c : ℕ) (hR : 1 ≤ R) (hc : 0 < c) (hKc : K < c)
    (q : ↥(squareRootLowPrimeDeepPartnerSet R c)) :
    ∃ s : ↥(squareRootLowPrimeResponseSeatIndexSet R K j c),
      squareRootLowPrimeResponseSeatPartnerEquiv R K j c hR hc hKc s = q := by
  exact (squareRootLowPrimeResponseSeatPartnerEquiv
    R K j c hR hc hKc).surjective q

end RHLean.Proof
