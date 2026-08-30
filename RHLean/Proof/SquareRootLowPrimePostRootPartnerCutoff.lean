import Mathlib
import RHLean.Proof.SquareRootLowPrimeNoTogglePopulationBound

/-!
# The actual deep high carrier lies below the crossing layer

The high response is compressed elsewhere to a natural seat index.  For the
quantitative residual argument the literal partner prime is the stable
coordinate.

Every owned response cofactor lies strictly above the shallow crossing depth
`K`.  Hence a post-root response atom `(c,q)` satisfies

`K + 1 <= c` and `c*q <= R^2 - 1`,

so necessarily

`q <= floor((R^2-1)/(K+1))`.

Thus no prime from the reciprocal crossing layer

`floor((R^2-1)/(K+1)) < q <= floor((R^2-1)/K)`

occurs anywhere in the actual deep post-root carrier.  This is the carrier-level
form of the no-fresh-descendant observation: the crossing-layer packet is
terminal before the deep prime chronology begins.  The signed interpolation
term involving `j*M(K)` must therefore remain a separate shallow scalar rather
than being copied into high no-toggle or high-instability populations.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Every owned response cofactor lies strictly beyond the shallow cutoff. -/
theorem squareRootLowPrimeOwnedResponseCofactor_crossing_lt
    {R K U c : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedResponseCofactors R K U) :
    K < c := by
  rcases mem_squareRootLowPrimeOwnedResponseCofactors.mp hc with hcBad | hcDel
  · exact (squareRootLowPrimeOwnedBadCofactor_data hcBad).2.1
  · exact (squareRootLowPrimeOwnedDeletionCofactor_data hcDel).2.1

/-- **Literal deep high partners lie below the crossing-layer boundary.** -/
theorem squareRootLowPrimePostRootResponseAtom_partner_le_crossingCutoff
    {R K U : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimePostRootResponseAtoms R K U) :
    z.2 ≤ squareRootEndpoint R / (K + 1) := by
  rcases mem_squareRootLowPrimePostRootResponseAtoms.mp hz with
    ⟨hzResponse, hzPost⟩
  have hcOwned :=
    squareRootLowPrimeOwnedResponseAtom_fst_mem_ownedResponseCofactors hzResponse
  have hKc : K + 1 ≤ z.1 := by
    exact Nat.succ_le_iff.mpr
      (squareRootLowPrimeOwnedResponseCofactor_crossing_lt hcOwned)
  have hproduct : z.1 * z.2 ≤ squareRootEndpoint R :=
    mul_le_squareRootEndpoint_of_mem_deepPartnerSet
      (Finset.mem_union.mpr (Or.inr hzPost))
  apply (Nat.le_div_iff_mul_le (Nat.succ_pos K)).2
  simpa [Nat.mul_comm] using
    ((Nat.mul_le_mul_right z.2 hKc).trans hproduct)

/-- No actual deep post-root response atom can use a prime from the reciprocal
crossing layer. -/
theorem squareRootLowPrimePostRootResponseAtom_not_crossingLayer
    {R K U : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimePostRootResponseAtoms R K U) :
    ¬ squareRootEndpoint R / (K + 1) < z.2 := by
  exact Nat.not_lt_of_ge
    (squareRootLowPrimePostRootResponseAtom_partner_le_crossingCutoff hz)

/-- Equivalently, a post-root prime above the crossing boundary has no owned
deep response cofactor at all. -/
theorem squareRootLowPrime_crossingLayerPrime_not_mem_postRootResponseAtoms
    {R K U c q : ℕ}
    (hq : squareRootEndpoint R / (K + 1) < q) :
    (c, q) ∉ squareRootLowPrimePostRootResponseAtoms R K U := by
  intro hmem
  exact
    (squareRootLowPrimePostRootResponseAtom_not_crossingLayer hmem) hq

end RHLean.Proof
