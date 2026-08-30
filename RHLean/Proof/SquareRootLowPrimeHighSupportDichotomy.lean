import Mathlib
import RHLean.Proof.SquareRootLowPrimeHighDivisorDownwardClosure

/-!
# High-channel support dichotomy

A post-root partner `Q` is independent of the internal factorization of its
cofactor: the only geometric condition is `d*Q <= R^2-1`.  Therefore any
positive squarefree cofactor `d` whose largest prime is still owned in `(K,U]`
produces a literal post-root response atom whenever that product inequality
holds.

Contrapositively, a missing high-channel corner has exactly two possible
causes:

* its owner has crossed the lower cutoff; or
* its cofactor/partner product has crossed the square endpoint.

There is no interior high residual beyond these two boundaries.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- A positive squarefree cofactor below the square endpoint is in the complete
owned signed carrier as soon as its canonical owner lies in `(K,U]`. -/
theorem squareRootLowPrimeSquarefreeCofactor_mem_ownedResponseCofactors
    {R K U d : ℕ} (hd : 0 < d) (hdSq : Squarefree d)
    (hdUpper : d ≤ squareRootEndpoint R)
    (hdOwner : canonicalLargestPrimeFactor d ∈
      squareRootLowPrimeFreshPrimeSet K U) :
    d ∈ squareRootLowPrimeOwnedResponseCofactors R K U := by
  have hdMuNe : μ d ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hdSq
  have hdBound := ArithmeticFunction.abs_moebius_le_one (n := d)
  rw [abs_le] at hdBound
  have hdSign : μ d = 1 ∨ μ d = -1 := by omega
  have hdFresh :
      d ∈ squareRootLowPrimeBornFreshCofactors R
        (canonicalLargestPrimeFactor d) := by
    unfold squareRootLowPrimeBornFreshCofactors
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd), hdUpper⟩,
        rfl⟩
  rcases hdSign with hpos | hneg
  · apply mem_squareRootLowPrimeOwnedResponseCofactors.mpr
    left
    unfold squareRootLowPrimeOwnedBadCofactors
    exact Finset.mem_biUnion.mpr
      ⟨canonicalLargestPrimeFactor d, hdOwner,
        Finset.mem_filter.mpr ⟨hdFresh, hpos⟩⟩
  · apply mem_squareRootLowPrimeOwnedResponseCofactors.mpr
    right
    unfold squareRootLowPrimeOwnedDeletionCofactors
    exact Finset.mem_biUnion.mpr
      ⟨canonicalLargestPrimeFactor d, hdOwner,
        Finset.mem_filter.mpr ⟨hdFresh, hneg⟩⟩

/-- Replacing the cofactor of a known post-root partner by any owned squarefree
cofactor preserves the literal atom whenever the hyperbolic product fits. -/
theorem squareRootLowPrimePostRootAtom_of_squarefreeCofactor
    {R K U c d q : ℕ}
    (hz : (c, q) ∈ squareRootLowPrimePostRootResponseAtoms R K U)
    (hd : 0 < d) (hdSq : Squarefree d)
    (hdOwner : canonicalLargestPrimeFactor d ∈
      squareRootLowPrimeFreshPrimeSet K U)
    (hdq : d * q ≤ squareRootEndpoint R) :
    (d, q) ∈ squareRootLowPrimePostRootResponseAtoms R K U := by
  have hzPost := (mem_squareRootLowPrimePostRootResponseAtoms.mp hz).2
  have hqData := Finset.mem_filter.mp hzPost
  have hdUpper : d ≤ squareRootEndpoint R := by
    have hdLeProd : d ≤ d * q := by
      simpa using Nat.mul_le_mul_left d hqData.2.1.pos
    exact hdLeProd.trans hdq
  have hdOwned :=
    squareRootLowPrimeSquarefreeCofactor_mem_ownedResponseCofactors
      hd hdSq hdUpper hdOwner
  have hdPost : q ∈ squareRootPostRootPrimePartnerSet R d := by
    unfold squareRootPostRootPrimePartnerSet
    exact Finset.mem_filter.mpr ⟨hqData.1, hqData.2.1, hdq⟩
  exact mem_squareRootLowPrimePostRootResponseAtoms.mpr
    ⟨squareRootLowPrimeOwnedResponseAtom_of_ownedCofactor
      hdOwned (Finset.mem_union.mpr (Or.inr hdPost)),
      hdPost⟩

/-- **Missing high corner dichotomy, hyperbolic form.**  Under squarefreeness
and active ownership, absence forces endpoint crossing. -/
theorem squareRootLowPrimePostRoot_missing_forces_endpoint_crossing
    {R K U c d q : ℕ}
    (hz : (c, q) ∈ squareRootLowPrimePostRootResponseAtoms R K U)
    (hd : 0 < d) (hdSq : Squarefree d)
    (hdOwner : canonicalLargestPrimeFactor d ∈
      squareRootLowPrimeFreshPrimeSet K U)
    (hmissing : (d, q) ∉
      squareRootLowPrimePostRootResponseAtoms R K U) :
    squareRootEndpoint R < d * q := by
  by_contra hnot
  have hdq : d * q ≤ squareRootEndpoint R := Nat.le_of_not_gt hnot
  exact hmissing
    (squareRootLowPrimePostRootAtom_of_squarefreeCofactor
      hz hd hdSq hdOwner hdq)

/-- **Complete support dichotomy.**  A missing positive squarefree post-root
corner is either owner-cutoff supported or endpoint-crossing supported. -/
theorem squareRootLowPrimePostRoot_missing_owner_or_endpoint
    {R K U c d q : ℕ}
    (hz : (c, q) ∈ squareRootLowPrimePostRootResponseAtoms R K U)
    (hd : 0 < d) (hdSq : Squarefree d)
    (hmissing : (d, q) ∉
      squareRootLowPrimePostRootResponseAtoms R K U) :
    canonicalLargestPrimeFactor d ∉ squareRootLowPrimeFreshPrimeSet K U ∨
      squareRootEndpoint R < d * q := by
  by_cases hdOwner : canonicalLargestPrimeFactor d ∈
      squareRootLowPrimeFreshPrimeSet K U
  · exact Or.inr
      (squareRootLowPrimePostRoot_missing_forces_endpoint_crossing
        hz hd hdSq hdOwner hmissing)
  · exact Or.inl hdOwner

end RHLean.Proof
