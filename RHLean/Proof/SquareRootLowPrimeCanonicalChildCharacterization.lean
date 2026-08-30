import Mathlib
import RHLean.Proof.SquareRootLowPrimeSignedResponseChildren

/-!
# Canonical characterization of the complete signed response children

The atom construction uses coordinates `(c,q)`, but below the root those
coordinates are intrinsic to the arithmetic child:

`c = canonicalCofactor(n)`, `q = P+(n)`.

This module first combines the positive and negative cofactor orientations into
one signed carrier, then characterizes the response atoms and children without
reference to which sign branch produced them.  This is the interface required
to apply the repository's existing cofactor-to-root transport directly to the
matched or rough-base residual populations.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Complete nonzero-Möbius cofactor carrier over `(K,U]`. -/
def squareRootLowPrimeOwnedSignedCofactors
    (R K U : ℕ) : Finset ℕ :=
  squareRootLowPrimeOwnedBadCofactors R K U ∪
    squareRootLowPrimeOwnedDeletionCofactors R K U

/-- Membership data for the complete signed cofactor carrier. -/
theorem squareRootLowPrimeOwnedSignedCofactor_data
    {R K U c : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedSignedCofactors R K U) :
    0 < c ∧ K < c ∧ canonicalLargestPrimeFactor c ≤ U ∧
      (μ c = 1 ∨ μ c = -1) := by
  rcases Finset.mem_union.mp hc with hbad | hdelete
  · have h := squareRootLowPrimeOwnedBadCofactor_data hbad
    exact ⟨h.1, h.2.1, h.2.2.1, Or.inl h.2.2.2⟩
  · have h := squareRootLowPrimeOwnedDeletionCofactor_data hdelete
    exact ⟨h.1, h.2.1, h.2.2.1, Or.inr h.2.2.2⟩

/-- The complete response-atom carrier is exactly the biunion over the signed
cofactor carrier. -/
theorem mem_squareRootLowPrimeOwnedResponseAtoms_iff
    {R K U : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeOwnedResponseAtoms R K U ↔
      z.1 ∈ squareRootLowPrimeOwnedSignedCofactors R K U ∧
        z.2 ∈ squareRootLowPrimeDeepPartnerSet R z.1 := by
  unfold squareRootLowPrimeOwnedResponseAtoms
    squareRootLowPrimeOwnedSignedCofactors
  constructor
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · unfold squareRootLowPrimeOwnedBadAtoms at hz
      rcases Finset.mem_biUnion.mp hz with ⟨c, hc, hzc⟩
      have hdata := mem_squareRootLowPrimeBadAtomFiber.mp hzc
      rw [hdata.1]
      exact ⟨Finset.mem_union.mpr (Or.inl hc), hdata.2⟩
    · unfold squareRootLowPrimeOwnedDeletionAtoms at hz
      rcases Finset.mem_biUnion.mp hz with ⟨c, hc, hzc⟩
      have hdata := mem_squareRootLowPrimeBadAtomFiber.mp hzc
      rw [hdata.1]
      exact ⟨Finset.mem_union.mpr (Or.inr hc), hdata.2⟩
  · rintro ⟨hc, hq⟩
    rcases Finset.mem_union.mp hc with hc | hc
    · apply Finset.mem_union.mpr
      left
      unfold squareRootLowPrimeOwnedBadAtoms
      apply Finset.mem_biUnion.mpr
      refine ⟨z.1, hc, ?_⟩
      exact mem_squareRootLowPrimeBadAtomFiber.mpr ⟨rfl, hq⟩
    · apply Finset.mem_union.mpr
      right
      unfold squareRootLowPrimeOwnedDeletionAtoms
      apply Finset.mem_biUnion.mpr
      refine ⟨z.1, hc, ?_⟩
      exact mem_squareRootLowPrimeBadAtomFiber.mpr ⟨rfl, hq⟩

/-- Existential arithmetic characterization of the complete child carrier. -/
theorem mem_squareRootLowPrimeOwnedResponseChildren_iff
    {R K U n : ℕ} :
    n ∈ squareRootLowPrimeOwnedResponseChildren R K U ↔
      ∃ c ∈ squareRootLowPrimeOwnedSignedCofactors R K U,
        ∃ q ∈ squareRootLowPrimeDeepPartnerSet R c, n = c * q := by
  unfold squareRootLowPrimeOwnedResponseChildren
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, hzn⟩
    have hdata := mem_squareRootLowPrimeOwnedResponseAtoms_iff.mp hz
    refine ⟨z.1, hdata.1, z.2, hdata.2, ?_⟩
    simpa [squareRootLowPrimeBadAtomChild] using hzn.symm
  · rintro ⟨c, hc, q, hq, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(c, q), ?_, ?_⟩
    · exact mem_squareRootLowPrimeOwnedResponseAtoms_iff.mpr ⟨hc, hq⟩
    · rfl

/-- Below the root, the atom cofactor is the child's canonical cofactor and the
partner is the child's canonical largest prime. -/
theorem squareRootLowPrimeOwnedResponseAtom_canonical_coordinates
    {R K U : ℕ} {z : ℕ × ℕ} (hUR : U < R)
    (hz : z ∈ squareRootLowPrimeOwnedResponseAtoms R K U) :
    canonicalCofactor (squareRootLowPrimeBadAtomChild z) = z.1 ∧
      canonicalLargestPrimeFactor (squareRootLowPrimeBadAtomChild z) = z.2 := by
  have hdata := squareRootLowPrimeOwnedResponseAtom_data hz
  have hqPrime := prime_of_mem_squareRootLowPrimeDeepPartnerSet hdata.2.2.2
  have hrough :=
    canonicalLargestPrimeFactor_lt_partner_of_ownedResponseAtom hUR hz
  constructor
  · exact canonicalCofactor_mul_prime_eq_of_rough hdata.1 hqPrime hrough
  · exact canonicalLargestPrimeFactor_mul_prime_eq_of_rough
      hdata.1 hqPrime hrough

/-- Every response child canonically recovers an owned signed cofactor and its
literal partner prime. -/
theorem squareRootLowPrimeOwnedResponseChild_has_canonical_data
    {R K U n : ℕ} (hUR : U < R)
    (hn : n ∈ squareRootLowPrimeOwnedResponseChildren R K U) :
    canonicalCofactor n ∈ squareRootLowPrimeOwnedSignedCofactors R K U ∧
      canonicalLargestPrimeFactor n ∈
        squareRootLowPrimeDeepPartnerSet R (canonicalCofactor n) := by
  unfold squareRootLowPrimeOwnedResponseChildren at hn
  rcases Finset.mem_image.mp hn with ⟨z, hz, hzn⟩
  have hdata := mem_squareRootLowPrimeOwnedResponseAtoms_iff.mp hz
  have hcoords :=
    squareRootLowPrimeOwnedResponseAtom_canonical_coordinates hUR hz
  rw [← hzn, hcoords.1, hcoords.2]
  exact hdata

end RHLean.Proof
