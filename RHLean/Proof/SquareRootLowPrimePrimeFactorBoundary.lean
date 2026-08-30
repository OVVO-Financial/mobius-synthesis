import Mathlib
import RHLean.Proof.SquareRootLowPrimeBornSupportDichotomy

/-!
# Literal prime-factor missing populations

The displacement square produces a missing corner by deleting one earlier
prime factor from a cofactor.  This module defines that population literally
and applies the born/high support dichotomies pointwise.

For the high channel, every such missing factor-parent is supported at the
lower owner cutoff.  For the born channel, it is supported either there or at
the order boundary where the smaller cofactor has fallen below its partner
prime.  These are exactly the proposed high no-toggle and born first-failure
frontiers; no interior residual remains.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Post-root atoms whose cofactor is divisible by `r` but whose literal
`r`-deleted parent atom is absent. -/
def squareRootLowPrimePostRootPrimeFactorMissingAtoms
    (R K U r : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimePostRootResponseAtoms R K U).filter fun z =>
    r ∣ z.1 ∧
      (z.1 / r, z.2) ∉ squareRootLowPrimePostRootResponseAtoms R K U

@[simp] theorem mem_squareRootLowPrimePostRootPrimeFactorMissingAtoms
    {R K U r : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimePostRootPrimeFactorMissingAtoms R K U r ↔
      z ∈ squareRootLowPrimePostRootResponseAtoms R K U ∧
        r ∣ z.1 ∧
          (z.1 / r, z.2) ∉
            squareRootLowPrimePostRootResponseAtoms R K U := by
  simp [squareRootLowPrimePostRootPrimeFactorMissingAtoms]

/-- **High prime-factor missing atoms are owner-cutoff supported.** -/
theorem squareRootLowPrimePostRootPrimeFactorMissing_owner_cutoff
    {R K U r : ℕ} (hr : r.Prime) {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimePostRootPrimeFactorMissingAtoms R K U r) :
    canonicalLargestPrimeFactor (z.1 / r) ∉
      squareRootLowPrimeFreshPrimeSet K U := by
  rcases mem_squareRootLowPrimePostRootPrimeFactorMissingAtoms.mp hz with
    ⟨hzPost, hrDiv, hmissing⟩
  have hzResponse :=
    (mem_squareRootLowPrimePostRootResponseAtoms.mp hzPost).1
  have hcOwned :=
    squareRootLowPrimeOwnedResponseAtom_fst_mem_ownedResponseCofactors
      hzResponse
  have hcPos : 0 < z.1 := by
    rcases mem_squareRootLowPrimeOwnedResponseCofactors.mp hcOwned with hbad | hdelete
    · exact (squareRootLowPrimeOwnedBadCofactor_data hbad).1
    · exact (squareRootLowPrimeOwnedDeletionCofactor_data hdelete).1
  have hrLe : r ≤ z.1 := Nat.le_of_dvd hcPos hrDiv
  have hdPos : 0 < z.1 / r := Nat.div_pos hrLe hr.pos
  have hdDiv : z.1 / r ∣ z.1 :=
    ⟨r, (Nat.div_mul_cancel hrDiv).symm⟩
  exact squareRootLowPrimePostRoot_missingDivisor_supported_at_owner_cutoff
    hzPost hdPos hdDiv hmissing

/-- Born atoms whose `r`-deleted factor-parent is absent. -/
def squareRootLowPrimeBornPrimeFactorMissingAtoms
    (R K U r : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeBornResponseAtoms R K U).filter fun z =>
    r ∣ z.1 ∧
      (z.1 / r, z.2) ∉ squareRootLowPrimeBornResponseAtoms R K U

@[simp] theorem mem_squareRootLowPrimeBornPrimeFactorMissingAtoms
    {R K U r : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeBornPrimeFactorMissingAtoms R K U r ↔
      z ∈ squareRootLowPrimeBornResponseAtoms R K U ∧
        r ∣ z.1 ∧
          (z.1 / r, z.2) ∉ squareRootLowPrimeBornResponseAtoms R K U := by
  simp [squareRootLowPrimeBornPrimeFactorMissingAtoms]

/-- **Born prime-factor missing atoms are owner-cutoff or root-crossing
supported.** -/
theorem squareRootLowPrimeBornPrimeFactorMissing_owner_or_rootCrossing
    {R K U r : ℕ} (hr : r.Prime) {z : ℕ × ℕ}
    (hz : z ∈ squareRootLowPrimeBornPrimeFactorMissingAtoms R K U r) :
    canonicalLargestPrimeFactor (z.1 / r) ∉
        squareRootLowPrimeFreshPrimeSet K U ∨
      z.1 / r < z.2 := by
  rcases mem_squareRootLowPrimeBornPrimeFactorMissingAtoms.mp hz with
    ⟨hzBorn, hrDiv, hmissing⟩
  have hzResponse := (mem_squareRootLowPrimeBornResponseAtoms.mp hzBorn).1
  have hcOwned :=
    squareRootLowPrimeOwnedResponseAtom_fst_mem_ownedResponseCofactors
      hzResponse
  have hcPos : 0 < z.1 := by
    rcases mem_squareRootLowPrimeOwnedResponseCofactors.mp hcOwned with hbad | hdelete
    · exact (squareRootLowPrimeOwnedBadCofactor_data hbad).1
    · exact (squareRootLowPrimeOwnedDeletionCofactor_data hdelete).1
  have hrLe : r ≤ z.1 := Nat.le_of_dvd hcPos hrDiv
  have hdPos : 0 < z.1 / r := Nat.div_pos hrLe hr.pos
  have hdDiv : z.1 / r ∣ z.1 :=
    ⟨r, (Nat.div_mul_cancel hrDiv).symm⟩
  exact squareRootLowPrimeBorn_missingDivisor_owner_or_rootCrossing
    hzBorn hdPos hdDiv hmissing

end RHLean.Proof
