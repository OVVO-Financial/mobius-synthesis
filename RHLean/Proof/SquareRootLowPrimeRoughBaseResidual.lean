import Mathlib
import RHLean.Proof.SquareRootLowPrimeSignedResponseChildren

/-!
# Signed response-child residuals on the rough-base coordinate

For a processed prime interval `(K,U]`, delete from a squarefree response child
all prime factors in that interval.  The remaining product is its rough base.
Children with the same base form one finite Boolean fibre in the processed
prime coordinates.

This module performs the exact finite regrouping

`sum_children mu = sum_base residual(base)`

and removes the zero residual fibres.  Thus a unit-residual theorem would bound
the whole signed response by the number of nonzero rough bases, which is the
natural population to charge through the existing cofactor/root map.

No numerical observation is used in the proofs below.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Product of the prime factors outside the processed interval `(K,U]`. -/
def squareRootLowPrimeResponseRoughBase (K U n : ℕ) : ℕ :=
  (n.primeFactors.filter fun p => ¬ (K < p ∧ p ≤ U)).prod id

/-- Rough bases represented by the exact response-child carrier. -/
def squareRootLowPrimeOwnedResponseRoughBases
    (R K U : ℕ) : Finset ℕ :=
  (squareRootLowPrimeOwnedResponseChildren R K U).image
    (squareRootLowPrimeResponseRoughBase K U)

/-- One rough-base fibre of exact response children. -/
def squareRootLowPrimeOwnedResponseRoughBaseFiber
    (R K U b : ℕ) : Finset ℕ :=
  (squareRootLowPrimeOwnedResponseChildren R K U).filter fun n =>
    squareRootLowPrimeResponseRoughBase K U n = b

/-- Signed Möbius residual on one rough-base fibre. -/
def squareRootLowPrimeOwnedResponseRoughBaseResidual
    (R K U b : ℕ) : ℤ :=
  ∑ n ∈ squareRootLowPrimeOwnedResponseRoughBaseFiber R K U b, μ n

/-- Rough bases whose Boolean fibre has nonzero signed residual. -/
def squareRootLowPrimeOwnedResponseNonzeroRoughBases
    (R K U : ℕ) : Finset ℕ :=
  (squareRootLowPrimeOwnedResponseRoughBases R K U).filter fun b =>
    squareRootLowPrimeOwnedResponseRoughBaseResidual R K U b ≠ 0

@[simp] theorem mem_squareRootLowPrimeOwnedResponseRoughBases
    {R K U b : ℕ} :
    b ∈ squareRootLowPrimeOwnedResponseRoughBases R K U ↔
      ∃ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
        squareRootLowPrimeResponseRoughBase K U n = b := by
  simp [squareRootLowPrimeOwnedResponseRoughBases]

@[simp] theorem mem_squareRootLowPrimeOwnedResponseRoughBaseFiber
    {R K U b n : ℕ} :
    n ∈ squareRootLowPrimeOwnedResponseRoughBaseFiber R K U b ↔
      n ∈ squareRootLowPrimeOwnedResponseChildren R K U ∧
        squareRootLowPrimeResponseRoughBase K U n = b := by
  simp [squareRootLowPrimeOwnedResponseRoughBaseFiber]

@[simp] theorem mem_squareRootLowPrimeOwnedResponseNonzeroRoughBases
    {R K U b : ℕ} :
    b ∈ squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U ↔
      b ∈ squareRootLowPrimeOwnedResponseRoughBases R K U ∧
        squareRootLowPrimeOwnedResponseRoughBaseResidual R K U b ≠ 0 := by
  simp [squareRootLowPrimeOwnedResponseNonzeroRoughBases]

/-- **Exact rough-base Fubini identity.** -/
theorem squareRootLowPrimeOwnedResponseChildren_moebiusSum_eq_roughBaseResidualSum
    (R K U : ℕ) :
    (∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U, μ n) =
      ∑ b ∈ squareRootLowPrimeOwnedResponseRoughBases R K U,
        squareRootLowPrimeOwnedResponseRoughBaseResidual R K U b := by
  classical
  have hmaps :
      ∀ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
        squareRootLowPrimeResponseRoughBase K U n ∈
          squareRootLowPrimeOwnedResponseRoughBases R K U := by
    intro n hn
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  unfold squareRootLowPrimeOwnedResponseRoughBaseResidual
    squareRootLowPrimeOwnedResponseRoughBaseFiber
  symm
  simpa using
    (Finset.sum_fiberwise_of_maps_to
      (s := squareRootLowPrimeOwnedResponseChildren R K U)
      (t := squareRootLowPrimeOwnedResponseRoughBases R K U)
      (g := squareRootLowPrimeResponseRoughBase K U)
      hmaps
      (fun n : ℕ => μ n))

/-- Zero rough-base fibres may be deleted without changing the signed mass. -/
theorem squareRootLowPrimeOwnedResponseRoughBaseResidualSum_eq_nonzero
    (R K U : ℕ) :
    (∑ b ∈ squareRootLowPrimeOwnedResponseRoughBases R K U,
      squareRootLowPrimeOwnedResponseRoughBaseResidual R K U b) =
      ∑ b ∈ squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U,
        squareRootLowPrimeOwnedResponseRoughBaseResidual R K U b := by
  unfold squareRootLowPrimeOwnedResponseNonzeroRoughBases
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hzero :
      squareRootLowPrimeOwnedResponseRoughBaseResidual R K U b = 0
  · simp [hzero]
  · simp [hzero]

/-- The complete child mass is supported only on nonzero rough-base fibres. -/
theorem squareRootLowPrimeOwnedResponseChildren_moebiusSum_eq_nonzeroRoughBaseResidualSum
    (R K U : ℕ) :
    (∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U, μ n) =
      ∑ b ∈ squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U,
        squareRootLowPrimeOwnedResponseRoughBaseResidual R K U b := by
  rw [squareRootLowPrimeOwnedResponseChildren_moebiusSum_eq_roughBaseResidualSum,
    squareRootLowPrimeOwnedResponseRoughBaseResidualSum_eq_nonzero]

/-- Absolute signed mass is bounded by the `L1` mass of the nonzero rough-base
residuals. -/
theorem abs_squareRootLowPrimeOwnedResponseChildren_moebiusSum_le_nonzeroRoughBaseL1
    (R K U : ℕ) :
    |∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U, μ n| ≤
      ∑ b ∈ squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U,
        |squareRootLowPrimeOwnedResponseRoughBaseResidual R K U b| := by
  rw [squareRootLowPrimeOwnedResponseChildren_moebiusSum_eq_nonzeroRoughBaseResidualSum]
  exact Finset.abs_sum_le_sum_abs _ _

/-- If every nonzero fibre has unit residual, the complete mass is bounded by
the number of nonzero rough bases. -/
theorem abs_squareRootLowPrimeOwnedResponseChildren_moebiusSum_le_nonzeroRoughBaseCard
    (R K U : ℕ)
    (hunit : ∀ b ∈ squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U,
      |squareRootLowPrimeOwnedResponseRoughBaseResidual R K U b| ≤ 1) :
    |∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U, μ n| ≤
      ((squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U).card : ℤ) := by
  calc
    |∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U, μ n| ≤
      ∑ b ∈ squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U,
        |squareRootLowPrimeOwnedResponseRoughBaseResidual R K U b| :=
      abs_squareRootLowPrimeOwnedResponseChildren_moebiusSum_le_nonzeroRoughBaseL1
        R K U
    _ ≤ ∑ _b ∈ squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U,
        (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro b hb
      exact hunit b hb
    _ = ((squareRootLowPrimeOwnedResponseNonzeroRoughBases R K U).card : ℤ) := by
      simp

end RHLean.Proof
