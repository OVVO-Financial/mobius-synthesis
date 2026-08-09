import Mathlib
import RHLean.Proof.InternalBlockLifetimeGram

/-!
# Bridge between the two lifetime Gram architectures

The lifetime incidence array has block-time rows and canonical-atom columns.
The repository contains two different Gram constructions from this array:

* `lifetimeOverlapGram` keeps atom indices and sums over common active times;
* `internalLifetimeBlockGramEntry` keeps block-time indices and sums over atoms.

These are the atom-side and block-side Gram views of the same finite incidence
array. Their coherent quadratic forms are not identified: one sums atoms inside
each time amplitude, while the other sums times inside each atom coordinate.
What they share exactly is the diagonal/Frobenius energy. This module records
that correct bridge and names both coherent forms without asserting a false
transpose equality.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace RHLean.Proof

/-- Diagonal energy of the block-side internal Gram over `[N,N+H)`. -/
def internalLifetimeBlockTrace
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (N H : ℕ) : ℂ :=
  ∑ h ∈ Finset.range H,
    internalLifetimeBlockGramEntry U w Λ (N + h) (N + h)

/-- Diagonal energy of the atom-side lifetime-overlap Gram. -/
def lifetimeOverlapDiagonalEnergy
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (N H : ℕ) : ℂ :=
  ∑ p ∈ U,
    conj (w p) * w p * lifetimeOverlapKernel Λ N H p p

/-- One coordinate contributes its weight energy exactly when it is active. -/
theorem internalLifetimeCoordinate_self
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (t : ℕ) (p : CanonicalSourceAtom) :
    conj (internalLifetimeCoordinate w Λ t p) *
        internalLifetimeCoordinate w Λ t p =
      if IsLifetimeActive Λ p t then conj (w p) * w p else 0 := by
  classical
  by_cases hactive : IsLifetimeActive Λ p t <;>
    simp [internalLifetimeCoordinate, hactive]

/-- The block-side and atom-side Gram matrices have the same diagonal/Frobenius
energy. This is the exact finite incidence-matrix transpose bridge. -/
theorem internalLifetimeBlockTrace_eq_overlapDiagonalEnergy
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (N H : ℕ) :
    internalLifetimeBlockTrace U w Λ N H =
      lifetimeOverlapDiagonalEnergy U w Λ N H := by
  classical
  unfold internalLifetimeBlockTrace lifetimeOverlapDiagonalEnergy
  simp_rw [internalLifetimeBlockGramEntry_self,
    internalLifetimeCoordinate_self, lifetimeOverlapKernel_self]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hactive : IsLifetimeActive Λ p (N + h) <;> simp [hactive]

/-- Name for the existing atom-coherent lifetime energy. -/
def lifetimeAtomCoherentEnergy
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (N H : ℕ) : ℂ :=
  lifetimeOverlapGram U w Λ N H

/-- Name for the block-coherent internal lifetime energy. -/
def lifetimeBlockCoherentEnergy
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (N H : ℕ) : ℂ :=
  ∑ s ∈ Finset.range H,
    ∑ t ∈ Finset.range H,
      internalLifetimeBlockGramEntry U w Λ (N + s) (N + t)

/-- The atom-coherent form is exactly the existing translated-window energy. -/
theorem lifetimeWindowEnergy_eq_atomCoherentEnergy
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (N H : ℕ) :
    lifetimeWindowEnergy U w Λ N H =
      lifetimeAtomCoherentEnergy U w Λ N H := by
  exact lifetimeWindowEnergy_eq_overlapGram U w Λ N H

/-- The block-coherent form is exactly the sum of squared time-accumulated atom
coordinates. -/
theorem lifetimeBlockCoherentEnergy_eq_coordinateEnergy
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (N H : ℕ) :
    lifetimeBlockCoherentEnergy U w Λ N H =
      ∑ p ∈ U,
        conj (∑ s ∈ Finset.range H,
          internalLifetimeCoordinate w Λ (N + s) p) *
        (∑ t ∈ Finset.range H,
          internalLifetimeCoordinate w Λ (N + t) p) := by
  exact sum_internalLifetimeBlockGramEntry_eq_coordinateEnergy U w Λ N H

end RHLean.Proof
