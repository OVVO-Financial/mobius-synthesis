import Mathlib
import RHLean.Proof.LifetimeOverlapKernel

/-!
# Internal lifetime Gram kernel across square blocks

The scalar block totals used in the coherent Gram are rank one.  This module
keeps the internal canonical source-atom coordinates before summation.

For a fixed finite atom universe `U`, weight function `w`, and lifetime boundary
parameter `Λ`, the coordinate of block `t` at atom `p` is

```text
if p is active at t then w p else 0.
```

The block Gram entry is the finite inner product of the two coordinate vectors.
This is a genuine internal Gram kernel: different blocks can overlap through
some atoms and not others.

The construction is defined for arbitrary lag.  Lags one and two are exposed as
special cases, but no finite-memory theorem is assumed; canonical atoms can
remain active across more than two blocks.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace RHLean.Proof

/-- Internal coordinate of block `t` at canonical source atom `p`. -/
def internalLifetimeCoordinate
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (t : ℕ) (p : CanonicalSourceAtom) : ℂ :=
  if IsLifetimeActive Λ p t then w p else 0

/-- Genuine internal Gram entry between blocks `s` and `t`. -/
def internalLifetimeBlockGramEntry
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (s t : ℕ) : ℂ :=
  ∑ p ∈ U,
    conj (internalLifetimeCoordinate w Λ s p) *
      internalLifetimeCoordinate w Λ t p

/-- General lag-`lag` block Gram entry. -/
def internalLifetimeLagGramEntry
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (lag t : ℕ) : ℂ :=
  internalLifetimeBlockGramEntry U w Λ t (t + lag)

/-- One-block-lag specialization. -/
def internalLifetimeOneLagGramEntry
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (t : ℕ) : ℂ :=
  internalLifetimeLagGramEntry U w Λ 1 t

/-- Two-block-lag specialization. -/
def internalLifetimeTwoLagGramEntry
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (t : ℕ) : ℂ :=
  internalLifetimeLagGramEntry U w Λ 2 t

@[simp] theorem internalLifetimeOneLagGramEntry_eq
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ) (t : ℕ) :
    internalLifetimeOneLagGramEntry U w Λ t =
      internalLifetimeBlockGramEntry U w Λ t (t + 1) := rfl

@[simp] theorem internalLifetimeTwoLagGramEntry_eq
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ) (t : ℕ) :
    internalLifetimeTwoLagGramEntry U w Λ t =
      internalLifetimeBlockGramEntry U w Λ t (t + 2) := rfl

/-- Hermitian symmetry of the internal block Gram kernel. -/
theorem internalLifetimeBlockGramEntry_conj_symm
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (s t : ℕ) :
    conj (internalLifetimeBlockGramEntry U w Λ s t) =
      internalLifetimeBlockGramEntry U w Λ t s := by
  classical
  unfold internalLifetimeBlockGramEntry
  simp [mul_comm]

/-- The diagonal is the sum of coordinate energies. -/
theorem internalLifetimeBlockGramEntry_self
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (t : ℕ) :
    internalLifetimeBlockGramEntry U w Λ t t =
      ∑ p ∈ U,
        conj (internalLifetimeCoordinate w Λ t p) *
          internalLifetimeCoordinate w Λ t p := rfl

/-- The scalar lifetime amplitude is the coordinate sum. -/
theorem lifetimeAmplitude_eq_sum_internalLifetimeCoordinate
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ) (t : ℕ) :
    lifetimeAmplitude U w Λ t =
      ∑ p ∈ U, internalLifetimeCoordinate w Λ t p := by
  rfl

/-- Exact coherent-energy identity for the internal block vectors on a finite
block window.  Summing every block-pair Gram entry equals the sum, over atoms,
of the squared coherent coordinate accumulated across the window. -/
theorem sum_internalLifetimeBlockGramEntry_eq_coordinateEnergy
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (N H : ℕ) :
    (∑ s ∈ Finset.range H,
      ∑ t ∈ Finset.range H,
        internalLifetimeBlockGramEntry U w Λ (N + s) (N + t)) =
      ∑ p ∈ U,
        conj (∑ s ∈ Finset.range H,
          internalLifetimeCoordinate w Λ (N + s) p) *
        (∑ t ∈ Finset.range H,
          internalLifetimeCoordinate w Λ (N + t) p) := by
  classical
  simp_rw [internalLifetimeBlockGramEntry, map_sum,
    Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ s ∈ Finset.range H,
      ∑ t ∈ Finset.range H,
        ∑ p ∈ U,
          conj (internalLifetimeCoordinate w Λ (N + s) p) *
            internalLifetimeCoordinate w Λ (N + t) p) =
      ∑ s ∈ Finset.range H,
        ∑ p ∈ U,
          ∑ t ∈ Finset.range H,
            conj (internalLifetimeCoordinate w Λ (N + s) p) *
              internalLifetimeCoordinate w Λ (N + t) p := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.sum_comm]
    _ = ∑ p ∈ U,
        ∑ s ∈ Finset.range H,
          ∑ t ∈ Finset.range H,
            conj (internalLifetimeCoordinate w Λ (N + s) p) *
              internalLifetimeCoordinate w Λ (N + t) p := by
        rw [Finset.sum_comm]

/-- General lag row over a finite starting-block window. -/
def internalLifetimeLagCorrelation
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (lag N H : ℕ) : ℂ :=
  ∑ h ∈ Finset.range H,
    internalLifetimeLagGramEntry U w Λ lag (N + h)

/-- Lag one is merely the first specialization of the general lag correlation. -/
theorem internalLifetimeLagCorrelation_one
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (N H : ℕ) :
    internalLifetimeLagCorrelation U w Λ 1 N H =
      ∑ h ∈ Finset.range H,
        internalLifetimeOneLagGramEntry U w Λ (N + h) := rfl

/-- Lag two is merely the second specialization of the general lag correlation. -/
theorem internalLifetimeLagCorrelation_two
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ) (Λ : ℝ)
    (N H : ℕ) :
    internalLifetimeLagCorrelation U w Λ 2 N H =
      ∑ h ∈ Finset.range H,
        internalLifetimeTwoLagGramEntry U w Λ (N + h) := rfl

end RHLean.Proof
