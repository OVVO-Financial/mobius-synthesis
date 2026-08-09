import Mathlib
import RHLean.Proof.SurvivorResidueCovarianceCriterion

/-!
# Survivor residue collision reindex

This module identifies the signed cross-cofactor covariance with the actual
active source-pair collision ledger.  It introduces no analytic estimate.

For fixed cofactors `c,c'`, the collision count is the number of active prime
pairs `(q,q')` with equal signed doubled-height residue

```text
q^2 - c^2 = q'^2 - c'^2  (mod s).
```

The cofactor Gram block is exactly `mu(c) * mu(c')` times this nonnegative
collision count.  Summing over unequal cofactors therefore exposes the precise
Möbius-signed pair population whose cancellation is required by the covariance
criterion.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

/-- Actual active prime-pair collisions between two cofactor fibres. -/
noncomputable def survivorResidueCollisionPairSet
    (Λ : ℝ) (t s c c' : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    ((survivorZeroModePrimeFiber Λ t c).product
      (survivorZeroModePrimeFiber Λ t c')).filter fun qq =>
        survivorHeightResidue s c qq.1 = survivorHeightResidue s c' qq.2

/-- Indicator-sum form of the actual active source-pair collision count. -/
def survivorResidueCollisionCount
    (Λ : ℝ) (t s c c' : ℕ) : ℕ :=
  ∑ q ∈ survivorZeroModePrimeFiber Λ t c,
    ∑ q' ∈ survivorZeroModePrimeFiber Λ t c',
      if survivorHeightResidue s c q = survivorHeightResidue s c' q' then 1 else 0

/-- The indicator-sum collision count is literally the cardinality of the
filtered active source-pair set. -/
theorem survivorResidueCollisionCount_eq_card_pairSet
    (Λ : ℝ) (t s c c' : ℕ) :
    survivorResidueCollisionCount Λ t s c c' =
      (survivorResidueCollisionPairSet Λ t s c c').card := by
  classical
  unfold survivorResidueCollisionCount survivorResidueCollisionPairSet
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simpa only using
    (Finset.sum_product
      (s := survivorZeroModePrimeFiber Λ t c)
      (t := survivorZeroModePrimeFiber Λ t c')
      (f := fun qq : ℕ × ℕ =>
        if survivorHeightResidue s c qq.1 =
            survivorHeightResidue s c' qq.2 then 1 else 0)).symm

private theorem sum_collision_indicators
    {α : Type*} [Fintype α] [DecidableEq α]
    (x y : α) :
    (∑ u : α, (if x = u then 1 else 0) * (if y = u then 1 else 0)) =
      (if x = y then 1 else 0 : ℕ) := by
  by_cases hxy : x = y
  · subst y
    simp
  · simp [hxy]

/-- Summing the product of the two residue kernels counts exactly the active
prime pairs whose signed doubled heights collide modulo `s`. -/
theorem sum_survivorResidueKernel_mul_eq_collisionCount
    (Λ : ℝ) (t s c c' : ℕ) [NeZero s] :
    (∑ u : ZMod s,
      survivorResidueKernel Λ t s c u * survivorResidueKernel Λ t s c' u) =
      survivorResidueCollisionCount Λ t s c c' := by
  classical
  unfold survivorResidueKernel survivorResiduePrimeFiber
    survivorResidueCollisionCount
  calc
    (∑ u : ZMod s,
        ((survivorZeroModePrimeFiber Λ t c).filter
          (fun q => survivorHeightResidue s c q = u)).card *
        ((survivorZeroModePrimeFiber Λ t c').filter
          (fun q' => survivorHeightResidue s c' q' = u)).card) =
      ∑ u : ZMod s,
        ∑ q ∈ survivorZeroModePrimeFiber Λ t c,
          ∑ q' ∈ survivorZeroModePrimeFiber Λ t c',
            (if survivorHeightResidue s c q = u then 1 else 0) *
              (if survivorHeightResidue s c' q' = u then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro u _hu
        rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones,
          Finset.sum_filter, Finset.sum_filter, Finset.sum_mul_sum]
    _ = ∑ q ∈ survivorZeroModePrimeFiber Λ t c,
          ∑ q' ∈ survivorZeroModePrimeFiber Λ t c',
            ∑ u : ZMod s,
              (if survivorHeightResidue s c q = u then 1 else 0) *
                (if survivorHeightResidue s c' q' = u then 1 else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro q _hq
          rw [Finset.sum_comm]
    _ = ∑ q ∈ survivorZeroModePrimeFiber Λ t c,
          ∑ q' ∈ survivorZeroModePrimeFiber Λ t c',
            if survivorHeightResidue s c q = survivorHeightResidue s c' q' then
              1 else 0 := by
          apply Finset.sum_congr rfl
          intro q _hq
          apply Finset.sum_congr rfl
          intro q' _hq'
          exact sum_collision_indicators
            (survivorHeightResidue s c q)
            (survivorHeightResidue s c' q')

/-- One cofactor Gram block is exactly the product of the two Möbius signs times
the nonnegative source-pair collision count. -/
theorem survivorResidueCofactorGramBlock_eq_mobius_mul_collisionCount
    (Λ : ℝ) (t s c c' : ℕ) [NeZero s] :
    survivorResidueCofactorGramBlock Λ t s c c' =
      (μ c) * (μ c') * (survivorResidueCollisionCount Λ t s c c' : ℤ) := by
  classical
  unfold survivorResidueCofactorGramBlock survivorResidueCofactorMass
  calc
    (∑ u : ZMod s,
        (-(μ c) * (survivorResidueKernel Λ t s c u : ℤ)) *
          (-(μ c') * (survivorResidueKernel Λ t s c' u : ℤ))) =
      ∑ u : ZMod s,
        ((μ c) * (μ c')) *
          ((survivorResidueKernel Λ t s c u : ℤ) *
            (survivorResidueKernel Λ t s c' u : ℤ)) := by
        apply Finset.sum_congr rfl
        intro u _hu
        ring
    _ = ((μ c) * (μ c')) *
          ∑ u : ZMod s,
            ((survivorResidueKernel Λ t s c u : ℤ) *
              (survivorResidueKernel Λ t s c' u : ℤ)) := by
        rw [Finset.mul_sum]
    _ = (μ c) * (μ c') *
          (survivorResidueCollisionCount Λ t s c c' : ℤ) := by
        congr 1
        exact_mod_cast
          sum_survivorResidueKernel_mul_eq_collisionCount Λ t s c c'

/-- The signed cross-cofactor covariance is exactly the Möbius-signed active
source-pair collision ledger over unequal cofactors. -/
theorem survivorResidueCrossCofactorCovariance_eq_signedCollisionLedger
    (Λ : ℝ) (t s : ℕ) [NeZero s] :
    survivorResidueCrossCofactorCovariance Λ t s =
      ∑ c ∈ survivorResidueCofactorRange t,
        ∑ c' ∈ (survivorResidueCofactorRange t).erase c,
          (μ c) * (μ c') * (survivorResidueCollisionCount Λ t s c c' : ℤ) := by
  rw [survivorResidueCrossCofactorCovariance_eq_offDiagonal]
  unfold survivorResidueOffDiagonalCofactorGram
  apply Finset.sum_congr rfl
  intro c _hc
  apply Finset.sum_congr rfl
  intro c' _hc'
  exact survivorResidueCofactorGramBlock_eq_mobius_mul_collisionCount
    Λ t s c c'

end RHLean.Proof
