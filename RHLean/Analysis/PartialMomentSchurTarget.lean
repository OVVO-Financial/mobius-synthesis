import Mathlib

/-!
# Arbitrary-target partial moments and target-invariant Schur covariance

This module records the exact algebra behind the partial-moment covariance
reassembly used by NNS, but in a form suitable for the physical finite-state
route.

For any observation vector `x` and target `t`, write each coordinate deviation
as

`x - t = upper - lower`.

The outer product therefore splits exactly into four directional blocks:

`Q_t = CLPM_t + CUPM_t - DLPM_t - DUPM_t`.

The target need not be the mean.  For an arbitrary finite weighted population,
let `W` be total weight, `m_t` the first moment about `t`, and `Q_t` the second
moment about `t`.  The scaled Schur complement

`W * Q_t - m_t m_t^T`

is exactly independent of `t`.  No positivity, probability normalization, or
asymptotic assumption is used.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Positive deviation above a scalar target. -/
def partialUpper (x t : ℝ) : ℝ :=
  if t ≤ x then x - t else 0

/-- Positive deviation below a scalar target. -/
def partialLower (x t : ℝ) : ℝ :=
  if x < t then t - x else 0

/-- Every scalar deviation is upper partial deviation minus lower partial
 deviation. -/
theorem partialUpper_sub_partialLower (x t : ℝ) :
    partialUpper x t - partialLower x t = x - t := by
  by_cases h : t ≤ x
  · have hnot : ¬ x < t := not_lt_of_ge h
    simp [partialUpper, partialLower, h, hnot]
  · have hlt : x < t := lt_of_not_ge h
    simp [partialUpper, partialLower, h, hlt]

/-- Pointwise four-block partial-moment identity. -/
theorem deviation_product_eq_partial_reassembly
    (x y tx ty : ℝ) :
    (x - tx) * (y - ty) =
      partialLower x tx * partialLower y ty +
        partialUpper x tx * partialUpper y ty -
        partialLower x tx * partialUpper y ty -
        partialUpper x tx * partialLower y ty := by
  rw [← partialUpper_sub_partialLower x tx,
    ← partialUpper_sub_partialLower y ty]
  ring

section FiniteWeighted

variable {α ι : Type*}

/-- Total mass of a finite weighted population. -/
def finiteTotalWeight (S : Finset α) (w : α → ℝ) : ℝ :=
  ∑ a ∈ S, w a

/-- First moment of the weighted vector population about an arbitrary target. -/
def finiteTargetFirstMoment
    (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ) (t : ι → ℝ) :
    ι → ℝ :=
  fun i => ∑ a ∈ S, w a * (x a i - t i)

/-- Second-moment matrix of the weighted vector population about an arbitrary
 target. -/
def finiteTargetSecondMoment
    (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ) (t : ι → ℝ) :
    Matrix ι ι ℝ :=
  fun i j => ∑ a ∈ S, w a * (x a i - t i) * (x a j - t j)

/-- Co-lower partial-moment block. -/
def finiteCLPM
    (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ) (t : ι → ℝ) :
    Matrix ι ι ℝ :=
  fun i j => ∑ a ∈ S,
    w a * partialLower (x a i) (t i) * partialLower (x a j) (t j)

/-- Co-upper partial-moment block. -/
def finiteCUPM
    (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ) (t : ι → ℝ) :
    Matrix ι ι ℝ :=
  fun i j => ∑ a ∈ S,
    w a * partialUpper (x a i) (t i) * partialUpper (x a j) (t j)

/-- Divergent lower-to-upper partial-moment block. -/
def finiteDLPM
    (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ) (t : ι → ℝ) :
    Matrix ι ι ℝ :=
  fun i j => ∑ a ∈ S,
    w a * partialLower (x a i) (t i) * partialUpper (x a j) (t j)

/-- Divergent upper-to-lower partial-moment block. -/
def finiteDUPM
    (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ) (t : ι → ℝ) :
    Matrix ι ι ℝ :=
  fun i j => ∑ a ∈ S,
    w a * partialUpper (x a i) (t i) * partialLower (x a j) (t j)

/-- **Arbitrary-target partial-moment reassembly.**  This is the matrix identity

`Q_t = CLPM_t + CUPM_t - DLPM_t - DUPM_t`

for every target `t`, not only the population mean. -/
theorem finiteTargetSecondMoment_eq_partial_reassembly
    (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ) (t : ι → ℝ) :
    finiteTargetSecondMoment S w x t =
      finiteCLPM S w x t + finiteCUPM S w x t -
        finiteDLPM S w x t - finiteDUPM S w x t := by
  ext i j
  simp only [finiteTargetSecondMoment, finiteCLPM, finiteCUPM,
    finiteDLPM, finiteDUPM, Matrix.add_apply, Matrix.sub_apply]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have h := deviation_product_eq_partial_reassembly
    (x a i) (x a j) (t i) (t j)
  calc
    w a * (x a i - t i) * (x a j - t j) =
        w a * ((x a i - t i) * (x a j - t j)) := by ring
    _ = w a *
        (partialLower (x a i) (t i) * partialLower (x a j) (t j) +
          partialUpper (x a i) (t i) * partialUpper (x a j) (t j) -
          partialLower (x a i) (t i) * partialUpper (x a j) (t j) -
          partialUpper (x a i) (t i) * partialLower (x a j) (t j)) := by rw [h]
    _ = w a * partialLower (x a i) (t i) * partialLower (x a j) (t j) +
          w a * partialUpper (x a i) (t i) * partialUpper (x a j) (t j) -
          w a * partialLower (x a i) (t i) * partialUpper (x a j) (t j) -
          w a * partialUpper (x a i) (t i) * partialLower (x a j) (t j) := by ring

/-- Exact change-of-target law for the first moment. -/
theorem finiteTargetFirstMoment_target_shift
    (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ)
    (s t : ι → ℝ) (i : ι) :
    finiteTargetFirstMoment S w x t i =
      finiteTargetFirstMoment S w x s i +
        finiteTotalWeight S w * (s i - t i) := by
  unfold finiteTargetFirstMoment finiteTotalWeight
  calc
    (∑ a ∈ S, w a * (x a i - t i)) =
        ∑ a ∈ S,
          (w a * (x a i - s i) + w a * (s i - t i)) := by
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = (∑ a ∈ S, w a * (x a i - s i)) +
          ∑ a ∈ S, w a * (s i - t i) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ a ∈ S, w a * (x a i - s i)) +
          (∑ a ∈ S, w a) * (s i - t i) := by
      rw [Finset.sum_mul]

/-- Exact change-of-target law for the second moment.  The two cross terms are
 the old first moments; this is the finite-population parallel-axis identity. -/
theorem finiteTargetSecondMoment_target_shift
    (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ)
    (s t : ι → ℝ) (i j : ι) :
    finiteTargetSecondMoment S w x t i j =
      finiteTargetSecondMoment S w x s i j +
        finiteTargetFirstMoment S w x s i * (s j - t j) +
        finiteTargetFirstMoment S w x s j * (s i - t i) +
        finiteTotalWeight S w * (s i - t i) * (s j - t j) := by
  unfold finiteTargetSecondMoment finiteTargetFirstMoment finiteTotalWeight
  calc
    (∑ a ∈ S, w a * (x a i - t i) * (x a j - t j)) =
        ∑ a ∈ S,
          (w a * (x a i - s i) * (x a j - s j) +
            (w a * (x a i - s i)) * (s j - t j) +
            (w a * (x a j - s j)) * (s i - t i) +
            w a * ((s i - t i) * (s j - t j))) := by
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = (∑ a ∈ S, w a * (x a i - s i) * (x a j - s j)) +
          (∑ a ∈ S, w a * (x a i - s i)) * (s j - t j) +
          (∑ a ∈ S, w a * (x a j - s j)) * (s i - t i) +
          (∑ a ∈ S, w a) * ((s i - t i) * (s j - t j)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib]
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    _ = (∑ a ∈ S, w a * (x a i - s i) * (x a j - s j)) +
          (∑ a ∈ S, w a * (x a i - s i)) * (s j - t j) +
          (∑ a ∈ S, w a * (x a j - s j)) * (s i - t i) +
          (∑ a ∈ S, w a) * (s i - t i) * (s j - t j) := by
      ring

/-- Scaled Schur complement of the augmented target moment matrix.  Scaling by
 `W` avoids division and makes the identity valid even before assuming positive
 or normalized weights. -/
def finiteTargetScaledSchur
    (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ) (t : ι → ℝ) :
    Matrix ι ι ℝ :=
  fun i j =>
    finiteTotalWeight S w * finiteTargetSecondMoment S w x t i j -
      finiteTargetFirstMoment S w x t i *
        finiteTargetFirstMoment S w x t j

/-- **Target invariance of the Schur covariance.**  Changing the partial-moment
 target changes the raw second moment by a rank-one/first-moment correction, but
 the scaled Schur complement is exactly unchanged. -/
theorem finiteTargetScaledSchur_target_invariant
    (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ)
    (s t : ι → ℝ) :
    finiteTargetScaledSchur S w x t =
      finiteTargetScaledSchur S w x s := by
  ext i j
  unfold finiteTargetScaledSchur
  rw [finiteTargetSecondMoment_target_shift S w x s t i j,
    finiteTargetFirstMoment_target_shift S w x s t i,
    finiteTargetFirstMoment_target_shift S w x s t j]
  ring

/-- If `s` is a weighted center, the arbitrary-target second moment is the
 centered second moment plus the expected rank-one target displacement. -/
theorem finiteTargetSecondMoment_eq_centered_add_rankOne
    (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ)
    (s t : ι → ℝ)
    (hs : ∀ i, finiteTargetFirstMoment S w x s i = 0) :
    finiteTargetSecondMoment S w x t =
      fun i j => finiteTargetSecondMoment S w x s i j +
        finiteTotalWeight S w * (s i - t i) * (s j - t j) := by
  funext i j
  rw [finiteTargetSecondMoment_target_shift S w x s t i j,
    hs i, hs j]
  ring

end FiniteWeighted

end RHLean.Analysis
