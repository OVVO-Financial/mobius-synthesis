import Mathlib
import RHLean.Analysis.TwoABScaleTransfer

/-!
# Prime dilation and exact scale-transfer discrepancy

This module adds the finite operator identities behind the numerical `2ab`
experiment.

* At the source entry radius `sqrt(cq)`, square-root inversion exchanges the two
  factors exactly.
* For an observable `G` and deterministic baseline `F`, the upper interval is
  the scaled lower interval plus one explicit discrepancy.
* The complete finite high-prime transport pair sum can be read prime-first as
  lower-scale cofactor Mobius fibers.

These are exact identities. No bound for the discrepancy or the prime-dilation
operator is asserted.

This module is classified under `RHLean/Analysis/` because its content is
represented in the bridge paper; the namespace remains `RHLean.Proof` for API
compatibility with existing references.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- At the source entry radius `sqrt(cq)`, square-root inversion sends the lower
factor to the upper factor. -/
theorem squareRootInversion_sqrt_mul_left
    {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    squareRootInversion (Real.sqrt (c * q)) c = q := by
  unfold squareRootInversion
  rw [Real.sq_sqrt (mul_nonneg hc.le hq.le)]
  field_simp [hc.ne']

/-- At the same radius, square-root inversion sends the upper factor back to the
lower factor. -/
theorem squareRootInversion_sqrt_mul_right
    {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    squareRootInversion (Real.sqrt (c * q)) q = c := by
  unfold squareRootInversion
  rw [Real.sq_sqrt (mul_nonneg hc.le hq.le)]
  field_simp [hq.ne']

/-- Discrepancy between an observed upper interval and the lower observed
interval scaled by a deterministic baseline. -/
def scaleTransferDiscrepancy
    (G F : ℝ → ℂ) (R c : ℝ) : ℂ :=
  baselineHighDifference G R c -
    baselineScaleMultiplier F R c * baselineLowDifference G R c

/-- Exact observed upper interval = scaled observed lower interval + explicit
discrepancy. This identity is total and needs no nonzero-denominator hypothesis,
because the discrepancy retains every unmatched term. -/
theorem baselineHighDifference_eq_scaledLow_add_discrepancy
    (G F : ℝ → ℂ) (R c : ℝ) :
    baselineHighDifference G R c =
      baselineScaleMultiplier F R c * baselineLowDifference G R c +
        scaleTransferDiscrepancy G F R c := by
  unfold scaleTransferDiscrepancy
  ring

/-- Weighted observed upper-interval sum. -/
def weightedHighObservableSum {ι : Type*}
    (U : Finset ι) (w : ι → ℂ) (c : ι → ℝ)
    (G : ℝ → ℂ) (R : ℝ) : ℂ :=
  ∑ i ∈ U, w i * baselineHighDifference G R (c i)

/-- Weighted baseline-scaled lower observable. -/
def weightedScaledLowObservableSum {ι : Type*}
    (U : Finset ι) (w : ι → ℂ) (c : ι → ℝ)
    (G F : ℝ → ℂ) (R : ℝ) : ℂ :=
  ∑ i ∈ U,
    w i *
      (baselineScaleMultiplier F R (c i) *
        baselineLowDifference G R (c i))

/-- Weighted scale-transfer discrepancy. -/
def weightedScaleTransferDiscrepancy {ι : Type*}
    (U : Finset ι) (w : ι → ℂ) (c : ι → ℝ)
    (G F : ℝ → ℂ) (R : ℝ) : ℂ :=
  ∑ i ∈ U, w i * scaleTransferDiscrepancy G F R (c i)

/-- Exact finite weighted decomposition into scaled-low main term plus the full
signed discrepancy. -/
theorem weightedHighObservableSum_eq_scaledLow_add_discrepancy
    {ι : Type*}
    (U : Finset ι) (w : ι → ℂ) (c : ι → ℝ)
    (G F : ℝ → ℂ) (R : ℝ) :
    weightedHighObservableSum U w c G R =
      weightedScaledLowObservableSum U w c G F R +
        weightedScaleTransferDiscrepancy U w c G F R := by
  unfold weightedHighObservableSum weightedScaledLowObservableSum
    weightedScaleTransferDiscrepancy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [baselineHighDifference_eq_scaledLow_add_discrepancy G F R (c i)]
  ring

/-- Endpoint immediately below the square cutoff `R^2`. -/
def squareRootEndpoint (R : ℕ) : ℕ :=
  R ^ 2 - 1

/-- Lower-scale cofactor Mobius mass attached to one upper prime coordinate. -/
def primeDilatedLowCofactorMass (R q : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    if c * q ≤ squareRootEndpoint R then canonicalMoebiusWeight c else 0

/-- High transport pair mass read cofactor first. -/
def squareRootTransportCofactorFirst (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
      if q.Prime ∧ c * q ≤ squareRootEndpoint R then
        canonicalMoebiusWeight c
      else 0

/-- The same high transport pair mass read upper-prime first. -/
def squareRootTransportPrimeFirst (R : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
    if q.Prime then primeDilatedLowCofactorMass R q else 0

/-- Exact finite Fubini reindexing from cofactor channels to upper-prime
channels. Every prime-first fiber is supported entirely below `R`. -/
theorem squareRootTransportCofactorFirst_eq_primeFirst (R : ℕ) :
    squareRootTransportCofactorFirst R = squareRootTransportPrimeFirst R := by
  unfold squareRootTransportCofactorFirst squareRootTransportPrimeFirst
    primeDilatedLowCofactorMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hprime : q.Prime <;> simp [hprime]

end RHLean.Proof
