import RHLean.Proof.CoreExtensionDefect
import RHLean.Analysis.ExactActivityPrimeIntervals

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius Interval

namespace RHLean.Analysis

/-- Logarithmic integral normalized to vanish at `2`. Only interval differences
are used below, so the normalization constant is immaterial. -/
def logarithmicIntegralFromTwo (x : ℝ) : ℝ :=
  ∫ u in (2 : ℝ)..x, (Real.log u)⁻¹

/-- Li mass of the exact active-prime interval for stage `t` and core `c`.
The core condition makes the increment vanish outside the active cofactor range. -/
def liActivityIncrement (c t : ℕ) : ℝ :=
  if c ≤ t then
    logarithmicIntegralFromTwo
        (RHLean.Proof.exactActivityPrimeUpper t c : ℝ) -
      logarithmicIntegralFromTwo
        (RHLean.Proof.exactActivityPrimeLower t c - 1 : ℝ)
  else 0

/-- Exact prime count in the same activity interval, cast to the reals. -/
def endpointCoreExtensionCount (c t : ℕ) : ℝ :=
  if c ≤ t then
    ((RHLean.Proof.exactActivityPrimeInterval t c).card : ℝ)
  else 0

/-- Pointwise Li-minus-prime-count discrepancy on the exact activity interval. -/
def liMinusPrimeCountIncrementError (c t : ℕ) : ℝ :=
  liActivityIncrement c t - endpointCoreExtensionCount c t

/-- Exact pointwise split of the Li interval mass into endpoint count and error. -/
theorem liActivityIncrement_eq_endpointCount_add_error (c t : ℕ) :
    liActivityIncrement c t =
      endpointCoreExtensionCount c t +
        liMinusPrimeCountIncrementError c t := by
  unfold liMinusPrimeCountIncrementError
  ring

/-- Finite cofactor support sufficient for the translated window `[N,N+H)`. -/
def liWindowCoreSupport (N H : ℕ) : Finset ℕ :=
  Finset.Icc 1 (N + H)

/-- The concrete finite Li prediction baseline on a translated window. -/
def liWindowPrediction (N H : ℕ) : ℕ → ℝ :=
  mobiusBaseline (liWindowCoreSupport N H) liActivityIncrement

/-- Complementary main `L - prediction`; when the prediction is `-Hhat_Li`,
this is exactly `L + Hhat_Li`. -/
def liComplementaryMain (L : ℕ → ℝ) (N H : ℕ) : ℕ → ℝ :=
  complementaryMainSequence L (liWindowPrediction N H)

/-- Dynamic Li weight from the exact projection-defect API. -/
def liDynamicCoreExtensionWeight
    (L : ℕ → ℝ) (N H c : ℕ) : ℝ :=
  dynamicCoreExtensionWeight (liComplementaryMain L N H)
    liActivityIncrement N H c

/-- Geometric endpoint/core weight: complementary main tested against the exact
active-prime count for the fixed middle core `c`. -/
def endpointCoreExtensionWeight
    (L : ℕ → ℝ) (N H c : ℕ) : ℝ :=
  dynamicCoreExtensionWeight (liComplementaryMain L N H)
    endpointCoreExtensionCount N H c

/-- Windowed Li-minus-prime-count error weight for the fixed middle core. -/
def liPrimeErrorWeight
    (L : ℕ → ℝ) (N H c : ℕ) : ℝ :=
  dynamicCoreExtensionWeight (liComplementaryMain L N H)
    liMinusPrimeCountIncrementError N H c

/-- Exact per-core realization of the dynamic Li weight as endpoint count plus
Li-minus-prime-count error. -/
theorem liDynamicWeight_eq_endpoint_add_primeError
    (L : ℕ → ℝ) (N H c : ℕ) :
    liDynamicCoreExtensionWeight L N H c =
      endpointCoreExtensionWeight L N H c +
        liPrimeErrorWeight L N H c := by
  unfold liDynamicCoreExtensionWeight endpointCoreExtensionWeight
    liPrimeErrorWeight dynamicCoreExtensionWeight localWindowInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← mul_add]
  congr 1
  exact liActivityIncrement_eq_endpointCount_add_error c (N + h)

/-- Möbius-weighted endpoint/core sum on the finite window support. -/
def endpointWeightedMobiusSum
    (L : ℕ → ℝ) (N H : ℕ) : ℝ :=
  ∑ c ∈ liWindowCoreSupport N H, (μ c : ℝ) *
    endpointCoreExtensionWeight L N H c

/-- Möbius-weighted Li-minus-prime-count error sum. -/
def liPrimeErrorMobiusSum
    (L : ℕ → ℝ) (N H : ℕ) : ℝ :=
  ∑ c ∈ liWindowCoreSupport N H, (μ c : ℝ) *
    liPrimeErrorWeight L N H c

/-- The complete weighted Li defect splits exactly into its geometric endpoint
sum and its Li-minus-prime-count error sum. -/
theorem weightedLiDefect_eq_endpoint_add_primeError
    (L : ℕ → ℝ) (N H : ℕ) :
    weightedCoreExtensionDefect (liWindowCoreSupport N H)
        (liComplementaryMain L N H) liActivityIncrement N H =
      endpointWeightedMobiusSum L N H +
        liPrimeErrorMobiusSum L N H := by
  unfold weightedCoreExtensionDefect endpointWeightedMobiusSum
    liPrimeErrorMobiusSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  change (μ c : ℝ) * liDynamicCoreExtensionWeight L N H c =
    (μ c : ℝ) * endpointCoreExtensionWeight L N H c +
      (μ c : ℝ) * liPrimeErrorWeight L N H c
  rw [liDynamicWeight_eq_endpoint_add_primeError]
  ring

/-- Ordinary proposition naming the hard weighted endpoint/core estimate.
It is a target, not an axiom and not a theorem asserted by this module. -/
def EndpointCoreWeightedMertensBound (L : ℕ → ℝ) : Prop :=
  ∀ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N H : ℕ,
    1 ≤ H → H ≤ N →
      |endpointWeightedMobiusSum L N H| ≤
        C * (H : ℝ) * (N : ℝ) ^ 2 /
          (Real.log (N + 2 : ℝ)) ^ A

/-- Ordinary proposition naming the corresponding Li-minus-prime-count error
estimate. Its proof is separate from the exact realization above. -/
def LiPrimeErrorWeightedBound (L : ℕ → ℝ) : Prop :=
  ∀ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N H : ℕ,
    1 ≤ H → H ≤ N →
      |liPrimeErrorMobiusSum L N H| ≤
        C * (H : ℝ) * (N : ℝ) ^ 2 /
          (Real.log (N + 2 : ℝ)) ^ A

/-- Separate endpoint and prime-error estimates bound the full weighted defect. -/
theorem weightedLiDefect_abs_le
    (L : ℕ → ℝ) (N H : ℕ) (endpointBound errorBound : ℝ)
    (hEndpoint : |endpointWeightedMobiusSum L N H| ≤ endpointBound)
    (hError : |liPrimeErrorMobiusSum L N H| ≤ errorBound) :
    |weightedCoreExtensionDefect (liWindowCoreSupport N H)
        (liComplementaryMain L N H) liActivityIncrement N H| ≤
      endpointBound + errorBound := by
  rw [weightedLiDefect_eq_endpoint_add_primeError]
  calc
    |endpointWeightedMobiusSum L N H + liPrimeErrorMobiusSum L N H| ≤
        |endpointWeightedMobiusSum L N H| +
          |liPrimeErrorMobiusSum L N H| := abs_add_le _ _
    _ ≤ endpointBound + errorBound := add_le_add hEndpoint hError

/-- A weighted-defect estimate at the prediction-energy scale gives the desired
coefficient-gap estimate. This is the machine-checked end of the reduction. -/
theorem liCoefficientGap_abs_le
    (L : ℕ → ℝ) (N H : ℕ) (gapBound : ℝ)
    (henergy : 0 < localWindowEnergy (liWindowPrediction N H) N H)
    (hdefect :
      |weightedCoreExtensionDefect (liWindowCoreSupport N H)
          (liComplementaryMain L N H) liActivityIncrement N H| ≤
        gapBound * localWindowEnergy (liWindowPrediction N H) N H) :
    |1 - twoVectorOptimalCoefficient
        (localWindowEnergy (liWindowPrediction N H) N H)
        (localWindowInner L (liWindowPrediction N H) N H)| ≤ gapBound := by
  have hgap :
      1 - twoVectorOptimalCoefficient
          (localWindowEnergy (liWindowPrediction N H) N H)
          (localWindowInner L (liWindowPrediction N H) N H) =
        -weightedCoreExtensionDefect (liWindowCoreSupport N H)
            (liComplementaryMain L N H) liActivityIncrement N H /
          localWindowEnergy (liWindowPrediction N H) N H := by
    simpa [liWindowPrediction, liComplementaryMain] using
      one_sub_optimalCoefficient_eq_weightedCoreExtension
        (liWindowCoreSupport N H) L liActivityIncrement N H
        (ne_of_gt henergy)
  rw [hgap, abs_div, abs_neg, abs_of_pos henergy]
  exact (div_le_iff₀ henergy).2 hdefect

end RHLean.Analysis
