import Mathlib
import RHLean.Proof.CumulativeHeightFlow
import RHLean.Geometry.TwoABDisplacement

/-!
# Exact 2ab scale transfer

This module formalizes the exact part of the numerical scale-transfer experiment.
It keeps three statements separate:

* one canonical source enters at its square-root block and, if necessary, moves
  to the smooth population at its largest-prime transition;
* the source-level identity `entered = smooth - transport` is exact;
* for every deterministic baseline `F`, square-root inversion scales the lower
  interval difference `F(R)-F(c)` into the upper interval difference
  `F(R^2/c)-F(R)` by an explicit multiplier.

No estimate for the multiplier-weighted Mobius sum is asserted. In particular,
the exact scale transfer is a realization theorem, not an RH-scale cancellation
theorem.

This module is classified under `RHLean/Analysis/` because its content is
represented in the bridge paper; the namespace remains `RHLean.Proof` for API
compatibility with existing references.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- A finite source with an entry block, a smoothness-transition block, and a
complex weight. No ordering assumption is required: sources whose transition
precedes entry are born smooth. -/
structure ScaleTransferAtom where
  entry : ℕ
  transition : ℕ
  weight : ℂ

/-- Contribution after the source has entered the square prefix. -/
def scaleTransferEnteredContribution (p : ScaleTransferAtom) (n : ℕ) : ℂ :=
  if p.entry ≤ n then p.weight else 0

/-- Contribution after the source has both entered and become smooth. -/
def scaleTransferSmoothContribution (p : ScaleTransferAtom) (n : ℕ) : ℂ :=
  if p.entry ≤ n ∧ p.transition ≤ n then p.weight else 0

/-- Sign-reversed transport contribution while the source has entered but has
not yet reached its smoothness transition. -/
def scaleTransferTransportContribution (p : ScaleTransferAtom) (n : ℕ) : ℂ :=
  if p.entry ≤ n ∧ n < p.transition then -p.weight else 0

/-- Exact source-level bookkeeping identity. -/
theorem scaleTransferEntered_eq_smooth_sub_transport
    (p : ScaleTransferAtom) (n : ℕ) :
    scaleTransferEnteredContribution p n =
      scaleTransferSmoothContribution p n -
        scaleTransferTransportContribution p n := by
  unfold scaleTransferEnteredContribution scaleTransferSmoothContribution
    scaleTransferTransportContribution
  by_cases hentry : p.entry ≤ n
  · by_cases htransition : p.transition ≤ n
    · have hnot : ¬n < p.transition := Nat.not_lt.mpr htransition
      simp [hentry, htransition, hnot]
    · have hlt : n < p.transition := Nat.lt_of_not_ge htransition
      simp [hentry, htransition, hlt]
  · simp [hentry]

/-- Entered amplitude of a finite source family. -/
def scaleTransferEnteredSum {ι : Type*}
    (U : Finset ι) (atom : ι → ScaleTransferAtom) (n : ℕ) : ℂ :=
  ∑ i ∈ U, scaleTransferEnteredContribution (atom i) n

/-- Smooth amplitude of a finite source family. -/
def scaleTransferSmoothSum {ι : Type*}
    (U : Finset ι) (atom : ι → ScaleTransferAtom) (n : ℕ) : ℂ :=
  ∑ i ∈ U, scaleTransferSmoothContribution (atom i) n

/-- Sign-reversed transport amplitude of a finite source family. -/
def scaleTransferTransportSum {ι : Type*}
    (U : Finset ι) (atom : ι → ScaleTransferAtom) (n : ℕ) : ℂ :=
  ∑ i ∈ U, scaleTransferTransportContribution (atom i) n

/-- Exact aggregate scale-transfer identity. -/
theorem scaleTransferEnteredSum_eq_smooth_sub_transport
    {ι : Type*} (U : Finset ι) (atom : ι → ScaleTransferAtom) (n : ℕ) :
    scaleTransferEnteredSum U atom n =
      scaleTransferSmoothSum U atom n - scaleTransferTransportSum U atom n := by
  unfold scaleTransferEnteredSum scaleTransferSmoothSum scaleTransferTransportSum
  calc
    (∑ i ∈ U, scaleTransferEnteredContribution (atom i) n) =
        ∑ i ∈ U,
          (scaleTransferSmoothContribution (atom i) n -
            scaleTransferTransportContribution (atom i) n) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact scaleTransferEntered_eq_smooth_sub_transport (atom i) n
    _ = (∑ i ∈ U, scaleTransferSmoothContribution (atom i) n) -
          ∑ i ∈ U, scaleTransferTransportContribution (atom i) n := by
      rw [Finset.sum_sub_distrib]

/-- Canonical source atom: entry block `floor(sqrt m)` and transition block
`P+(m)-1`. -/
def canonicalScaleTransferAtom (m : ℕ) : ScaleTransferAtom where
  entry := Nat.sqrt m
  transition := canonicalLargestPrimeFactor m - 1
  weight := canonicalMoebiusWeight m

/-- Entry by block `n` is exactly membership in the complete square prefix
`[0,(n+1)^2)`. -/
theorem canonicalEntry_le_iff_mem_cumulativeSquarePrefixSet
    (n m : ℕ) :
    Nat.sqrt m ≤ n ↔ m ∈ cumulativeSquarePrefixSet n := by
  simp only [cumulativeSquarePrefixSet, Finset.mem_range]
  constructor
  · intro h
    apply (Nat.sqrt_lt').1
    omega
  · intro h
    have hsqrt : Nat.sqrt m < n + 1 := (Nat.sqrt_lt').2 h
    omega

/-- The canonical transition block is reached exactly when the largest prime
factor is at most the current square-root cutoff. -/
theorem canonicalTransition_le_iff_largestPrimeFactor_le
    (n m : ℕ) :
    canonicalLargestPrimeFactor m - 1 ≤ n ↔
      canonicalLargestPrimeFactor m ≤ n + 1 := by
  omega

/-- Current square-root-smooth mass inside the complete square prefix. -/
def squareRootSmoothMass (n : ℕ) : ℂ :=
  ∑ m ∈ cumulativeSquarePrefixSet n,
    if canonicalLargestPrimeFactor m ≤ n + 1 then canonicalMoebiusWeight m else 0

/-- Sign-reversed current transport mass inside the complete square prefix. -/
def squareRootTransportMass (n : ℕ) : ℂ :=
  -∑ m ∈ cumulativeSquarePrefixSet n,
    if n + 1 < canonicalLargestPrimeFactor m then canonicalMoebiusWeight m else 0

/-- The complete square-prefix population is exactly the current smooth mass
minus the sign-reversed current transport mass. -/
theorem cumulativeSquarePrefixMass_eq_smooth_sub_transport (n : ℕ) :
    canonicalMoebiusMass (cumulativeSquarePrefixSet n) =
      squareRootSmoothMass n - squareRootTransportMass n := by
  unfold canonicalMoebiusMass squareRootSmoothMass squareRootTransportMass
  rw [sub_neg_eq_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hsmooth : canonicalLargestPrimeFactor m ≤ n + 1
  · simp [hsmooth, Nat.not_lt.mpr hsmooth]
  · have htransport : n + 1 < canonicalLargestPrimeFactor m :=
      Nat.lt_of_not_ge hsmooth
    simp [hsmooth, htransport]

/-- The complete square-prefix population mass is the existing concrete Mertens
value. -/
theorem cumulativeSquarePrefixMass_eq_squarePrefixMertens (n : ℕ) :
    canonicalMoebiusMass (cumulativeSquarePrefixSet n) =
      RHLean.Analysis.squarePrefixMertens n := by
  unfold canonicalMoebiusMass cumulativeSquarePrefixSet canonicalMoebiusWeight
    RHLean.Analysis.squarePrefixMertens RHLean.Analysis.mertensSummatory
  rw [RHLean.Analysis.squarePrefixEndpoint_add_one]

/-- Exact dynamic smooth-minus-transport form of the square-prefix Mertens
value. -/
theorem squarePrefixMertens_eq_squareRootSmooth_sub_transport (n : ℕ) :
    RHLean.Analysis.squarePrefixMertens n =
      squareRootSmoothMass n - squareRootTransportMass n := by
  rw [← cumulativeSquarePrefixMass_eq_squarePrefixMertens]
  exact cumulativeSquarePrefixMass_eq_smooth_sub_transport n

/-- Multiplicative inversion about the square-root cutoff `R`. -/
def squareRootInversion (R x : ℝ) : ℝ :=
  R ^ 2 / x

/-- The cutoff is the fixed point of square-root inversion. -/
theorem squareRootInversion_fixed
    {R : ℝ} (hR : R ≠ 0) :
    squareRootInversion R R = R := by
  unfold squareRootInversion
  field_simp [hR]

/-- Square-root inversion is an involution away from zero. -/
theorem squareRootInversion_involutive
    {R x : ℝ} (hR : R ≠ 0) (hx : x ≠ 0) :
    squareRootInversion R (squareRootInversion R x) = x := by
  unfold squareRootInversion
  field_simp [hR, hx]

/-- The upper interval has exactly `R/c` times the Euclidean length of the lower
interval. -/
theorem squareRootInversion_interval_length
    {R c : ℝ} (hc : c ≠ 0) :
    squareRootInversion R c - R = (R / c) * (R - c) := by
  unfold squareRootInversion
  field_simp [hc]

/-- Normalized doubled `2ab` height of a positive factor pair. -/
def normalizedTwoABHeight (c q : ℝ) : ℝ :=
  (q ^ 2 - c ^ 2) / (2 * c * q)

/-- The normalized `2ab` location is exactly the antisymmetric multiplicative
factor ratio. -/
theorem normalizedTwoABHeight_eq_factorRatio
    {c q : ℝ} (hc : c ≠ 0) (hq : q ≠ 0) :
    normalizedTwoABHeight c q = ((q / c) - (c / q)) / 2 := by
  unfold normalizedTwoABHeight
  field_simp [hc, hq]

/-- Continuous source dilation from entry scale `sqrt(cq)` to transition scale
`q`. -/
def factorDilation (c q : ℝ) : ℝ :=
  q / Real.sqrt (c * q)

/-- The squared continuous dilation is the factor ratio `q/c`. -/
theorem factorDilation_sq
    {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    factorDilation c q ^ 2 = q / c := by
  have hprod : 0 ≤ c * q := mul_nonneg hc.le hq.le
  have hsqrt_ne : Real.sqrt (c * q) ≠ 0 := by positivity
  unfold factorDilation
  rw [div_pow, Real.sq_sqrt hprod]
  field_simp [hc.ne', hq.ne', hsqrt_ne]

/-- Lower baseline difference on the interval below the square-root cutoff. -/
def baselineLowDifference (F : ℝ → ℂ) (R c : ℝ) : ℂ :=
  F R - F c

/-- Upper baseline difference on the square-root-inverted interval. -/
def baselineHighDifference (F : ℝ → ℂ) (R c : ℝ) : ℂ :=
  F (squareRootInversion R c) - F R

/-- Exact multiplier carrying a nonzero lower baseline difference to its upper
square-root-inverted difference. -/
def baselineScaleMultiplier (F : ℝ → ℂ) (R c : ℝ) : ℂ :=
  baselineHighDifference F R c / baselineLowDifference F R c

/-- For every deterministic baseline, the upper interval difference is exactly
the explicit multiplier times the lower interval difference. -/
theorem baselineHighDifference_eq_scale_mul_low
    (F : ℝ → ℂ) (R c : ℝ)
    (hlow : baselineLowDifference F R c ≠ 0) :
    baselineHighDifference F R c =
      baselineScaleMultiplier F R c * baselineLowDifference F R c := by
  unfold baselineScaleMultiplier
  field_simp [hlow]

/-- Direct weighted upper-baseline sum. -/
def weightedHighBaselineSum {ι : Type*}
    (U : Finset ι) (w : ι → ℂ) (c : ι → ℝ)
    (F : ℝ → ℂ) (R : ℝ) : ℂ :=
  ∑ i ∈ U, w i * baselineHighDifference F R (c i)

/-- The same weighted upper-baseline sum written as scaled lower differences. -/
def weightedScaledLowBaselineSum {ι : Type*}
    (U : Finset ι) (w : ι → ℂ) (c : ι → ℝ)
    (F : ℝ → ℂ) (R : ℝ) : ℂ :=
  ∑ i ∈ U,
    w i *
      (baselineScaleMultiplier F R (c i) * baselineLowDifference F R (c i))

/-- Exact finite weighted low-to-high baseline scaling identity. -/
theorem weightedHighBaselineSum_eq_scaledLow
    {ι : Type*}
    (U : Finset ι) (w : ι → ℂ) (c : ι → ℝ)
    (F : ℝ → ℂ) (R : ℝ)
    (hlow : ∀ i ∈ U, baselineLowDifference F R (c i) ≠ 0) :
    weightedHighBaselineSum U w c F R =
      weightedScaledLowBaselineSum U w c F R := by
  unfold weightedHighBaselineSum weightedScaledLowBaselineSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [baselineHighDifference_eq_scale_mul_low F R (c i) (hlow i hi)]

end RHLean.Proof
