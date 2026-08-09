import Mathlib
import RHLean.Proof.BlockLyapunovClosure

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/--
Low-height shell positions at every scale. The positive gap and pairwise
separation hypotheses are kept explicit; the incidence bound is derived below
from these hypotheses and the declared height cutoff.
-/
structure LowHeightSpacingData where
  count : ℕ → ℕ
  cutoff : ℕ → ℕ
  gap : ℕ → ℕ
  height : (M : ℕ) → Fin (count M) → ℕ
  gap_pos : ∀ M, 0 < gap M
  height_le_cutoff : ∀ M i, height M i ≤ cutoff M
  separated :
    ∀ (M : ℕ) {i j : Fin (count M)}, i < j →
      height M i + gap M ≤ height M j

/-- Positive separated low-height positions are strictly increasing. -/
theorem lowHeight_height_strictMono
    (spacing : LowHeightSpacingData) (M : ℕ) :
    StrictMono (spacing.height M) := by
  intro i j hij
  have hsep := spacing.separated M hij
  have hgap := spacing.gap_pos M
  omega

/--
A separated family of low-height shells lying below `cutoff M` has at most
`cutoff M + 1` incidences. This is the spacing-to-incidence step used by the
forcing estimates.
-/
theorem lowHeight_count_le_cutoff_succ
    (spacing : LowHeightSpacingData) (M : ℕ) :
    spacing.count M ≤ spacing.cutoff M + 1 := by
  let embed : Fin (spacing.count M) → Fin (spacing.cutoff M + 1) :=
    fun i =>
      ⟨spacing.height M i, by
        have hle := spacing.height_le_cutoff M i
        omega⟩
  have hinjective : Function.Injective embed := by
    intro i j hij
    apply (lowHeight_height_strictMono spacing M).injective
    exact congrArg Fin.val hij
  simpa using Fintype.card_le_of_injective embed hinjective

/-- A reusable norm estimate for a finite complex family with a uniform envelope. -/
theorem norm_fin_sum_le_card_mul
    {n : ℕ} (term : Fin n → ℂ) (envelope : ℝ)
    (hterm : ∀ i, ‖term i‖ ≤ envelope) :
    ‖∑ i, term i‖ ≤ (n : ℝ) * envelope := by
  calc
    ‖∑ i, term i‖ ≤ ∑ i, ‖term i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, envelope := by
      exact Finset.sum_le_sum fun i _ => hterm i
    _ = (n : ℝ) * envelope := by simp

/--
The actual low-height forcing data in both recurrence rows. Shell positions,
term values, and row-specific envelopes remain separate.
-/
structure ActualLowHeightForcingData where
  spacing : LowHeightSpacingData
  resonantTerm : (M : ℕ) → Fin (spacing.count M) → ℂ
  nonresonantTerm : (M : ℕ) → Fin (spacing.count M) → ℂ
  resonantEnvelope : ℕ → ℝ
  nonresonantEnvelope : ℕ → ℝ
  resonantEnvelope_nonneg : ∀ M, 0 ≤ resonantEnvelope M
  nonresonantEnvelope_nonneg : ∀ M, 0 ≤ nonresonantEnvelope M
  resonantTerm_norm_le :
    ∀ M i, ‖resonantTerm M i‖ ≤ resonantEnvelope M
  nonresonantTerm_norm_le :
    ∀ M i, ‖nonresonantTerm M i‖ ≤ nonresonantEnvelope M

/-- Exact low-height forcing in the resonant row. -/
def actualLowHeightResonant
    (data : ActualLowHeightForcingData) (M : ℕ) : ℂ :=
  ∑ i, data.resonantTerm M i

/-- Exact low-height forcing in the nonresonant row. -/
def actualLowHeightNonresonant
    (data : ActualLowHeightForcingData) (M : ℕ) : ℂ :=
  ∑ i, data.nonresonantTerm M i

/-- Incidence-count estimate for the resonant low-height forcing. -/
theorem norm_actualLowHeightResonant_le_count
    (data : ActualLowHeightForcingData) (M : ℕ) :
    ‖actualLowHeightResonant data M‖ ≤
      (data.spacing.count M : ℝ) * data.resonantEnvelope M := by
  exact norm_fin_sum_le_card_mul
    (data.resonantTerm M) (data.resonantEnvelope M)
    (data.resonantTerm_norm_le M)

/-- Incidence-count estimate for the nonresonant low-height forcing. -/
theorem norm_actualLowHeightNonresonant_le_count
    (data : ActualLowHeightForcingData) (M : ℕ) :
    ‖actualLowHeightNonresonant data M‖ ≤
      (data.spacing.count M : ℝ) * data.nonresonantEnvelope M := by
  exact norm_fin_sum_le_card_mul
    (data.nonresonantTerm M) (data.nonresonantEnvelope M)
    (data.nonresonantTerm_norm_le M)

/-- Spacing and the height cutoff bound the resonant low-height forcing. -/
theorem norm_actualLowHeightResonant_le_cutoff
    (data : ActualLowHeightForcingData) (M : ℕ) :
    ‖actualLowHeightResonant data M‖ ≤
      ((data.spacing.cutoff M + 1 : ℕ) : ℝ) * data.resonantEnvelope M := by
  have hcount :
      (data.spacing.count M : ℝ) ≤
        ((data.spacing.cutoff M + 1 : ℕ) : ℝ) := by
    exact_mod_cast lowHeight_count_le_cutoff_succ data.spacing M
  calc
    ‖actualLowHeightResonant data M‖ ≤
        (data.spacing.count M : ℝ) * data.resonantEnvelope M :=
      norm_actualLowHeightResonant_le_count data M
    _ ≤ ((data.spacing.cutoff M + 1 : ℕ) : ℝ) * data.resonantEnvelope M :=
      mul_le_mul_of_nonneg_right hcount (data.resonantEnvelope_nonneg M)

/-- Spacing and the height cutoff bound the nonresonant low-height forcing. -/
theorem norm_actualLowHeightNonresonant_le_cutoff
    (data : ActualLowHeightForcingData) (M : ℕ) :
    ‖actualLowHeightNonresonant data M‖ ≤
      ((data.spacing.cutoff M + 1 : ℕ) : ℝ) * data.nonresonantEnvelope M := by
  have hcount :
      (data.spacing.count M : ℝ) ≤
        ((data.spacing.cutoff M + 1 : ℕ) : ℝ) := by
    exact_mod_cast lowHeight_count_le_cutoff_succ data.spacing M
  calc
    ‖actualLowHeightNonresonant data M‖ ≤
        (data.spacing.count M : ℝ) * data.nonresonantEnvelope M :=
      norm_actualLowHeightNonresonant_le_count data M
    _ ≤ ((data.spacing.cutoff M + 1 : ℕ) : ℝ) * data.nonresonantEnvelope M :=
      mul_le_mul_of_nonneg_right hcount (data.nonresonantEnvelope_nonneg M)

/--
Endpoint forcing keeps the left and right endpoints distinct in both rows,
together with separate norm bounds for every endpoint.
-/
structure ActualEndpointForcingData where
  leftResonant : ℕ → ℂ
  rightResonant : ℕ → ℂ
  leftNonresonant : ℕ → ℂ
  rightNonresonant : ℕ → ℂ
  leftResonantBound : ℕ → ℝ
  rightResonantBound : ℕ → ℝ
  leftNonresonantBound : ℕ → ℝ
  rightNonresonantBound : ℕ → ℝ
  norm_leftResonant_le : ∀ M, ‖leftResonant M‖ ≤ leftResonantBound M
  norm_rightResonant_le : ∀ M, ‖rightResonant M‖ ≤ rightResonantBound M
  norm_leftNonresonant_le : ∀ M, ‖leftNonresonant M‖ ≤ leftNonresonantBound M
  norm_rightNonresonant_le : ∀ M, ‖rightNonresonant M‖ ≤ rightNonresonantBound M

/-- Exact two-sided endpoint forcing in the resonant row. -/
def actualEndpointResonant
    (data : ActualEndpointForcingData) (M : ℕ) : ℂ :=
  data.leftResonant M + data.rightResonant M

/-- Exact two-sided endpoint forcing in the nonresonant row. -/
def actualEndpointNonresonant
    (data : ActualEndpointForcingData) (M : ℕ) : ℂ :=
  data.leftNonresonant M + data.rightNonresonant M

/-- The resonant endpoint forcing is bounded by the sum of its two endpoint bounds. -/
theorem norm_actualEndpointResonant_le
    (data : ActualEndpointForcingData) (M : ℕ) :
    ‖actualEndpointResonant data M‖ ≤
      data.leftResonantBound M + data.rightResonantBound M := by
  calc
    ‖actualEndpointResonant data M‖ ≤
        ‖data.leftResonant M‖ + ‖data.rightResonant M‖ := by
      exact norm_add_le _ _
    _ ≤ data.leftResonantBound M + data.rightResonantBound M :=
      add_le_add (data.norm_leftResonant_le M) (data.norm_rightResonant_le M)

/-- The nonresonant endpoint forcing is bounded by the sum of its endpoint bounds. -/
theorem norm_actualEndpointNonresonant_le
    (data : ActualEndpointForcingData) (M : ℕ) :
    ‖actualEndpointNonresonant data M‖ ≤
      data.leftNonresonantBound M + data.rightNonresonantBound M := by
  calc
    ‖actualEndpointNonresonant data M‖ ≤
        ‖data.leftNonresonant M‖ + ‖data.rightNonresonant M‖ := by
      exact norm_add_le _ _
    _ ≤ data.leftNonresonantBound M + data.rightNonresonantBound M :=
      add_le_add
        (data.norm_leftNonresonant_le M)
        (data.norm_rightNonresonant_le M)

/--
Boundary forcing is a finite family in each row. The incidence cap is separate
from the pointwise envelope, so later geometry can instantiate them independently.
-/
structure ActualBoundaryForcingData where
  count : ℕ → ℕ
  incidenceCap : ℕ → ℕ
  count_le_incidenceCap : ∀ M, count M ≤ incidenceCap M
  resonantTerm : (M : ℕ) → Fin (count M) → ℂ
  nonresonantTerm : (M : ℕ) → Fin (count M) → ℂ
  resonantEnvelope : ℕ → ℝ
  nonresonantEnvelope : ℕ → ℝ
  resonantEnvelope_nonneg : ∀ M, 0 ≤ resonantEnvelope M
  nonresonantEnvelope_nonneg : ∀ M, 0 ≤ nonresonantEnvelope M
  resonantTerm_norm_le :
    ∀ M i, ‖resonantTerm M i‖ ≤ resonantEnvelope M
  nonresonantTerm_norm_le :
    ∀ M i, ‖nonresonantTerm M i‖ ≤ nonresonantEnvelope M

/-- Exact boundary forcing in the resonant row. -/
def actualBoundaryResonant
    (data : ActualBoundaryForcingData) (M : ℕ) : ℂ :=
  ∑ i, data.resonantTerm M i

/-- Exact boundary forcing in the nonresonant row. -/
def actualBoundaryNonresonant
    (data : ActualBoundaryForcingData) (M : ℕ) : ℂ :=
  ∑ i, data.nonresonantTerm M i

/-- The resonant boundary forcing is bounded by incidence times envelope. -/
theorem norm_actualBoundaryResonant_le
    (data : ActualBoundaryForcingData) (M : ℕ) :
    ‖actualBoundaryResonant data M‖ ≤
      (data.incidenceCap M : ℝ) * data.resonantEnvelope M := by
  have hcount :
      (data.count M : ℝ) ≤ (data.incidenceCap M : ℝ) := by
    exact_mod_cast data.count_le_incidenceCap M
  calc
    ‖actualBoundaryResonant data M‖ ≤
        (data.count M : ℝ) * data.resonantEnvelope M :=
      norm_fin_sum_le_card_mul
        (data.resonantTerm M) (data.resonantEnvelope M)
        (data.resonantTerm_norm_le M)
    _ ≤ (data.incidenceCap M : ℝ) * data.resonantEnvelope M :=
      mul_le_mul_of_nonneg_right hcount (data.resonantEnvelope_nonneg M)

/-- The nonresonant boundary forcing is bounded by incidence times envelope. -/
theorem norm_actualBoundaryNonresonant_le
    (data : ActualBoundaryForcingData) (M : ℕ) :
    ‖actualBoundaryNonresonant data M‖ ≤
      (data.incidenceCap M : ℝ) * data.nonresonantEnvelope M := by
  have hcount :
      (data.count M : ℝ) ≤ (data.incidenceCap M : ℝ) := by
    exact_mod_cast data.count_le_incidenceCap M
  calc
    ‖actualBoundaryNonresonant data M‖ ≤
        (data.count M : ℝ) * data.nonresonantEnvelope M :=
      norm_fin_sum_le_card_mul
        (data.nonresonantTerm M) (data.nonresonantEnvelope M)
        (data.nonresonantTerm_norm_le M)
    _ ≤ (data.incidenceCap M : ℝ) * data.nonresonantEnvelope M :=
      mul_le_mul_of_nonneg_right hcount (data.nonresonantEnvelope_nonneg M)

/-- All six actual forcing sources required by the two recurrence rows. -/
structure ActualForcingData where
  lowHeight : ActualLowHeightForcingData
  endpoint : ActualEndpointForcingData
  boundary : ActualBoundaryForcingData

/-- Total actual forcing in the resonant recurrence row. -/
def actualResonantForcing (data : ActualForcingData) (M : ℕ) : ℂ :=
  actualLowHeightResonant data.lowHeight M +
    actualEndpointResonant data.endpoint M +
      actualBoundaryResonant data.boundary M

/-- Total actual forcing in the nonresonant recurrence row. -/
def actualNonresonantForcing (data : ActualForcingData) (M : ℕ) : ℂ :=
  actualLowHeightNonresonant data.lowHeight M +
    actualEndpointNonresonant data.endpoint M +
      actualBoundaryNonresonant data.boundary M

/-- Explicit upper bound for the resonant forcing row. -/
def actualResonantForcingBound (data : ActualForcingData) (M : ℕ) : ℝ :=
  ((data.lowHeight.spacing.cutoff M + 1 : ℕ) : ℝ) *
      data.lowHeight.resonantEnvelope M +
    (data.endpoint.leftResonantBound M + data.endpoint.rightResonantBound M) +
      (data.boundary.incidenceCap M : ℝ) * data.boundary.resonantEnvelope M

/-- Explicit upper bound for the nonresonant forcing row. -/
def actualNonresonantForcingBound (data : ActualForcingData) (M : ℕ) : ℝ :=
  ((data.lowHeight.spacing.cutoff M + 1 : ℕ) : ℝ) *
      data.lowHeight.nonresonantEnvelope M +
    (data.endpoint.leftNonresonantBound M + data.endpoint.rightNonresonantBound M) +
      (data.boundary.incidenceCap M : ℝ) * data.boundary.nonresonantEnvelope M

/-- The three separately estimated sources bound the total resonant forcing. -/
theorem norm_actualResonantForcing_le
    (data : ActualForcingData) (M : ℕ) :
    ‖actualResonantForcing data M‖ ≤ actualResonantForcingBound data M := by
  have hlow := norm_actualLowHeightResonant_le_cutoff data.lowHeight M
  have hend := norm_actualEndpointResonant_le data.endpoint M
  have hboundary := norm_actualBoundaryResonant_le data.boundary M
  calc
    ‖actualResonantForcing data M‖ ≤
        ‖actualLowHeightResonant data.lowHeight M +
            actualEndpointResonant data.endpoint M‖ +
          ‖actualBoundaryResonant data.boundary M‖ := by
      exact norm_add_le _ _
    _ ≤ (‖actualLowHeightResonant data.lowHeight M‖ +
          ‖actualEndpointResonant data.endpoint M‖) +
          ‖actualBoundaryResonant data.boundary M‖ := by
      exact add_le_add_right (norm_add_le _ _) _
    _ ≤ actualResonantForcingBound data M := by
      exact add_le_add (add_le_add hlow hend) hboundary

/-- The three separately estimated sources bound the total nonresonant forcing. -/
theorem norm_actualNonresonantForcing_le
    (data : ActualForcingData) (M : ℕ) :
    ‖actualNonresonantForcing data M‖ ≤ actualNonresonantForcingBound data M := by
  have hlow := norm_actualLowHeightNonresonant_le_cutoff data.lowHeight M
  have hend := norm_actualEndpointNonresonant_le data.endpoint M
  have hboundary := norm_actualBoundaryNonresonant_le data.boundary M
  calc
    ‖actualNonresonantForcing data M‖ ≤
        ‖actualLowHeightNonresonant data.lowHeight M +
            actualEndpointNonresonant data.endpoint M‖ +
          ‖actualBoundaryNonresonant data.boundary M‖ := by
      exact norm_add_le _ _
    _ ≤ (‖actualLowHeightNonresonant data.lowHeight M‖ +
          ‖actualEndpointNonresonant data.endpoint M‖) +
          ‖actualBoundaryNonresonant data.boundary M‖ := by
      exact add_le_add_right (norm_add_le _ _) _
    _ ≤ actualNonresonantForcingBound data M := by
      exact add_le_add (add_le_add hlow hend) hboundary

/--
Replace only the six forcing fields of an existing complex leakage operator by
the actual forcing data, leaving all four propagation and leakage maps unchanged.
-/
def withActualForcing
    (operator : ResonantLeakageOperator ℂ ℂ ℂ)
    (data : ActualForcingData) : ResonantLeakageOperator ℂ ℂ ℂ where
  A_M := operator.A_M
  B_M := operator.B_M
  C_M := operator.C_M
  D_M := operator.D_M
  lowHeightResonant := actualLowHeightResonant data.lowHeight
  lowHeightNonresonant := actualLowHeightNonresonant data.lowHeight
  endpointResonant := actualEndpointResonant data.endpoint
  endpointNonresonant := actualEndpointNonresonant data.endpoint
  boundaryResonant := actualBoundaryResonant data.boundary
  boundaryNonresonant := actualBoundaryNonresonant data.boundary

/-- The instantiated resonant forcing is definitionally the actual resonant forcing. -/
theorem resonantForcing_withActualForcing
    (operator : ResonantLeakageOperator ℂ ℂ ℂ)
    (data : ActualForcingData) (M : ℕ) :
    resonantForcing (withActualForcing operator data) M =
      actualResonantForcing data M := by
  rfl

/-- The instantiated nonresonant forcing is definitionally the actual nonresonant forcing. -/
theorem nonresonantForcing_withActualForcing
    (operator : ResonantLeakageOperator ℂ ℂ ℂ)
    (data : ActualForcingData) (M : ℕ) :
    nonresonantForcing (withActualForcing operator data) M =
      actualNonresonantForcing data M := by
  rfl

/-- Actual estimates bound the resonant forcing field used by the recurrence. -/
theorem norm_resonantForcing_withActualForcing_le
    (operator : ResonantLeakageOperator ℂ ℂ ℂ)
    (data : ActualForcingData) (M : ℕ) :
    ‖resonantForcing (withActualForcing operator data) M‖ ≤
      actualResonantForcingBound data M := by
  rw [resonantForcing_withActualForcing]
  exact norm_actualResonantForcing_le data M

/-- Actual estimates bound the nonresonant forcing field used by the recurrence. -/
theorem norm_nonresonantForcing_withActualForcing_le
    (operator : ResonantLeakageOperator ℂ ℂ ℂ)
    (data : ActualForcingData) (M : ℕ) :
    ‖nonresonantForcing (withActualForcing operator data) M‖ ≤
      actualNonresonantForcingBound data M := by
  rw [nonresonantForcing_withActualForcing]
  exact norm_actualNonresonantForcing_le data M

/-- Weighted norm of the two actual forcing rows. -/
def actualWeightedForcingNorm
    (weights : BlockLyapunovWeights)
    (operator : ResonantLeakageOperator ℂ ℂ ℂ)
    (data : ActualForcingData) (M : ℕ) : ℝ :=
  weights.resonant * ‖resonantForcing (withActualForcing operator data) M‖ +
    weights.nonresonant *
      ‖nonresonantForcing (withActualForcing operator data) M‖

/-- Explicit weighted bound supplied to the affine Lyapunov recurrence. -/
def actualWeightedForcingBound
    (weights : BlockLyapunovWeights)
    (data : ActualForcingData) (M : ℕ) : ℝ :=
  weights.resonant * actualResonantForcingBound data M +
    weights.nonresonant * actualNonresonantForcingBound data M

/-- Both row estimates combine into the exact weighted forcing bound. -/
theorem actualWeightedForcingNorm_le
    (weights : BlockLyapunovWeights)
    (operator : ResonantLeakageOperator ℂ ℂ ℂ)
    (data : ActualForcingData) (M : ℕ) :
    actualWeightedForcingNorm weights operator data M ≤
      actualWeightedForcingBound weights data M := by
  unfold actualWeightedForcingNorm actualWeightedForcingBound
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (norm_resonantForcing_withActualForcing_le operator data M)
      weights.resonant_nonneg)
    (mul_le_mul_of_nonneg_left
      (norm_nonresonantForcing_withActualForcing_le operator data M)
      weights.nonresonant_nonneg)

end RHLean.Analysis
