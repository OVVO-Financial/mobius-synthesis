import Mathlib
import RHLean.Proof.FirstJumpPrimeSliceObstruction
import RHLean.Proof.ComplexVerticalLineSquarefreeDiagonal

/-!
# Global first-jump cofactor compression and recombination

The fixed-first-jump-prime norm estimate is too strong: the upper-half slice can
have prime-count size even when `R / p = 1`.  This file keeps the first-jump
prime cancellation intact and instead expands every completed predecessor
residual on one common low-cofactor carrier.

The arbitrary-prime cofactor-window transform from `TerminalAxiomAudit` permits
choosing the fresh coordinate `2`.  Thus every statewise first-jump residual is
written as a signed sum over `1 <= d <= sqrt R` before any norm is taken.  A
finite Fubini swap then produces global cofactor columns.

The first proposed column estimate `||G_R(d)|| <= R/d` is retained below only as
a diagnostic conditional implication.  Direct finite tests show that estimate
is too strong, just as the earlier fixed-first-jump-prime estimate was too
strong.  The important exact correction is therefore recorded in this same
module: the first-jump aggregate must be recombined with the square-root-dense
piece before a critical norm is taken.  That recombined scalar is exactly the
canonical defect ledger and, through the vertical-line normalization, exactly
the signed squarefree shell between `R` and `R^2`.

No analytic estimate is introduced by the recombination theorems.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open SignedOwnershipInterval

attribute [local instance] Classical.propDecidable

/-- Contribution of one low cofactor `d` to one oriented state's complete
first-jump residual.  The prime-dilate coordinate is fixed at `2`; no norm is
present in this definition. -/
noncomputable def firstJumpStateCofactorResponse
    (R d : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  if (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty ∧
      Nat.sqrt R < lowWheelCanonicalDowncrossPivot x then
    canonicalMoebiusWeight x.1 *
      (firstJumpHighPrimeCofactorResponse
          2 R (lowWheelCanonicalDowncrossPivot x - 1) (R / x.2) d -
        firstJumpHighPrimeCofactorResponse
          2 R (lowWheelCanonicalDowncrossPivot x - 1)
            (lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2) d)
  else
    0

/-- Global signed column at low cofactor `d`, after every oriented state and
first-jump-prime coordinate has been summed. -/
noncomputable def signedFirstJumpCofactorColumnAggregate
    (R d : ℕ) : ℂ :=
  ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
    firstJumpStateCofactorResponse R d x

/-- **Statewise cofactor expansion.**  One complete first-jump state fibre is
exactly the signed sum of its low-cofactor responses on `d <= sqrt R`.
The proof uses the existing arbitrary-prime window transform at the fresh
coordinate `2`. -/
theorem lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre_eq_sum_cofactorResponses
    (R : ℕ) (x : LowWheelCofactorQuotientState) :
    lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x =
      ∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
        canonicalMoebiusWeight d * firstJumpStateCofactorResponse R d x := by
  classical
  by_cases hstate :
      (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty ∧
        Nat.sqrt R < lowWheelCanonicalDowncrossPivot x
  · have hBR :
        lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2 ≤ R := by
      unfold lowWheelCanonicalDowncrossOwnershipUpper
      exact (min_le_left _ _).trans (Nat.div_le_self _ _)
    have hAB :
        R / x.2 ≤ lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2 := by
      rcases lowWheelCanonicalDowncrossChargingFaces_nonempty_of_oriented hstate.1 with
        ⟨t, ht⟩
      have hI := primeFaceProduct_mem_exactOwnershipInterval ht
      rcases Finset.mem_Ioc.mp hI with ⟨hlow, hup⟩
      exact hlow.le.trans hup
    have hJ :=
      sqrtFirstJumpResidual_cast_eq_cofactorWindowDifference
        (p := 2) (R := R) (q := lowWheelCanonicalDowncrossPivot x)
        (A := R / x.2)
        (B := lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2)
        Nat.prime_two hstate.2 hBR hAB
    unfold lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre
      firstJumpStateCofactorResponse
    simp only [if_pos hstate]
    rw [hJ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  · simp [lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre,
      firstJumpStateCofactorResponse, hstate]

/-- **Global cofactor Fubini.**  The live first-jump aggregate is a single
Möbius-weighted sum of global low-cofactor columns.  In particular, no norm is
taken after fixing the first-jump prime. -/
theorem signedLiveFirstJumpAggregate_eq_sum_cofactorColumns
    (R : ℕ) :
    signedLiveFirstJumpAggregate R =
      ∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
        canonicalMoebiusWeight d *
          signedFirstJumpCofactorColumnAggregate R d := by
  classical
  unfold signedLiveFirstJumpAggregate
  calc
    (∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x) =
      ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        ∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
          canonicalMoebiusWeight d * firstJumpStateCofactorResponse R d x := by
            apply Finset.sum_congr rfl
            intro x _hx
            exact
              lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre_eq_sum_cofactorResponses
                R x
    _ = ∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
        ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
          canonicalMoebiusWeight d * firstJumpStateCofactorResponse R d x := by
            rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
        canonicalMoebiusWeight d *
          signedFirstJumpCofactorColumnAggregate R d := by
            apply Finset.sum_congr rfl
            intro d _hd
            unfold signedFirstJumpCofactorColumnAggregate
            rw [Finset.mul_sum]

/-! ## Correct critical recombination

The first-jump term is only one half of the exact square-root contraction.
The dense half has to remain coupled to it.  The sum is the historical oriented
Euler ledger, hence the canonical defect, and the vertical-line normalization
puts that defect on one physical squarefree shell.
-/

/-- Global square-root-dense contribution on the same oriented state carrier as
`signedLiveFirstJumpAggregate`. -/
noncomputable def signedLiveSqrtDenseAggregate (R : ℕ) : ℂ :=
  ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
    lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre R x

/-- **Dense + first jump = oriented ledger.**  This is the aggregate form of the
statewise square-root contraction, with no norm inserted between the two
pieces. -/
theorem signedLiveSqrtDenseAggregate_add_firstJump_eq_orientedLedger
    (R : ℕ) :
    signedLiveSqrtDenseAggregate R + signedLiveFirstJumpAggregate R =
      lowWheelCanonicalDowncrossOrientedLedger R := by
  unfold signedLiveSqrtDenseAggregate
  exact (lowWheelCanonicalDowncrossOrientedLedger_eq_sqrtDense_add_signedLive R).symm

/-- **Correct endpoint object.**  After late-parent cancellation, the recombined
square-root contraction is exactly the canonical defect ledger. -/
theorem signedLiveSqrtDenseAggregate_add_firstJump_eq_canonicalDefect
    (R : ℕ) :
    signedLiveSqrtDenseAggregate R + signedLiveFirstJumpAggregate R =
      lowWheelCanonicalDefectLedger R := by
  calc
    signedLiveSqrtDenseAggregate R + signedLiveFirstJumpAggregate R =
        lowWheelCanonicalDowncrossOrientedLedger R :=
      signedLiveSqrtDenseAggregate_add_firstJump_eq_orientedLedger R
    _ = lowWheelCanonicalDowncrossLedger R :=
      (LateParentCancellation.downcrossLedger_eq_orientedLedger R).symm
    _ = lowWheelCanonicalDefectLedger R :=
      (lowWheelCanonicalDefectLedger_eq_downcrossLedger R).symm

/-- Signed charge of the literal squarefree physical shell between the root and
its square wall. -/
noncomputable def canonicalDefectSquarefreeShellCharge (R : ℕ) : ℂ :=
  ∑ n ∈ orderedEulerCutSquarefreeShell R,
    -canonicalMoebiusWeight n

/-- **Canonical defect = signed squarefree shell.**  The ordered Euler cut has
one active atom per physical child and the active children are exactly the
squarefree integers `R < n < R^2`. -/
theorem canonicalDefectLedger_eq_squarefreeShellCharge
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelCanonicalDefectLedger R =
      canonicalDefectSquarefreeShellCharge R := by
  calc
    lowWheelCanonicalDefectLedger R = signedVerticalIntervalEndpointMass R :=
      (signedVerticalIntervalEndpointMass_eq_canonicalDefectLedger R).symm
    _ = ∑ n ∈ orderedEulerCutActiveChildren R,
          orderedEulerCutChildCharge n :=
      signedVerticalIntervalEndpointMass_eq_sum_activeChildCharges R
    _ = ∑ n ∈ orderedEulerCutSquarefreeShell R,
          orderedEulerCutChildCharge n := by
      rw [orderedEulerCutActiveChildren_eq_squarefreeShell R hR]
    _ = canonicalDefectSquarefreeShellCharge R := by
      unfold canonicalDefectSquarefreeShellCharge orderedEulerCutChildCharge
      rfl

/-- **Full recombination on the physical shell.**  This is the endpoint on which
any subsequent quantitative contraction must act. -/
theorem signedLiveSqrtDenseAggregate_add_firstJump_eq_squarefreeShellCharge
    (R : ℕ) (hR : 2 ≤ R) :
    signedLiveSqrtDenseAggregate R + signedLiveFirstJumpAggregate R =
      canonicalDefectSquarefreeShellCharge R := by
  rw [signedLiveSqrtDenseAggregate_add_firstJump_eq_canonicalDefect R,
    canonicalDefectLedger_eq_squarefreeShellCharge R hR]

/-- The corrected direct root-scale target.  Unlike the first-jump-only target,
this keeps the exact dense/first-jump cancellation intact before taking the
norm. -/
def RecombinedCanonicalDefectLogBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      ‖lowWheelCanonicalDefectLedger R‖ ≤
        C * (R : ℝ) * (Real.log (R : ℝ) + 1)

/-- The corrected target can equivalently be stated directly on the two pieces
of the square-root contraction, provided they are summed before the norm. -/
theorem recombinedCanonicalDefectLogBound_iff_dense_add_firstJump :
    RecombinedCanonicalDefectLogBound ↔
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ R : ℕ, 3 ≤ R →
          ‖signedLiveSqrtDenseAggregate R + signedLiveFirstJumpAggregate R‖ ≤
            C * (R : ℝ) * (Real.log (R : ℝ) + 1) := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R hR
    rw [signedLiveSqrtDenseAggregate_add_firstJump_eq_canonicalDefect R]
    exact hbound R hR
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R hR
    rw [← signedLiveSqrtDenseAggregate_add_firstJump_eq_canonicalDefect R]
    exact hbound R hR

/-! ## Rejected diagnostic harmonic packing seam

The implication below is mathematically valid and useful as a record of the
scale one would obtain from `R/d` column packing.  Finite diagnostics reject the
premise itself, so this proposition is not treated as the active proof seam.
-/

/-- Diagnostic only: a fully signed cofactor-column bound that would have been
sufficient for the first-jump-only target. -/
def FirstJumpCofactorColumnPackingBound : Prop :=
  ∀ R d : ℕ, 3 ≤ R → d ∈ Finset.Icc 1 (Nat.sqrt R) →
    ‖signedFirstJumpCofactorColumnAggregate R d‖ ≤
      (R : ℝ) / (d : ℝ)

/-- If the rejected diagnostic premise held, the first-jump-only target would
follow with constant `1`.  The theorem is retained only to document the exact
strength of that failed route. -/
theorem pntFiniteDifferenceLiveExposureBound_of_cofactorColumnPacking
    (hcol : FirstJumpCofactorColumnPackingBound) :
    PNTFiniteDifferenceLiveExposureBound := by
  refine ⟨1, by norm_num, ?_⟩
  intro R hR
  rw [signedLiveFirstJumpAggregate_eq_sum_cofactorColumns]
  have hsqrtR : Nat.sqrt R ≤ R := Nat.sqrt_le_self R
  have hsubset :
      Finset.Icc 1 (Nat.sqrt R) ⊆ Finset.Icc 1 R := by
    intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hd1, hds⟩
    exact Finset.mem_Icc.mpr ⟨hd1, hds.trans hsqrtR⟩
  have hsumSubset :
      (∑ d ∈ Finset.Icc 1 (Nat.sqrt R), (R : ℝ) / (d : ℝ)) ≤
        ∑ d ∈ Finset.Icc 1 R, (R : ℝ) / (d : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro d _hdR _hdOld
    positivity
  have hharm :
      (harmonic R : ℝ) =
        ∑ d ∈ Finset.Icc 1 R, (1 : ℝ) / (d : ℝ) := by
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, one_div]
  have hsumHarm :
      (∑ d ∈ Finset.Icc 1 R, (R : ℝ) / (d : ℝ)) =
        (R : ℝ) * (harmonic R : ℝ) := by
    rw [hharm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  have hharmBound :
      (harmonic R : ℝ) ≤ 1 + Real.log (R : ℝ) := by
    simpa using harmonic_le_one_add_log R
  have hRnonneg : (0 : ℝ) ≤ (R : ℝ) := by positivity
  calc
    ‖∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
        canonicalMoebiusWeight d *
          signedFirstJumpCofactorColumnAggregate R d‖ ≤
      ∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
        ‖canonicalMoebiusWeight d *
          signedFirstJumpCofactorColumnAggregate R d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
        (R : ℝ) / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hmu : ‖canonicalMoebiusWeight d‖ ≤ (1 : ℝ) := by
        rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;>
          simp [canonicalMoebiusWeight, h]
      have hc := hcol R d hR hd
      rw [norm_mul]
      have hmul := mul_le_mul hmu hc (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa using hmul
    _ ≤ ∑ d ∈ Finset.Icc 1 R, (R : ℝ) / (d : ℝ) := hsumSubset
    _ = (R : ℝ) * (harmonic R : ℝ) := hsumHarm
    _ ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) :=
      mul_le_mul_of_nonneg_left hharmBound hRnonneg
    _ = (1 : ℝ) * (R : ℝ) * (Real.log (R : ℝ) + 1) := by ring

end RHLean.Proof