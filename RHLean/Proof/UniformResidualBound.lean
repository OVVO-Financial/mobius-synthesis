import Mathlib
import RHLean.Proof.ActualForcingEstimates
import RHLean.Proof.BlockLyapunovClosure
import RHLean.Proof.JointGramControl
import RHLean.Verification.FiniteRangeCertificates

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Verification

/--
A checked finite-range certificate together with the mathematical realization
that identifies each checked joint-energy numerator with the actual signed
joint-Gram energy at the corresponding scale.
-/
structure ActualFiniteRangeJointGramRealization
    (skeleton : ResonantProjectionSkeleton ℂ ℂ)
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (expectation : FiniteRangeCertificateExpectation) where
  accepted : AcceptedFiniteRangeCertificate expectation
  rangeStart_eq_zero : accepted.certificate.rangeStart = 0
  energy_eq :
    ∀ index : Fin accepted.certificate.rows.length,
      (accepted.certificate.valueDenominator : ℝ) *
          actualJointGramEnergy skeleton
            (accepted.certificate.rangeStart + (index : ℕ))
            (data (accepted.certificate.rangeStart + (index : ℕ))) =
        ((accepted.certificate.rows.get index).jointGram.claimedJointEnergy : ℝ)

/--
A canonical finite-range base bound computed from the checked energy numerators.
The sum of absolute values is deliberately used instead of an unchecked external
maximum, so every checked row is bounded by construction.
-/
noncomputable def finiteRangeCertificateBaseBound
    (certificate : FiniteRangeCertificate) : ℝ :=
  (certificate.rows.map
      (fun row =>
        |((row.jointGram.claimedJointEnergy : ℤ) : ℝ)|)).sum /
    (certificate.valueDenominator : ℝ)

/-- Every realized checked scale is bounded by the canonical certificate base bound. -/
theorem actualFiniteRangeJointGram_energy_le_baseBound
    (skeleton : ResonantProjectionSkeleton ℂ ℂ)
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (expectation : FiniteRangeCertificateExpectation)
    (realization : ActualFiniteRangeJointGramRealization
      skeleton data expectation) :
    ∀ M, M ≤ realization.accepted.certificate.rangeEnd →
      actualJointGramEnergy skeleton M (data M) ≤
        finiteRangeCertificateBaseBound realization.accepted.certificate := by
  intro M hM
  let certificate := realization.accepted.certificate
  rcases realization.accepted.valid with
    ⟨_hcode, _hsource, _hdata, _hpayload, _hrange,
      hvalueDenominator, _hrhoDenominator, _hrho, hlength, _hrows⟩
  have hstart : certificate.rangeStart = 0 := by
    simpa [certificate] using realization.rangeStart_eq_zero
  have hMcertificate : M ≤ certificate.rangeEnd := by
    simpa [certificate] using hM
  have hlengthCertificate :
      certificate.rows.length =
        certificate.rangeEnd - certificate.rangeStart + 1 := by
    simpa [certificate] using hlength
  have hlength' : certificate.rows.length = certificate.rangeEnd + 1 := by
    simpa [hstart] using hlengthCertificate
  have hindex : M < certificate.rows.length := by
    omega
  let index : Fin certificate.rows.length := ⟨M, hindex⟩
  have henergyRaw := realization.energy_eq index
  rw [realization.rangeStart_eq_zero, zero_add] at henergyRaw
  have henergy_eq :
      (certificate.valueDenominator : ℝ) *
          actualJointGramEnergy skeleton M (data M) =
        ((certificate.rows.get index).jointGram.claimedJointEnergy : ℝ) := by
    simpa [certificate, index] using henergyRaw
  let energyNumerators : List ℝ :=
    certificate.rows.map
      (fun row => |((row.jointGram.claimedJointEnergy : ℤ) : ℝ)|)
  have hrow_mem : certificate.rows.get index ∈ certificate.rows :=
    List.get_mem certificate.rows index
  have habs_mem :
      |(((certificate.rows.get index).jointGram.claimedJointEnergy : ℤ) : ℝ)| ∈
        energyNumerators := by
    exact List.mem_map.mpr ⟨certificate.rows.get index, hrow_mem, rfl⟩
  have hnonneg : ∀ value ∈ energyNumerators, (0 : ℝ) ≤ value := by
    intro value hvalue
    rcases List.mem_map.mp hvalue with ⟨row, _hrow, rfl⟩
    exact abs_nonneg _
  have habs_le_sum :
      |(((certificate.rows.get index).jointGram.claimedJointEnergy : ℤ) : ℝ)| ≤
        energyNumerators.sum :=
    List.single_le_sum hnonneg _ habs_mem
  have hclaimed_le_sum :
      ((certificate.rows.get index).jointGram.claimedJointEnergy : ℝ) ≤
        energyNumerators.sum :=
    (le_abs_self _).trans habs_le_sum
  have hmul :
      (certificate.valueDenominator : ℝ) *
          actualJointGramEnergy skeleton M (data M) ≤ energyNumerators.sum := by
    rw [henergy_eq]
    exact hclaimed_le_sum
  have hdenominator_real : 0 < (certificate.valueDenominator : ℝ) := by
    exact_mod_cast hvalueDenominator
  unfold finiteRangeCertificateBaseBound
  change actualJointGramEnergy skeleton M (data M) ≤
    energyNumerators.sum / (certificate.valueDenominator : ℝ)
  apply (le_div_iff₀ hdenominator_real).2
  simpa [mul_comm] using hmul

/--
The full signed joint-Gram recurrence and actual forcing control above a finite
base range. The hard analytic inputs are explicit fields: strict descent, the
single complete joint-Gram recurrence, and a uniform bound on the compiled
actual weighted forcing expression.
-/
structure ActualJointGramAsymptoticControl
    (skeleton : ResonantProjectionSkeleton ℂ ℂ)
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (weights : BlockLyapunovWeights)
    (forcingData : ActualForcingData)
    (N0 : ℕ) where
  ancestor : ℕ → ℕ
  rho : ℝ
  forcingBound : ℝ
  rho_nonneg : 0 ≤ rho
  rho_lt_one : rho < 1
  ancestor_lt : ∀ M, N0 < M → ancestor M < M
  recurrence :
    ∀ M, N0 < M →
      ActualJointGramRecurrenceControl skeleton M (data M) rho
        (actualJointGramEnergy skeleton (ancestor M) (data (ancestor M)))
        (actualWeightedForcingBound weights forcingData M)
  forcing_le :
    ∀ M, N0 < M →
      actualWeightedForcingBound weights forcingData M ≤ forcingBound

/--
A realized accepted finite certificate and an asymptotic full-joint recurrence
imply a uniform bound for the actual residual energy at every scale.
-/
theorem uniform_actualResidual_energy_bound
    (skeleton : ResonantProjectionSkeleton ℂ ℂ)
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (expectation : FiniteRangeCertificateExpectation)
    (realization : ActualFiniteRangeJointGramRealization
      skeleton data expectation)
    (weights : BlockLyapunovWeights)
    (forcingData : ActualForcingData)
    (control : ActualJointGramAsymptoticControl
      skeleton data weights forcingData
        realization.accepted.certificate.rangeEnd) :
    ∀ M,
      ‖actualResidual (data M)‖ ^ 2 ≤
        affineInvariantBound control.rho control.forcingBound
          (finiteRangeCertificateBaseBound realization.accepted.certificate) := by
  have hbase :
      ∀ M, M ≤ realization.accepted.certificate.rangeEnd →
        actualJointGramEnergy skeleton M (data M) ≤
          finiteRangeCertificateBaseBound realization.accepted.certificate :=
    actualFiniteRangeJointGram_energy_le_baseBound
      skeleton data expectation realization
  have hcontract :
      ∀ M, realization.accepted.certificate.rangeEnd < M →
        actualJointGramEnergy skeleton M (data M) ≤
          control.rho *
              actualJointGramEnergy skeleton (control.ancestor M)
                (data (control.ancestor M)) +
            actualWeightedForcingBound weights forcingData M := by
    intro M hM
    simpa [ActualJointGramRecurrenceControl] using control.recurrence M hM
  have huniform :
      ∀ M,
        actualJointGramEnergy skeleton M (data M) ≤
          affineInvariantBound control.rho control.forcingBound
            (finiteRangeCertificateBaseBound realization.accepted.certificate) :=
    uniform_bound_of_affine_descent
      control.ancestor
      (fun M => actualJointGramEnergy skeleton M (data M))
      (fun M => actualWeightedForcingBound weights forcingData M)
      realization.accepted.certificate.rangeEnd
      control.rho
      control.forcingBound
      (finiteRangeCertificateBaseBound realization.accepted.certificate)
      control.rho_nonneg
      control.rho_lt_one
      hbase
      control.ancestor_lt
      hcontract
      control.forcing_le
  intro M
  rw [actualResidual_energy_eq_jointGram skeleton M (data M)]
  exact huniform M

end RHLean.Analysis
