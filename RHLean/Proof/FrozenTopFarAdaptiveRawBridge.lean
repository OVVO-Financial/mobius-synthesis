import Mathlib
import RHLean.Proof.GlobalFirstJumpCriticalCorrelationBridge
import RHLean.Proof.CanonicalRoughAdaptiveRawAnnihilation
import RHLean.Proof.PhysicalQ2ExceptionalTerminalSynthesis

/-!
# Frozen/top/far residual on the adaptive zero-factor carrier

The hard far packet is already the negative frozen/top/far residual.
This file puts that residual directly onto the canonical rough-correlation
carrier and then onto the exact adaptive zero-factor fresh-prime descent.

No norm is taken in the two bridge identities.  The only terms omitted from the
rough correlation are the already root-scale unique/near/external corrections.
Thus the adaptive raw boundary/mismatch ledger is now attached to the literal
physical residual rather than living in a parallel coordinate system.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

/-- Root-scale correction separating the frozen/top/far residual from the
canonical rough correlation. -/
def frozenTopFarRoughRootCorrection (R : ℕ) : ℂ :=
  canonicalMoebiusWeight R -
    lowWheelCanonicalDowncrossUniqueParentLedger R -
    squareRootNearPrimeTransport R + squareRootERuniq R

/-- **Exact frozen/top/far to rough-correlation splice.**  The entire non-root
far residual is the uncentered canonical rough correlation plus the explicit
root-scale correction. -/
theorem lowWheelFrozenTopFarResidual_eq_roughCorrelation_add_rootCorrection
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      squareRootCanonicalRoughCorrelation R +
        frozenTopFarRoughRootCorrection R := by
  have hdef :=
    lowWheelCanonicalDefectLedger_eq_frozenTopFarResidual_add_rootTerms R hR
  have hcorr :=
    canonicalDefectLedger_eq_roughCorrelation_add_rootAtom R (by omega)
  unfold frozenTopFarRoughRootCorrection
  linear_combination hcorr - hdef

/-- The splice correction is uniformly root scale. -/
theorem norm_frozenTopFarRoughRootCorrection_le_ten_root
    (R : ℕ) (hR : 56 ≤ R) :
    ‖frozenTopFarRoughRootCorrection R‖ ≤ 10 * (R : ℝ) := by
  unfold frozenTopFarRoughRootCorrection
  have hmu := norm_canonicalMoebiusWeight_le_one R
  have hU := norm_lowWheelCanonicalDowncrossUniqueParentLedger_le_root R
  have hN := norm_squareRootNearPrimeTransport_le R hR
  have hE := norm_squareRootERuniq_le_root R
  have hRone : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show 1 ≤ R by omega)
  calc
    ‖canonicalMoebiusWeight R -
        lowWheelCanonicalDowncrossUniqueParentLedger R -
        squareRootNearPrimeTransport R + squareRootERuniq R‖ ≤
      ‖canonicalMoebiusWeight R -
          lowWheelCanonicalDowncrossUniqueParentLedger R -
          squareRootNearPrimeTransport R‖ + ‖squareRootERuniq R‖ :=
        norm_add_le _ _
    _ ≤ (‖canonicalMoebiusWeight R -
            lowWheelCanonicalDowncrossUniqueParentLedger R‖ +
          ‖squareRootNearPrimeTransport R‖) + ‖squareRootERuniq R‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ ((‖canonicalMoebiusWeight R‖ +
            ‖lowWheelCanonicalDowncrossUniqueParentLedger R‖) +
          ‖squareRootNearPrimeTransport R‖) + ‖squareRootERuniq R‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ ((1 + (R : ℝ)) + 7 * (R : ℝ)) + (R : ℝ) := by
        gcongr
    _ ≤ 10 * (R : ℝ) := by nlinarith

/-- **Exact adaptive zero-factor representation of the hard packet.**
For any finite prime schedule, the frozen/top/far residual is the final adaptive
raw mass plus the signed wall/mismatch ledger plus only the explicit root-scale
correction.  This is the direct attachment needed to use the fresh-prime
zero-factor machinery on the actual far residual. -/
theorem lowWheelFrozenTopFarResidual_eq_adaptiveRawFinal_add_ledger_add_rootCorrection
    (R : ℕ) (hR : 56 ≤ R)
    (ps : List ℕ) (hprime : ∀ p ∈ ps, p.Prime) :
    lowWheelFrozenTopFarResidual R =
      squareRootCanonicalRoughAdaptiveRawWeightedMass R
        (squareRootCanonicalRoughAdaptiveCarrier ps
          (Finset.Icc 1 (squareRootEndpoint R)))
        (squareRootCanonicalRoughAdaptiveRawCoefficient ps
          (Finset.Icc 1 (squareRootEndpoint R))
          (fun _ => (1 : ℂ))) +
      squareRootCanonicalRoughAdaptiveRawLedger R ps
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) +
      frozenTopFarRoughRootCorrection R := by
  have hadapt :=
    sum_rawCorrelation_eq_adaptiveRawFinal_add_ledger
      R (by omega) ps (Finset.Icc 1 (squareRootEndpoint R)) hprime
  have hcorr :
      squareRootCanonicalRoughCorrelation R =
        ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
          squareRootCanonicalRoughRawCorrelationSummand R n := by
    rfl
  rw [← hcorr] at hadapt
  rw [lowWheelFrozenTopFarResidual_eq_roughCorrelation_add_rootCorrection R hR,
    hadapt]

/-- Quantitative consequence of the exact splice: after all fresh-prime
reassembly, the only extra cost outside the coupled adaptive raw packet is ten
root units. -/
theorem norm_lowWheelFrozenTopFarResidual_le_adaptiveRawPacket_add_ten_root
    (R : ℕ) (hR : 56 ≤ R)
    (ps : List ℕ) (hprime : ∀ p ∈ ps, p.Prime) :
    ‖lowWheelFrozenTopFarResidual R‖ ≤
      ‖squareRootCanonicalRoughAdaptiveRawWeightedMass R
          (squareRootCanonicalRoughAdaptiveCarrier ps
            (Finset.Icc 1 (squareRootEndpoint R)))
          (squareRootCanonicalRoughAdaptiveRawCoefficient ps
            (Finset.Icc 1 (squareRootEndpoint R))
            (fun _ => (1 : ℂ))) +
        squareRootCanonicalRoughAdaptiveRawLedger R ps
          (Finset.Icc 1 (squareRootEndpoint R))
          (fun _ => (1 : ℂ))‖ +
      10 * (R : ℝ) := by
  rw [lowWheelFrozenTopFarResidual_eq_adaptiveRawFinal_add_ledger_add_rootCorrection
    R hR ps hprime]
  calc
    ‖squareRootCanonicalRoughAdaptiveRawWeightedMass R
          (squareRootCanonicalRoughAdaptiveCarrier ps
            (Finset.Icc 1 (squareRootEndpoint R)))
          (squareRootCanonicalRoughAdaptiveRawCoefficient ps
            (Finset.Icc 1 (squareRootEndpoint R))
            (fun _ => (1 : ℂ))) +
        squareRootCanonicalRoughAdaptiveRawLedger R ps
          (Finset.Icc 1 (squareRootEndpoint R))
          (fun _ => (1 : ℂ)) +
        frozenTopFarRoughRootCorrection R‖ ≤
      ‖squareRootCanonicalRoughAdaptiveRawWeightedMass R
          (squareRootCanonicalRoughAdaptiveCarrier ps
            (Finset.Icc 1 (squareRootEndpoint R)))
          (squareRootCanonicalRoughAdaptiveRawCoefficient ps
            (Finset.Icc 1 (squareRootEndpoint R))
            (fun _ => (1 : ℂ))) +
        squareRootCanonicalRoughAdaptiveRawLedger R ps
          (Finset.Icc 1 (squareRootEndpoint R))
          (fun _ => (1 : ℂ))‖ +
        ‖frozenTopFarRoughRootCorrection R‖ := norm_add_le _ _
    _ ≤ _ := add_le_add_left
      (norm_frozenTopFarRoughRootCorrection_le_ten_root R hR) _

end RHLean.Proof
