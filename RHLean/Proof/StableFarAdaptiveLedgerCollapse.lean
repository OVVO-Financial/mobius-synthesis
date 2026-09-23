import RHLean.Proof.StableFarCoordinateOverlap
import RHLean.Proof.PostRootPartnerEulerMemory
import RHLean.Proof.FarSurvivorRenewal_is_LowerMertens

/-!
# Stable-far adaptive ledger collapse

The smooth-shell identification proves that the canonical unique-parent
ledger and the external unique grid carry the same signed mass.  Consequently
the old four-term root correction in the frozen/top/far-to-rough bridge reduces
to the single root Mobius atom minus the seven-coordinate near transport.

On any complete descending schedule the final raw mass is already zero.  Thus
the complete signed adaptive raw ledger is not merely another representation of
the hard packet: after removing the now-collapsed root correction it is exactly
the canonical rough correlation itself.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- **Root correction collapse.**  The two separately carried unique-parent
coordinates cancel exactly after the coordinate overlap. -/
theorem frozenTopFarRoughRootCorrection_eq_rootAtom_sub_nearTransport
    (R : ℕ) (hR : 56 ≤ R) :
    frozenTopFarRoughRootCorrection R =
      canonicalMoebiusWeight R - squareRootNearPrimeTransport R := by
  unfold frozenTopFarRoughRootCorrection
  rw [lowWheelCanonicalDowncrossUniqueParentLedger_eq_squareRootERuniq R hR]
  ring

/-- The sharpened root correction costs only the root atom and the seven-prime
near strip. -/
theorem norm_frozenTopFarRoughRootCorrection_le_eight_root
    (R : ℕ) (hR : 56 ≤ R) :
    ‖frozenTopFarRoughRootCorrection R‖ ≤ 8 * (R : ℝ) := by
  rw [frozenTopFarRoughRootCorrection_eq_rootAtom_sub_nearTransport R hR]
  have hmu := norm_canonicalMoebiusWeight_le_one R
  have hnear := norm_squareRootNearPrimeTransport_le R hR
  have hRone : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show 1 ≤ R by omega)
  calc
    ‖canonicalMoebiusWeight R - squareRootNearPrimeTransport R‖ ≤
        ‖canonicalMoebiusWeight R‖ + ‖squareRootNearPrimeTransport R‖ :=
      norm_sub_le _ _
    _ ≤ 1 + 7 * (R : ℝ) := add_le_add hmu hnear
    _ ≤ 8 * (R : ℝ) := by nlinarith

/-- **Complete chronological collapse.**  On every complete descending prime
schedule, the whole adaptive raw Euler boundary ledger is exactly the canonical
rough critical correlation.  No final adaptive state, unique-parent correction,
or stable-far terminal term remains. -/
theorem adaptiveRawLedger_eq_roughCorrelation_of_completeSchedule
    (R : ℕ) (hR : 56 ≤ R)
    (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    squareRootCanonicalRoughAdaptiveRawLedger R ps
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) =
      squareRootCanonicalRoughCorrelation R := by
  have hfar :=
    lowWheelFrozenTopFarResidual_eq_rawLedger_add_rootCorrection_of_completeSchedule
      R hR ps hsched
  have hcorr :=
    lowWheelFrozenTopFarResidual_eq_roughCorrelation_add_rootCorrection R hR
  rw [hfar] at hcorr
  exact add_right_cancel hcorr

/-- Equivalent global q2/Euler normal form with the root bookkeeping removed.
The rough critical correlation is exactly the odd q2 Mertens owner column plus
the signed ownerwise synthesis error, minus the explicit root correction. -/
theorem roughCorrelation_add_rootCorrection_eq_oddMertensColumn_add_ownerwiseError
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootCanonicalRoughCorrelation R +
        frozenTopFarRoughRootCorrection R =
      farFourOddMertensColumn R + farFourOwnerwiseSynthesisError R := by
  rw [← lowWheelFrozenTopFarResidual_eq_roughCorrelation_add_rootCorrection R hR,
    lowWheelFrozenTopFarResidual_eq_oddMertensColumn_add_ownerwiseError R hR]

end RHLean.Proof
