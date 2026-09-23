import RHLean.Analysis.SquareRootBornSmoothReciprocalForm
import RHLean.Analysis.ThreeSlotDegreeOneCriterion
import RHLean.Proof.SquareRootCanonicalOrientedEpsilonBound
import RHLean.Proof.SquareRootLowPrimeSmoothTransportRecoupling

/-!
# Recover the Mertens-visible mode from matched transport

Put `H_R = sum_{p <= R, p prime} M(p-1)`.  The exact orientation split says

`M(R^2-1) = matched R - H_R`.

Consequently the unified reciprocal transform is exactly `1 - M(R^2-1)`.
Its presence in the born-smooth reindexing does not provide a new cancellation
estimate.  In particular, the matched-channel target alone is not the bound
consumed by the existing square-prefix or three-slot criterion: the signed
correction `-H_R` must remain inside the recovered quantity.

The terminal low-prime state is `matched - shallowBoundary`.  After the same
correction it differs from the Mertens sample by at most `R+K`, and from the
complete four-cell degree-one sample by at most `R+K+3`.  These are exact
recovery and boundary estimates, not a bound on the recovered amplitude.

The final equivalence and implication retain `-H_R` inside the norm.  They do
not assume, or attempt to prove, separate bounds on `matched` and `H_R`.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis

/-- The positive-orientation correction must be restored before passing from
matched transport to the square-prefix Mertens criterion. -/
theorem squareRootMatched_sub_positivePrimeTransform_eq_squarePrefixMertens
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootMatchedBornSmoothTransport R -
        squareRootPositiveSmoothPrimeMertensTransform R =
      squarePrefixMertens (R - 1) := by
  rw [squarePrefixMertens_eq_neg_positivePrimeTransform_add_matched R hR]
  ring

/-- The full reciprocal reindexing is the ordinary Mertens sample, with its
unit source removed and sign reversed.  Reindexing alone gives no estimate. -/
theorem squareRootUnifiedReciprocalTransform_eq_one_sub_squarePrefixMertens
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootUnifiedReciprocalTransform R =
      1 - squarePrefixMertens (R - 1) := by
  have hrec := squareRootMatchedBornSmoothTransport_eq_unifiedReciprocalForm R hR
  have hfull := squarePrefixMertens_eq_neg_positivePrimeTransform_add_matched
    R (by omega)
  linear_combination hrec + hfull

/-- Exact recovery with all Li, floor, prime-error, and orientation signs
visible.  No asymptotic expansion or separated norm is used. -/
theorem squareRootMatchedPNT_sub_floor_sub_error_sub_positive_eq_squarePrefixMertens
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootMatchedBornSmoothPNTMain R -
        squareRootTransportFloorCorrection R -
        squareRootTransportPNTError R -
        squareRootPositiveSmoothPrimeMertensTransform R =
      squarePrefixMertens (R - 1) := by
  rw [← squareRootMatchedBornSmoothTransport_eq_pntMain_sub_floor_sub_error]
  exact squareRootMatched_sub_positivePrimeTransform_eq_squarePrefixMertens R hR

/-- The corrected terminal state recovers the square-prefix Mertens value
with precisely the pre-existing shallow boundary still attached. -/
theorem squareRootLowPrimeRunningImbalance_sub_positivePrimeTransform_eq_recovered
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeRunningImbalance R K j
          (squareRootBornPostTailLowPrimeCutoff R) -
        squareRootPositiveSmoothPrimeMertensTransform R =
      squarePrefixMertens (R - 1) -
        squareRootLowPrimeTerminalShallowBoundary R K j := by
  rw [squareRootLowPrimeRunningImbalance_at_cutoff_eq_matched_sub_shallowBoundary
    R K j hR hK hKR hj]
  have h := squareRootMatched_sub_positivePrimeTransform_eq_squarePrefixMertens
    R (by omega)
  linear_combination h

/-- Only after subtracting the ancestral prime transform does the terminal
state have an `R+K` recovery error relative to Mertens. -/
theorem norm_recoveredLowPrimeTerminal_sub_mertens_le_root_add_depth
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    ‖(squareRootLowPrimeRunningImbalance R K j
            (squareRootBornPostTailLowPrimeCutoff R) -
          squareRootPositiveSmoothPrimeMertensTransform R) -
        mertensSummatory (squareRootEndpoint R)‖ ≤ (R : ℝ) + (K : ℝ) := by
  rw [squareRootLowPrimeRunningImbalance_sub_positivePrimeTransform_eq_recovered
    R K j hR hK hKR hj]
  have hsample : squarePrefixMertens (R - 1) =
      mertensSummatory (squareRootEndpoint R) := by
    unfold squarePrefixMertens squarePrefixEndpoint squareRootEndpoint
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R)]
  rw [hsample]
  have hcancel :
      mertensSummatory (squareRootEndpoint R) -
          squareRootLowPrimeTerminalShallowBoundary R K j -
          mertensSummatory (squareRootEndpoint R) =
        -squareRootLowPrimeTerminalShallowBoundary R K j := by ring
  rw [hcancel, norm_neg]
  exact norm_squareRootLowPrimeTerminalShallowBoundary_le_root_add_depth
    R K j hR hK hKR hj hV0 hVK

/-- Explicit terminal-to-three-slot bridge.  The correction is the full
ancestral prime transform, not an additional root-width boundary. -/
theorem norm_recoveredLowPrimeTerminal_sub_threeSlot_le_root_add_depth_add_three
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    ‖(squareRootLowPrimeRunningImbalance R K j
            (squareRootBornPostTailLowPrimeCutoff R) -
          squareRootPositiveSmoothPrimeMertensTransform R) -
        (((threeSlotWa (squareRootEndpoint R / 4) +
            threeSlotWb (squareRootEndpoint R / 4) +
            threeSlotWc (squareRootEndpoint R / 4) : ℤ)) : ℂ)‖ ≤
      (R : ℝ) + (K : ℝ) + 3 := by
  rw [← mertensSummatory_four_mul_eq_degreeOne]
  have hterminal := norm_recoveredLowPrimeTerminal_sub_mertens_le_root_add_depth
    R K j hR hK hKR hj hV0 hVK
  have hcell := norm_mertensSummatory_sub_fourCell_le (squareRootEndpoint R)
  let V := squareRootLowPrimeRunningImbalance R K j
      (squareRootBornPostTailLowPrimeCutoff R) -
    squareRootPositiveSmoothPrimeMertensTransform R
  calc
    ‖V - mertensSummatory (4 * (squareRootEndpoint R / 4))‖ =
        ‖(V - mertensSummatory (squareRootEndpoint R)) +
          (mertensSummatory (squareRootEndpoint R) -
            mertensSummatory (4 * (squareRootEndpoint R / 4)))‖ := by
              congr 1
              ring
    _ ≤ ‖V - mertensSummatory (squareRootEndpoint R)‖ +
        ‖mertensSummatory (squareRootEndpoint R) -
          mertensSummatory (4 * (squareRootEndpoint R / 4))‖ := norm_add_le _ _
    _ ≤ (R : ℝ) + (K : ℝ) + 3 := add_le_add hterminal hcell

/-- The existing square-prefix energy criterion is exactly the bound on the
recovered signed difference.  This is not the matched-only proposition. -/
theorem squarePrefixEnergyBounded_iff_recoveredMatchedTransportBounded :
    SquarePrefixEnergyBoundedStatement ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ R : ℕ, 2 ≤ R →
            ‖squareRootMatchedBornSmoothTransport R -
                squareRootPositiveSmoothPrimeMertensTransform R‖ ^ 2 ≤
              C * Real.rpow (R : ℝ) (2 + ε) := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro R hR
    rw [squareRootMatched_sub_positivePrimeTransform_eq_squarePrefixMertens
      R (by omega)]
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ R)] using hbound (R - 1)
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n
    by_cases hn : n = 0
    · subst n
      simpa [squarePrefixMertens, squarePrefixEndpoint, mertensSummatory] using hC
    · have hR : 2 ≤ n + 1 := by omega
      have hb := hbound (n + 1) hR
      rw [squareRootMatched_sub_positivePrimeTransform_eq_squarePrefixMertens
        (n + 1) (by omega)] at hb
      simpa only [Nat.add_sub_cancel] using hb

/-- A bound on the recovered signed difference supplies the three-slot energy
criterion.  The ancestral correction is retained inside the norm. -/
theorem threeSlotDegreeOneEnergy_of_recoveredMatchedTransportBounded
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ R : ℕ, 2 ≤ R →
          ‖squareRootMatchedBornSmoothTransport R -
              squareRootPositiveSmoothPrimeMertensTransform R‖ ^ 2 ≤
            C * Real.rpow (R : ℝ) (2 + ε)) :
    ThreeSlotDegreeOneEnergyBoundedStatement := by
  apply threeSlotDegreeOneEnergy_of_sqrtWheelRecoveredEnergy
  apply sqrtWheelRecoveredEnergyBounded_iff_squarePrefixEnergyBounded.mpr
  exact squarePrefixEnergyBounded_iff_recoveredMatchedTransportBounded.mpr h

/-- Terminal implication for the corrected signed target.  No estimate is
asserted for the hypothesis. -/
theorem riemannHypothesis_of_recoveredMatchedTransportBounded
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ R : ℕ, 2 ≤ R →
          ‖squareRootMatchedBornSmoothTransport R -
              squareRootPositiveSmoothPrimeMertensTransform R‖ ^ 2 ≤
            C * Real.rpow (R : ℝ) (2 + ε)) :
    RiemannHypothesis :=
  riemannHypothesis_of_threeSlotDegreeOneEnergy
    (threeSlotDegreeOneEnergy_of_recoveredMatchedTransportBounded h)

/-! ## Reconnect the recovered target to the existing canonical seam -/

/-- Restoring the ancestral correction turns the matched channel back into the
complete smooth-minus-high-transport endpoint. -/
theorem squareRootRecoveredMatchedTransport_eq_smooth_sub_transport
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootMatchedBornSmoothTransport R -
        squareRootPositiveSmoothPrimeMertensTransform R =
      squareRootSmoothMass (R - 1) -
        squareRootTransportCofactorFirst R := by
  rw [squareRootMatched_sub_positivePrimeTransform_eq_squarePrefixMertens
    R (by omega),
    squarePrefixMertens_eq_squareRootSmooth_sub_transport,
    squareRootTransportMass_pred_eq_cofactorFirst R (by omega)]

/-- The recovered signed target is exactly lower-root Mertens minus the
canonical mate-crosses-root defect.  This is the existing canonical seam, not a
new residual coordinate. -/
theorem squareRootRecoveredMatchedTransport_eq_lowerMertens_sub_canonicalDefect
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMatchedBornSmoothTransport R -
        squareRootPositiveSmoothPrimeMertensTransform R =
      mertensSummatory R - lowWheelCanonicalDefectLedger R := by
  rw [squareRootMatched_sub_positivePrimeTransform_eq_squarePrefixMertens
    R (by omega),
    squarePrefixMertens_eq_mertens_sub_canonicalDefect R hR]

/-- Exact sign-correct comparison with the q²-era hard residual.  After the
canonical frozen reduction, the recovered endpoint plus `FrozenTopFarResidual`
contains only the four pre-existing root-scale terms. -/
theorem squareRootRecoveredMatchedTransport_add_frozenTopFar_eq_rootTerms
    (R : ℕ) (hR : 56 ≤ R) :
    (squareRootMatchedBornSmoothTransport R -
        squareRootPositiveSmoothPrimeMertensTransform R) +
      lowWheelFrozenTopFarResidual R =
        mertensSummatory R -
          lowWheelCanonicalDowncrossUniqueParentLedger R -
          squareRootNearPrimeTransport R + squareRootERuniq R := by
  rw [squareRootRecoveredMatchedTransport_eq_lowerMertens_sub_canonicalDefect
      R (by omega),
    lowWheelCanonicalDefectLedger_eq_frozenTopFarResidual_add_rootTerms R hR]
  ring

/-- Quantitative version of the exact comparison: the corrected recovered
endpoint is the negative frozen/top/far residual up to at most `10R`.  The
constant is `1 + 1 + 7 + 1`, from lower-root Mertens, unique-parent, near-prime,
and unique-external root-scale terms respectively. -/
theorem norm_squareRootRecoveredMatchedTransport_add_frozenTopFar_le_ten_root
    (R : ℕ) (hR : 56 ≤ R) :
    ‖(squareRootMatchedBornSmoothTransport R -
        squareRootPositiveSmoothPrimeMertensTransform R) +
      lowWheelFrozenTopFarResidual R‖ ≤ 10 * (R : ℝ) := by
  rw [squareRootRecoveredMatchedTransport_add_frozenTopFar_eq_rootTerms R hR]
  have hMstep := norm_mertensSummatory_sub_le 0 R (Nat.zero_le R)
  have hM : ‖mertensSummatory R‖ ≤ (R : ℝ) := by
    simpa using hMstep
  have hU := norm_lowWheelCanonicalDowncrossUniqueParentLedger_le_root R
  have hN := norm_squareRootNearPrimeTransport_le R hR
  have hE := norm_squareRootERuniq_le_root R
  calc
    ‖mertensSummatory R - lowWheelCanonicalDowncrossUniqueParentLedger R -
        squareRootNearPrimeTransport R + squareRootERuniq R‖ ≤
      ‖mertensSummatory R - lowWheelCanonicalDowncrossUniqueParentLedger R -
          squareRootNearPrimeTransport R‖ + ‖squareRootERuniq R‖ :=
        norm_add_le _ _
    _ ≤ (‖mertensSummatory R - lowWheelCanonicalDowncrossUniqueParentLedger R‖ +
          ‖squareRootNearPrimeTransport R‖) + ‖squareRootERuniq R‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ ((‖mertensSummatory R‖ +
            ‖lowWheelCanonicalDowncrossUniqueParentLedger R‖) +
          ‖squareRootNearPrimeTransport R‖) + ‖squareRootERuniq R‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ (((R : ℝ) + (R : ℝ)) + 7 * (R : ℝ)) + (R : ℝ) := by
        gcongr
    _ = 10 * (R : ℝ) := by ring

/-- The frozen/top/far `R^(1+eps)` target already present in the repository
supplies the corrected recovered bound.  This routes through the canonical
oriented seam and never estimates the ancestral transform separately. -/
theorem recoveredMatchedTransportBounded_of_frozenTopFarResidualEpsilon
    (h : OrientedEpsilonBound.SquareRootFrozenTopFarResidualEpsilonBound) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ R : ℕ, 2 ≤ R →
          ‖squareRootMatchedBornSmoothTransport R -
              squareRootPositiveSmoothPrimeMertensTransform R‖ ^ 2 ≤
            C * Real.rpow (R : ℝ) (2 + ε) := by
  apply squarePrefixEnergyBounded_iff_recoveredMatchedTransportBounded.mp
  exact OrientedEpsilonBound.squarePrefixEnergyBounded_of_canonicalOrientedEpsilon
    (OrientedEpsilonBound.canonicalOrientedEpsilon_of_frozenTopFarResidualEpsilon h)

/-- Explicit terminal route through the corrected recovered target.  This is a
wiring theorem only; the frozen/top/far epsilon hypothesis remains the open
arithmetic estimate. -/
theorem riemannHypothesis_of_frozenTopFarResidualEpsilon_via_recovered
    (h : OrientedEpsilonBound.SquareRootFrozenTopFarResidualEpsilonBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_recoveredMatchedTransportBounded
    (recoveredMatchedTransportBounded_of_frozenTopFarResidualEpsilon h)

end RHLean.Proof