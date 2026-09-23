import Mathlib
import RHLean.Proof.SurvivorFarUpperRigidity
import RHLean.Proof.SurvivorPrimeFaceFiniteDifference
import RHLean.Proof.StableFarWallUnitRenewalCentering
import RHLean.Proof.StableFarWallCrossingOwnerWindow
import RHLean.Proof.StableFarWallRenewalTerminalPrimeCount
import RHLean.Proof.PostRootPartnerLogAlignment

/-!
# Far survivor renewal is lower-scale Mertens

In the rigid far-upper sector, the exact `2,3,5` Boolean third-difference
stencil is not an autonomous cancellation term.  The prime-face realization
identifies it with the full fixed-prime survivor fibre, while far-upper
rigidity identifies that same fibre with the negative lower-scale Mertens
prefix.  Cancelling the common minus sign gives an exact renewal identity.

No estimate, asymptotic input, Markov approximation, or independence
hypothesis is used.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- **Far survivor renewal is exactly lower-scale Mertens.**  For `t >= 55`
and a prime coordinate `q >= t + 9`, the exact signed eight-state Boolean
third difference in the prime coordinates `2,3,5` is the lower-scale Mertens
value at `floor(X_t / q)`, where `X_t = (t+1)^2 - 1`.

This is the kernel-checked composition of
`survivorFixedPrimeCofactorMass_eq_neg_two_three_five_difference` and
`survivorFixedPrimeCofactorMass_sixteen_eq_neg_mertensSummatory`. -/
theorem farSurvivorRenewal_is_LowerMertens
    (t q : ℕ) (ht : 55 ≤ t) (hqPrime : q.Prime)
    (hqFar : t + 9 ≤ q) :
    (((∑ u ∈
        ((((survivorPrimeFaceAmbient q).erase 2).erase 3).erase 5).powerset,
        booleanCubeSign u *
          booleanThreePivotDifference 2 3 5
            (survivorPrimeFaceHigh 16 t q) u : ℤ)) : ℂ) =
      RHLean.Analysis.mertensSummatory
        (RHLean.Analysis.squarePrefixEndpoint t / q) := by
  have hq : 7 ≤ q := by omega
  have hstencil :=
    survivorFixedPrimeCofactorMass_eq_neg_two_three_five_difference
      16 t hqPrime hq
  have hfar :=
    survivorFixedPrimeCofactorMass_sixteen_eq_neg_mertensSummatory
      t q ht hqPrime hqFar
  have hneg :
      -(((∑ u ∈
          ((((survivorPrimeFaceAmbient q).erase 2).erase 3).erase 5).powerset,
          booleanCubeSign u *
            booleanThreePivotDifference 2 3 5
              (survivorPrimeFaceHigh 16 t q) u : ℤ)) : ℂ) =
        -RHLean.Analysis.mertensSummatory
          (RHLean.Analysis.squarePrefixEndpoint t / q) := by
    calc
      -(((∑ u ∈
          ((((survivorPrimeFaceAmbient q).erase 2).erase 3).erase 5).powerset,
          booleanCubeSign u *
            booleanThreePivotDifference 2 3 5
              (survivorPrimeFaceHigh 16 t q) u : ℤ)) : ℂ) =
          survivorFixedPrimeCofactorMass 16 t q := hstencil.symm
      _ = -RHLean.Analysis.mertensSummatory
          (RHLean.Analysis.squarePrefixEndpoint t / q) := hfar
  exact neg_inj.mp hneg

/-! ## FAR-4 on the explicit stable-far carrier

The stable-far routing is exact before energy.  After the pointwise sign
classification, the former opaque cancelled boundary packet has the literal
normal form

`cancelled boundary = extra crossings - terminal boundary`.

Thus the final carrier is

`frozenTopFar = descended q^2 packet + extra crossings - terminal boundary`.

The declarations below keep that full signed synthesis intact.  No triangle
inequality or separate packet estimate is introduced.
-/

/-- Literal true-product q^2-descended packet from the stable-far census. -/
def farFourDescendedPacket (R : ℕ) : ℂ :=
  ∑ x ∈ lowWheelFarPrimeDescendedProductCarrier R,
    canonicalMoebiusWeight x.2

/-- Fully reassembled signed complement after the legitimate unit/crossing
cancellations have already been performed occurrence-by-occurrence. -/
def farFourCancelledBoundaryPacket (R : ℕ) : ℂ :=
  ∑ n ∈ lowWheelFarWallBoundaryProductHomes R,
    (lowWheelFarWallCancelledBoundaryCoefficient R n : ℂ) *
      canonicalMoebiusWeight n

/-- The nonnegative extra-crossing packet left after deleting one genuine
crossing occurrence against each cancellable unit prime. -/
def farFourExtraCrossingPacket (R : ℕ) : ℂ :=
  ∑ n ∈ lowWheelFarWallBoundaryProductHomes R,
    (lowWheelFarWallExtraCrossingCoefficient R n : ℂ) *
      canonicalMoebiusWeight n

/-- Multiplicity-one terminal coefficient.  An earlier layer proves that the top-unit and
owned-terminal supports are disjoint, and that these are exactly the negative
support of the cancelled coefficient. -/
def farFourTerminalCoefficient (R n : ℕ) : ℤ :=
  (if n ∈ lowWheelFarPrimeTopUnitProducts R then 1 else 0) +
    (if n ∈ lowWheelFrozenTopFarOwnedProducts R then 1 else 0)

/-- The multiplicity-one top-unit plus owned-terminal packet, kept on the same
integer homes as the crossing packet so the signed subtraction is literal. -/
def farFourTerminalPacket (R : ℕ) : ℂ :=
  ∑ n ∈ lowWheelFarWallBoundaryProductHomes R,
    (farFourTerminalCoefficient R n : ℂ) * canonicalMoebiusWeight n

/-- Pointwise coefficient normal form behind `B_R = P_R - T_R`.  This is still
an exact signed identity, before any norm. -/
theorem lowWheelFarWallCancelledBoundaryCoefficient_eq_extra_sub_terminal
    (R n : ℕ) :
    lowWheelFarWallCancelledBoundaryCoefficient R n =
      lowWheelFarWallExtraCrossingCoefficient R n -
        farFourTerminalCoefficient R n := by
  unfold lowWheelFarWallCancelledBoundaryCoefficient farFourTerminalCoefficient
  ring

/-- **Boundary normal form.**  The old cancelled packet is exactly the
nonnegative extra-crossing packet minus the multiplicity-one terminal packet. -/
theorem farFourCancelledBoundaryPacket_eq_extraCrossing_sub_terminal
    (R : ℕ) :
    farFourCancelledBoundaryPacket R =
      farFourExtraCrossingPacket R - farFourTerminalPacket R := by
  unfold farFourCancelledBoundaryPacket farFourExtraCrossingPacket
    farFourTerminalPacket
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [lowWheelFarWallCancelledBoundaryCoefficient_eq_extra_sub_terminal]
  push_cast
  ring

/-- The genuine whole-daughter energy used by the existing FAR-4 terminal
consumer.  The owner `2` is erased exactly as in the terminal statement. -/
def farFourOddQ2DaughterEnergy (R : ℕ) : ℝ :=
  ∑ q ∈ (primesUpTo (R - 1)).erase 2,
    rawQ2ChildEnergyReal R q

/-- The merged signed census, first in the historical two-packet form. -/
theorem lowWheelFrozenTopFarResidual_eq_farFourDescended_add_cancelled
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      farFourDescendedPacket R + farFourCancelledBoundaryPacket R := by
  simpa [farFourDescendedPacket, farFourCancelledBoundaryPacket] using
    lowWheelFrozenTopFarResidual_eq_descended_add_cancelledBoundary R hR

/-- **Canonical final carrier.**  After an earlier layer there is no opaque boundary packet:
`F_R = D_R + P_R - T_R` exactly. -/
theorem lowWheelFrozenTopFarResidual_eq_farFourDescended_add_extra_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      farFourDescendedPacket R + farFourExtraCrossingPacket R -
        farFourTerminalPacket R := by
  rw [lowWheelFrozenTopFarResidual_eq_farFourDescended_add_cancelled R hR,
    farFourCancelledBoundaryPacket_eq_extraCrossing_sub_terminal]
  ring

/-- Off-diagonal energy of the exact final synthesis.  The boundary side is
kept as the signed packet `P_R - T_R`; no coordinatewise absolute value is
taken. -/
def farFourCancelledCrossEnergy (R : ℕ) : ℝ :=
  ‖farFourDescendedPacket R + farFourExtraCrossingPacket R -
      farFourTerminalPacket R‖ ^ 2 -
    ‖farFourDescendedPacket R‖ ^ 2 -
    ‖farFourExtraCrossingPacket R - farFourTerminalPacket R‖ ^ 2

/-- Exact Gram expansion for the explicit `D_R + P_R - T_R` synthesis. -/
theorem farFour_jointEnergy_eq_diagonal_add_cross (R : ℕ) :
    ‖farFourDescendedPacket R + farFourExtraCrossingPacket R -
        farFourTerminalPacket R‖ ^ 2 =
      ‖farFourDescendedPacket R‖ ^ 2 +
      ‖farFourExtraCrossingPacket R - farFourTerminalPacket R‖ ^ 2 +
      farFourCancelledCrossEnergy R := by
  unfold farFourCancelledCrossEnergy
  ring

/-- The remaining quantitative statement with the cancellation isolated in the
single cross-energy term, now on the explicit packets. -/
def FarFourCancelledCrossEnergyStatement : Prop :=
  ∃ CF : ℝ, 0 ≤ CF ∧
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      farFourCancelledCrossEnergy R ≤
        4 * farFourOddQ2DaughterEnergy R +
          CF * (R : ℝ) ^ 2 * K -
          ‖farFourDescendedPacket R‖ ^ 2 -
          ‖farFourExtraCrossingPacket R - farFourTerminalPacket R‖ ^ 2

/-- The same remaining theorem in its direct final-energy form.  This is the
canonical next target after an earlier layer:

`||D_R + P_R - T_R||^2 <= 4 Q_R + C R^2 K`. -/
def FarFourExplicitEnergyStatement : Prop :=
  ∃ CF : ℝ, 0 ≤ CF ∧
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖farFourDescendedPacket R + farFourExtraCrossingPacket R -
          farFourTerminalPacket R‖ ^ 2 ≤
        4 * farFourOddQ2DaughterEnergy R + CF * (R : ℝ) ^ 2 * K

/-- Polarization introduces no new hypothesis: the cross-energy version and the
explicit final-energy version are equivalent. -/
theorem farFourCancelledCrossEnergy_iff_explicitEnergy :
    FarFourCancelledCrossEnergyStatement ↔
      FarFourExplicitEnergyStatement := by
  constructor
  · rintro ⟨CF, hCF, hcross⟩
    refine ⟨CF, hCF, ?_⟩
    intro R K hR hK
    have hc := hcross R K hR hK
    unfold farFourCancelledCrossEnergy at hc
    linarith
  · rintro ⟨CF, hCF, henergy⟩
    refine ⟨CF, hCF, ?_⟩
    intro R K hR hK
    have he := henergy R K hR hK
    unfold farFourCancelledCrossEnergy
    linarith

/-- **Exact localization of FAR-4.**  After signed reassembly and its exact
coefficient classification, FAR-4 is exactly the explicit energy inequality on
`D_R + P_R - T_R`. -/
theorem farFourExplicitEnergy_iff_frozenTopFarFourEnergy :
    FarFourExplicitEnergyStatement ↔
      FrozenTopFarFourEnergyStatement := by
  constructor
  · rintro ⟨CF, hCF, henergy⟩
    refine ⟨CF, hCF, ?_⟩
    intro R K hR hK
    have he := henergy R K hR hK
    rw [lowWheelFrozenTopFarResidual_eq_farFourDescended_add_extra_sub_terminal
      R hR]
    exact he
  · rintro ⟨CF, hCF, hfar⟩
    refine ⟨CF, hCF, ?_⟩
    intro R K hR hK
    have hf := hfar R K hR hK
    rw [lowWheelFrozenTopFarResidual_eq_farFourDescended_add_extra_sub_terminal
      R hR] at hf
    exact hf

/-- Backward-compatible cross-energy localization, now factored through the
canonical explicit carrier. -/
theorem farFourCancelledCrossEnergy_iff_frozenTopFarFourEnergy :
    FarFourCancelledCrossEnergyStatement ↔
      FrozenTopFarFourEnergyStatement :=
  farFourCancelledCrossEnergy_iff_explicitEnergy.trans
    farFourExplicitEnergy_iff_frozenTopFarFourEnergy

/-! ## Restore the owner coordinate before the final energy theorem

The nonnegative coefficients of `farFourExtraCrossingPacket` are multiplicity
counts multiplying Möbius signs; they are not positivity.  For the final
synthesis the crossing occurrence must therefore be returned to its original
owner-tagged chronology before any norm is taken.
-/

/-- **Owner coordinate restored.**  The compressed `D_R + P_R - T_R` carrier
is exactly the pre-compression chronology: ownerwise child-far slices, every
owner-tagged stable renewal occurrence, and the terminal product population.
No crossing multiplicity is replaced by an absolute value. -/
theorem farFourExplicitCarrier_eq_ownerwiseChronology
    (R : ℕ) (hR : 56 ≤ R) :
    farFourDescendedPacket R + farFourExtraCrossingPacket R -
        farFourTerminalPacket R =
      -(∑ q ∈ primesUpTo (R - 1),
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1) -
      (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        lowWheelFullTaggedPhysicalWeight
          (lowWheelFarPrimeCrossingStableState x)) -
      ∑ n ∈ lowWheelFarWallTerminalProducts R,
        canonicalMoebiusWeight n := by
  rw [← lowWheelFrozenTopFarResidual_eq_farFourDescended_add_extra_sub_terminal
    R hR]
  exact lowWheelFrozenTopFarResidual_eq_neg_childFarSlices_sub_stableRenewal_sub_terminal
    R hR

/-- Exact signed remainder after the full all-prime q² Mertens column is
extracted ownerwise.  Every term is still a signed chronology term: near
high-transport, the q²-or-deeper intermediate-prime tower, stable renewal,
terminal products, and the original Go column. -/
def farFourAllPrimeOwnerwiseSynthesisError (R : ℕ) : ℂ :=
  (((squareEndpointQ2NearHighTransportColumn R : ℤ) : ℂ)) -
    (((squareEndpointQ2IntermediatePrimeTower R : ℤ) : ℂ)) -
    stableFarRenewalColumn R - stableFarTerminalProductColumn R -
    (((squareEndpointQ2GoColumn R : ℤ) : ℂ))

/-- **Exact all-prime Mertens synthesis.**  The stable-far residual is a column
of genuine q² Mertens daughters plus the explicit ownerwise signed remainder.
This is an equality before energy. -/
theorem lowWheelFrozenTopFarResidual_eq_mertensColumn_add_ownerwiseError
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      (((squareEndpointQ2MertensColumn R : ℤ) : ℂ)) +
        farFourAllPrimeOwnerwiseSynthesisError R := by
  have hmismatch :=
    q2TransportFarMismatch_eq_compiled_near_sub_tower_sub_renewal_sub_terminal
      R hR
  unfold q2TransportFarMismatch at hmismatch
  rw [← squareEndpointQ2HighTransportDefect_eq_actualColumn R] at hmismatch
  unfold squareEndpointQ2HighTransportDefect at hmismatch
  push_cast at hmismatch
  unfold farFourAllPrimeOwnerwiseSynthesisError
  linear_combination hmismatch

/-- Odd-owner q² Mertens column in the exact complex currency of FAR-4. -/
def farFourOddMertensColumn (R : ℕ) : ℂ :=
  (((∑ q ∈ (primesUpTo (R - 1)).erase 2,
      mertensSummatoryInt (squareRootEndpoint R / (q * q)) : ℤ) : ℂ))

/-- The owner-two daughter is not part of the physical odd-owner energy budget,
so it remains signed inside the synthesis error rather than being normed on its
own. -/
def farFourOwnerwiseSynthesisError (R : ℕ) : ℂ :=
  (((mertensSummatoryInt (squareRootEndpoint R / 4) : ℤ) : ℂ)) +
    farFourAllPrimeOwnerwiseSynthesisError R

/-- **Exact odd-owner synthesis.**  This is the requested pre-energy normal
form: the physical FAR-4 carrier equals the odd q² Mertens column plus one
explicit signed chronology error.  The straight extraction has coefficient
`+1` on every odd owner; any factor-four gain must therefore come from the
signed synthesis itself (or from a genuinely sharper change of basis), not from
pretending these scalar coefficients have bounded ℓ² norm. -/
theorem lowWheelFrozenTopFarResidual_eq_oddMertensColumn_add_ownerwiseError
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      farFourOddMertensColumn R + farFourOwnerwiseSynthesisError R := by
  rw [lowWheelFrozenTopFarResidual_eq_mertensColumn_add_ownerwiseError R hR,
    squareEndpointQ2MertensColumn_eq_oddColumn_add_two R (by omega)]
  unfold farFourOddMertensColumn farFourOwnerwiseSynthesisError
  push_cast
  ring

/-- **The one remaining ownerwise signed synthesis theorem.**  This formulation
keeps the genuine odd q² daughters and the complete signed chronology error in
one norm.  It is deliberately not split into a norm of `P_R` or of the error. -/
def FarFourOwnerwiseSignedSynthesisStatement : Prop :=
  ∃ CF : ℝ, 0 ≤ CF ∧
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖farFourOddMertensColumn R + farFourOwnerwiseSynthesisError R‖ ^ 2 ≤
        4 * farFourOddQ2DaughterEnergy R + CF * (R : ℝ) ^ 2 * K

/-- The ownerwise signed synthesis statement is exactly FAR-4, now with the
recursive Mertens daughters exposed.  Compiling this equivalence leaves one
quantitative theorem rather than parallel carrier formulations. -/
theorem farFourOwnerwiseSignedSynthesis_iff_frozenTopFarFourEnergy :
    FarFourOwnerwiseSignedSynthesisStatement ↔
      FrozenTopFarFourEnergyStatement := by
  constructor
  · rintro ⟨CF, hCF, hsynth⟩
    refine ⟨CF, hCF, ?_⟩
    intro R K hR hK
    have hs := hsynth R K hR hK
    rw [lowWheelFrozenTopFarResidual_eq_oddMertensColumn_add_ownerwiseError
      R hR]
    simpa [farFourOddQ2DaughterEnergy] using hs
  · rintro ⟨CF, hCF, hfar⟩
    refine ⟨CF, hCF, ?_⟩
    intro R K hR hK
    have hf := hfar R K hR hK
    rw [lowWheelFrozenTopFarResidual_eq_oddMertensColumn_add_ownerwiseError
      R hR] at hf
    simpa [farFourOddQ2DaughterEnergy] using hf

/-! ## Euler chronology / q² owner correspondence

The two exact descriptions of the frozen/top/far residual are now put in one
commuting diagram.  On any complete descending prime schedule, the full signed
raw Euler boundary ledger plus the explicit root correction is exactly the odd
q² Mertens owner column plus the ownerwise chronology error.  This is an
identity of the whole signed objects before any norm; it does not estimate either
side or replace a physical daughter by an incidence coefficient norm. -/

/-- **Exact global Euler-to-q² bridge.**  The descending zero-factor chronology
and the ownerwise q² synthesis are two representations of the same signed
frozen/top/far state. -/
theorem adaptiveRawLedger_add_rootCorrection_eq_oddMertensColumn_add_ownerwiseError_of_completeSchedule
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    squareRootCanonicalRoughAdaptiveRawLedger R ps
          (Finset.Icc 1 (squareRootEndpoint R))
          (fun _ => (1 : ℂ)) +
        frozenTopFarRoughRootCorrection R =
      farFourOddMertensColumn R + farFourOwnerwiseSynthesisError R := by
  rw [← lowWheelFrozenTopFarResidual_eq_rawLedger_add_rootCorrection_of_completeSchedule
      R hR ps hsched,
    lowWheelFrozenTopFarResidual_eq_oddMertensColumn_add_ownerwiseError R hR]

end RHLean.Proof
