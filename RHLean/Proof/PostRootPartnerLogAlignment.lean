import Mathlib
import RHLean.Proof.PostRootPartnerEulerMemory
import RHLean.Proof.CanonicalRoughTruncatedWheelManyPrimeTelescope
import RHLean.Proof.CanonicalRoughColumnAbelBridge
import RHLean.Proof.LowWheelCanonicalSqrtDenseContraction
import RHLean.Analysis.SquareRootMatchedTransport
import RHLean.Proof.StableFarWallUnitRenewalCentering
import RHLean.Proof.PhysicalQ2ExceptionalTerminalSynthesis
import RHLean.Proof.PostRootPartnerMellinInterpolation
import RHLean.Proof.LogSquareCorrectionQ2Tower

/-!
# Exact Euler-hazard alignment of the post-root partner ledger

This module keeps the chronology signed until the physical/canonical
first-power column has been identified.  No norm is taken in the splice layer.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-! ## Scalar Euler-hazard mass -/

def postRootEulerHazardMass : List ℕ → ℝ
  | [] => 0
  | p :: ps =>
      canonicalRoughEulerFactor p * postRootEulerHazardMass ps +
        1 / (p : ℝ)

@[simp] theorem postRootEulerHazardMass_nil :
    postRootEulerHazardMass [] = 0 := by
  rfl

@[simp] theorem postRootEulerHazardMass_cons (p : ℕ) (ps : List ℕ) :
    postRootEulerHazardMass (p :: ps) =
      canonicalRoughEulerFactor p * postRootEulerHazardMass ps +
        1 / (p : ℝ) := by
  rfl

theorem postRootEulerHazardMass_eq_one_sub_eulerProduct (ps : List ℕ) :
    postRootEulerHazardMass ps =
      1 - canonicalRoughPrimeListEulerProduct ps := by
  induction ps with
  | nil =>
      simp [postRootEulerHazardMass, canonicalRoughPrimeListEulerProduct]
  | cons p ps ih =>
      simp only [postRootEulerHazardMass_cons,
        canonicalRoughPrimeListEulerProduct_cons]
      rw [ih]
      unfold canonicalRoughEulerFactor
      ring

/-! ## Boundary-valued Euler-hazard ledger -/

def postRootEulerHazardLedger (boundary : ℕ → ℂ) : List ℕ → ℂ
  | [] => 0
  | p :: ps =>
      (canonicalRoughEulerFactor p : ℂ) *
          postRootEulerHazardLedger boundary ps +
        boundary p / (p : ℂ)

@[simp] theorem postRootEulerHazardLedger_nil (boundary : ℕ → ℂ) :
    postRootEulerHazardLedger boundary [] = 0 := by
  rfl

@[simp] theorem postRootEulerHazardLedger_cons
    (boundary : ℕ → ℂ) (p : ℕ) (ps : List ℕ) :
    postRootEulerHazardLedger boundary (p :: ps) =
      (canonicalRoughEulerFactor p : ℂ) *
          postRootEulerHazardLedger boundary ps +
        boundary p / (p : ℂ) := by
  rfl

theorem postRootEulerHazardLedger_append
    (boundary : ℕ → ℂ) (pre post : List ℕ) :
    postRootEulerHazardLedger boundary (pre ++ post) =
      (canonicalRoughPrimeListEulerProduct pre : ℂ) *
          postRootEulerHazardLedger boundary post +
        postRootEulerHazardLedger boundary pre := by
  induction pre with
  | nil =>
      simp [postRootEulerHazardLedger, canonicalRoughPrimeListEulerProduct]
  | cons p pre ih =>
      simp only [List.cons_append, postRootEulerHazardLedger_cons,
        canonicalRoughPrimeListEulerProduct_cons]
      rw [ih]
      push_cast
      ring

/-! ## Literal connection to the physical defect ledger -/

def squareRootCanonicalRoughPhysicalStepBoundaryCharge
    (R : ℕ) (step : CanonicalRoughPhysicalEulerStep) : ℂ :=
  (step.1 : ℂ) * squareRootCanonicalRoughPhysicalStepDefect R step

def squareRootCanonicalRoughTransportedBoundaryChargeLedger
    (R : ℕ) : List CanonicalRoughPhysicalEulerStep → ℂ
  | [] => 0
  | step :: steps =>
      (canonicalRoughEulerFactor step.1 : ℂ) *
          squareRootCanonicalRoughTransportedBoundaryChargeLedger R steps +
        squareRootCanonicalRoughPhysicalStepBoundaryCharge R step /
          (step.1 : ℂ)

theorem squareRootCanonicalRoughTransportedBoundaryChargeLedger_eq_defectLedger
    (R : ℕ) (steps : List CanonicalRoughPhysicalEulerStep)
    (hprime : ∀ step ∈ steps, step.1.Prime) :
    squareRootCanonicalRoughTransportedBoundaryChargeLedger R steps =
      squareRootCanonicalRoughTransportedDefectLedger R steps := by
  induction steps with
  | nil =>
      rfl
  | cons step steps ih =>
      have hp : step.1.Prime := hprime step (by simp)
      have htail : ∀ s ∈ steps, s.1.Prime := by
        intro s hs
        exact hprime s (by simp [hs])
      have hp0 : (step.1 : ℂ) ≠ 0 := by
        exact_mod_cast hp.ne_zero
      have hscale :
          squareRootCanonicalRoughPhysicalStepBoundaryCharge R step /
              (step.1 : ℂ) =
            squareRootCanonicalRoughPhysicalStepDefect R step := by
        unfold squareRootCanonicalRoughPhysicalStepBoundaryCharge
        field_simp [hp0]
      simp only [squareRootCanonicalRoughTransportedBoundaryChargeLedger,
        squareRootCanonicalRoughTransportedDefectLedger]
      rw [ih htail, hscale]

/-- Canonical endpoint of the hazard-coordinate splice. -/
theorem postRootCanonicalColumn_logAlignmentTarget (X K : ℕ) :
    (∑ q ∈ primesUpTo K,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1)) (X / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive X K := by
  exact canonicalUnweightedColumn_eq_abelPrimitive X K

/-! ## FAR-4 splice: exact q² carrier first, energy second -/

/-- The centered q²-descended carrier obtained from the old stable-far census
after every nonunit strict crossing is sent to its unique next child. -/
def farFourQ2CenteredTower (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
    (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ)) *
      canonicalMoebiusWeight y.2.1

/-- The complementary terminal population in the old census.  It is kept only
as a signed bookkeeping object; it must not be normed separately. -/
def farFourTerminalRemainder (R : ℕ) : ℂ :=
  (∑ p ∈ lowWheelFarPrimeUnitProducts R,
      ((lowWheelFarPrimeQ2UnitCrossingMultiplicity R p : ℂ) - 1)) +
    ∑ n ∈ lowWheelFrozenTopFarOwnedProducts R,
      canonicalMoebiusWeight n

theorem lowWheelFarWallTerminalProducts_mass_eq_unit_add_owned (R : ℕ) :
    (∑ n ∈ lowWheelFarWallTerminalProducts R,
        canonicalMoebiusWeight n) =
      (∑ p ∈ lowWheelFarPrimeUnitProducts R,
        canonicalMoebiusWeight p) +
      ∑ n ∈ lowWheelFrozenTopFarOwnedProducts R,
        canonicalMoebiusWeight n := by
  unfold lowWheelFarWallTerminalProducts
  rw [Finset.sum_union (lowWheelFarPrimeUnitProducts_disjoint_owned R)]

/-- Exact old-census normal form, before any norm.  This theorem is retained to
make the cancellation requirement visible; the two displayed terms are not
separate errors. -/
theorem lowWheelFrozenTopFarResidual_eq_neg_q2CenteredTower_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      -farFourQ2CenteredTower R - farFourTerminalRemainder R := by
  have hfar :=
    lowWheelFrozenTopFarResidual_eq_neg_childFarSlices_sub_stableRenewal_sub_terminal
      R hR
  have hcenter :=
    lowWheelFarPrimeChildFar_add_crossingRenewal_add_unitTerminal_eq_centered R
  have hterminal := lowWheelFarWallTerminalProducts_mass_eq_unit_add_owned R
  unfold farFourQ2CenteredTower farFourTerminalRemainder
  rw [hterminal] at hfar
  rw [hfar]
  linear_combination -hcenter

/-- Literal factor-four FAR splice with the root-envelope constant exposed. -/
def FarFourSplice (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    ‖lowWheelFrozenTopFarResidual R‖ ^ 2 ≤
      4 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
        rawQ2ChildEnergyReal R q +
      C * (R : ℝ) ^ 2 * K

/-- The named splice is definitionally the body of the pre-existing FAR-4
terminal criterion. -/
theorem frozenTopFarFourEnergy_iff_exists_nonneg_farFourSplice :
    FrozenTopFarFourEnergyStatement ↔
      ∃ C : ℝ, 0 ≤ C ∧ FarFourSplice C := by
  rfl

/-! ## Exact far high-transport predecessor telescope -/

/-- Portion of one q² high-transport daughter with outer prime in the same
far-prime range used by the stable-far chronology. -/
def q2DaughterFarHighTransport (R q : ℕ) : ℤ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7)
      (squareRootEndpoint R / (q * q)),
    frozenPrimeUniverseMass (primesUpTo (p - 1))
      ((squareRootEndpoint R / (q * q)) / p)

/-- The same far-prime schedule, but with every predecessor cube moved back to
the common q-predecessor universe.  This is the source shape expected by the
literal q² child-far slice. -/
def q2DaughterFarBaseColumn (R q : ℕ) : ℤ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7)
      (squareRootEndpoint R / (q * q)),
    frozenPrimeUniverseMass (primesUpTo (q - 1))
      ((squareRootEndpoint R / (q * q)) / p)

/-- Ordered intermediate-prime population created when the moving predecessor
cube `p^-` is telescoped back to `q^-`.  Every atom has parent denominator
`q²*p*r`, so this object is q²-or-deeper before any norm is taken. -/
def q2DaughterFarIntermediatePrimeTower (R q : ℕ) : ℤ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7)
      (squareRootEndpoint R / (q * q)),
    ∑ r ∈ frozenPrimeUniverseHighPrimeSet (q - 1) (p - 1),
      frozenPrimeUniverseMass (primesUpTo (r - 1))
        (((squareRootEndpoint R / (q * q)) / p) / r)

/-- **Ownerwise exact predecessor-cube correction.**  This is the precise
repair of the false `P⁺(d)<p` versus `P⁺(d)<q` identification: moving the cube
from `p^-` back to `q^-` produces exactly the intermediate-prime tower. -/
theorem q2DaughterFarHighTransport_eq_base_sub_intermediatePrimeTower
    {R q : ℕ} (hqR : q < R) :
    q2DaughterFarHighTransport R q =
      q2DaughterFarBaseColumn R q -
        q2DaughterFarIntermediatePrimeTower R q := by
  unfold q2DaughterFarHighTransport q2DaughterFarBaseColumn
    q2DaughterFarIntermediatePrimeTower
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
  have hqp : q - 1 ≤ p - 1 := by
    have hpLower : R + 7 < p := hpData.2.1
    omega
  have htel :=
    frozenPrimeUniverse_highUpperColumn_telescope
      ((squareRootEndpoint R / (q * q)) / p) (q - 1) (p - 1) hqp
  linear_combination htel

/-- The complementary near-prime part is defined by exact signed subtraction,
so no prime-range mass is lost while the far portion is isolated. -/
def q2DaughterNearHighTransport (R q : ℕ) : ℤ :=
  q2DaughterHighTransport q (squareRootEndpoint R) -
    q2DaughterFarHighTransport R q

def squareEndpointQ2NearHighTransportColumn (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1), q2DaughterNearHighTransport R q

def squareEndpointQ2FarHighTransportColumn (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1), q2DaughterFarHighTransport R q

def squareEndpointQ2FarBaseColumn (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1), q2DaughterFarBaseColumn R q

def squareEndpointQ2IntermediatePrimeTower (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1), q2DaughterFarIntermediatePrimeTower R q

/-- Exact near/far split of the actual q² high-transport source. -/
theorem squareEndpointQ2HighTransportColumn_eq_near_add_far (R : ℕ) :
    squareEndpointQ2HighTransportColumn R =
      squareEndpointQ2NearHighTransportColumn R +
        squareEndpointQ2FarHighTransportColumn R := by
  unfold squareEndpointQ2HighTransportColumn
    squareEndpointQ2NearHighTransportColumn squareEndpointQ2FarHighTransportColumn
    q2DaughterNearHighTransport
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  ring

/-- Summing the ownerwise predecessor telescope leaves one common-base far
column minus one explicit q²-or-deeper intermediate-prime tower. -/
theorem squareEndpointQ2FarHighTransportColumn_eq_base_sub_intermediatePrimeTower
    (R : ℕ) :
    squareEndpointQ2FarHighTransportColumn R =
      squareEndpointQ2FarBaseColumn R -
        squareEndpointQ2IntermediatePrimeTower R := by
  unfold squareEndpointQ2FarHighTransportColumn squareEndpointQ2FarBaseColumn
    squareEndpointQ2IntermediatePrimeTower
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hqData := mem_primesUpTo.mp hq
  have hq2 : 2 ≤ q := hqData.1.two_le
  exact q2DaughterFarHighTransport_eq_base_sub_intermediatePrimeTower
    (by omega : q < R)

/-! ## Corrected post-diagnostic transport/far seam -/

/-- The exact signed mismatch between the q² daughter high-transport column and
the stable-far destination census.  The diagnostic after an earlier layer shows that this
quantity is not identically zero; it is therefore kept as the genuine next
signed seam rather than hidden in a false support equality. -/
def q2TransportFarMismatch (R : ℕ) : ℂ :=
  (((squareEndpointQ2HighTransportColumn R : ℤ) : ℂ)) +
    lowWheelFrozenTopFarResidual R

/-- Equivalent source/destination form of the mismatch.  The three routed far
populations are exactly the negative frozen/top/far residual, so the mismatch
is `HighTransport - (ChildFar + Renewal + Terminal)`. -/
theorem q2TransportFarMismatch_eq_highTransport_sub_farPopulations
    (R : ℕ) (hR : 56 ≤ R) :
    q2TransportFarMismatch R =
      (((squareEndpointQ2HighTransportColumn R : ℤ) : ℂ)) -
        (squareEndpointQ2ChildFarSliceColumn R +
          stableFarRenewalColumn R + stableFarTerminalProductColumn R) := by
  have hfar := farPopulations_eq_neg_frozenTopFar R hR
  unfold q2TransportFarMismatch
  rw [hfar]
  ring

/-- The mismatch after the exact predecessor telescope.  The only difference
between the actual high-transport source and the stable-far side is now exposed
as a near column, a common-q far base, the q²-or-deeper intermediate tower, and
the original signed frozen/top/far residual. -/
theorem q2TransportFarMismatch_eq_near_add_base_sub_tower_add_frozenTopFar
    (R : ℕ) :
    q2TransportFarMismatch R =
      (((squareEndpointQ2NearHighTransportColumn R : ℤ) : ℂ)) +
        (((squareEndpointQ2FarBaseColumn R : ℤ) : ℂ)) -
        (((squareEndpointQ2IntermediatePrimeTower R : ℤ) : ℂ)) +
        lowWheelFrozenTopFarResidual R := by
  unfold q2TransportFarMismatch
  rw [squareEndpointQ2HighTransportColumn_eq_near_add_far R,
    squareEndpointQ2FarHighTransportColumn_eq_base_sub_intermediatePrimeTower R]
  push_cast
  ring

/-- The remaining local carrier bridge is now named separately: the common-q
far predecessor column should be identified with the already-compiled child-far
slice.  Unlike the refuted high-transport support equality, these two objects
have the same `P⁺(d)<q`, `p≥R+8`, and `q²*d*p≤X_R` support. -/
def FarBaseChildSliceMatch : Prop :=
  ∀ R : ℕ, 56 ≤ R →
    (((squareEndpointQ2FarBaseColumn R : ℤ) : ℂ)) =
      squareEndpointQ2ChildFarSliceColumn R

/-- Rectangular common-base carrier before the final product cutoff is imposed. -/
private def q2FarBasePairCarrier (R q : ℕ) : Finset (ℕ × ℕ) :=
  let Y := squareRootEndpoint R / (q * q)
  ((squareRootLowPrimeGoSmoothCofactors q Y).product
      (frozenPrimeUniverseHighPrimeSet (R + 7) Y)).filter fun dp =>
    dp.1 * dp.2 ≤ Y

/-- Restricting the q-smooth cofactor cutoff from `Y` to `Y/p` is exactly the
same as retaining the full q-smooth population and imposing `d*p <= Y`. -/
private theorem q2SmoothCofactors_div_eq_filter
    {q Y p : ℕ} (hp : 0 < p) :
    squareRootLowPrimeGoSmoothCofactors q (Y / p) =
      (squareRootLowPrimeGoSmoothCofactors q Y).filter fun d => d * p ≤ Y := by
  ext d
  simp only [Finset.mem_filter, mem_squareRootLowPrimeGoSmoothCofactors]
  constructor
  · rintro ⟨hd1, hdCut, hsq, hrough⟩
    have hmul : d * p ≤ Y := (Nat.le_div_iff_mul_le hp).1 hdCut
    have hdY : d ≤ Y := hdCut.trans (Nat.div_le_self Y p)
    exact ⟨⟨hd1, hdY, hsq, hrough⟩, hmul⟩
  · rintro ⟨⟨hd1, _hdY, hsq, hrough⟩, hmul⟩
    have hdCut : d ≤ Y / p := (Nat.le_div_iff_mul_le hp).2 hmul
    exact ⟨hd1, hdCut, hsq, hrough⟩

/-- **Exact carrier equality.**  The common-q far-base rectangle with the
product cutoff is literally the q² child-far slice. -/
private theorem q2FarBasePairCarrier_eq_childFarSlice
    (R q : ℕ) :
    q2FarBasePairCarrier R q = lowWheelFarPrimeQ2ChildFarSlice R q := by
  ext dp
  rcases dp with ⟨d, p⟩
  unfold q2FarBasePairCarrier
  constructor
  · intro hdp
    rcases Finset.mem_filter.mp hdp with ⟨hprod, hdpCut⟩
    rcases Finset.mem_product.mp hprod with ⟨hd, hpHigh⟩
    rcases mem_frozenPrimeUniverseHighPrimeSet.mp hpHigh with
      ⟨hpPrime, hpLower, hpUpper⟩
    have hpRange : p ∈ Finset.Icc (R + 8) (squareRootEndpoint R) := by
      apply Finset.mem_Icc.mpr
      refine ⟨?_, ?_⟩
      · omega
      · exact hpUpper.trans
          (Nat.div_le_self (squareRootEndpoint R) (q * q))
    exact mem_lowWheelFarPrimeQ2ChildFarSlice.mpr
      ⟨hd, hpRange, hpPrime, hdpCut⟩
  · intro hdp
    rcases mem_lowWheelFarPrimeQ2ChildFarSlice.mp hdp with
      ⟨hd, hpRange, hpPrime, hdpCut⟩
    have hd1 : 1 ≤ d :=
      (mem_squareRootLowPrimeGoSmoothCofactors.mp hd).1
    have hpLeDp : p ≤ d * p := by
      simpa using Nat.mul_le_mul_right p hd1
    have hpUpper : p ≤ squareRootEndpoint R / (q * q) :=
      hpLeDp.trans hdpCut
    have hpLower : R + 8 ≤ p := (Finset.mem_Icc.mp hpRange).1
    have hpHigh :
        p ∈ frozenPrimeUniverseHighPrimeSet
          (R + 7) (squareRootEndpoint R / (q * q)) :=
      mem_frozenPrimeUniverseHighPrimeSet.mpr
        ⟨hpPrime, by omega, hpUpper⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hd, hpHigh⟩, hdpCut⟩

/-- The common-q far-base column is the integer Möbius mass of the exact pair
carrier.  This is finite Fubini only. -/
private theorem q2DaughterFarBaseColumn_eq_pairCarrierMass
    {R q : ℕ} (hq : q.Prime) :
    q2DaughterFarBaseColumn R q =
      ∑ dp ∈ q2FarBasePairCarrier R q, μ dp.1 := by
  let Y := squareRootEndpoint R / (q * q)
  unfold q2DaughterFarBaseColumn q2FarBasePairCarrier
  change
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7) Y,
      frozenPrimeUniverseMass (primesUpTo (q - 1)) (Y / p)) =
      ∑ dp ∈
        ((squareRootLowPrimeGoSmoothCofactors q Y).product
          (frozenPrimeUniverseHighPrimeSet (R + 7) Y)).filter
            (fun dp => dp.1 * dp.2 ≤ Y),
        μ dp.1
  calc
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7) Y,
        frozenPrimeUniverseMass (primesUpTo (q - 1)) (Y / p)) =
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7) Y,
        ∑ d ∈ squareRootLowPrimeGoSmoothCofactors q (Y / p), μ d := by
          apply Finset.sum_congr rfl
          intro p _hp
          exact frozenPrimeUniverseMass_eq_goSmoothCofactorSum hq
    _ = ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7) Y,
        ∑ d ∈ squareRootLowPrimeGoSmoothCofactors q Y,
          if d * p ≤ Y then μ d else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpPrime := (mem_frozenPrimeUniverseHighPrimeSet.mp hp).1
          rw [q2SmoothCofactors_div_eq_filter hpPrime.pos, Finset.sum_filter]
    _ = ∑ d ∈ squareRootLowPrimeGoSmoothCofactors q Y,
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7) Y,
          if d * p ≤ Y then μ d else 0 := by
          exact Finset.sum_comm
    _ = ∑ dp ∈
        (squareRootLowPrimeGoSmoothCofactors q Y).product
          (frozenPrimeUniverseHighPrimeSet (R + 7) Y),
        if dp.1 * dp.2 ≤ Y then μ dp.1 else 0 := by
          symm
          simpa only using
            (Finset.sum_product
              (s := squareRootLowPrimeGoSmoothCofactors q Y)
              (t := frozenPrimeUniverseHighPrimeSet (R + 7) Y)
              (f := fun dp : ℕ × ℕ =>
                if dp.1 * dp.2 ≤ Y then μ dp.1 else 0))
    _ = ∑ dp ∈
        ((squareRootLowPrimeGoSmoothCofactors q Y).product
          (frozenPrimeUniverseHighPrimeSet (R + 7) Y)).filter
            (fun dp => dp.1 * dp.2 ≤ Y),
        μ dp.1 := by
          rw [Finset.sum_filter]

/-- Ownerwise common-base mass equals the already-compiled child-far mass in
complex Möbius currency. -/
theorem q2DaughterFarBaseColumn_cast_eq_childFarSliceMass
    {R q : ℕ} (hq : q.Prime) :
    ((q2DaughterFarBaseColumn R q : ℤ) : ℂ) =
      ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
        canonicalMoebiusWeight dp.1 := by
  have h := q2DaughterFarBaseColumn_eq_pairCarrierMass (R := R) (q := q) hq
  rw [q2FarBasePairCarrier_eq_childFarSlice R q] at h
  have hcast := congrArg (fun z : ℤ => (z : ℂ)) h
  push_cast at hcast
  simpa [canonicalMoebiusWeight] using hcast

/-- **The local bridge left after the failed full-support splice is true.**
Summing the ownerwise carrier identity proves the named common-base/child-far
match without any root-scale estimate. -/
theorem farBaseChildSliceMatch : FarBaseChildSliceMatch := by
  intro R _hR
  unfold squareEndpointQ2FarBaseColumn squareEndpointQ2ChildFarSliceColumn
  push_cast
  apply Finset.sum_congr rfl
  intro q hq
  exact q2DaughterFarBaseColumn_cast_eq_childFarSliceMass
    (mem_primesUpTo.mp hq).1

/-- Conditional exact normal form after only the *local* common-base/child-far
carrier bridge.  No zero-mismatch claim is made: the surviving signed seam is
near transport minus the q²-or-deeper intermediate tower minus renewal and
terminal populations. -/
theorem q2TransportFarMismatch_eq_near_sub_tower_sub_renewal_sub_terminal
    (hmatch : FarBaseChildSliceMatch)
    (R : ℕ) (hR : 56 ≤ R) :
    q2TransportFarMismatch R =
      (((squareEndpointQ2NearHighTransportColumn R : ℤ) : ℂ)) -
        (((squareEndpointQ2IntermediatePrimeTower R : ℤ) : ℂ)) -
        stableFarRenewalColumn R - stableFarTerminalProductColumn R := by
  rw [q2TransportFarMismatch_eq_near_add_base_sub_tower_add_frozenTopFar R,
    hmatch R hR]
  have hfar := farPopulations_eq_neg_frozenTopFar R hR
  linear_combination hfar

/-- The corrected transport/far mismatch seam is therefore unconditional: the
only surviving terms are near high transport, the q²-or-deeper intermediate
prime tower, stable renewal, and the terminal population. -/
theorem q2TransportFarMismatch_eq_compiled_near_sub_tower_sub_renewal_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    q2TransportFarMismatch R =
      (((squareEndpointQ2NearHighTransportColumn R : ℤ) : ℂ)) -
        (((squareEndpointQ2IntermediatePrimeTower R : ℤ) : ℂ)) -
        stableFarRenewalColumn R - stableFarTerminalProductColumn R :=
  q2TransportFarMismatch_eq_near_sub_tower_sub_renewal_sub_terminal
    farBaseChildSliceMatch R hR

/-- **Exact corrected survivor seam.**  No cancellation is assumed: the
survivor is the root reassembly boundary minus the literal transport/far
mismatch. -/
theorem finalQ2SurvivorCorrection_eq_root_sub_q2TransportFarMismatch
    (R : ℕ) (hR : 56 ≤ R) :
    finalQ2SurvivorCorrection R =
      finalQ2RootReassemblyBoundary R - q2TransportFarMismatch R := by
  have hfar := farPopulations_eq_neg_frozenTopFar R hR
  unfold finalQ2SurvivorCorrection q2TransportFarMismatch
  linear_combination hfar

/-- **Exact corrected low/high normal form.**  The genuine lower-scale q²
Mertens column is exposed, while the only remaining signed seam is the explicit
transport/far mismatch.  No norm or estimate enters this identity. -/
theorem finalCompensatedLowHighDifference_eq_neg_mertensColumn_add_root_sub_mismatch
    (R : ℕ) (hR : 56 ≤ R) :
    finalCompensatedLowHighDifference R =
      -(((squareEndpointQ2MertensColumn R : ℤ) : ℂ)) +
        (finalQ2RootReassemblyBoundary R - q2TransportFarMismatch R) := by
  rw [finalCompensatedLowHighDifference_eq_neg_mertensColumn_add_survivor R hR,
    finalQ2SurvivorCorrection_eq_root_sub_q2TransportFarMismatch R hR]

/-- **Candidate signed q²-tower support statement.**

The exact integer diagnostic `EMPIRICAL_DIAGNOSTICS.md`
refutes this candidate at `R = 56`: high transport is `8`, while the three
destination columns total `160 + 309 - 466 = 3`. This diagnostic has not been
formalized as a Lean certificate. The proposition is retained to name the
failed target; the implications below remain conditional algebra only.

The existing routing theorems classify the stable-far source, whose cofactor
cube is below `q` and whose original cutoff is `q*d*p <= X_R`. High transport
instead uses the predecessor cube below `p` at `q^2*d*p <= X_R`. LOG-MATCH
preserves the former carrier and does not identify these two sources. -/
def FarFourSignedQ2TowerSupport : Prop :=
  ∀ R : ℕ, 56 ≤ R →
    (((squareEndpointQ2HighTransportColumn R : ℤ) : ℂ)) =
      squareEndpointQ2ChildFarSliceColumn R +
        stableFarRenewalColumn R + stableFarTerminalProductColumn R

/-- The support statement is exactly the assertion that the survivor is
only the root-scale reassembly boundary. -/
theorem farFourSignedQ2TowerSupport_iff_survivor_eq_root :
    FarFourSignedQ2TowerSupport ↔
      ∀ R : ℕ, 56 ≤ R →
        finalQ2SurvivorCorrection R = finalQ2RootReassemblyBoundary R := by
  constructor
  · intro h R hR
    have hs := h R hR
    unfold finalQ2SurvivorCorrection
    linear_combination -hs
  · intro h R hR
    have hs := h R hR
    unfold finalQ2SurvivorCorrection at hs
    linear_combination -hs

/-- Once the signed support identity is proved, the exact low/high packet is a
column of genuine q² Mertens daughters plus only the root reassembly boundary.
No norm appears in this composition. -/
theorem finalCompensatedLowHighDifference_eq_neg_mertensColumn_add_root_of_q2Support
    (hsupport : FarFourSignedQ2TowerSupport)
    (R : ℕ) (hR : 56 ≤ R) :
    finalCompensatedLowHighDifference R =
      -(((squareEndpointQ2MertensColumn R : ℤ) : ℂ)) +
        finalQ2RootReassemblyBoundary R := by
  rw [finalCompensatedLowHighDifference_eq_neg_mertensColumn_add_survivor R hR]
  rw [(farFourSignedQ2TowerSupport_iff_survivor_eq_root.mp hsupport) R hR]

/-- Pin the exact Mellin/q² commutator next to the global signed splice. -/
theorem farFour_logMatch : LOG_MATCH := log_match

end RHLean.Proof
