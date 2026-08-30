import Mathlib
import RHLean.Proof.LowWheelExternalTerminalParentSplit
import RHLean.Proof.MatchedFarSurvivorBridge

/-!
# External repeated-parent cancellation at square-root scale

This module closes the external `R < p` terminal population quantitatively.
The complete high-prime transport is first read on the literal face/high-prime
grid.  That same finite carrier is split by the already-proved canonical
root-parent ownership into unique and repeated pieces.

The unique part injects into the global unique-parent downcross carrier and
therefore has at most `R` occurrences.  The repeated part is then recombined
with the already-existing far-upper survivor.  The exact far-survivor theorem
leaves only the seven-coordinate near-prime strip minus the unique-parent mass,
so the final signed norm is at most `7R + R = 8R`.

No prime-density estimate, PNT input, asymptotic hypothesis, or further Euler
descent is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The signed unique-parent part of the external high-prime grid. -/
def squareRootERuniq (R : ℕ) : ℂ :=
  ∑ z ∈ squareRootExternalTerminalUniqueFaceCarrier R,
    (booleanCubeSign z.1 : ℂ)

/-- The signed repeated-parent part of the external high-prime grid. -/
def squareRootERrep (R : ℕ) : ℂ :=
  ∑ z ∈ squareRootExternalTerminalRepeatedFaceCarrier R,
    (booleanCubeSign z.1 : ℂ)

/-- The nested terminal face/high-prime ledger is exactly the flattened
face/high-prime carrier used by the parent split. -/
theorem squareRootExternalTerminalFaceLedger_eq_carrierSum
    (R : ℕ) :
    squareRootExternalTerminalFaceLedger R =
      ∑ z ∈ squareRootExternalTerminalFaceCarrier R,
        (booleanCubeSign z.1 : ℂ) := by
  classical
  unfold squareRootExternalTerminalFaceLedger
    squareRootExternalTerminalFaceCarrier
  rw [Finset.sum_filter]
  calc
    (∑ t ∈ admissiblePrimeFaces (R - 1),
        ∑ _p ∈ squareRootHighPrimeCofactorSet R (primeFaceProduct t),
          (booleanCubeSign t : ℂ)) =
      ∑ t ∈ admissiblePrimeFaces (R - 1),
        ∑ p ∈ Finset.Ioc R (squareRootEndpoint R),
          if p.Prime ∧ primeFaceProduct t * p ≤ squareRootEndpoint R then
            (booleanCubeSign t : ℂ)
          else 0 := by
      apply Finset.sum_congr rfl
      intro t _ht
      unfold squareRootHighPrimeCofactorSet
      rw [Finset.sum_filter]
    _ = ∑ z ∈
        (admissiblePrimeFaces (R - 1)).product
          (Finset.Ioc R (squareRootEndpoint R)),
        if z.2.Prime ∧ primeFaceProduct z.1 * z.2 ≤ squareRootEndpoint R then
          (booleanCubeSign z.1 : ℂ)
        else 0 := by
      symm
      simpa only using
        (Finset.sum_product
          (s := admissiblePrimeFaces (R - 1))
          (t := Finset.Ioc R (squareRootEndpoint R))
          (f := fun z : LowWheelExternalTerminalFacePrime =>
            if z.2.Prime ∧ primeFaceProduct z.1 * z.2 ≤ squareRootEndpoint R then
              (booleanCubeSign z.1 : ℂ)
            else 0))

/-- **External high-prime / high-prime-grid identification.**  The original
cofactor-first `T_R` is literally the flattened terminal face/high-prime grid. -/
theorem squareRootExternalHighPrime_eq_highPrimeGrid
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootTransportCofactorFirst R =
      ∑ z ∈ squareRootExternalTerminalFaceCarrier R,
        (booleanCubeSign z.1 : ℂ) := by
  rw [squareRootTransportCofactorFirst_eq_externalTerminalFaceLedger R hR,
    squareRootExternalTerminalFaceLedger_eq_carrierSum]

/-- **Exact parent split of high transport.**

`T_R = ERuniq + ERrep` on the same existing high-prime grid. -/
theorem squareRootTransport_eq_ERuniq_add_ERrep
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootTransportCofactorFirst R =
      squareRootERuniq R + squareRootERrep R := by
  rw [squareRootExternalHighPrime_eq_highPrimeGrid R hR]
  rw [squareRootExternalTerminalFaceCarrier_eq_unique_union_repeated R hR]
  rw [Finset.sum_union (squareRootExternalTerminalUnique_disjoint_repeated R)]
  rfl

/-- **Unique external parent ownership.**  The exact occurrence carrier of
`ERuniq` has at most `R` elements. -/
theorem squareRootERuniq_card_le_root
    (R : ℕ) :
    (squareRootExternalTerminalUniqueFaceCarrier R).card ≤ R :=
  squareRootExternalTerminalUniqueFaceCarrier_card_le_root R

/-- Every atom of the external terminal face ledger has unit norm. -/
private theorem norm_externalTerminalFaceAtom
    (z : LowWheelExternalTerminalFacePrime) :
    ‖(booleanCubeSign z.1 : ℂ)‖ = 1 := by
  simp [booleanCubeSign]

/-- The signed unique-parent mass is therefore bounded by its already-owned
root cardinality. -/
theorem norm_squareRootERuniq_le_root
    (R : ℕ) :
    ‖squareRootERuniq R‖ ≤ (R : ℝ) := by
  unfold squareRootERuniq
  calc
    ‖∑ z ∈ squareRootExternalTerminalUniqueFaceCarrier R,
        (booleanCubeSign z.1 : ℂ)‖ ≤
      ∑ z ∈ squareRootExternalTerminalUniqueFaceCarrier R,
        ‖(booleanCubeSign z.1 : ℂ)‖ := by
          exact norm_sum_le _ _
    _ = ∑ _z ∈ squareRootExternalTerminalUniqueFaceCarrier R, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro z _hz
      exact norm_externalTerminalFaceAtom z
    _ = ((squareRootExternalTerminalUniqueFaceCarrier R).card : ℝ) := by simp
    _ ≤ (R : ℝ) := by
      exact_mod_cast squareRootERuniq_card_le_root R

/-- Exact signed recombination of the repeated external population with the
pre-existing far survivor.  Only the seven-coordinate near strip and the
already-owned unique-parent mass remain. -/
theorem squareRootERrep_add_farSurvivor_eq_near_sub_ERuniq
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootERrep R + survivorSixteenFarUpperPrimeMass (R - 1) =
      squareRootNearPrimeTransport R - squareRootERuniq R := by
  have hsplit := squareRootTransport_eq_ERuniq_add_ERrep R (by omega)
  have hfar := squareRootTransportPrimeFirst_eq_near_sub_farSurvivor R hR
  have htransport :
      squareRootERuniq R + squareRootERrep R =
        squareRootNearPrimeTransport R -
          survivorSixteenFarUpperPrimeMass (R - 1) := by
    calc
      squareRootERuniq R + squareRootERrep R =
          squareRootTransportCofactorFirst R := hsplit.symm
      _ = squareRootTransportPrimeFirst R :=
        squareRootTransportCofactorFirst_eq_primeFirst R
      _ = squareRootNearPrimeTransport R -
          survivorSixteenFarUpperPrimeMass (R - 1) := hfar
  linear_combination htransport

/-- **Quantitative external repeated-parent closure.**

The repeated high-prime parent mass plus the already-existing far survivor is
unconditionally square-root scale:

`||ERrep + FarSurvivor_R|| <= 8 R`.
-/
theorem norm_squareRootERrep_add_farSurvivor_le_eight_root
    (R : ℕ) (hR : 56 ≤ R) :
    ‖squareRootERrep R + survivorSixteenFarUpperPrimeMass (R - 1)‖ ≤
      8 * (R : ℝ) := by
  rw [squareRootERrep_add_farSurvivor_eq_near_sub_ERuniq R hR]
  calc
    ‖squareRootNearPrimeTransport R - squareRootERuniq R‖ ≤
        ‖squareRootNearPrimeTransport R‖ + ‖squareRootERuniq R‖ :=
      norm_sub_le _ _
    _ ≤ 7 * (R : ℝ) + (R : ℝ) :=
      add_le_add (norm_squareRootNearPrimeTransport_le R hR)
        (norm_squareRootERuniq_le_root R)
    _ = 8 * (R : ℝ) := by ring

end RHLean.Proof
