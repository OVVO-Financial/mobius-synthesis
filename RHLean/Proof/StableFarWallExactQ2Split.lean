import RHLean.Proof.StableFarWallQ2ChildFarSlice
import RHLean.Proof.LowWheelFrozenFirstFailureBridge

/-!
# Exact q^2 split of the stable far wall

The merged low-cofactor descent decomposes every nonunit squarefree far pair
`(c,p)` by stripping `q=P+(c)` and then splitting at the second-q wall.
This file reconnects that decomposition to the original far-prime transport.

No estimate is taken.  The raw far transport is exactly

  unitFace - descendedMass - crossingMass.

The unit face is kept signed and explicit.  The descended mass is already
identified ownerwise with the far-prime slice of the q^2 child high transport.
Thus every remaining obstruction is concentrated in cancellation of the unit
face and the strict q^2-crossing population against the two already-owned
physical ledgers (internal mate and frozen top image).
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open FrozenCofactorTopBottom

attribute [local instance] Classical.propDecidable

/-- The cofactor-one face of the squarefree far-prime pair carrier. -/
def lowWheelFarPrimeUnitPairSet (R : ℕ) : Finset (ℕ × ℕ) :=
  (lowWheelFarPrimeSquarefreePairSet R).filter fun cp => cp.1 = 1

/-- Signed mass of the cofactor-one far face.  Every summand is `mu(1)=1`, but
we retain the signed sum rather than replacing it by cardinality. -/
def lowWheelFarPrimeUnitFaceMass (R : ℕ) : ℂ :=
  ∑ cp ∈ lowWheelFarPrimeUnitPairSet R,
    canonicalMoebiusWeight cp.1

/-- Signed stripped mass of the descended q^2 half. -/
def lowWheelFarPrimeQ2DescendedMass (R : ℕ) : ℂ :=
  ∑ t ∈ lowWheelFarPrimeQ2DescendedTriples R,
    canonicalMoebiusWeight t.2.1

/-- Signed stripped mass of the strict second-contact half. -/
def lowWheelFarPrimeQ2CrossingMass (R : ℕ) : ℂ :=
  ∑ t ∈ lowWheelFarPrimeQ2CrossingTriples R,
    canonicalMoebiusWeight t.2.1

/-- The squarefree far-pair carrier is the disjoint union of the unit face and
its nonunit part. -/
theorem lowWheelFarPrimeSquarefreePairSet_eq_unit_union_nonUnit
    (R : ℕ) :
    lowWheelFarPrimeSquarefreePairSet R =
      lowWheelFarPrimeUnitPairSet R ∪ lowWheelFarPrimeNonUnitPairSet R := by
  ext cp
  constructor
  · intro hcp
    have hpair := (mem_lowWheelFarPrimeSquarefreePairSet.mp hcp).1
    have hcI := (mem_lowWheelFarPrimePairSet.mp hpair).1
    have hc1 := (Finset.mem_Ico.mp hcI).1
    by_cases h1 : cp.1 = 1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hcp, h1⟩)
    · have hgt : 1 < cp.1 := by omega
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hcp, hgt⟩)
  · intro hcp
    rcases Finset.mem_union.mp hcp with hunit | hnon
    · exact (Finset.mem_filter.mp hunit).1
    · exact (Finset.mem_filter.mp hnon).1

/-- The two pieces are genuinely disjoint. -/
theorem lowWheelFarPrimeUnitPairSet_disjoint_nonUnit (R : ℕ) :
    Disjoint (lowWheelFarPrimeUnitPairSet R) (lowWheelFarPrimeNonUnitPairSet R) := by
  rw [Finset.disjoint_left]
  intro cp hu hn
  have h1 := (Finset.mem_filter.mp hu).2
  have hgt := (Finset.mem_filter.mp hn).2
  omega

/-- Exact signed partition of the squarefree far-pair mass. -/
theorem lowWheelFarPrimeSquarefreePairMass_eq_unit_add_nonUnit
    (R : ℕ) :
    lowWheelFarPrimeSquarefreePairMass R =
      lowWheelFarPrimeUnitFaceMass R +
        ∑ cp ∈ lowWheelFarPrimeNonUnitPairSet R,
          canonicalMoebiusWeight cp.1 := by
  unfold lowWheelFarPrimeSquarefreePairMass lowWheelFarPrimeUnitFaceMass
  rw [lowWheelFarPrimeSquarefreePairSet_eq_unit_union_nonUnit R,
    Finset.sum_union (lowWheelFarPrimeUnitPairSet_disjoint_nonUnit R)]

/-- The nonunit far-pair mass is the negative sum of its descended and crossing
stripped-cofactor populations. -/
theorem lowWheelFarPrimeNonUnitPairMass_eq_neg_descended_sub_crossing
    (R : ℕ) :
    (∑ cp ∈ lowWheelFarPrimeNonUnitPairSet R,
        canonicalMoebiusWeight cp.1) =
      -lowWheelFarPrimeQ2DescendedMass R -
        lowWheelFarPrimeQ2CrossingMass R := by
  have hstrip := lowWheelFarPrimeNonUnitPairMass_eq_neg_strippedMass R
  have hsplit := lowWheelFarPrimeLowCofactorTriples_sum_eq_descended_add_crossing
    R (fun t => canonicalMoebiusWeight t.2.1)
  unfold lowWheelFarPrimeQ2DescendedMass lowWheelFarPrimeQ2CrossingMass
  linear_combination hstrip - hsplit

/-- **Exact raw far-wall q^2 split.**  Before subtracting any old owned images,
the complete far-prime transport is the unit face minus the descended child
high-transport mass minus the strict second-contact crossing mass. -/
theorem squareRootFarPrimeTransport_eq_unit_sub_descended_sub_crossing
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootFarPrimeTransport R =
      lowWheelFarPrimeUnitFaceMass R -
        lowWheelFarPrimeQ2DescendedMass R -
          lowWheelFarPrimeQ2CrossingMass R := by
  rw [← lowWheelFarPrimePairMass_eq_farPrimeTransport R hR,
    ← lowWheelFarPrimeSquarefreePairMass_eq_pairMass R,
    lowWheelFarPrimeSquarefreePairMass_eq_unit_add_nonUnit R,
    lowWheelFarPrimeNonUnitPairMass_eq_neg_descended_sub_crossing R]
  ring

/-- Consequently the old hard frozen/top/far residual has one completely
explicit census.  This is the exact target for the final crossing compensation:
the only nonrecursive terms are the unit face, crossing mass, internal-mate
ledger, and frozen-top image ledger. -/
theorem lowWheelFrozenTopFarResidual_eq_unit_sub_descended_sub_crossing_sub_owned
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      lowWheelFarPrimeUnitFaceMass R -
        lowWheelFarPrimeQ2DescendedMass R -
        lowWheelFarPrimeQ2CrossingMass R -
        lowWheelCanonicalRepeatedTerminalInternalMateLedger R -
        lowWheelFrozenCofactorTopImageLedger R := by
  rw [lowWheelFrozenTopFarResidual_eq_farTransport_sub_internalMate_sub_topImage R hR,
    squareRootFarPrimeTransport_eq_unit_sub_descended_sub_crossing R (by omega)]

end RHLean.Proof
