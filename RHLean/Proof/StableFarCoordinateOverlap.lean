import RHLean.Proof.StableFarOwnedSmoothShellCompletion
import RHLean.Proof.LowWheelCanonicalDefectReduction
import RHLean.Proof.SquareRootLowPrimeFirstOwnerWallRecurrence
import RHLean.Proof.MatchedFarSurvivorBridge
import RHLean.Proof.FinalCompensatedParentReduction
import RHLean.Analysis.PrimeSieveCollapseIdentity
import RHLean.Arithmetic.SquarefreePrimeFaceSurjectivity

/-!
# Stable-far / canonical-defect coordinate overlap

The stable-far terminal products are now the complete squarefree
`R`-smooth shell `(R,R^2)`.  This module identifies that shell with the older
canonical fixed-state sector and then eliminates duplicated root coordinates.
Everything is exact and pre-energy.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Boolean-face realization of the smooth square shell. -/
def lowWheelFrozenTopFarSmoothShellFaces (R : ℕ) : Finset (Finset ℕ) :=
  frozenPrimeUniverseWindowFaces (primesUpTo R) R (squareRootEndpoint R)

/-- Prime-face product is injective on the smooth shell faces. -/
theorem lowWheelFrozenTopFarSmoothShellFaces_product_injOn (R : ℕ) :
    Set.InjOn primeFaceProduct (lowWheelFrozenTopFarSmoothShellFaces R : Set (Finset ℕ)) := by
  intro t ht u hu hprod
  have htPow := (mem_frozenPrimeUniverseWindowFaces.mp ht).1
  have huPow := (mem_frozenPrimeUniverseWindowFaces.mp hu).1
  have htSub := Finset.mem_powerset.mp htPow
  have huSub := Finset.mem_powerset.mp huPow
  exact (primeFaceProduct_eq_iff
    (fun p hp => prime_of_mem_primesUpTo (htSub hp))
    (fun p hp => prime_of_mem_primesUpTo (huSub hp))).mp hprod

/-- The Boolean-face shell and its integer smooth shell are literally the
same finite population under prime-face product. -/
theorem lowWheelFrozenTopFarSmoothShellFaces_image_eq_smoothShell
    (R : ℕ) (hR : 2 ≤ R) :
    (lowWheelFrozenTopFarSmoothShellFaces R).image primeFaceProduct =
      lowWheelFrozenTopFarSmoothShell R := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨t, ht, rfl⟩
    rcases mem_frozenPrimeUniverseWindowFaces.mp ht with ⟨htPow, hlow, hupp⟩
    have htSub := Finset.mem_powerset.mp htPow
    have hprime : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact prime_of_mem_primesUpTo (htSub hp)
    have hmu := moebius_primeFaceProduct_eq_booleanCubeSign t hprime
    have hmuNe : μ (primeFaceProduct t) ≠ 0 := by
      rw [hmu]
      simp [booleanCubeSign]
    have hsq : Squarefree (primeFaceProduct t) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuNe
    have hltR2 : primeFaceProduct t < R ^ 2 := by
      have hXlt : squareRootEndpoint R < R ^ 2 := by
        unfold squareRootEndpoint
        have hpos : 0 < R ^ 2 := by positivity
        exact Nat.pred_lt (Nat.ne_of_gt hpos)
      exact hupp.trans_lt hXlt
    have hprodPos : 0 < primeFaceProduct t :=
      primeFaceProduct_pos_of_mem_powerset htPow
    have hlpf : canonicalLargestPrimeFactor (primeFaceProduct t) ≤ R := by
      apply (canonicalLargestPrimeFactor_le_iff_forall_primeFactors_le
        (by omega : 1 ≤ R) hprodPos).2
      intro p hpFactors
      have hpData := Nat.mem_primeFactors.mp hpFactors
      have hpPrime : p.Prime := hpData.1
      have hpDiv : p ∣ primeFaceProduct t := hpData.2.1
      have hpDivProd : p ∣ t.prod id := by
        simpa [primeFaceProduct] using hpDiv
      rcases (Prime.dvd_finset_prod_iff hpPrime.prime id).mp hpDivProd with
        ⟨q, hqt, hpq⟩
      have hqPrime := hprime q hqt
      rcases hqPrime.eq_one_or_self_of_dvd p hpq with hpOne | hpEq
      · exact (hpPrime.ne_one hpOne).elim
      · subst p
        exact (mem_primesUpTo.mp (htSub hqt)).2
    exact mem_lowWheelFrozenTopFarSmoothShell.mpr ⟨hlow, hltR2, hsq, hlpf⟩
  · intro hn
    rcases mem_lowWheelFrozenTopFarSmoothShell.mp hn with
      ⟨hlow, hupp, hsq, hlpf⟩
    let t := squarefreePrimeFace n
    have hnPos : 0 < n := by omega
    have htSub : t ⊆ primesUpTo R := by
      intro p hp
      have hpLe : p ≤ R :=
        (canonicalLargestPrimeFactor_le_iff_forall_primeFactors_le
          (by omega : 1 ≤ R) hnPos).1 hlpf p hp
      exact mem_primesUpTo.mpr ⟨(Nat.mem_primeFactors.mp hp).1, hpLe⟩
    have hprod : primeFaceProduct t = n :=
      primeFaceProduct_squarefreePrimeFace hsq
    apply Finset.mem_image.mpr
    refine ⟨t, ?_, hprod⟩
    apply mem_frozenPrimeUniverseWindowFaces.mpr
    refine ⟨Finset.mem_powerset.mpr htSub, ?_, ?_⟩
    · simpa [hprod] using hlow
    · rw [hprod]
      unfold squareRootEndpoint
      exact Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hupp)

/-- The Möbius mass of its smooth terminal shell is the ordinary frozen
window mass on the old canonical low-wheel faces. -/
theorem lowWheelFrozenTopFarSmoothShell_mass_eq_window
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ n ∈ lowWheelFrozenTopFarSmoothShell R, canonicalMoebiusWeight n) =
      ((frozenPrimeUniverseWindowMass (primesUpTo R) R
        (squareRootEndpoint R) : ℤ) : ℂ) := by
  rw [← lowWheelFrozenTopFarSmoothShellFaces_image_eq_smoothShell R hR]
  unfold lowWheelFrozenTopFarSmoothShellFaces frozenPrimeUniverseWindowMass
  rw [Finset.sum_image]
  · push_cast
    apply Finset.sum_congr rfl
    intro t ht
    have htPow := (mem_frozenPrimeUniverseWindowFaces.mp ht).1
    have htSub := Finset.mem_powerset.mp htPow
    have hmu := moebius_primeFaceProduct_eq_booleanCubeSign t
      (fun p hp => prime_of_mem_primesUpTo (htSub hp))
    simp [canonicalMoebiusWeight, hmu]
  · intro a ha b hb hab
    exact lowWheelFrozenTopFarSmoothShellFaces_product_injOn R ha hb hab

/-- **First cross-coordinate collapse.**  The newly saturated stable-far smooth
terminal shell is exactly the old canonical fixed-state ledger. -/
theorem lowWheelFrozenTopFarSmoothShell_mass_eq_fixedLedger
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ n ∈ lowWheelFrozenTopFarSmoothShell R, canonicalMoebiusWeight n) =
      lowWheelCanonicalFixedLedger R := by
  rw [lowWheelFrozenTopFarSmoothShell_mass_eq_window R hR]
  rw [frozenPrimeUniverseWindowMass_eq_sub]
  · rw [lowWheelCanonicalFixedLedger_eq_frozenDifference R hR]
    push_cast
    rfl
  · have hquad : R + 1 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega

/-- The owned terminal products therefore carry exactly the canonical
fixed-state mass. -/
theorem lowWheelFrozenTopFarOwnedProducts_mass_eq_fixedLedger
    (R : ℕ) (hR : 56 ≤ R) :
    (∑ n ∈ lowWheelFrozenTopFarOwnedProducts R, canonicalMoebiusWeight n) =
      lowWheelCanonicalFixedLedger R := by
  rw [lowWheelFrozenTopFarOwnedProducts_eq_smoothShell R hR]
  exact lowWheelFrozenTopFarSmoothShell_mass_eq_fixedLedger R (by omega)

/-- The two old stable-far owned images are the fixed sector of the canonical
involution. -/
theorem lowWheelInternalMate_add_topImage_eq_fixedLedger
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelCanonicalRepeatedTerminalInternalMateLedger R +
        FrozenCofactorTopBottom.lowWheelFrozenCofactorTopImageLedger R =
      lowWheelCanonicalFixedLedger R := by
  rw [lowWheelInternalMate_add_topImage_eq_ownedProductMass R,
    lowWheelFrozenTopFarOwnedProducts_mass_eq_fixedLedger R hR]

/-- Hence the owned terminal mass is also full transport minus the canonical
defect, using the original canonical involution itself. -/
theorem lowWheelFrozenTopFarOwnedProducts_mass_eq_transport_sub_defect
    (R : ℕ) (hR : 56 ≤ R) :
    (∑ n ∈ lowWheelFrozenTopFarOwnedProducts R, canonicalMoebiusWeight n) =
      squareRootTransportCofactorFirst R - lowWheelCanonicalDefectLedger R := by
  rw [lowWheelFrozenTopFarOwnedProducts_mass_eq_fixedLedger R hR,
    squareRootTransportCofactorFirst_eq_canonicalPhysicalLedger R (by omega),
    lowWheelCanonicalPhysicalLedger_eq_fixed_add_defect]
  ring

/-- **FAR and canonical-defect coordinates collapse.**  Once its terminal
carrier is recognized as the canonical fixed sector, the far transport cancels
against the far part of the full transport. -/
theorem lowWheelFrozenTopFarResidual_eq_canonicalDefect_sub_nearTransport
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      lowWheelCanonicalDefectLedger R - squareRootNearPrimeTransport R := by
  have hfar :=
    lowWheelFrozenTopFarResidual_eq_farTransport_sub_internalMate_sub_topImage
      R hR
  have howned := lowWheelInternalMate_add_topImage_eq_fixedLedger R hR
  have htransport :
      squareRootTransportCofactorFirst R =
        lowWheelCanonicalFixedLedger R + lowWheelCanonicalDefectLedger R := by
    rw [squareRootTransportCofactorFirst_eq_canonicalPhysicalLedger R (by omega),
      lowWheelCanonicalPhysicalLedger_eq_fixed_add_defect]
  have hsplit :
      squareRootTransportCofactorFirst R =
        squareRootNearPrimeTransport R + squareRootFarPrimeTransport R := by
    rw [squareRootTransportCofactorFirst_eq_primeFirst,
      squareRootTransportPrimeFirst_eq_near_add_far R hR]
  linear_combination hfar - howned + htransport - hsplit

/-- **Previously separate root coordinates have the same signed mass.** -/
theorem lowWheelCanonicalDowncrossUniqueParentLedger_eq_squareRootERuniq
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelCanonicalDowncrossUniqueParentLedger R = squareRootERuniq R := by
  have hdef := lowWheelCanonicalDefectLedger_eq_frozenTopFarResidual_add_rootTerms R hR
  have hfar := lowWheelFrozenTopFarResidual_eq_canonicalDefect_sub_nearTransport R hR
  linear_combination -hdef - hfar

/-- Consequently the final root boundary loses two previously independent
root-scale bookkeeping terms. -/
theorem finalRootBoundary_eq_mertens_sub_nearTransport
    (R : ℕ) (hR : 56 ≤ R) :
    finalCompensatedRootBoundary R =
      mertensSummatory R - squareRootNearPrimeTransport R := by
  unfold finalCompensatedRootBoundary
  rw [lowWheelCanonicalDowncrossUniqueParentLedger_eq_squareRootERuniq R hR]
  ring

end RHLean.Proof
