import RHLean.Proof.LowWheelFrozenSquareResidualParentSurjectivity
import RHLean.Proof.SquareRootLowPrimeGoRecursiveDescent

/-!
# The reassembled square residual is the root-floored predecessor column

Once the parent-product carrier is identified ownerwise with the complete
post-root q-smooth strip, its signed mass is just a difference of two frozen
predecessor prefixes.  This file performs that last finite Fubini step.

For `B_q = X_R/q^2`, one owner fibre has mass

`F_{q^-}(max R B_q) - F_{q^-}(R)`.

Hence the complete square residual from an earlier layer is

`- sum_q F_{q^-}(max R B_q) + sum_q F_{q^-}(R)`.

The first sum is exactly the already-compiled root-floored lower column of
`LowWheelFrozenSecondContactGlobalTelescope`; the second is now an explicit
root-anchor column.  No norm or estimate is introduced.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- One square-owner fibre of the true `(q,m)` parent carrier. -/
def lowWheelFrozenSquareResidualParentOwnerCarrier
    (R q : ℕ) : Finset (ℕ × ℕ) :=
  (lowWheelFrozenSquareResidualParentCarrier R).filter fun x => x.1 = q

private theorem lowWheelFrozenSquareResidualParentOwnerCarrier_snd_injOn
    (R q : ℕ) :
    Set.InjOn Prod.snd
      (lowWheelFrozenSquareResidualParentOwnerCarrier R q : Set (ℕ × ℕ)) := by
  intro a ha b hb hab
  have haQ := (Finset.mem_filter.mp ha).2
  have hbQ := (Finset.mem_filter.mp hb).2
  apply Prod.ext
  · exact haQ.trans hbQ.symm
  · exact hab

/-- Reindex one owner fibre by its arithmetic parent product. -/
theorem lowWheelFrozenSquareResidualParentOwnerCarrier_mass_eq_postRootSmooth
    {R q : ℕ} (hq : q.Prime) (hqR : q < R) :
    (∑ x ∈ lowWheelFrozenSquareResidualParentOwnerCarrier R q,
        canonicalMoebiusWeight x.2) =
      ∑ m ∈ lowWheelFrozenSquareResidualPostRootSmoothCarrier R q,
        canonicalMoebiusWeight m := by
  have himage :=
    lowWheelFrozenSquareResidualParentOwner_eq_postRootSmooth hq hqR
  change
    (∑ x ∈ (lowWheelFrozenSquareResidualParentCarrier R).filter
        (fun x => x.1 = q), canonicalMoebiusWeight x.2) = _
  have hsum :
      (∑ m ∈ ((lowWheelFrozenSquareResidualParentCarrier R).filter
          (fun x => x.1 = q)).image Prod.snd,
        canonicalMoebiusWeight m) =
      ∑ x ∈ (lowWheelFrozenSquareResidualParentCarrier R).filter
          (fun x => x.1 = q), canonicalMoebiusWeight x.2 := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact lowWheelFrozenSquareResidualParentOwnerCarrier_snd_injOn R q ha hb hab
  rw [himage] at hsum
  exact hsum.symm

private theorem squareRootLowPrimeGoSmoothCofactors_mono
    {q U V : ℕ} (hUV : U ≤ V) :
    squareRootLowPrimeGoSmoothCofactors q U ⊆
      squareRootLowPrimeGoSmoothCofactors q V := by
  intro m hm
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hm with
    ⟨hm1, hmU, hsq, hrough⟩
  exact mem_squareRootLowPrimeGoSmoothCofactors.mpr
    ⟨hm1, hmU.trans hUV, hsq, hrough⟩

/-- The post-root part of one frozen predecessor cube is exactly the difference
between its root-floored state and its state at the root. -/
theorem lowWheelFrozenSquareResidualPostRootSmooth_mass_eq_rootFlooredDiff
    {R q : ℕ} (hq : q.Prime) :
    (∑ m ∈ lowWheelFrozenSquareResidualPostRootSmoothCarrier R q,
        canonicalMoebiusWeight m) =
      (((frozenPrimeUniverseMass (primesUpTo (q - 1))
            (max R (squareRootEndpoint R / (q * q))) -
          frozenPrimeUniverseMass (primesUpTo (q - 1)) R : ℤ) : ℂ)) := by
  let B := squareRootEndpoint R / (q * q)
  by_cases hRB : R ≤ B
  · have hsub :
        squareRootLowPrimeGoSmoothCofactors q R ⊆
          squareRootLowPrimeGoSmoothCofactors q B :=
      squareRootLowPrimeGoSmoothCofactors_mono hRB
    have hset :
        lowWheelFrozenSquareResidualPostRootSmoothCarrier R q =
          squareRootLowPrimeGoSmoothCofactors q B \
            squareRootLowPrimeGoSmoothCofactors q R := by
      ext m
      constructor
      · intro hm
        rcases Finset.mem_filter.mp hm with ⟨hmB, hRm⟩
        apply Finset.mem_sdiff.mpr
        refine ⟨hmB, ?_⟩
        intro hmR
        have hmRle := (mem_squareRootLowPrimeGoSmoothCofactors.mp hmR).2.1
        omega
      · intro hm
        rcases Finset.mem_sdiff.mp hm with ⟨hmB, hmNotR⟩
        apply Finset.mem_filter.mpr
        refine ⟨hmB, ?_⟩
        have hmData := mem_squareRootLowPrimeGoSmoothCofactors.mp hmB
        by_contra hnot
        have hmleR : m ≤ R := Nat.le_of_not_gt hnot
        exact hmNotR (mem_squareRootLowPrimeGoSmoothCofactors.mpr
          ⟨hmData.1, hmleR, hmData.2.2.1, hmData.2.2.2⟩)
    have hBmass := frozenPrimeUniverseMass_eq_goSmoothCofactorSum
      (r := q) (Y := B) hq
    have hRmass := frozenPrimeUniverseMass_eq_goSmoothCofactorSum
      (r := q) (Y := R) hq
    have hBcast :
        (∑ m ∈ squareRootLowPrimeGoSmoothCofactors q B,
          canonicalMoebiusWeight m) =
        ((frozenPrimeUniverseMass (primesUpTo (q - 1)) B : ℤ) : ℂ) := by
      have h := congrArg (fun z : ℤ => (z : ℂ)) hBmass
      simpa [canonicalMoebiusWeight] using h.symm
    have hRcast :
        (∑ m ∈ squareRootLowPrimeGoSmoothCofactors q R,
          canonicalMoebiusWeight m) =
        ((frozenPrimeUniverseMass (primesUpTo (q - 1)) R : ℤ) : ℂ) := by
      have h := congrArg (fun z : ℤ => (z : ℂ)) hRmass
      simpa [canonicalMoebiusWeight] using h.symm
    rw [hset, max_eq_right hRB]
    calc
      (∑ m ∈ squareRootLowPrimeGoSmoothCofactors q B \
          squareRootLowPrimeGoSmoothCofactors q R,
          canonicalMoebiusWeight m) =
        (∑ m ∈ squareRootLowPrimeGoSmoothCofactors q B,
          canonicalMoebiusWeight m) -
        ∑ m ∈ squareRootLowPrimeGoSmoothCofactors q R,
          canonicalMoebiusWeight m :=
        (eq_sub_iff_add_eq).2 (Finset.sum_sdiff hsub)
      _ = ((frozenPrimeUniverseMass (primesUpTo (q - 1)) B : ℤ) : ℂ) -
          ((frozenPrimeUniverseMass (primesUpTo (q - 1)) R : ℤ) : ℂ) := by
            rw [hBcast, hRcast]
      _ = (((frozenPrimeUniverseMass (primesUpTo (q - 1)) B -
          frozenPrimeUniverseMass (primesUpTo (q - 1)) R : ℤ) : ℂ)) := by
            push_cast
            ring
  · have hBR : B < R := Nat.lt_of_not_ge hRB
    have hset : lowWheelFrozenSquareResidualPostRootSmoothCarrier R q = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      rcases Finset.mem_filter.mp hm with ⟨hmB, hRm⟩
      have hmleB := (mem_squareRootLowPrimeGoSmoothCofactors.mp hmB).2.1
      omega
    have hmax : max R B = R := max_eq_left hBR.le
    rw [hset, hmax]
    simp

/-- Every owner occurring in the true parent carrier is a prime below the old
root, so `primesUpTo (R-1)` is an exact finite indexing set for the Fubini sum. -/
theorem lowWheelFrozenSquareResidualParentCarrier_sum_eq_ownerFibers
    (R : ℕ) :
    (∑ x ∈ lowWheelFrozenSquareResidualParentCarrier R,
        canonicalMoebiusWeight x.2) =
      ∑ q ∈ primesUpTo (R - 1),
        ∑ x ∈ lowWheelFrozenSquareResidualParentOwnerCarrier R q,
          canonicalMoebiusWeight x.2 := by
  let S := lowWheelFrozenSquareResidualParentCarrier R
  let O := primesUpTo (R - 1)
  let owner : ℕ × ℕ → ℕ := Prod.fst
  have hmaps : ∀ x ∈ S, owner x ∈ O := by
    intro x hx
    rcases x with ⟨q, m⟩
    have hdata := lowWheelFrozenSquareResidualParentCarrier_basicData hx
    exact mem_primesUpTo.mpr ⟨hdata.1, Nat.le_pred_of_lt hdata.2.1⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := O) (g := owner) hmaps
    (fun x => canonicalMoebiusWeight x.2)
  have hraw :
      (∑ x ∈ S, canonicalMoebiusWeight x.2) =
        ∑ q ∈ O,
          ∑ x ∈ S with owner x = q, canonicalMoebiusWeight x.2 :=
    hfiber.symm
  change (∑ x ∈ S, canonicalMoebiusWeight x.2) =
    ∑ q ∈ O,
      ∑ x ∈ lowWheelFrozenSquareResidualParentOwnerCarrier R q,
        canonicalMoebiusWeight x.2
  rw [hraw]
  apply Finset.sum_congr rfl
  intro q hq
  rfl

/-- Root-anchor predecessor column left after the exact q^2 parent reassembly. -/
def lowWheelFrozenSquareResidualRootAnchorColumn (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1),
    frozenPrimeUniverseMass (primesUpTo (q - 1)) R

/-- Root-floored predecessor column already present in the saturated source
identity. -/
def lowWheelFrozenSquareResidualRootFlooredColumn (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1),
    frozenPrimeUniverseMass (primesUpTo (q - 1))
      (max R (squareRootEndpoint R / (q * q)))

/-- **Global column splice.**  The entire true parent-carrier mass is exactly
the root-floored predecessor column minus the common root-anchor column. -/
theorem lowWheelFrozenSquareResidualParentCarrier_mass_eq_rootFloored_sub_anchor
    (R : ℕ) :
    (∑ x ∈ lowWheelFrozenSquareResidualParentCarrier R,
        canonicalMoebiusWeight x.2) =
      (((lowWheelFrozenSquareResidualRootFlooredColumn R -
          lowWheelFrozenSquareResidualRootAnchorColumn R : ℤ) : ℂ)) := by
  rw [lowWheelFrozenSquareResidualParentCarrier_sum_eq_ownerFibers]
  unfold lowWheelFrozenSquareResidualRootFlooredColumn
    lowWheelFrozenSquareResidualRootAnchorColumn
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hqd := mem_primesUpTo.mp hq
  have hRpos : 0 < R := by
    have hqpos := hqd.1.pos
    have hqle := hqd.2
    omega
  have hqR : q < R := Nat.lt_of_le_pred hRpos hqd.2
  rw [lowWheelFrozenSquareResidualParentOwnerCarrier_mass_eq_postRootSmooth
      hqd.1 hqR,
    lowWheelFrozenSquareResidualPostRootSmooth_mass_eq_rootFlooredDiff hqd.1]
  push_cast
  rfl

/-- **Square-residual normal form after an earlier layer.**  All source-scale parity and
interval-prime bookkeeping have disappeared.  The residual is one explicit
root-anchor column minus the already-existing root-floored column. -/
theorem lowWheelFrozenSecondContactSquareResidualMass_eq_anchor_sub_rootFloored
    (R : ℕ) :
    lowWheelFrozenSecondContactSquareResidualMass R =
      (((lowWheelFrozenSquareResidualRootAnchorColumn R -
          lowWheelFrozenSquareResidualRootFlooredColumn R : ℤ) : ℂ)) := by
  rw [lowWheelFrozenSecondContactSquareResidualMass_eq_parentCarrier,
    lowWheelFrozenSquareResidualParentCarrier_mass_eq_rootFloored_sub_anchor]
  push_cast
  ring

end RHLean.Proof
