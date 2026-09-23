import RHLean.Proof.LowWheelFrozenSquareResidualParentCarrier
import RHLean.Proof.SquareRootLowPrimeGoWallStripTelescope

/-!
# Geometry of the reassembled q^2 parent-product carrier

The `(q,m)` carrier produced after flattening is not an abstract incidence
space.  Every point is a genuine post-root predecessor below the literal q^2
cutoff, squarefree, and q-smooth:

`R < m`,  `q^2*m <= X_R`,  `P+(m) < q`.

This file proves that inclusion without taking a norm.  The reverse inclusion is
the next target: it amounts to showing that the first root-crossing source scale
of every such `m` is represented in the historical second-contact source-scale
set.  Keeping the two directions separate prevents that representation claim
from being smuggled into the Fubini reindex.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- The natural post-root q-smooth predecessor strip at the q^2 daughter
cutoff. -/
def lowWheelFrozenSquareResidualPostRootSmoothCarrier
    (R q : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoSmoothCofactors q
    (squareRootEndpoint R / (q * q))).filter fun m => R < m

/-- The owner coordinate occurring in the flattened parent carrier is a genuine
prime strictly below the old root; its arithmetic product lies above the root
and below the q^2 cutoff. -/
theorem lowWheelFrozenSquareResidualParentCarrier_basicData
    {R q m : ℕ}
    (hm : (q, m) ∈ lowWheelFrozenSquareResidualParentCarrier R) :
    q.Prime ∧ q < R ∧ R < m ∧
      q * q * m ≤ squareRootEndpoint R := by
  rcases Finset.mem_image.mp hm with ⟨t, ht, hkey⟩
  rcases t with ⟨A, ⟨r, d⟩⟩
  change (r, A * d) = (q, m) at hkey
  have hrq : r = q := congrArg Prod.fst hkey
  have hprod : A * d = m := congrArg Prod.snd hkey
  subst q
  subst m
  have hdata := (mem_lowWheelFrozenSquareResidualTriples).mp ht
  rcases Finset.mem_image.mp hdata.2.1 with ⟨c, hcResidual, howner⟩
  have hcFiber :
      c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber
        (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) r :=
    mem_lowWheelFrozenSourceSquareResidualOwnerFiber.mpr
      ⟨hcResidual, howner⟩
  rcases lowWheelFrozenSourceSquareResidualOwnerFiber_data hcFiber with
    ⟨hrPrime, _hpq, _hdSq, _hdRough, _hdLt, _hfactor, _hr2, _hweight⟩
  have hcPrefix := (Finset.mem_filter.mp hcResidual).1
  have hcIcc := (Finset.mem_filter.mp hcPrefix).1
  have hcBounds := Finset.mem_Icc.mp hcIcc
  have hcgt : 1 < c := by omega
  have hrDvd : r ∣ c := by
    simpa [howner] using canonicalLargestPrimeFactor_dvd hcgt
  have hrLeC : r ≤ c := Nat.le_of_dvd (by omega) hrDvd
  have hBR := lowWheelFrozenSourceScale_cutoff_lt_root hdata.1
  have hrR : r < R := hrLeC.trans_lt (hcBounds.2.trans_lt hBR)
  have hroot :=
    lowWheelFrozenSquareResidualDaughter_product_root_lt hdata.1 hdata.2.2
  have hq2 :=
    lowWheelFrozenSquareResidualDaughter_ownerSquare_mul_product_le_endpoint
      hdata.1 hdata.2.2
  exact ⟨hrPrime, hrR, hroot, hq2⟩

/-- Every flattened product is an actual active squarefree physical child. -/
theorem lowWheelFrozenSquareResidualParentCarrier_squarefree
    {R q m : ℕ}
    (hm : (q, m) ∈ lowWheelFrozenSquareResidualParentCarrier R) :
    Squarefree m := by
  rcases Finset.mem_image.mp hm with ⟨t, ht, hkey⟩
  rcases t with ⟨A, ⟨r, d⟩⟩
  change (r, A * d) = (q, m) at hkey
  have hprod : A * d = m := congrArg Prod.snd hkey
  have hdata := (mem_lowWheelFrozenSquareResidualTriples).mp ht
  rcases lowWheelFrozenSquareResidualDaughter_realizedCut hdata.1 hdata.2.2 with
    ⟨z, hz, _hzA, _hzd, hzchild⟩
  have hmActive : m ∈ orderedEulerCutActiveChildren R := by
    unfold orderedEulerCutActiveChildren
    apply Finset.mem_image.mpr
    refine ⟨z, hz, ?_⟩
    exact hzchild.trans hprod
  exact orderedEulerCutActiveChild_squarefree hmActive

/-- The true parent product has no prime factor reaching the square owner. -/
theorem lowWheelFrozenSquareResidualParentCarrier_largestPrime_lt_owner
    {R q m : ℕ}
    (hm : (q, m) ∈ lowWheelFrozenSquareResidualParentCarrier R) :
    canonicalLargestPrimeFactor m < q := by
  rcases Finset.mem_image.mp hm with ⟨t, ht, hkey⟩
  rcases t with ⟨A, ⟨r, d⟩⟩
  change (r, A * d) = (q, m) at hkey
  have hrq : r = q := congrArg Prod.fst hkey
  have hprod : A * d = m := congrArg Prod.snd hkey
  subst q
  subst m
  have hdata := (mem_lowWheelFrozenSquareResidualTriples).mp ht
  rcases Finset.mem_image.mp hdata.2.1 with ⟨c, hcResidual, howner⟩
  have hcFiber :
      c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber
        (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) r :=
    mem_lowWheelFrozenSourceSquareResidualOwnerFiber.mpr
      ⟨hcResidual, howner⟩
  rcases lowWheelFrozenSourceSquareResidualOwnerFiber_data hcFiber with
    ⟨_hrPrime, hpR, _hcSq, _hcRough, _hcLt, _hfactor, _hr2, _hweight⟩
  rcases Finset.mem_filter.mp hdata.2.2 with
    ⟨_hdIcc, _hdSq, _hdRough, hdLt⟩
  have hbasic := lowWheelFrozenSquareResidualParentCarrier_basicData
    (show (r, A * d) ∈ lowWheelFrozenSquareResidualParentCarrier R by
      exact Finset.mem_image.mpr ⟨(A, (r, d)), ht, rfl⟩)
  have hmgt : 1 < A * d := by omega
  let s := canonicalLargestPrimeFactor (A * d)
  have hsPrime : s.Prime := canonicalLargestPrimeFactor_prime hmgt
  have hsDvd : s ∣ A * d := canonicalLargestPrimeFactor_dvd hmgt
  rcases hsPrime.dvd_mul.mp hsDvd with hsA | hsd
  · have hAgt : 1 < A := by
      have hroot := lowWheelFrozenSourceScale_root_lt hdata.1
      have hrTwo := hbasic.1.two_le
      omega
    have hsLe := prime_dvd_le_canonicalLargestPrimeFactor hAgt hsPrime hsA
    exact lt_of_le_of_lt hsLe hpR
  · by_cases hdOne : d = 1
    · subst d
      exact (hsPrime.not_dvd_one hsd).elim
    · have hdgt : 1 < d := by
        have hdPos : 0 < d := by
          have hsf := lowWheelFrozenSquareResidualParentCarrier_squarefree
            (show (r, A * d) ∈ lowWheelFrozenSquareResidualParentCarrier R by
              exact Finset.mem_image.mpr ⟨(A, (r, d)), ht, rfl⟩)
          exact Nat.pos_of_ne_zero
            (fun h0 => by subst d; simpa using hsf.ne_zero)
        omega
      have hsLe := prime_dvd_le_canonicalLargestPrimeFactor hdgt hsPrime hsd
      exact lt_of_le_of_lt hsLe hdLt

/-- **One-sided carrier identification.**  The reassembled parent products are
literally a subcarrier of the post-root q-smooth predecessor strip. -/
theorem lowWheelFrozenSquareResidualParentOwner_subset_postRootSmooth
    {R q : ℕ} :
    ((lowWheelFrozenSquareResidualParentCarrier R).filter fun x => x.1 = q).image
        Prod.snd ⊆
      lowWheelFrozenSquareResidualPostRootSmoothCarrier R q := by
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨x, hx, rfl⟩
  rcases Finset.mem_filter.mp hx with ⟨hxParent, hxq⟩
  rcases x with ⟨r, n⟩
  simp only at hxq
  subst r
  have hbasic := lowWheelFrozenSquareResidualParentCarrier_basicData hxParent
  have hsq := lowWheelFrozenSquareResidualParentCarrier_squarefree hxParent
  have hlt :=
    lowWheelFrozenSquareResidualParentCarrier_largestPrime_lt_owner hxParent
  have hqqPos : 0 < q * q := Nat.mul_pos hbasic.1.pos hbasic.1.pos
  have hnUpper : n ≤ squareRootEndpoint R / (q * q) := by
    apply (Nat.le_div_iff_mul_le hqqPos).2
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbasic.2.2.2
  apply Finset.mem_filter.mpr
  refine ⟨mem_squareRootLowPrimeGoSmoothCofactors.mpr
      ⟨by omega, hnUpper, hsq, hlt⟩, hbasic.2.2.1⟩

end RHLean.Proof
