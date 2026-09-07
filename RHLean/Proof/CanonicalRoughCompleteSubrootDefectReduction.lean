import Mathlib
import RHLean.Arithmetic.PrimorialTruncatedWheelBoundary
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.CanonicalRoughCriticalDefectWindows
import RHLean.Proof.LowPrimeParentChildWindowDifference

/-!
# Complete sub-root wheel reduction of the critical defect

The signed defect windows from `CanonicalRoughCriticalDefectWindows` become much
more rigid when the current fresh-prime step sits inside a *complete* low-prime
Boolean wheel whose full product is still below the square root.

Fix a prime `p`.  An old face `u` lies in the complete cube
`(primesUpTo (p-1)).powerset`, so `c = primeFaceProduct u` is genuinely rough
below `p`.  Assume moreover that the full wheel through `p` satisfies

```text
primeFaceProduct (primesUpTo p) < R.
```

Then every fresh face obtained from `u` by adjoining any prime `q <= p` is still
below `R`.  Consequently the threshold-loss channel is literally empty.

For the remaining channels:

* every top escape is forced strictly beyond the root, `R < q`;
* every birth still has fresh child `p*c < R`, by the existing lower-root birth
  theorem.

Thus on a complete sub-root Euler cube the critical signed boundary is exactly

```text
post-root top escape - lower-root birth,
```

with no threshold term at all.  This is stronger than a support/cardinality
bound: it removes one whole defect channel and sends the other two to opposite
sides of the square-root boundary before any norm is taken.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open CanonicalRoughFreshPrimeDifference
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- The complete prime wheel through `p` still fits strictly below the root. -/
def SquareRootCanonicalRoughCompleteWheelBelowRoot (R p : ℕ) : Prop :=
  primeFaceProduct (primesUpTo p) < R

/-- Any prime face contained in the full wheel has product at most the full
wheel product. -/
theorem primeFaceProduct_le_full_primesUpTo
    {p : ℕ} {u : Finset ℕ} (hu : u ⊆ primesUpTo p) :
    primeFaceProduct u ≤ primeFaceProduct (primesUpTo p) := by
  have hle := primeFaceProduct_le_primorialWheelProduct hu (by
    intro q hq
    exact (prime_of_mem_primesUpTo hq).one_le)
  simpa [primorialWheelProduct, primeFaceProduct] using hle

/-- A partner strictly above the canonical largest prime factor of an old face
cannot already be one of that face's coordinates. -/
theorem fresh_partner_not_mem_oldFace
    {p q : ℕ} {u : Finset ℕ}
    (hu : u ∈ (primesUpTo (p - 1)).powerset) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor (primeFaceProduct u) < q) :
    q ∉ u := by
  intro hqu
  have hcpos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset hu
  have hqdvd : q ∣ primeFaceProduct u := by
    unfold primeFaceProduct
    exact Finset.dvd_prod_of_mem id hqu
  have hqleC : q ≤ primeFaceProduct u := Nat.le_of_dvd hcpos hqdvd
  have hcgt : 1 < primeFaceProduct u := hq.one_lt.trans_le hqleC
  have hqle :=
    CanonicalGapAncestryBridge.prime_dvd_le_canonicalLargestPrimeFactor
      hcgt hq hqdvd
  omega

/-- Adjoining a prime partner `q <= p` to an old face produces another face of
the complete wheel through `p`. -/
theorem insert_partner_subset_primesUpTo
    {p q : ℕ} {u : Finset ℕ}
    (hu : u ∈ (primesUpTo (p - 1)).powerset) (hq : q.Prime) (hqp : q ≤ p) :
    insert q u ⊆ primesUpTo p := by
  intro r hr
  rcases Finset.mem_insert.mp hr with rfl | hru
  · exact mem_primesUpTo.mpr ⟨hq, hqp⟩
  · have hrOld : r ∈ primesUpTo (p - 1) :=
      (Finset.mem_powerset.mp hu) hru
    rcases mem_primesUpTo.mp hrOld with ⟨hrPrime, hrLe⟩
    exact mem_primesUpTo.mpr ⟨hrPrime, hrLe.trans (Nat.sub_le p 1)⟩

/-- The actual fresh child face `insert p u` is below the root whenever the
complete wheel through `p` is. -/
theorem freshPrime_mul_oldFace_lt_root_of_completeWheel
    {R p : ℕ} {u : Finset ℕ} (hp : p.Prime)
    (hu : u ∈ (primesUpTo (p - 1)).powerset)
    (hWheel : SquareRootCanonicalRoughCompleteWheelBelowRoot R p) :
    p * primeFaceProduct u < R := by
  have hpNot : p ∉ u :=
    Finset.notMem_of_mem_powerset_of_notMem hu
      (freshPrime_not_mem_primesUpTo_pred hp)
  have hsub : insert p u ⊆ primesUpTo p :=
    insert_partner_subset_primesUpTo hu hp le_rfl
  have hprod : primeFaceProduct (insert p u) = p * primeFaceProduct u := by
    simp [primeFaceProduct, hpNot]
  have hle := primeFaceProduct_le_full_primesUpTo hsub
  rw [hprod] at hle
  exact hle.trans_lt hWheel

/-- **Complete-wheel threshold elimination.**

If the full wheel through `p` is still below `R`, no parent partner `q <= p`
can already lie above the root: `c*q` is itself a face product in the same full
wheel.  Hence the threshold-loss channel is empty. -/
theorem squareRootCanonicalRoughFreshThresholdLossBoundary_eq_empty_of_completeWheel
    {R p : ℕ} {u : Finset ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hu : u ∈ (primesUpTo (p - 1)).powerset)
    (hWheel : SquareRootCanonicalRoughCompleteWheelBelowRoot R p) :
    squareRootCanonicalRoughFreshThresholdLossBoundary
      R (primeFaceProduct u) p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hcpos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset hu
  have hfresh :=
    canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hp hu
  rcases
      (mem_squareRootCanonicalRoughFreshThresholdLossBoundary_iff
        hR hcpos hp hfresh).1 hq with
    ⟨hqPrime, hqRough, hroot, _hupper, hqp⟩
  have hqNot : q ∉ u := fresh_partner_not_mem_oldFace hu hqPrime hqRough
  have hsub : insert q u ⊆ primesUpTo p :=
    insert_partner_subset_primesUpTo hu hqPrime hqp
  have hfaceLe := primeFaceProduct_le_full_primesUpTo hsub
  have hprod : primeFaceProduct (insert q u) = q * primeFaceProduct u := by
    simp [primeFaceProduct, hqNot]
  rw [hprod] at hfaceLe
  have hcqLt : primeFaceProduct u * q < R := by
    rw [Nat.mul_comm]
    exact hfaceLe.trans_lt hWheel
  omega

/-- **Complete-wheel top escapes are post-root.**

The fresh child cofactor `p*c` is below `R`.  If a partner `q` nevertheless
pushes `(p*c)*q` through `X_R = R^2-1`, then necessarily `q > R`. -/
theorem squareRootCanonicalRoughFreshTopEscapeBoundary_partner_gt_root_of_completeWheel
    {R p q : ℕ} {u : Finset ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hu : u ∈ (primesUpTo (p - 1)).powerset)
    (hWheel : SquareRootCanonicalRoughCompleteWheelBelowRoot R p)
    (hq : q ∈ squareRootCanonicalRoughFreshTopEscapeBoundary
      R (primeFaceProduct u) p) :
    R < q := by
  have hcpos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset hu
  have hfresh :=
    canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hp hu
  have hdata :=
    (mem_squareRootCanonicalRoughFreshTopEscapeBoundary_iff
      hR hcpos hp hfresh).1 hq
  rcases hdata with
    ⟨_hqPrime, _hqRough, _hroot, _hupper, _hpq, hwall⟩
  have hpcLt : p * primeFaceProduct u < R :=
    freshPrime_mul_oldFace_lt_root_of_completeWheel hp hu hWheel
  by_contra hnot
  have hqLe : q ≤ R := Nat.le_of_not_gt hnot
  have hpcLe : p * primeFaceProduct u ≤ R - 1 := by omega
  have hprodLe : (p * primeFaceProduct u) * q ≤ (R - 1) * R :=
    Nat.mul_le_mul hpcLe hqLe
  have hboundaryLt : (R - 1) * R < R * R := by
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have hboundary : (R - 1) * R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    rw [pow_two]
    omega
  have hwallLe : (p * primeFaceProduct u) * q ≤ squareRootEndpoint R :=
    hprodLe.trans hboundary
  exact (Nat.not_lt_of_ge hwallLe) hwall

/-- Every top-escape set on a complete sub-root wheel lies entirely in the
post-root partner range. -/
theorem squareRootCanonicalRoughFreshTopEscapeBoundary_subset_postRoot_of_completeWheel
    {R p : ℕ} {u : Finset ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hu : u ∈ (primesUpTo (p - 1)).powerset)
    (hWheel : SquareRootCanonicalRoughCompleteWheelBelowRoot R p) :
    squareRootCanonicalRoughFreshTopEscapeBoundary
        R (primeFaceProduct u) p ⊆
      (Finset.Ioc R (squareRootEndpoint R / primeFaceProduct u)).filter Nat.Prime := by
  intro q hq
  have hcpos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset hu
  have hfresh :=
    canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hp hu
  have hdata :=
    (mem_squareRootCanonicalRoughFreshTopEscapeBoundary_iff
      hR hcpos hp hfresh).1 hq
  rcases hdata with
    ⟨hqPrime, _hqRough, _hroot, hupper, _hpq, _hwall⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨
      squareRootCanonicalRoughFreshTopEscapeBoundary_partner_gt_root_of_completeWheel
        hR hp hu hWheel hq, ?_⟩, hqPrime⟩
  exact (Nat.le_div_iff_mul_le hcpos).2 (by
    simpa [Nat.mul_comm] using hupper)

/-- Births remain on the opposite side of the root: their fresh child cofactor
is strictly below `R`. -/
theorem squareRootCanonicalRoughFreshBirthBoundary_child_lt_root_on_completeWheel
    {R p q : ℕ} {u : Finset ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hu : u ∈ (primesUpTo (p - 1)).powerset)
    (hq : q ∈ squareRootCanonicalRoughFreshBirthBoundary
      R (primeFaceProduct u) p) :
    p * primeFaceProduct u < R := by
  have hcpos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset hu
  have hfresh :=
    canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hp hu
  simpa [Nat.mul_comm] using
    (squareRootCanonicalRoughFreshBirthBoundary_child_lt_root
      hR hcpos hp hfresh hq)

/-- On a complete wheel below the root, the intact signed physical boundary
scalar loses its threshold channel exactly: only post-root top escape minus
lower-root birth remains. -/
theorem squareRootCanonicalRoughFreshPrimeSignedBoundaryScalar_eq_topEscape_sub_birth_of_completeWheel
    {R p : ℕ} {u : Finset ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hu : u ∈ (primesUpTo (p - 1)).powerset)
    (hWheel : SquareRootCanonicalRoughCompleteWheelBelowRoot R p) :
    squareRootCanonicalRoughFreshPrimeSignedBoundaryScalar
        R (primeFaceProduct u) p =
      ((squareRootCanonicalRoughFreshTopEscapeBoundary
          R (primeFaceProduct u) p).card : ℂ) -
        ((squareRootCanonicalRoughFreshBirthBoundary
          R (primeFaceProduct u) p).card : ℂ) := by
  unfold squareRootCanonicalRoughFreshPrimeSignedBoundaryScalar
  rw [squareRootCanonicalRoughFreshThresholdLossBoundary_eq_empty_of_completeWheel
    hR hp hu hWheel]
  simp

/-- **Critical one-edge reduction on a complete sub-root wheel.**

After scaling out the native `1/p`, the exact defect is the reciprocal Möbius
parent weight times `post-root top escape - lower-root birth`. -/
theorem natCast_mul_squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect_eq_topEscape_sub_birth_of_completeWheel
    {R p : ℕ} {u : Finset ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hu : u ∈ (primesUpTo (p - 1)).powerset)
    (hWheel : SquareRootCanonicalRoughCompleteWheelBelowRoot R p) :
    (p : ℂ) * squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect
        R (primeFaceProduct u) p =
      squareRootCanonicalRoughParityReciprocalSummand (primeFaceProduct u) *
        (((squareRootCanonicalRoughFreshTopEscapeBoundary
            R (primeFaceProduct u) p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary
            R (primeFaceProduct u) p).card : ℂ)) := by
  have hcpos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset hu
  rw [natCast_mul_squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect
    hcpos hp,
    squareRootCanonicalRoughFreshPrimeSignedBoundaryScalar_eq_topEscape_sub_birth_of_completeWheel
      hR hp hu hWheel]

end RHLean.Proof
