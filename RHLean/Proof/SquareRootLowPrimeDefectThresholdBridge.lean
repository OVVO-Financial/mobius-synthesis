import Mathlib
import RHLean.Arithmetic.PrimeProductCubeFrontier
import RHLean.Proof.SquareRootLowPrimeBornSquareBoundary
import RHLean.Proof.SquareRootLowPrimeHighProductBoundary

/-!
# One threshold normal form for both channel defects

The two arithmetic defect faces found in the born and high channels have the
same multiplicative normal form

```text
a <= B < p*a.
```

* For a high product defect with post-root partner `r`, the threshold is the
  reciprocal label `B = floor((R^2-1)/r)`.
* For a born birth defect with partner `r`, the threshold is `B = r-1`.

Thus both channel defects push directly into the repository's existing smooth
shell / first-failure machinery.  They are not separate error mechanisms.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A fresh-prime multiplication crosses one integer threshold. -/
def squareRootLowPrimeThresholdCrosses
    (p B a : ℕ) : Prop :=
  a ≤ B ∧ B < p * a

/-- **High product defects are reciprocal-threshold crossings.** -/
theorem mem_squareRootPostRootPrimePartnerProductBoundary_iff_thresholdCrosses
    {R p a r : ℕ} :
    r ∈ squareRootPostRootPrimePartnerProductBoundary R a (p * a) ↔
      r ∈ squareRootPostRootPrimePartnerSet R a ∧
        squareRootLowPrimeThresholdCrosses p
          (squareRootEndpoint R / r) a := by
  constructor
  · intro hr
    rcases mem_squareRootPostRootPrimePartnerProductBoundary.mp hr with
      ⟨hrLower, hcross⟩
    have hrPrime :=
      (Finset.mem_filter.mp hrLower).2.1
    have harX :=
      (Finset.mem_filter.mp hrLower).2.2
    have haDiv : a ≤ squareRootEndpoint R / r :=
      (Nat.le_div_iff_mul_le hrPrime.pos).2 harX
    have hDivCross : squareRootEndpoint R / r < p * a :=
      (Nat.div_lt_iff_lt_mul hrPrime.pos).2 <| by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcross
    exact ⟨hrLower, haDiv, hDivCross⟩
  · rintro ⟨hrLower, haDiv, hDivCross⟩
    have hrPrime :=
      (Finset.mem_filter.mp hrLower).2.1
    have hcross : squareRootEndpoint R < (p * a) * r :=
      (Nat.div_lt_iff_lt_mul hrPrime.pos).1 hDivCross
    apply mem_squareRootPostRootPrimePartnerProductBoundary.mpr
    exact ⟨hrLower, by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcross⟩

/-- **Born birth defects are predecessor-threshold crossings.** -/
theorem mem_squareRootBornPartnerBirthBoundary_iff_thresholdCrosses
    {R p a r : ℕ} :
    r ∈ squareRootBornPartnerBirthBoundary R a (p * a) ↔
      r ∈ squareRootBornPartnerSet R (p * a) ∧
        squareRootLowPrimeThresholdCrosses p (r - 1) a := by
  constructor
  · intro hr
    rcases mem_squareRootBornPartnerBirthBoundary.mp hr with
      ⟨hrUpper, har⟩
    have hrOrder := (Finset.mem_filter.mp hrUpper).2.2.2.1
    have haPred : a ≤ r - 1 := by omega
    have hPredCross : r - 1 < p * a := by omega
    exact ⟨hrUpper, haPred, hPredCross⟩
  · rintro ⟨hrUpper, haPred, _hPredCross⟩
    apply mem_squareRootBornPartnerBirthBoundary.mpr
    refine ⟨hrUpper, ?_⟩
    have hrPrime := (Finset.mem_filter.mp hrUpper).2.1
    have hrPos : 0 < r := hrPrime.pos
    omega

/-- The generic threshold predicate is exactly the geometric part of the
existing transition-face membership condition. -/
theorem squareRootLowPrimeThresholdCrosses_primeFaceProduct
    {p B : ℕ} {u : Finset ℕ} :
    squareRootLowPrimeThresholdCrosses p B (primeFaceProduct u) ↔
      primeFaceProduct u ≤ B ∧ B < p * primeFaceProduct u := by
  rfl

end RHLean.Proof
