import Mathlib
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.SquareRootBornPostTailLowPrimeCollapse

/-!
# The unique downward-closure failure in the born channel

Let `a` divide `b` and let `r` be a born partner of the larger cofactor `b`.
Passing from `b` down to `a` preserves

* primality and the root range of `r`;
* the roughness inequality `P+(a) < r`;
* the hyperbolic product bound `a*r <= R^2-1`.

The only condition that can fail is the birth/order condition `r <= a`.
Consequently

```text
r in BornPartnerSet(R,a)  <->  r <= a
```

under the stated upper-partner hypothesis.  Thus every reverse four-corner
born defect is exactly a first-birth crossing `a < r <= b`; no second arithmetic
obstruction is hidden in the born channel.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The largest prime factor is monotone under positive divisibility. -/
theorem canonicalLargestPrimeFactor_le_of_dvd
    {a b : ℕ} (ha : 0 < a) (hb : 1 < b) (hab : a ∣ b) :
    canonicalLargestPrimeFactor a ≤ canonicalLargestPrimeFactor b := by
  by_cases haOne : a = 1
  · subst a
    have hone : canonicalLargestPrimeFactor 1 = 1 := by
      simp [canonicalLargestPrimeFactor]
    have hpos : 0 < canonicalLargestPrimeFactor b :=
      (canonicalLargestPrimeFactor_prime hb).pos
    rw [hone]
    omega
  · have haGt : 1 < a := by omega
    have hp : (canonicalLargestPrimeFactor a).Prime :=
      canonicalLargestPrimeFactor_prime haGt
    have hpDvdA : canonicalLargestPrimeFactor a ∣ a :=
      canonicalLargestPrimeFactor_dvd haGt
    have hpDvdB : canonicalLargestPrimeFactor a ∣ b :=
      dvd_trans hpDvdA hab
    exact CanonicalGapAncestryBridge.prime_dvd_le_canonicalLargestPrimeFactor
      hb hp hpDvdB

/-- **A born partner descends through divisibility exactly until its numerical
birth threshold is crossed.** -/
theorem mem_squareRootBornPartnerSet_of_dvd_iff_order
    {R a b r : ℕ} (ha : 0 < a) (hab : a ∣ b)
    (hrUpper : r ∈ squareRootBornPartnerSet R b) :
    r ∈ squareRootBornPartnerSet R a ↔ r ≤ a := by
  rcases Finset.mem_filter.mp hrUpper with
    ⟨hrRange, hrPrime, hbRough, hrb, hbrX⟩
  have hbPos : 0 < b := lt_of_lt_of_le hrPrime.pos hrb
  have hbGt : 1 < b := lt_of_lt_of_le hrPrime.one_lt hrb
  have habLe : a ≤ b := Nat.le_of_dvd hbPos hab
  have hlpfLe :
      canonicalLargestPrimeFactor a ≤ canonicalLargestPrimeFactor b :=
    canonicalLargestPrimeFactor_le_of_dvd ha hbGt hab
  constructor
  · intro hrLower
    exact (Finset.mem_filter.mp hrLower).2.2.2.1
  · intro hra
    apply Finset.mem_filter.mpr
    refine ⟨hrRange, hrPrime, ?_, hra, ?_⟩
    · exact lt_of_le_of_lt hlpfLe hbRough
    · exact (Nat.mul_le_mul_right r habLe).trans hbrX

/-- Born partners of `b` that are not yet born at the divisor `a`. -/
def squareRootBornPartnerBirthBoundary
    (R a b : ℕ) : Finset ℕ :=
  (squareRootBornPartnerSet R b).filter fun r => a < r

@[simp] theorem mem_squareRootBornPartnerBirthBoundary
    {R a b r : ℕ} :
    r ∈ squareRootBornPartnerBirthBoundary R a b ↔
      r ∈ squareRootBornPartnerSet R b ∧ a < r := by
  simp [squareRootBornPartnerBirthBoundary]

/-- **The failed downward born partners are exactly the birth boundary.** -/
theorem squareRootBornPartnerSet_sdiff_divisor_eq_birthBoundary
    {R a b : ℕ} (ha : 0 < a) (hab : a ∣ b) :
    squareRootBornPartnerSet R b \ squareRootBornPartnerSet R a =
      squareRootBornPartnerBirthBoundary R a b := by
  ext r
  constructor
  · intro hr
    rcases Finset.mem_sdiff.mp hr with ⟨hrUpper, hrNotLower⟩
    apply mem_squareRootBornPartnerBirthBoundary.mpr
    refine ⟨hrUpper, ?_⟩
    have hiff := mem_squareRootBornPartnerSet_of_dvd_iff_order
      ha hab hrUpper
    exact Nat.lt_of_not_ge (fun hra => hrNotLower (hiff.mpr hra))
  · intro hr
    rcases mem_squareRootBornPartnerBirthBoundary.mp hr with
      ⟨hrUpper, har⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hrUpper, ?_⟩
    intro hrLower
    have hra :=
      (mem_squareRootBornPartnerSet_of_dvd_iff_order ha hab hrUpper).mp
        hrLower
    omega

/-- Multiplicative specialization used by a prime square. -/
theorem squareRootBornPartnerSet_sdiff_mul_eq_birthBoundary
    {R p a : ℕ} (_hp : 0 < p) (ha : 0 < a) :
    squareRootBornPartnerSet R (p * a) \
        squareRootBornPartnerSet R a =
      squareRootBornPartnerBirthBoundary R a (p * a) := by
  apply squareRootBornPartnerSet_sdiff_divisor_eq_birthBoundary ha
  exact ⟨p, by ring⟩

end RHLean.Proof
