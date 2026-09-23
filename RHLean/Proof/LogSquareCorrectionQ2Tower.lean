import Mathlib
import RHLean.Analysis.PrimeDilateTransportCompression
import RHLean.Analysis.LogWeightedPrimeExtension

/-!
# The logarithmic square correction is a q^2-and-deeper Mertens tower

The log-weighted prime-extension route separates fresh prime extensions from
square-producing collisions.  For a fixed prime `p`, a square-producing parent
is divisible by `p`; writing it as `p*d` puts the child at `p^2*d`.

The repository already proves the exact complete-prefix identity

```text
M(B) = P_p(B) - P_p(B/p),
```

where `P_p(B)` is the Mobius mass of positive cofactors through `B` that are
free of `p`.  This file records the immediate consequence needed by the current
Mellin route:

```text
P_p(B) = M(B) + P_p(B/p).
```

Taking differences between two cutoffs gives

```text
Delta P_p(A,B)
  = Delta M(A,B) + Delta P_p(A/p,B/p).
```

Thus a square-correction block whose first cutoff is already `N/p^2` is a
literal `p^2` Mertens daughter plus a remainder at `p^3`; iterating leaves only
`p^2,p^3,...` scales.  There is no first-power `N/p` term hidden in the square
correction.

No norm, PNT estimate, or RH-scale hypothesis occurs here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- Mobius mass of the positive prefix through `B` after deleting multiples of
`p`.  This is the exact `p`-free potential naturally produced by one
square-collision reindexing. -/
def canonicalPrimeFreeMobiusPrefixMass (p B : ℕ) : ℂ :=
  ∑ d ∈ primeFreeCofactorPrefix p B, canonicalMoebiusWeight d

/-- Signed `p`-free block mass between two prefix cutoffs. -/
def canonicalPrimeFreeMobiusBlockMass (p A B : ℕ) : ℂ :=
  canonicalPrimeFreeMobiusPrefixMass p B -
    canonicalPrimeFreeMobiusPrefixMass p A

/-- Signed ordinary Mobius block mass between two prefix cutoffs. -/
def canonicalMobiusBlockMass (A B : ℕ) : ℂ :=
  cofactorMobiusPrefixMass B - cofactorMobiusPrefixMass A

/-- **One exact prime-power peel.**  The `p`-free potential is the full Mobius
prefix plus the same `p`-free potential after one more division by `p`.

This is just the already-compiled arbitrary-prime cofactor compression read in
the opposite direction. -/
theorem canonicalPrimeFreeMobiusPrefixMass_eq_mertens_add_div
    (p B : ℕ) (hp : p.Prime) :
    canonicalPrimeFreeMobiusPrefixMass p B =
      cofactorMobiusPrefixMass B +
        canonicalPrimeFreeMobiusPrefixMass p (B / p) := by
  have hboundary := cofactorMobiusPrefixMass_eq_primeCofactorBoundaryMass p B hp
  have hsubset := primeFreeCofactorPrefix_div_subset p B
  have hpartition :
      (∑ d ∈ primeFreeCofactorPrefix p B \
          primeFreeCofactorPrefix p (B / p), canonicalMoebiusWeight d) +
        (∑ d ∈ primeFreeCofactorPrefix p (B / p), canonicalMoebiusWeight d) =
      ∑ d ∈ primeFreeCofactorPrefix p B, canonicalMoebiusWeight d :=
    Finset.sum_sdiff hsubset
  unfold canonicalPrimeFreeMobiusPrefixMass
  unfold primeCofactorBoundaryMass at hboundary
  unfold primeCofactorBoundary at hboundary
  rw [← hboundary] at hpartition
  exact hpartition.symm

/-- **Block form of the prime-power peel.**  Every `p`-free block is one full
Mobius block plus the same `p`-free block one scale deeper. -/
theorem canonicalPrimeFreeMobiusBlockMass_eq_mertensBlock_add_deeper
    (p A B : ℕ) (hp : p.Prime) :
    canonicalPrimeFreeMobiusBlockMass p A B =
      canonicalMobiusBlockMass A B +
        canonicalPrimeFreeMobiusBlockMass p (A / p) (B / p) := by
  unfold canonicalPrimeFreeMobiusBlockMass canonicalMobiusBlockMass
  rw [canonicalPrimeFreeMobiusPrefixMass_eq_mertens_add_div p B hp,
    canonicalPrimeFreeMobiusPrefixMass_eq_mertens_add_div p A hp]
  ring

/-- The first square-dilated specialization: a `p`-free block at scale `p^2`
is an ordinary q^2 Mertens block plus a p-free q^3 remainder. -/
theorem canonicalPrimeFreeQ2Block_eq_mertensQ2Block_add_q3Remainder
    (N p : ℕ) (hp : p.Prime) :
    canonicalPrimeFreeMobiusBlockMass p
        (N / (p * p)) ((2 * N) / (p * p)) =
      canonicalMobiusBlockMass
          (N / (p * p)) ((2 * N) / (p * p)) +
        canonicalPrimeFreeMobiusBlockMass p
          ((N / (p * p)) / p) (((2 * N) / (p * p)) / p) := by
  exact canonicalPrimeFreeMobiusBlockMass_eq_mertensBlock_add_deeper
    p (N / (p * p)) ((2 * N) / (p * p)) hp

/-- The q^3 remainder can be written with a single denominator `p^3`; this is
only floor arithmetic. -/
theorem canonicalPrimeFreeQ2Block_eq_mertensQ2Block_add_q3Remainder_pow
    (N p : ℕ) (hp : p.Prime) :
    canonicalPrimeFreeMobiusBlockMass p
        (N / (p * p)) ((2 * N) / (p * p)) =
      canonicalMobiusBlockMass
          (N / (p * p)) ((2 * N) / (p * p)) +
        canonicalPrimeFreeMobiusBlockMass p
          (N / ((p * p) * p)) ((2 * N) / ((p * p) * p)) := by
  rw [canonicalPrimeFreeQ2Block_eq_mertensQ2Block_add_q3Remainder N p hp]
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]

/-! ## Exact square-correction reindex onto q² blocks

The logarithmic renewal identity in `LogWeightedPrimeExtensionEndpoint` leaves
one explicit non-fresh correction.  The next statements put that correction on
its native square scale.  No estimate is used: for fixed `p`, the condition
`p ∣ c` writes `c = p*d`; Möbius kills the cases `p ∣ d`, and the remaining
cutoff is exactly `N/p² < d ≤ 2N/p²`.
-/

/-- Real version of the `p`-free prefix mass, matching the currency of the
logarithmic extension identities. -/
def canonicalPrimeFreeMobiusPrefixMassReal (p B : ℕ) : ℝ :=
  ∑ d ∈ primeFreeCofactorPrefix p B, moebiusReal d

/-- Real `p`-free block mass. -/
def canonicalPrimeFreeMobiusBlockMassReal (p A B : ℕ) : ℝ :=
  canonicalPrimeFreeMobiusPrefixMassReal p B -
    canonicalPrimeFreeMobiusPrefixMassReal p A

/-- Taking real parts of the existing complex prefix loses no information. -/
theorem canonicalPrimeFreeMobiusPrefixMassReal_eq_re (p B : ℕ) :
    canonicalPrimeFreeMobiusPrefixMassReal p B =
      (canonicalPrimeFreeMobiusPrefixMass p B).re := by
  unfold canonicalPrimeFreeMobiusPrefixMassReal canonicalPrimeFreeMobiusPrefixMass
  simp [canonicalMoebiusWeight, moebiusReal]

/-- Real form of arbitrary-prime cofactor compression on the divisible part. -/
theorem sum_primeDivisibleCofactorPrefix_real_eq_neg_primeFree_div
    (p B : ℕ) (hp : p.Prime) :
    (∑ c ∈ primeDivisibleCofactorPrefix p B, moebiusReal c) =
      -canonicalPrimeFreeMobiusPrefixMassReal p (B / p) := by
  have h := sum_primeDivisibleCofactorPrefix_eq_neg_primeFree_div p B hp
  have hre := congrArg Complex.re h
  unfold canonicalPrimeFreeMobiusPrefixMassReal
  simpa [canonicalMoebiusWeight, moebiusReal] using hre

/-- For one fixed prime, the non-fresh square-collision support is exactly one
block of `p`-divisible cofactors. -/
private theorem logSquarePrimeExtension_support_eq_divisibleBlock
    (N : ℕ) {p : ℕ} (hp : p.Prime) :
    (Finset.Icc 1 (2 * N)).filter
        (fun c => N < c * p ∧ c * p ≤ 2 * N ∧ p ∣ c) =
      primeDivisibleCofactorPrefix p ((2 * N) / p) \
        primeDivisibleCofactorPrefix p (N / p) := by
  ext c
  constructor
  · intro hc
    rcases Finset.mem_filter.mp hc with
      ⟨hcRange, hlow, hupp, hdiv⟩
    rcases Finset.mem_Icc.mp hcRange with ⟨hc1, _hc2N⟩
    have hcUpper : c ≤ (2 * N) / p :=
      (Nat.le_div_iff_mul_le hp.pos).2 hupp
    have hcLower : N / p < c :=
      (Nat.div_lt_iff_lt_mul hp.pos).2 hlow
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_primeDivisibleCofactorPrefix.mpr ⟨hc1, hcUpper, hdiv⟩, ?_⟩
    intro hsmall
    exact (not_lt_of_ge (mem_primeDivisibleCofactorPrefix.mp hsmall).2.1) hcLower
  · intro hc
    rcases Finset.mem_sdiff.mp hc with ⟨hbig, hsmall⟩
    rcases mem_primeDivisibleCofactorPrefix.mp hbig with
      ⟨hc1, hcUpper, hdiv⟩
    have hcLower : N / p < c := by
      by_contra hnot
      apply hsmall
      exact mem_primeDivisibleCofactorPrefix.mpr
        ⟨hc1, Nat.le_of_not_gt hnot, hdiv⟩
    have hupp : c * p ≤ 2 * N :=
      (Nat.le_div_iff_mul_le hp.pos).1 hcUpper
    have hlow : N < c * p :=
      (Nat.div_lt_iff_lt_mul hp.pos).1 hcLower
    have hc2N : c ≤ 2 * N :=
      hcUpper.trans (Nat.div_le_self (2 * N) p)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hc1, hc2N⟩, hlow, hupp, hdiv⟩

/-- The smaller divisible prefix is contained in the larger one appearing in a
fixed-prime square-collision block. -/
private theorem primeDivisibleCofactorPrefix_lower_subset_upper
    (N p : ℕ) :
    primeDivisibleCofactorPrefix p (N / p) ⊆
      primeDivisibleCofactorPrefix p ((2 * N) / p) := by
  intro c hc
  rcases mem_primeDivisibleCofactorPrefix.mp hc with ⟨hc1, hcN, hdiv⟩
  have hcut : N / p ≤ (2 * N) / p :=
    Nat.div_le_div_right (by omega : N ≤ 2 * N)
  exact mem_primeDivisibleCofactorPrefix.mpr
    ⟨hc1, hcN.trans hcut, hdiv⟩

/-- **One logarithmic square-correction fibre is a literal `p²` block.** -/
theorem logSquarePrimeExtensionFiber_eq_neg_log_mul_primeFreeQ2Block
    (N p : ℕ) (hp : p.Prime) :
    (∑ c ∈ Finset.Icc 1 (2 * N), logSquarePrimeExtensionTerm N c p) =
      -Real.log p *
        canonicalPrimeFreeMobiusBlockMassReal p
          (N / (p * p)) ((2 * N) / (p * p)) := by
  unfold logSquarePrimeExtensionTerm
  simp only [hp, true_and]
  rw [← Finset.sum_filter]
  rw [logSquarePrimeExtension_support_eq_divisibleBlock N hp]
  rw [← Finset.sum_mul]
  have hsubset := primeDivisibleCofactorPrefix_lower_subset_upper N p
  have hpartition := Finset.sum_sdiff hsubset
    (f := fun c => moebiusReal c)
  have hdiff :
      (∑ c ∈ primeDivisibleCofactorPrefix p ((2 * N) / p) \
          primeDivisibleCofactorPrefix p (N / p), moebiusReal c) =
        (∑ c ∈ primeDivisibleCofactorPrefix p ((2 * N) / p), moebiusReal c) -
          ∑ c ∈ primeDivisibleCofactorPrefix p (N / p), moebiusReal c := by
    linarith
  rw [hdiff,
    sum_primeDivisibleCofactorPrefix_real_eq_neg_primeFree_div p ((2 * N) / p) hp,
    sum_primeDivisibleCofactorPrefix_real_eq_neg_primeFree_div p (N / p) hp]
  unfold canonicalPrimeFreeMobiusBlockMassReal
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  ring

/-- **Global square correction = log-weighted q² curvature.**  The exact
non-fresh term in the Euler/log renewal is already a signed sum of `p²`-dilated
`p`-free Möbius blocks.  No first-power prime carrier remains. -/
theorem squareCorrection_eq_logWeightedPrimeFreeQ2Blocks (N : ℕ) :
    squareCorrection N =
      ∑ p ∈ Finset.Icc 2 (2 * N),
        if p.Prime then
          -Real.log p *
            canonicalPrimeFreeMobiusBlockMassReal p
              (N / (p * p)) ((2 * N) / (p * p))
        else 0 := by
  unfold squareCorrection
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _hpRange
  by_cases hp : p.Prime
  · rw [if_pos hp]
    exact logSquarePrimeExtensionFiber_eq_neg_log_mul_primeFreeQ2Block N p hp
  · rw [if_neg hp]
    unfold logSquarePrimeExtensionTerm
    simp [hp]

end RHLean.Proof
