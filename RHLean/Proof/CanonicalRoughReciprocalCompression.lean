import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedMassReduction
import RHLean.Analysis.NativePNTSquarePrefixContraction

/-!
# Reciprocal Euler compression on the canonical rough covariance carrier

The native square-prefix PNT proof does not delete a fresh-prime parent/child
pair.  It compresses the pair back onto the parent with the exact Euler factor
`1 - 1 / p`, leaving only an explicitly weighted defect.

This file transports that arithmetic mechanism to the RH-critical canonical
rough covariance carrier formalized in `LowWheelCanonicalRepeatedMassReduction`.
The centered covariance summand is divided by its cofactor.  For a legal fresh
prime `p`, the exact physical parent/child law then becomes

```text
v_R(c) + v_R(c*p)
  = (1 - 1/p) * v_R(c)
    + mu(c)/(c*p) * (threshold + topEscape - birth).
```

Thus the interior part receives the same Euler contraction as the native PNT
reciprocal fibre, while all failure of exact contraction is confined to the
already-formalized threshold, top-escape, and lower-root birth channels and is
suppressed by the reciprocal child cofactor `1/(c*p)`.

The final section proves that the Euler factors really accumulate.  For
ordered fresh primes `p < q`, compress the two `q`-edges of the Boolean square
first and then the remaining `p`-edge.  The base potential acquires the exact
product `(1 - 1/q) * (1 - 1/p)`, while the only remainder is the corresponding
signed reciprocal physical defects.  This is the finite two-prime model for a
chronological descending-prime compression.

No norm, independence assumption, or analytic estimate is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughFreshPrimeDifference
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Reciprocal version of the centered canonical rough covariance summand.
This is the direct analogue of the reciprocal Möbius fibre used by the native
square-prefix PNT contraction. -/
def squareRootCanonicalRoughResponseCenteredReciprocalSummand
    (R c : ℕ) : ℂ :=
  squareRootCanonicalRoughResponseCenteredSummand R c / (c : ℂ)

/-- Reciprocal-weighted physical defect left by one fresh-prime compression.
The three signed channels are exactly those of the unweighted covariance
descent; the only new feature is the child-cofactor divisor `c*p`. -/
def squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect
    (R c p : ℕ) : ℂ :=
  canonicalMoebiusWeight c / (((c * p : ℕ) : ℂ)) *
    (((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℂ) +
      ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℂ) -
      ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ))

/-- **Exact PNT-style Euler contraction on one RH-critical covariance pair.**
A legal fresh-prime parent/child pair compresses onto the reciprocal parent
with factor `1 - 1/p`.  The only remainder is the reciprocal-weighted physical
threshold/top-escape/birth defect. -/
theorem squareRootCanonicalRoughResponseCenteredReciprocalSummand_add_mul_freshPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
        squareRootCanonicalRoughResponseCenteredReciprocalSummand R (c * p) =
      (1 - 1 / (p : ℂ)) *
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p := by
  let D : ℂ :=
    ((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℂ) +
      ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℂ) -
      ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)
  have hpair :
      squareRootCanonicalRoughResponseCenteredSummand R c +
          squareRootCanonicalRoughResponseCenteredSummand R (c * p) =
        canonicalMoebiusWeight c * D := by
    simpa [D] using
      (squareRootCanonicalRoughResponseCenteredSummand_add_mul_freshPrime_eq_threshold_add_topEscape_sub_birth
        hR hc hp hfresh)
  have hchild :
      squareRootCanonicalRoughResponseCenteredSummand R (c * p) =
        canonicalMoebiusWeight c * D -
          squareRootCanonicalRoughResponseCenteredSummand R c := by
    calc
      squareRootCanonicalRoughResponseCenteredSummand R (c * p) =
          (squareRootCanonicalRoughResponseCenteredSummand R c +
              squareRootCanonicalRoughResponseCenteredSummand R (c * p)) -
            squareRootCanonicalRoughResponseCenteredSummand R c := by ring
      _ = canonicalMoebiusWeight c * D -
            squareRootCanonicalRoughResponseCenteredSummand R c := by rw [hpair]
  have hc0 : (c : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hc)
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  unfold squareRootCanonicalRoughResponseCenteredReciprocalSummand
    squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect
  rw [hchild]
  change
    squareRootCanonicalRoughResponseCenteredSummand R c / (c : ℂ) +
        (canonicalMoebiusWeight c * D -
            squareRootCanonicalRoughResponseCenteredSummand R c) /
          (((c * p : ℕ) : ℂ)) =
      (1 - 1 / (p : ℂ)) *
          (squareRootCanonicalRoughResponseCenteredSummand R c / (c : ℂ)) +
        canonicalMoebiusWeight c / (((c * p : ℕ) : ℂ)) * D
  push_cast
  field_simp [hc0, hp0]
  ring

/-- If none of the three physical boundary channels fires, the covariance pair
obeys the pure native-PNT Euler contraction with no remainder. -/
theorem squareRootCanonicalRoughResponseCenteredReciprocalSummand_add_mul_freshPrime_eq_eulerContraction
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p)
    (hthreshold : squareRootCanonicalRoughFreshThresholdLossBoundary R c p = ∅)
    (htop : squareRootCanonicalRoughFreshTopEscapeBoundary R c p = ∅)
    (hbirth : squareRootCanonicalRoughFreshBirthBoundary R c p = ∅) :
    squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
        squareRootCanonicalRoughResponseCenteredReciprocalSummand R (c * p) =
      (1 - 1 / (p : ℂ)) *
        squareRootCanonicalRoughResponseCenteredReciprocalSummand R c := by
  rw [squareRootCanonicalRoughResponseCenteredReciprocalSummand_add_mul_freshPrime
    hR hc hp hfresh]
  simp [squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect,
    hthreshold, htop, hbirth]

/-- Once the child has reached the root, the birth channel vanishes from the
reciprocal compression law.  The only defects left at the same root are the
order threshold and genuine top escape. -/
theorem squareRootCanonicalRoughResponseCenteredReciprocalSummand_add_mul_freshPrime_of_root_reached
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hroot : R ≤ p * c) :
    squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
        squareRootCanonicalRoughResponseCenteredReciprocalSummand R (c * p) =
      (1 - 1 / (p : ℂ)) *
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
        canonicalMoebiusWeight c / (((c * p : ℕ) : ℂ)) *
          (((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℂ) +
            ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℂ)) := by
  rw [squareRootCanonicalRoughResponseCenteredReciprocalSummand_add_mul_freshPrime
    hR hc hp hfresh]
  unfold squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect
  rw [squareRootCanonicalRoughFreshBirthBoundary_eq_empty_of_root_reached
    hR hc hp hfresh hroot]
  simp

/-- Contracted reciprocal parent mass for all legal parents of one fresh prime
on an arbitrary active carrier. -/
def squareRootCanonicalRoughFreshPrimeReciprocalCompressedMass
    (R p : ℕ) (U : Finset ℕ) : ℂ :=
  ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
    (1 - 1 / (p : ℂ)) *
      squareRootCanonicalRoughResponseCenteredReciprocalSummand R c

/-- Aggregate reciprocal physical defect for one fresh prime on an arbitrary
active carrier. -/
def squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass
    (R p : ℕ) (U : Finset ℕ) : ℂ :=
  ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
    squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p

/-- The whole paired population compresses exactly into contracted parent mass
plus reciprocal-weighted physical defect.  This is the carrier-level analogue
of the native PNT reciprocal-fibre contraction. -/
theorem sum_squareRootCanonicalRoughFreshPrimePairedOn_reciprocal_eq_compressed_add_defect
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (hR : 2 ≤ R) (hp : p.Prime) :
    (∑ n ∈ squareRootCanonicalRoughFreshPrimePairedOn p U,
        squareRootCanonicalRoughResponseCenteredReciprocalSummand R n) =
      squareRootCanonicalRoughFreshPrimeReciprocalCompressedMass R p U +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U := by
  unfold squareRootCanonicalRoughFreshPrimePairedOn
  rw [Finset.sum_union
    (squareRootCanonicalRoughFreshPrimeParentsOn_disjoint_childrenOn U hp)]
  unfold squareRootCanonicalRoughFreshPrimeChildrenOn
  rw [Finset.sum_image]
  · rw [← Finset.sum_add_distrib]
    calc
      (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          (squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
            squareRootCanonicalRoughResponseCenteredReciprocalSummand R (c * p))) =
        ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          ((1 - 1 / (p : ℂ)) *
              squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
            squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p) := by
        apply Finset.sum_congr rfl
        intro c hcParent
        rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
          ⟨_hcU, hcpos, hcrough, _hcchild⟩
        exact
          squareRootCanonicalRoughResponseCenteredReciprocalSummand_add_mul_freshPrime
            hR hcpos hp hcrough
      _ = squareRootCanonicalRoughFreshPrimeReciprocalCompressedMass R p U +
          squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U := by
        rw [Finset.sum_add_distrib]
        rfl
  · intro a _ha b _hb hab
    exact Nat.mul_right_cancel hp.pos hab

/-- **One exact reciprocal Euler-compression step on the full active carrier.**
The original reciprocal covariance potential is the contracted parent mass,
plus the reciprocal physical defect, plus the still-unpaired reciprocal
survivor mass.  Unlike pair-and-delete, the paired contribution is retained in
its compressed parent coordinate. -/
theorem sum_squareRootCanonicalRoughResponseCenteredReciprocal_eq_compressed_add_defect_add_survivors
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (hR : 2 ≤ R) (hp : p.Prime) :
    (∑ n ∈ U,
        squareRootCanonicalRoughResponseCenteredReciprocalSummand R n) =
      squareRootCanonicalRoughFreshPrimeReciprocalCompressedMass R p U +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U +
        ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R n := by
  have hsub := squareRootCanonicalRoughFreshPrimePairedOn_subset p U
  have hsplit :
      (∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R n) +
        (∑ n ∈ squareRootCanonicalRoughFreshPrimePairedOn p U,
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R n) =
        ∑ n ∈ U,
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R n := by
    simpa [squareRootCanonicalRoughFreshPrimeSurvivorsOn] using
      (Finset.sum_sdiff hsub
        (f := squareRootCanonicalRoughResponseCenteredReciprocalSummand R))
  rw [sum_squareRootCanonicalRoughFreshPrimePairedOn_reciprocal_eq_compressed_add_defect
    R U hR hp] at hsplit
  calc
    (∑ n ∈ U,
        squareRootCanonicalRoughResponseCenteredReciprocalSummand R n) =
      (∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R n) +
        (squareRootCanonicalRoughFreshPrimeReciprocalCompressedMass R p U +
          squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U) :=
      hsplit.symm
    _ = squareRootCanonicalRoughFreshPrimeReciprocalCompressedMass R p U +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U +
        ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R n := by ring

/-! ## Accumulation of Euler factors on a descending two-prime square -/

/-- **Two-prime Euler compression.**  Let `p < q` be successive fresh prime
coordinates above the canonical largest prime of `c`.  Compressing the two
`q`-edges first and then the remaining `p`-edge produces the exact product
`(1 - 1/q) * (1 - 1/p)` on the base reciprocal covariance potential.

All departure from the pure Euler product is explicit: the `p`-defect is itself
carried through the later `q` contraction, and the two `q`-edge defects are
added without taking norms.  This is the finite Boolean-square mechanism by
which PNT-style contraction can accumulate on the RH-critical carrier. -/
theorem squareRootCanonicalRoughResponseCenteredReciprocal_twoPrime_descending_compression
    {R c p q : ℕ} (hR : 2 ≤ R) (hc : 0 < c)
    (hp : p.Prime) (hq : q.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hpq : p < q) :
    (squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
        squareRootCanonicalRoughResponseCenteredReciprocalSummand R (c * q)) +
      (squareRootCanonicalRoughResponseCenteredReciprocalSummand R (c * p) +
        squareRootCanonicalRoughResponseCenteredReciprocalSummand R ((c * p) * q)) =
      (1 - 1 / (q : ℂ)) * (1 - 1 / (p : ℂ)) *
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
        (1 - 1 / (q : ℂ)) *
          squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c q +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R (c * p) q := by
  have hfreshq : canonicalLargestPrimeFactor c < q := hfresh.trans hpq
  have hcp : 0 < c * p := Nat.mul_pos hc hp.pos
  have hlpfcp : canonicalLargestPrimeFactor (c * p) = p :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hp hfresh
  have hcpfreshq : canonicalLargestPrimeFactor (c * p) < q := by
    rw [hlpfcp]
    exact hpq
  have hqBase :=
    squareRootCanonicalRoughResponseCenteredReciprocalSummand_add_mul_freshPrime
      hR hc hq hfreshq
  have hqChild :=
    squareRootCanonicalRoughResponseCenteredReciprocalSummand_add_mul_freshPrime
      hR hcp hq hcpfreshq
  have hpBase :=
    squareRootCanonicalRoughResponseCenteredReciprocalSummand_add_mul_freshPrime
      hR hc hp hfresh
  calc
    (squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
        squareRootCanonicalRoughResponseCenteredReciprocalSummand R (c * q)) +
      (squareRootCanonicalRoughResponseCenteredReciprocalSummand R (c * p) +
        squareRootCanonicalRoughResponseCenteredReciprocalSummand R ((c * p) * q)) =
      ((1 - 1 / (q : ℂ)) *
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c q) +
      ((1 - 1 / (q : ℂ)) *
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R (c * p) +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R (c * p) q) := by
          rw [hqBase, hqChild]
    _ = (1 - 1 / (q : ℂ)) *
          (squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
            squareRootCanonicalRoughResponseCenteredReciprocalSummand R (c * p)) +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c q +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R (c * p) q := by
          ring
    _ = (1 - 1 / (q : ℂ)) *
          ((1 - 1 / (p : ℂ)) *
              squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
            squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p) +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c q +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R (c * p) q := by
          rw [hpBase]
    _ = (1 - 1 / (q : ℂ)) * (1 - 1 / (p : ℂ)) *
          squareRootCanonicalRoughResponseCenteredReciprocalSummand R c +
        (1 - 1 / (q : ℂ)) *
          squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c q +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R (c * p) q := by
          ring

end RHLean.Proof
