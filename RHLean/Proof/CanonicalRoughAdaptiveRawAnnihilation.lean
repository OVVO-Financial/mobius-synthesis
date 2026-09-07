import Mathlib
import RHLean.Proof.CanonicalRoughAdaptiveCriticalCompression
import RHLean.Proof.LowWheelCanonicalRepeatedMassReduction

/-!
# Zero-factor adaptive descent of the critical raw correlation

The reciprocal coordinate carries the familiar Euler factor `1 - 1/p`.  The
unweighted RH-critical correlation is stronger.  For a fresh prime `p`, the
Möbius signs of `c` and `c*p` are opposite, so the common response bulk cancels
with coefficient zero:

```text
raw(c) + raw(c*p)
  = mu(c) * (loss(c,p) - birth(c,p)).
```

To preserve future pairing opportunities we delete only the child from the
physical carrier.  Algebraically the surviving parent must then receive
coefficient zero.  If a later pair inherited equal coefficients, its entire
bulk again annihilates; if not, the exact discrepancy is retained as one signed
coefficient-mismatch atom.

This module iterates that zero-factor descent.  No norm, probability model, or
support estimate occurs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Uncentered critical atom on one cofactor. -/
def squareRootCanonicalRoughRawCorrelationSummand (R n : ℕ) : ℂ :=
  canonicalMoebiusWeight n * squareRootCanonicalRoughCofactorResponse R n

/-- The uncentered fresh-prime pair has **zero bulk coefficient**: only the
literal signed loss/birth wall survives. -/
theorem squareRootCanonicalRoughRawCorrelationSummand_add_mul_freshPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughRawCorrelationSummand R c +
        squareRootCanonicalRoughRawCorrelationSummand R (c * p) =
      canonicalMoebiusWeight c *
        (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)) := by
  unfold squareRootCanonicalRoughRawCorrelationSummand
  rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R c hR,
    squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R (c * p) hR,
    canonicalMoebiusWeight_mul_prime_eq_neg_of_rough hc hp hfresh]
  have hdiff :=
    squareRootCanonicalRoughPrimePartnerCount_sub_freshChild_eq_loss_sub_birth
      (R := R) (c := c) (p := p)
  have hdiff' :
      squareRootCanonicalRoughPrimePartnerCount R c -
          squareRootCanonicalRoughPrimePartnerCount R (c * p) =
        ((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ) := by
    simpa [Nat.mul_comm] using hdiff
  calc
    canonicalMoebiusWeight c * squareRootCanonicalRoughPrimePartnerCount R c +
        -canonicalMoebiusWeight c *
          squareRootCanonicalRoughPrimePartnerCount R (c * p) =
      canonicalMoebiusWeight c *
        (squareRootCanonicalRoughPrimePartnerCount R c -
          squareRootCanonicalRoughPrimePartnerCount R (c * p)) := by ring
    _ = canonicalMoebiusWeight c *
        (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)) := by
      rw [hdiff']

/-- Coefficient update for zero-factor cancellation: a retained parent has
already spent its current mass in the pair and therefore receives coefficient
zero; all other surviving states retain their coefficient. -/
def squareRootCanonicalRoughAdaptiveRawNextCoefficient
    (p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U then 0 else a n

/-- Weighted raw mass on a finite adaptive carrier. -/
def squareRootCanonicalRoughAdaptiveRawWeightedMass
    (R : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ n ∈ U, a n * squareRootCanonicalRoughRawCorrelationSummand R n

/-- Signed physical loss/birth charge with the inherited parent coefficient. -/
def squareRootCanonicalRoughAdaptiveRawBoundaryMass
    (R p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
    a c * canonicalMoebiusWeight c *
      (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
        ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ))

/-- Exact leakage caused by unequal inherited coefficients at a current pair. -/
def squareRootCanonicalRoughAdaptiveRawMismatchMass
    (R p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
    (a (c * p) - a c) * squareRootCanonicalRoughRawCorrelationSummand R (c * p)

/-- Weighted pair law with zero parent coefficient. -/
theorem weighted_rawPair_eq_boundary_add_mismatch
    {R c p : ℕ} (a : ℕ → ℂ)
    (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    a c * squareRootCanonicalRoughRawCorrelationSummand R c +
        a (c * p) * squareRootCanonicalRoughRawCorrelationSummand R (c * p) =
      a c * canonicalMoebiusWeight c *
          (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
            ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)) +
        (a (c * p) - a c) *
          squareRootCanonicalRoughRawCorrelationSummand R (c * p) := by
  have hpair :=
    squareRootCanonicalRoughRawCorrelationSummand_add_mul_freshPrime
      hR hc hp hfresh
  calc
    a c * squareRootCanonicalRoughRawCorrelationSummand R c +
        a (c * p) * squareRootCanonicalRoughRawCorrelationSummand R (c * p) =
      a c *
          (squareRootCanonicalRoughRawCorrelationSummand R c +
            squareRootCanonicalRoughRawCorrelationSummand R (c * p)) +
        (a (c * p) - a c) *
          squareRootCanonicalRoughRawCorrelationSummand R (c * p) := by ring
    _ = a c *
          (canonicalMoebiusWeight c *
            (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
              ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ))) +
        (a (c * p) - a c) *
          squareRootCanonicalRoughRawCorrelationSummand R (c * p) := by
      rw [hpair]
    _ = _ := by ring

/-- Reindex the weighted raw child population by its unique parents. -/
theorem sum_adaptiveRawWeighted_children_eq_parents
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (a : ℕ → ℂ) (hp : p.Prime) :
    (∑ n ∈ squareRootCanonicalRoughFreshPrimeChildrenOn p U,
        a n * squareRootCanonicalRoughRawCorrelationSummand R n) =
      ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
        a (c * p) * squareRootCanonicalRoughRawCorrelationSummand R (c * p) := by
  unfold squareRootCanonicalRoughFreshPrimeChildrenOn
  rw [Finset.sum_image]
  intro c _hc d _hd hcd
  exact Nat.mul_right_cancel hp.pos hcd

/-- On the next child-deleted carrier, zeroing all current parents leaves exactly
the unchanged weighted survivor mass. -/
theorem adaptiveRawNext_weightedMass_eq_survivors
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (a : ℕ → ℂ) (hp : p.Prime) :
    squareRootCanonicalRoughAdaptiveRawWeightedMass R
        (squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a) =
      ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
        a n * squareRootCanonicalRoughRawCorrelationSummand R n := by
  unfold squareRootCanonicalRoughAdaptiveRawWeightedMass
  rw [squareRootCanonicalRoughAdaptiveNextCarrier_eq_parents_union_survivors U hp,
    Finset.sum_union
      (squareRootCanonicalRoughFreshPrimeParentsOn_disjoint_survivorsOn p U)]
  have hparents :
      (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
        squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a c *
          squareRootCanonicalRoughRawCorrelationSummand R c) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    simp [squareRootCanonicalRoughAdaptiveRawNextCoefficient, hc]
  rw [hparents, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  have hnNotParent : n ∉ squareRootCanonicalRoughFreshPrimeParentsOn p U := by
    intro hnParent
    exact (Finset.mem_sdiff.mp hn).2 (Finset.mem_union_left _ hnParent)
  simp [squareRootCanonicalRoughAdaptiveRawNextCoefficient, hnNotParent]

/-- **Exact zero-factor adaptive step.**  The common bulk of every coherent
fresh-prime pair is gone; only the signed wall charge and the exact inherited
coefficient mismatch remain. -/
theorem adaptiveRawWeightedMass_eq_next_add_boundary_add_mismatch
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (a : ℕ → ℂ)
    (hR : 2 ≤ R) (hp : p.Prime) :
    squareRootCanonicalRoughAdaptiveRawWeightedMass R U a =
      squareRootCanonicalRoughAdaptiveRawWeightedMass R
        (squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a) +
      squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a +
      squareRootCanonicalRoughAdaptiveRawMismatchMass R p U a := by
  have hchildrenSubset := squareRootCanonicalRoughFreshPrimeChildrenOn_subset p U
  have hsplit :
      squareRootCanonicalRoughAdaptiveRawWeightedMass R U a =
        (∑ n ∈ squareRootCanonicalRoughFreshPrimeChildrenOn p U,
          a n * squareRootCanonicalRoughRawCorrelationSummand R n) +
        (∑ n ∈ U \ squareRootCanonicalRoughFreshPrimeChildrenOn p U,
          a n * squareRootCanonicalRoughRawCorrelationSummand R n) := by
    unfold squareRootCanonicalRoughAdaptiveRawWeightedMass
    have hs := Finset.sum_sdiff hchildrenSubset
      (f := fun n => a n * squareRootCanonicalRoughRawCorrelationSummand R n)
    simpa [add_comm] using hs.symm
  rw [hsplit, sum_adaptiveRawWeighted_children_eq_parents R U a hp]
  have hnextSet :
      U \ squareRootCanonicalRoughFreshPrimeChildrenOn p U =
        squareRootCanonicalRoughAdaptiveNextCarrier p U := by
    rfl
  rw [hnextSet]
  have hnext := adaptiveRawNext_weightedMass_eq_survivors R U a hp
  have hcarrierSplit :
      (∑ n ∈ squareRootCanonicalRoughAdaptiveNextCarrier p U,
        a n * squareRootCanonicalRoughRawCorrelationSummand R n) =
        (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          a c * squareRootCanonicalRoughRawCorrelationSummand R c) +
        (∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          a n * squareRootCanonicalRoughRawCorrelationSummand R n) := by
    rw [squareRootCanonicalRoughAdaptiveNextCarrier_eq_parents_union_survivors U hp,
      Finset.sum_union
        (squareRootCanonicalRoughFreshPrimeParentsOn_disjoint_survivorsOn p U)]
  rw [hcarrierSplit]
  have hpair :
      (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          a (c * p) * squareRootCanonicalRoughRawCorrelationSummand R (c * p)) +
        (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          a c * squareRootCanonicalRoughRawCorrelationSummand R c) =
      squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a +
        squareRootCanonicalRoughAdaptiveRawMismatchMass R p U a := by
    unfold squareRootCanonicalRoughAdaptiveRawBoundaryMass
      squareRootCanonicalRoughAdaptiveRawMismatchMass
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hc with
      ⟨_hcU, hcpos, hcrough, _hchildU⟩
    have hpEq := weighted_rawPair_eq_boundary_add_mismatch
      (R := R) a hR hcpos hp hcrough
    simpa [add_comm] using hpEq
  rw [hnext]
  calc
    (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
        a (c * p) * squareRootCanonicalRoughRawCorrelationSummand R (c * p)) +
        ((∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
            a c * squareRootCanonicalRoughRawCorrelationSummand R c) +
          ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
            a n * squareRootCanonicalRoughRawCorrelationSummand R n) =
      ((∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          a (c * p) * squareRootCanonicalRoughRawCorrelationSummand R (c * p)) +
        ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          a c * squareRootCanonicalRoughRawCorrelationSummand R c) +
        ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          a n * squareRootCanonicalRoughRawCorrelationSummand R n := by ring
    _ = (squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a +
          squareRootCanonicalRoughAdaptiveRawMismatchMass R p U a) +
        ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          a n * squareRootCanonicalRoughRawCorrelationSummand R n := by
      rw [hpair]
    _ = (∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          a n * squareRootCanonicalRoughRawCorrelationSummand R n) +
        squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a +
        squareRootCanonicalRoughAdaptiveRawMismatchMass R p U a := by ring

/-- Evolving zero-factor coefficient field along a chronological adaptive run. -/
def squareRootCanonicalRoughAdaptiveRawCoefficient :
    List ℕ → Finset ℕ → (ℕ → ℂ) → (ℕ → ℂ)
  | [], _U, a => a
  | p :: ps, U, a =>
      squareRootCanonicalRoughAdaptiveRawCoefficient ps
        (squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a)

/-- Cumulative signed wall-plus-mismatch ledger for zero-factor descent. -/
def squareRootCanonicalRoughAdaptiveRawLedger
    (R : ℕ) : List ℕ → Finset ℕ → (ℕ → ℂ) → ℂ
  | [], _U, _a => 0
  | p :: ps, U, a =>
      squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a +
      squareRootCanonicalRoughAdaptiveRawMismatchMass R p U a +
      squareRootCanonicalRoughAdaptiveRawLedger R ps
        (squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a)

/-- **Exact many-prime zero-factor descent.** -/
theorem adaptiveRawWeightedMass_eq_final_add_ledger
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ) (U : Finset ℕ) (a : ℕ → ℂ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    squareRootCanonicalRoughAdaptiveRawWeightedMass R U a =
      squareRootCanonicalRoughAdaptiveRawWeightedMass R
        (squareRootCanonicalRoughAdaptiveCarrier ps U)
        (squareRootCanonicalRoughAdaptiveRawCoefficient ps U a) +
      squareRootCanonicalRoughAdaptiveRawLedger R ps U a := by
  induction ps generalizing U a with
  | nil =>
      simp [squareRootCanonicalRoughAdaptiveCarrier,
        squareRootCanonicalRoughAdaptiveRawCoefficient,
        squareRootCanonicalRoughAdaptiveRawLedger]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hps : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      let U' := squareRootCanonicalRoughAdaptiveNextCarrier p U
      let a' := squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a
      have hone := adaptiveRawWeightedMass_eq_next_add_boundary_add_mismatch
        R U a hR hp
      have htail := ih (U := U') (a := a') hps
      calc
        squareRootCanonicalRoughAdaptiveRawWeightedMass R U a =
            squareRootCanonicalRoughAdaptiveRawWeightedMass R U' a' +
              squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a +
              squareRootCanonicalRoughAdaptiveRawMismatchMass R p U a := by
          simpa [U', a'] using hone
        _ = (squareRootCanonicalRoughAdaptiveRawWeightedMass R
              (squareRootCanonicalRoughAdaptiveCarrier ps U')
              (squareRootCanonicalRoughAdaptiveRawCoefficient ps U' a') +
              squareRootCanonicalRoughAdaptiveRawLedger R ps U' a') +
              squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a +
              squareRootCanonicalRoughAdaptiveRawMismatchMass R p U a := by
          rw [htail]
        _ = squareRootCanonicalRoughAdaptiveRawWeightedMass R
              (squareRootCanonicalRoughAdaptiveCarrier (p :: ps) U)
              (squareRootCanonicalRoughAdaptiveRawCoefficient (p :: ps) U a) +
              squareRootCanonicalRoughAdaptiveRawLedger R (p :: ps) U a := by
          simp only [squareRootCanonicalRoughAdaptiveCarrier,
            squareRootCanonicalRoughAdaptiveRawCoefficient,
            squareRootCanonicalRoughAdaptiveRawLedger]
          dsimp [U', a']
          ring

/-- Unit coefficients identify the initial weighted raw mass with the exact
uncentered critical correlation on any chosen carrier. -/
theorem sum_rawCorrelation_eq_adaptiveRawFinal_add_ledger
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ) (U : Finset ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    (∑ n ∈ U, squareRootCanonicalRoughRawCorrelationSummand R n) =
      squareRootCanonicalRoughAdaptiveRawWeightedMass R
        (squareRootCanonicalRoughAdaptiveCarrier ps U)
        (squareRootCanonicalRoughAdaptiveRawCoefficient ps U (fun _ => (1 : ℂ))) +
      squareRootCanonicalRoughAdaptiveRawLedger R ps U (fun _ => (1 : ℂ)) := by
  have h := adaptiveRawWeightedMass_eq_final_add_ledger
    R hR ps U (fun _ => (1 : ℂ)) hprime
  simpa [squareRootCanonicalRoughAdaptiveRawWeightedMass] using h

end RHLean.Proof