import Mathlib
import RHLean.Proof.CanonicalRoughAdaptiveCriticalCompression

/-!
# Weighted adaptive Euler compression

Deleting only paired children keeps future pairing opportunities alive, but with
unit coefficients that update is merely a repartition of the original sum.  To
retain genuine Euler contraction one must also transport the accumulated Euler
coefficient carried by each surviving state.

For a coefficient field `a`, one fresh-prime pair contributes

```text
a(c) v(c) + a(cp) v(cp).
```

The exact critical Euler law for `v` shows that this equals

```text
E_p a(c) v(c)
+ a(c) Defect(c,p)
+ (a(cp)-a(c)) v(cp).
```

The last term is the only obstruction to transporting the Euler coefficient
through a later pair.  It vanishes whenever the two endpoints inherited the
same history from previously processed larger primes.  This is precisely the
coherence controlled geometrically by descending displacement diamonds; a
coefficient mismatch can only be created when a commuting-square corner is
missing from the physical carrier.

This file proves the weighted one-step identity and isolates that mismatch
without any norm or estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Euler-updated coefficient field after processing `p`: paired parents inherit
the factor `1-1/p`; all other surviving states retain their old coefficient. -/
def squareRootCanonicalRoughAdaptiveNextCoefficient
    (p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U then
    (canonicalRoughEulerFactor p : ℂ) * a n
  else
    a n

/-- Signed physical defect with the coefficient of its parent attached before
any norm is taken. -/
def squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass
    (R p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
    a c * squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p

/-- Failure of coefficient coherence across the current parent/child pairs. -/
def squareRootCanonicalRoughAdaptiveCoefficientMismatchMass
    (R p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
    (a (c * p) - a c) *
      squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p)

/-- Exact predicate saying previously processed coordinates gave both endpoints
of every current `p`-pair the same accumulated coefficient. -/
def SquareRootCanonicalRoughAdaptiveCoefficientCoherent
    (p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) : Prop :=
  ∀ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
    a (c * p) = a c

/-- Coherence kills the complete mismatch mass pointwise. -/
theorem squareRootCanonicalRoughAdaptiveCoefficientMismatchMass_eq_zero_of_coherent
    {R p : ℕ} {U : Finset ℕ} {a : ℕ → ℂ}
    (hcoh : SquareRootCanonicalRoughAdaptiveCoefficientCoherent p U a) :
    squareRootCanonicalRoughAdaptiveCoefficientMismatchMass R p U a = 0 := by
  unfold squareRootCanonicalRoughAdaptiveCoefficientMismatchMass
  apply Finset.sum_eq_zero
  intro c hc
  rw [hcoh c hc]
  simp

/-- Unit coefficients are coherent at the first processed prime. -/
theorem squareRootCanonicalRoughAdaptiveCoefficientCoherent_one
    (p : ℕ) (U : Finset ℕ) :
    SquareRootCanonicalRoughAdaptiveCoefficientCoherent p U (fun _ => (1 : ℂ)) := by
  intro c _hc
  rfl

/-- Weighted mass on one finite active carrier. -/
def squareRootCanonicalRoughAdaptiveWeightedMass
    (R : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ n ∈ U, a n * squareRootCanonicalRoughCorrelationReciprocalSummand R n

/-- Reindex the weighted child population by its unique parents. -/
theorem sum_weighted_freshPrimeChildrenOn_eq_parents
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (a : ℕ → ℂ) (hp : p.Prime) :
    (∑ n ∈ squareRootCanonicalRoughFreshPrimeChildrenOn p U,
        a n * squareRootCanonicalRoughCorrelationReciprocalSummand R n) =
      ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
        a (c * p) *
          squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p) := by
  unfold squareRootCanonicalRoughFreshPrimeChildrenOn
  rw [Finset.sum_image]
  intro c _hc d _hd hcd
  exact Nat.mul_right_cancel hp.pos hcd

/-- Weighted mass of the paired population is the sum of weighted pair atoms. -/
theorem sum_weighted_freshPrimePairedOn_eq_pairs
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (a : ℕ → ℂ) (hp : p.Prime) :
    (∑ n ∈ squareRootCanonicalRoughFreshPrimePairedOn p U,
        a n * squareRootCanonicalRoughCorrelationReciprocalSummand R n) =
      ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
        (a c * squareRootCanonicalRoughCorrelationReciprocalSummand R c +
          a (c * p) *
            squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p)) := by
  unfold squareRootCanonicalRoughFreshPrimePairedOn
  rw [Finset.sum_union
    (squareRootCanonicalRoughFreshPrimeParentsOn_disjoint_childrenOn U hp),
    sum_weighted_freshPrimeChildrenOn_eq_parents R U a hp,
    ← Finset.sum_add_distrib]

/-- **Weighted local Euler law.**  The only new term beyond the transported
Euler parent and signed physical defect is the explicit coefficient mismatch. -/
theorem weighted_correlationPair_eq_eulerParent_add_defect_add_mismatch
    {R c p : ℕ} (a : ℕ → ℂ)
    (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    a c * squareRootCanonicalRoughCorrelationReciprocalSummand R c +
        a (c * p) *
          squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p) =
      squareRootCanonicalRoughAdaptiveNextCoefficient p
          ({c, c * p} : Finset ℕ) a c *
        squareRootCanonicalRoughCorrelationReciprocalSummand R c +
      a c * squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p +
      (a (c * p) - a c) *
        squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p) := by
  have hlocal :=
    squareRootCanonicalRoughCorrelationReciprocalSummand_add_mul_freshPrime
      hR hc hp hfresh
  have hparent :
      c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p ({c, c * p} : Finset ℕ) := by
    apply mem_squareRootCanonicalRoughFreshPrimeParentsOn.mpr
    simp [hc, hfresh]
  unfold squareRootCanonicalRoughAdaptiveNextCoefficient
  rw [if_pos hparent]
  calc
    a c * squareRootCanonicalRoughCorrelationReciprocalSummand R c +
        a (c * p) *
          squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p) =
      a c *
        (squareRootCanonicalRoughCorrelationReciprocalSummand R c +
          squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p)) +
        (a (c * p) - a c) *
          squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p) := by ring
    _ = a c *
        ((canonicalRoughEulerFactor p : ℂ) *
            squareRootCanonicalRoughCorrelationReciprocalSummand R c +
          squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p) +
        (a (c * p) - a c) *
          squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p) := by
      rw [hlocal]
    _ = (canonicalRoughEulerFactor p : ℂ) * a c *
          squareRootCanonicalRoughCorrelationReciprocalSummand R c +
        a c * squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p +
        (a (c * p) - a c) *
          squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p) := by ring

/-- The next weighted carrier is the Euler-updated parent mass plus unchanged
current-survivor mass. -/
theorem adaptiveNext_weightedMass_eq_eulerParents_add_survivors
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (a : ℕ → ℂ) (hp : p.Prime) :
    squareRootCanonicalRoughAdaptiveWeightedMass R
        (squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (squareRootCanonicalRoughAdaptiveNextCoefficient p U a) =
      (canonicalRoughEulerFactor p : ℂ) *
        (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          a c * squareRootCanonicalRoughCorrelationReciprocalSummand R c) +
      (∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
        a n * squareRootCanonicalRoughCorrelationReciprocalSummand R n) := by
  unfold squareRootCanonicalRoughAdaptiveWeightedMass
  rw [squareRootCanonicalRoughAdaptiveNextCarrier_eq_parents_union_survivors U hp,
    Finset.sum_union
      (squareRootCanonicalRoughFreshPrimeParentsOn_disjoint_survivorsOn p U)]
  apply congrArg₂ (· + ·)
  · calc
      (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          squareRootCanonicalRoughAdaptiveNextCoefficient p U a c *
            squareRootCanonicalRoughCorrelationReciprocalSummand R c) =
        ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          ((canonicalRoughEulerFactor p : ℂ) * a c) *
            squareRootCanonicalRoughCorrelationReciprocalSummand R c := by
          apply Finset.sum_congr rfl
          intro c hc
          simp [squareRootCanonicalRoughAdaptiveNextCoefficient, hc]
      _ = (canonicalRoughEulerFactor p : ℂ) *
          (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
            a c * squareRootCanonicalRoughCorrelationReciprocalSummand R c) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _hc
          ring
  · apply Finset.sum_congr rfl
    intro n hn
    have hnNotParent : n ∉ squareRootCanonicalRoughFreshPrimeParentsOn p U := by
      intro hnParent
      exact
        (Finset.mem_sdiff.mp hn).2
          (Finset.mem_union_left _ hnParent)
    simp [squareRootCanonicalRoughAdaptiveNextCoefficient, hnNotParent]

/-- **Exact weighted adaptive step.**  Genuine Euler contraction survives on
all coherent pairs; every failure of inherited coefficient equality is kept as
one explicit signed mismatch term. -/
theorem adaptiveWeightedMass_eq_next_add_physicalDefect_add_mismatch
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (a : ℕ → ℂ)
    (hR : 2 ≤ R) (hp : p.Prime) :
    squareRootCanonicalRoughAdaptiveWeightedMass R U a =
      squareRootCanonicalRoughAdaptiveWeightedMass R
        (squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (squareRootCanonicalRoughAdaptiveNextCoefficient p U a) +
      squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U a +
      squareRootCanonicalRoughAdaptiveCoefficientMismatchMass R p U a := by
  have hpairedSubset := squareRootCanonicalRoughFreshPrimePairedOn_subset p U
  have hsplit :
      squareRootCanonicalRoughAdaptiveWeightedMass R U a =
        (∑ n ∈ squareRootCanonicalRoughFreshPrimePairedOn p U,
          a n * squareRootCanonicalRoughCorrelationReciprocalSummand R n) +
        (∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          a n * squareRootCanonicalRoughCorrelationReciprocalSummand R n) := by
    unfold squareRootCanonicalRoughAdaptiveWeightedMass
    have hs := Finset.sum_sdiff hpairedSubset
      (f := fun n => a n * squareRootCanonicalRoughCorrelationReciprocalSummand R n)
    simpa [squareRootCanonicalRoughFreshPrimeSurvivorsOn, add_comm] using hs.symm
  rw [hsplit, sum_weighted_freshPrimePairedOn_eq_pairs R U a hp]
  have hpair :
      (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
        (a c * squareRootCanonicalRoughCorrelationReciprocalSummand R c +
          a (c * p) *
            squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p))) =
      (canonicalRoughEulerFactor p : ℂ) *
        (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
          a c * squareRootCanonicalRoughCorrelationReciprocalSummand R c) +
      squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U a +
      squareRootCanonicalRoughAdaptiveCoefficientMismatchMass R p U a := by
    unfold squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass
      squareRootCanonicalRoughAdaptiveCoefficientMismatchMass
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hc with
      ⟨_hcU, hcpos, hcrough, _hchildU⟩
    have hlocal :=
      squareRootCanonicalRoughCorrelationReciprocalSummand_add_mul_freshPrime
        hR hcpos hp hcrough
    calc
      a c * squareRootCanonicalRoughCorrelationReciprocalSummand R c +
          a (c * p) *
            squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p) =
        a c *
          (squareRootCanonicalRoughCorrelationReciprocalSummand R c +
            squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p)) +
          (a (c * p) - a c) *
            squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p) := by ring
      _ = a c *
          ((canonicalRoughEulerFactor p : ℂ) *
              squareRootCanonicalRoughCorrelationReciprocalSummand R c +
            squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p) +
          (a (c * p) - a c) *
            squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p) := by
        rw [hlocal]
      _ = (canonicalRoughEulerFactor p : ℂ) *
            (a c * squareRootCanonicalRoughCorrelationReciprocalSummand R c) +
          a c * squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p +
          (a (c * p) - a c) *
            squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p) := by ring
  rw [hpair]
  rw [adaptiveNext_weightedMass_eq_eulerParents_add_survivors R U a hp]
  ring

end RHLean.Proof