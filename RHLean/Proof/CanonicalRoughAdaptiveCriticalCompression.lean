import Mathlib
import RHLean.Proof.CanonicalRoughCriticalCorrelationContraction

/-!
# Adaptive critical rough-prime compression

The existing critical many-prime compression recurses on the current parent
carrier and books all unpaired states immediately as a survivor ledger.  The
older centered descent does the opposite: it recurses only on the survivor
carrier.  For chronological Euler cancellation neither update is ideal.  A
state unpaired at the current prime may become pairable at a later prime, while
a paired parent must remain because its pair has compressed onto it.

The natural adaptive carrier therefore deletes only the paired child copy:

```text
U' = U \ Children_p(U)
   = Parents_p(U) union Survivors_p(U).
```

On the RH-critical reciprocal correlation this gives the exact one-step law

```text
S(U) = S(U') - (1/p) S(Parents_p(U)) + Defect_p(U).
```

Thus no survivor mass is frozen.  Every still-unpaired state remains available
to later prime coordinates.  Iterating this identity yields a cumulative
signed Euler-hazard/physical-defect ledger plus one final adaptive carrier.
No norm or estimate appears in this file.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Adaptive Euler update: remove only children already compressed into their
parents.  Current survivors remain active for later prime coordinates. -/
def squareRootCanonicalRoughAdaptiveNextCarrier
    (p : ℕ) (U : Finset ℕ) : Finset ℕ :=
  U \ squareRootCanonicalRoughFreshPrimeChildrenOn p U

/-- **Carrier identity.**  The adaptive carrier consists exactly of the paired
parents together with the states that were unpaired at this coordinate. -/
theorem squareRootCanonicalRoughAdaptiveNextCarrier_eq_parents_union_survivors
    {p : ℕ} (U : Finset ℕ) (hp : p.Prime) :
    squareRootCanonicalRoughAdaptiveNextCarrier p U =
      squareRootCanonicalRoughFreshPrimeParentsOn p U ∪
        squareRootCanonicalRoughFreshPrimeSurvivorsOn p U := by
  classical
  ext n
  constructor
  · intro hn
    have hnU : n ∈ U := (Finset.mem_sdiff.mp hn).1
    have hnChild : n ∉ squareRootCanonicalRoughFreshPrimeChildrenOn p U :=
      (Finset.mem_sdiff.mp hn).2
    by_cases hnParent : n ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U
    · exact Finset.mem_union_left _ hnParent
    · apply Finset.mem_union_right
      apply Finset.mem_sdiff.mpr
      refine ⟨hnU, ?_⟩
      intro hnPaired
      rcases Finset.mem_union.mp hnPaired with hparent | hchild
      · exact hnParent hparent
      · exact hnChild hchild
  · intro hn
    rcases Finset.mem_union.mp hn with hnParent | hnSurvivor
    · apply Finset.mem_sdiff.mpr
      refine ⟨squareRootCanonicalRoughFreshPrimeParentsOn_subset p U hnParent, ?_⟩
      intro hnChild
      exact
        (Finset.disjoint_left.mp
          (squareRootCanonicalRoughFreshPrimeParentsOn_disjoint_childrenOn U hp))
          hnParent hnChild
    · have hsurv := Finset.mem_sdiff.mp hnSurvivor
      have hnU : n ∈ U := hsurv.1
      have hnNotPaired := hsurv.2
      apply Finset.mem_sdiff.mpr
      refine ⟨hnU, ?_⟩
      intro hnChild
      apply hnNotPaired
      exact Finset.mem_union_right _ hnChild

/-- Parents and current survivors are disjoint. -/
theorem squareRootCanonicalRoughFreshPrimeParentsOn_disjoint_survivorsOn
    (p : ℕ) (U : Finset ℕ) :
    Disjoint (squareRootCanonicalRoughFreshPrimeParentsOn p U)
      (squareRootCanonicalRoughFreshPrimeSurvivorsOn p U) := by
  rw [Finset.disjoint_left]
  intro n hnParent hnSurvivor
  have hnNotPaired := (Finset.mem_sdiff.mp hnSurvivor).2
  apply hnNotPaired
  exact Finset.mem_union_left _ hnParent

/-- Sum on the adaptive carrier is parent mass plus still-live survivor mass. -/
theorem sum_squareRootCanonicalRoughAdaptiveNextCarrier
    (R p : ℕ) (U : Finset ℕ) (hp : p.Prime) :
    (∑ n ∈ squareRootCanonicalRoughAdaptiveNextCarrier p U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R n) =
      (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R c) +
      (∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R n) := by
  rw [squareRootCanonicalRoughAdaptiveNextCarrier_eq_parents_union_survivors U hp,
    Finset.sum_union
      (squareRootCanonicalRoughFreshPrimeParentsOn_disjoint_survivorsOn p U)]

/-- Signed correction created by one adaptive critical Euler step.  The first
term is the exact missing `1/p` parent hazard; the second is the intact signed
threshold/top-escape/birth physical defect. -/
def squareRootCanonicalRoughAdaptiveCriticalIncrement
    (R p : ℕ) (U : Finset ℕ) : ℂ :=
  -(1 / (p : ℂ)) *
      (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R c) +
    squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U

/-- **One adaptive critical Euler step.**  Unlike the previous parent-only
recursion, no unpaired mass is frozen: it remains in `AdaptiveNextCarrier`. -/
theorem sum_squareRootCanonicalRoughCorrelationReciprocal_eq_adaptiveNext_add_increment
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (hR : 2 ≤ R) (hp : p.Prime) :
    (∑ n ∈ U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R n) =
      (∑ n ∈ squareRootCanonicalRoughAdaptiveNextCarrier p U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R n) +
      squareRootCanonicalRoughAdaptiveCriticalIncrement R p U := by
  have hone :=
    sum_squareRootCanonicalRoughCorrelationReciprocal_eq_compressed_add_defect_add_survivors
      R U hR hp
  have hnext := sum_squareRootCanonicalRoughAdaptiveNextCarrier R p U hp
  unfold squareRootCanonicalRoughAdaptiveCriticalIncrement
  rw [hnext]
  rw [canonicalRoughEulerFactor_cast_complex] at hone
  calc
    (∑ n ∈ U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R n) =
      (1 - 1 / (p : ℂ)) *
          (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
            squareRootCanonicalRoughCorrelationReciprocalSummand R c) +
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U +
        ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          squareRootCanonicalRoughCorrelationReciprocalSummand R n := hone
    _ = ((∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
            squareRootCanonicalRoughCorrelationReciprocalSummand R c) +
          ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
            squareRootCanonicalRoughCorrelationReciprocalSummand R n) +
        (-(1 / (p : ℂ)) *
          (∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
            squareRootCanonicalRoughCorrelationReciprocalSummand R c) +
          squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U) := by
      ring

/-- Adaptive carrier after a chronological prime list. -/
def squareRootCanonicalRoughAdaptiveCarrier :
    List ℕ → Finset ℕ → Finset ℕ
  | [], U => U
  | p :: ps, U =>
      squareRootCanonicalRoughAdaptiveCarrier ps
        (squareRootCanonicalRoughAdaptiveNextCarrier p U)

/-- Cumulative signed adaptive Euler corrections.  Each prime acts on the
carrier still alive at that point. -/
def squareRootCanonicalRoughAdaptiveCriticalLedger
    (R : ℕ) : List ℕ → Finset ℕ → ℂ
  | [], _U => 0
  | p :: ps, U =>
      squareRootCanonicalRoughAdaptiveCriticalIncrement R p U +
        squareRootCanonicalRoughAdaptiveCriticalLedger R ps
          (squareRootCanonicalRoughAdaptiveNextCarrier p U)

/-- **Exact adaptive many-prime descent.**  All processed child copies are
removed, all current survivors remain eligible for later primes, and the only
booked terms are the signed `1/p` parent hazards and physical defects. -/
theorem sum_squareRootCanonicalRoughCorrelationReciprocal_eq_adaptiveCarrier_add_ledger
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ) (U : Finset ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    (∑ n ∈ U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R n) =
      (∑ n ∈ squareRootCanonicalRoughAdaptiveCarrier ps U,
        squareRootCanonicalRoughCorrelationReciprocalSummand R n) +
      squareRootCanonicalRoughAdaptiveCriticalLedger R ps U := by
  induction ps generalizing U with
  | nil =>
      simp [squareRootCanonicalRoughAdaptiveCarrier,
        squareRootCanonicalRoughAdaptiveCriticalLedger]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hps : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      rw [sum_squareRootCanonicalRoughCorrelationReciprocal_eq_adaptiveNext_add_increment
        R U hR hp]
      rw [ih (U := squareRootCanonicalRoughAdaptiveNextCarrier p U) hps]
      simp only [squareRootCanonicalRoughAdaptiveCarrier,
        squareRootCanonicalRoughAdaptiveCriticalLedger]
      ring

end RHLean.Proof
