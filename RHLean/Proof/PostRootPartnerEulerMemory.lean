import Mathlib
import RHLean.Proof.PostRootPartnerReciprocalCompression
import RHLean.Proof.FrozenTopFarAdaptiveRawBridge
import RHLean.Proof.TerminalMertensReduction

/-!
# Euler retention of the post-root signed boundary

The previous module puts the partner column on the reciprocal compression
carrier and proves the exact scaled Stokes identity.  This file adds two exact
layers before any norm is taken.

First, a complete descending prime schedule leaves no final raw mass.  Every
cofactor with nonzero rough response has an actual prime partner `q`; when that
partner is processed, the cofactor is a literal parent, its zero-factor
coefficient is killed, and that zero persists through the remaining schedule.
Thus the frozen/top/far residual is exactly its signed chronological ledger plus
the already root-scale correction.

Second, compare the two exact evolutions of the same current state:

* the zero-factor raw/Othello step, which leaves the signed raw boundary `B_p`;
* the cofactor-weighted reciprocal Euler step, whose defect `D_p` satisfies
  `p * D_p = B_p`.

On a complete descending prefix both coefficient-mismatch ledgers vanish.
Subtracting the two step identities gives the exact memory law

```text
p * (EulerNext - RawNext) = (p - 1) * B_p.
```

Thus the signed boundary is not discarded when one changes coordinates.  It is
transported to the difference of the next states with exactly the Euler factor
`1 - 1/p`.

No norm or asymptotic estimate is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-! ## Complete descending schedules kill the final raw mass -/

/-- A schedule contains every prime that could occur below the square endpoint,
and each such prime occurs after a prefix consisting only of strictly larger
prime coordinates.  This is exactly the structural property needed by the
zero-factor parent kill; no quantitative statement is included. -/
def SquareRootCanonicalRoughCompleteDescendingSchedule
    (R : ℕ) (ps : List ℕ) : Prop :=
  (∀ p ∈ ps, p.Prime) ∧
    ∀ q : ℕ, q.Prime → q ≤ squareRootEndpoint R →
      ∃ pre post,
        ps = pre ++ q :: post ∧
          (∀ r ∈ pre, r.Prime) ∧
          (∀ r ∈ pre, q < r)

/-- Every cofactor carrying nonzero raw rough correlation is killed somewhere
in a complete descending schedule. -/
theorem rawCoefficient_eq_zero_of_nonzero_rawCorrelation_completeSchedule
    (R : ℕ) (ps : List ℕ)
    (hR : 2 ≤ R)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps)
    {n : ℕ}
    (hnFinal : n ∈ squareRootCanonicalRoughAdaptiveCarrier ps
      (Finset.Icc 1 (squareRootEndpoint R)))
    (hraw : squareRootCanonicalRoughRawCorrelationSummand R n ≠ 0) :
    squareRootCanonicalRoughAdaptiveRawCoefficient ps
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) n = 0 := by
  let U0 : Finset ℕ := Finset.Icc 1 (squareRootEndpoint R)
  have hnU0 : n ∈ U0 :=
    squareRootCanonicalRoughAdaptiveCarrier_subset ps U0 hnFinal
  have hnRange := Finset.mem_Icc.mp hnU0
  have hnpos : 0 < n := by omega

  have hresponse : squareRootCanonicalRoughCofactorResponse R n ≠ 0 := by
    intro hzero
    apply hraw
    simp [squareRootCanonicalRoughRawCorrelationSummand, hzero]

  have hpartners : (squareRootCanonicalRoughPrimePartnerSet R n).Nonempty := by
    by_contra hempty
    have hset : squareRootCanonicalRoughPrimePartnerSet R n = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    apply hresponse
    rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R n hR,
      squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card R n, hset]
    simp

  rcases hpartners with ⟨q, hqSet⟩
  rcases (mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hnpos).mp hqSet with
    ⟨hqPrime, hrough, _hroot, hupper⟩
  have hqleProd : q ≤ n * q := by
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right q hnpos
  have hqUpper : q ≤ squareRootEndpoint R := hqleProd.trans hupper
  rcases hsched.2 q hqPrime hqUpper with
    ⟨pre, post, hsplit, hprePrime, hpreLarger⟩

  have hnPre : n ∈ squareRootCanonicalRoughAdaptiveCarrier pre U0 := by
    apply mem_adaptiveCarrier_of_all_larger_primes pre hnU0 hprePrime
    intro r hr
    exact hrough.trans (hpreLarger r hr)

  have hnqPos : 0 < n * q := Nat.mul_pos hnpos hqPrime.pos
  have hnqU0 : n * q ∈ U0 := by
    apply Finset.mem_Icc.mpr
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnqPos), hupper⟩
  have hlpfNQ : canonicalLargestPrimeFactor (n * q) = q :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough hnpos hqPrime hrough
  have hnqPre : n * q ∈ squareRootCanonicalRoughAdaptiveCarrier pre U0 := by
    apply mem_adaptiveCarrier_of_all_larger_primes pre hnqU0 hprePrime
    intro r hr
    rw [hlpfNQ]
    exact hpreLarger r hr

  have hnParent :
      n ∈ squareRootCanonicalRoughFreshPrimeParentsOn q
        (squareRootCanonicalRoughAdaptiveCarrier pre U0) := by
    apply mem_squareRootCanonicalRoughFreshPrimeParentsOn.mpr
    exact ⟨hnPre, hnpos, hrough, hnqPre⟩

  rw [hsplit]
  exact squareRootCanonicalRoughAdaptiveRawCoefficient_eq_zero_of_parent_at_split
    pre post U0 (fun _ => (1 : ℂ)) hnParent

/-- **Complete descending schedules have zero final raw mass.** -/
theorem adaptiveRawFinalMass_eq_zero_of_completeDescendingSchedule
    (R : ℕ) (ps : List ℕ)
    (hR : 2 ≤ R)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    squareRootCanonicalRoughAdaptiveRawWeightedMass R
        (squareRootCanonicalRoughAdaptiveCarrier ps
          (Finset.Icc 1 (squareRootEndpoint R)))
        (squareRootCanonicalRoughAdaptiveRawCoefficient ps
          (Finset.Icc 1 (squareRootEndpoint R))
          (fun _ => (1 : ℂ))) = 0 := by
  unfold squareRootCanonicalRoughAdaptiveRawWeightedMass
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hraw : squareRootCanonicalRoughRawCorrelationSummand R n = 0
  · simp [hraw]
  · have hcoef :=
      rawCoefficient_eq_zero_of_nonzero_rawCorrelation_completeSchedule
        R ps hR hsched hn hraw
    rw [hcoef]
    simp

/-- On a complete descending schedule the frozen/top/far residual has no final
adaptive raw remainder: it is exactly the signed chronological ledger plus the
explicit root-scale correction. -/
theorem lowWheelFrozenTopFarResidual_eq_rawLedger_add_rootCorrection_of_completeSchedule
    (R : ℕ) (hR : 56 ≤ R)
    (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    lowWheelFrozenTopFarResidual R =
      squareRootCanonicalRoughAdaptiveRawLedger R ps
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) +
      frozenTopFarRoughRootCorrection R := by
  have hprime := hsched.1
  have hbridge :=
    lowWheelFrozenTopFarResidual_eq_adaptiveRawFinal_add_ledger_add_rootCorrection
      R hR ps hprime
  have hfinal :=
    adaptiveRawFinalMass_eq_zero_of_completeDescendingSchedule
      R ps (by omega) hsched
  rw [hfinal, zero_add] at hbridge
  exact hbridge

/-! ## Exact Euler retention of each signed boundary -/

/-- **Exact Euler memory law.**  On the actual evolved raw chronology, the
cofactor-weighted reciprocal next state and the zero-factor raw next state
differ by exactly the retained fraction `1 - 1/p` of the current signed raw
boundary.  The scaled form avoids division and is valid as a literal ring
identity. -/
theorem evolvedEulerNext_sub_rawNext_scaled_eq_boundaryMemory
    (R : ℕ) {p : ℕ} (qs : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs) :
    let U0 := Finset.Icc 1 (squareRootEndpoint R)
    let U := squareRootCanonicalRoughAdaptiveCarrier qs U0
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient qs U0
      (fun _ => (1 : ℂ))
    let b := fun n : ℕ => (n : ℂ) * a n
    let nextU := squareRootCanonicalRoughAdaptiveNextCarrier p U
    (p : ℂ) *
        (squareRootCanonicalRoughAdaptiveWeightedMass R nextU
            (squareRootCanonicalRoughAdaptiveNextCoefficient p U b) -
          squareRootCanonicalRoughAdaptiveRawWeightedMass R nextU
            (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a)) =
      ((p : ℂ) - 1) *
        squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a := by
  dsimp
  let U0 : Finset ℕ := Finset.Icc 1 (squareRootEndpoint R)
  let U : Finset ℕ := squareRootCanonicalRoughAdaptiveCarrier qs U0
  let a : ℕ → ℂ := squareRootCanonicalRoughAdaptiveRawCoefficient qs U0
    (fun _ => (1 : ℂ))
  let b : ℕ → ℂ := fun n => (n : ℂ) * a n
  let nextU : Finset ℕ := squareRootCanonicalRoughAdaptiveNextCarrier p U
  let E : ℂ := squareRootCanonicalRoughAdaptiveWeightedMass R nextU
    (squareRootCanonicalRoughAdaptiveNextCoefficient p U b)
  let N : ℂ := squareRootCanonicalRoughAdaptiveRawWeightedMass R nextU
    (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a)
  let D : ℂ := squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U b
  let B : ℂ := squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a

  have hpos : ∀ n ∈ U, 0 < n := by
    intro n hn
    have hn0 : n ∈ U0 :=
      squareRootCanonicalRoughAdaptiveCarrier_subset qs U0 hn
    have hnRange := Finset.mem_Icc.mp hn0
    omega

  have hcoord :
      squareRootCanonicalRoughAdaptiveRawWeightedMass R U a =
        squareRootCanonicalRoughAdaptiveWeightedMass R U b := by
    exact adaptiveRawWeightedMass_eq_cofactorWeightedReciprocalMass R U a hpos

  have hraw :=
    adaptiveRawWeightedMass_eq_next_add_boundary_add_mismatch R U a hR hp
  have hrawZero :=
    squareRootCanonicalRoughAdaptiveRawMismatchMass_evolved_eq_zero_of_completeDescendingPrefix
      R qs hR hp hcomplete
  change squareRootCanonicalRoughAdaptiveRawMismatchMass R p U a = 0 at hrawZero
  rw [hrawZero, add_zero] at hraw
  change squareRootCanonicalRoughAdaptiveRawWeightedMass R U a = N + B at hraw

  have heuler :=
    cofactorWeighted_evolvedMass_eq_next_add_physicalDefect_of_completeDescendingPrefix
      R qs hR hp hcomplete
  dsimp [U0, U, a, b] at heuler
  change squareRootCanonicalRoughAdaptiveWeightedMass R U b = E + D at heuler

  have hdef :=
    natCast_mul_adaptiveCofactorWeightedPhysicalDefectMass_eq_rawBoundaryMass
      R (p := p) U a hp
  change (p : ℂ) * D = B at hdef

  have hcompare : E + D = N + B := by
    calc
      E + D = squareRootCanonicalRoughAdaptiveWeightedMass R U b := heuler.symm
      _ = squareRootCanonicalRoughAdaptiveRawWeightedMass R U a := hcoord.symm
      _ = N + B := hraw

  change (p : ℂ) * (E - N) = ((p : ℂ) - 1) * B
  rw [← hdef] at hcompare ⊢
  linear_combination (p : ℂ) * hcompare

/-- The previous scaled identity is exactly the Euler-retention law after
solving for the next-state difference. -/
theorem evolvedEulerNext_sub_rawNext_eq_one_sub_inv_mul_boundary
    (R : ℕ) {p : ℕ} (qs : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs) :
    let U0 := Finset.Icc 1 (squareRootEndpoint R)
    let U := squareRootCanonicalRoughAdaptiveCarrier qs U0
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient qs U0
      (fun _ => (1 : ℂ))
    let b := fun n : ℕ => (n : ℂ) * a n
    let nextU := squareRootCanonicalRoughAdaptiveNextCarrier p U
    squareRootCanonicalRoughAdaptiveWeightedMass R nextU
          (squareRootCanonicalRoughAdaptiveNextCoefficient p U b) -
        squareRootCanonicalRoughAdaptiveRawWeightedMass R nextU
          (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a) =
      (1 - (1 : ℂ) / (p : ℂ)) *
        squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a := by
  dsimp
  have hscaled :=
    evolvedEulerNext_sub_rawNext_scaled_eq_boundaryMemory R qs hR hp hcomplete
  dsimp at hscaled
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  field_simp [hp0] at hscaled ⊢
  simpa [sub_eq_add_neg] using hscaled

end RHLean.Proof
