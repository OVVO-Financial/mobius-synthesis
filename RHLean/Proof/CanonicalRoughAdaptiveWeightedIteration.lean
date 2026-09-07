import Mathlib
import RHLean.Proof.CanonicalRoughAdaptiveWeightedEulerCompression
import RHLean.Proof.CanonicalRoughAdaptiveLargestPrimeElimination

/-!
# Iterated weighted adaptive Euler compression

The one-prime weighted adaptive identity keeps the genuine Euler factor on every
coherent parent/child pair and records the exact coefficient mismatch when two
endpoints inherited different larger-prime histories.  This module iterates that
identity without taking a norm.

The result is a literal chronological formula:

```text
initial weighted mass
  = final adaptive weighted mass
    + signed weighted physical defects
    + signed coefficient mismatches.
```

Thus a descending-prime proof may attack the two signed ledgers directly.  No
survivor is frozen and no missing commuting-square corner is silently assigned
an Euler factor.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Coefficient field remaining after a chronological adaptive prime list. -/
def squareRootCanonicalRoughAdaptiveCoefficient :
    List ℕ → Finset ℕ → (ℕ → ℂ) → (ℕ → ℂ)
  | [], _U, a => a
  | p :: ps, U, a =>
      squareRootCanonicalRoughAdaptiveCoefficient ps
        (squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (squareRootCanonicalRoughAdaptiveNextCoefficient p U a)

/-- Signed correction created at one weighted adaptive step. -/
def squareRootCanonicalRoughAdaptiveWeightedStepCorrection
    (R p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U a +
    squareRootCanonicalRoughAdaptiveCoefficientMismatchMass R p U a

/-- Cumulative signed weighted corrections along a chronological adaptive run. -/
def squareRootCanonicalRoughAdaptiveWeightedLedger
    (R : ℕ) : List ℕ → Finset ℕ → (ℕ → ℂ) → ℂ
  | [], _U, _a => 0
  | p :: ps, U, a =>
      squareRootCanonicalRoughAdaptiveWeightedStepCorrection R p U a +
        squareRootCanonicalRoughAdaptiveWeightedLedger R ps
          (squareRootCanonicalRoughAdaptiveNextCarrier p U)
          (squareRootCanonicalRoughAdaptiveNextCoefficient p U a)

/-- Split the cumulative ledger into its current physical-defect and mismatch
atoms followed by the later adaptive run. -/
@[simp] theorem squareRootCanonicalRoughAdaptiveWeightedLedger_cons
    (R p : ℕ) (ps : List ℕ) (U : Finset ℕ) (a : ℕ → ℂ) :
    squareRootCanonicalRoughAdaptiveWeightedLedger R (p :: ps) U a =
      squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U a +
      squareRootCanonicalRoughAdaptiveCoefficientMismatchMass R p U a +
      squareRootCanonicalRoughAdaptiveWeightedLedger R ps
        (squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (squareRootCanonicalRoughAdaptiveNextCoefficient p U a) := by
  simp [squareRootCanonicalRoughAdaptiveWeightedLedger,
    squareRootCanonicalRoughAdaptiveWeightedStepCorrection]

/-- **Exact iterated weighted adaptive descent.**  Every requested prime acts on
exactly the carrier and coefficient field left by the earlier primes.  The only
booked correction terms are the intact signed physical defect and the intact
signed coefficient mismatch. -/
theorem adaptiveWeightedMass_eq_adaptiveCarrier_add_weightedLedger
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ) (U : Finset ℕ) (a : ℕ → ℂ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    squareRootCanonicalRoughAdaptiveWeightedMass R U a =
      squareRootCanonicalRoughAdaptiveWeightedMass R
        (squareRootCanonicalRoughAdaptiveCarrier ps U)
        (squareRootCanonicalRoughAdaptiveCoefficient ps U a) +
      squareRootCanonicalRoughAdaptiveWeightedLedger R ps U a := by
  induction ps generalizing U a with
  | nil =>
      simp [squareRootCanonicalRoughAdaptiveCarrier,
        squareRootCanonicalRoughAdaptiveCoefficient,
        squareRootCanonicalRoughAdaptiveWeightedLedger]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hps : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      let U' := squareRootCanonicalRoughAdaptiveNextCarrier p U
      let a' := squareRootCanonicalRoughAdaptiveNextCoefficient p U a
      have hone :=
        adaptiveWeightedMass_eq_next_add_physicalDefect_add_mismatch
          R U a hR hp
      have htail := ih (U := U') (a := a') hps
      calc
        squareRootCanonicalRoughAdaptiveWeightedMass R U a =
            squareRootCanonicalRoughAdaptiveWeightedMass R U' a' +
              squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U a +
              squareRootCanonicalRoughAdaptiveCoefficientMismatchMass R p U a := by
          simpa [U', a'] using hone
        _ = (squareRootCanonicalRoughAdaptiveWeightedMass R
              (squareRootCanonicalRoughAdaptiveCarrier ps U')
              (squareRootCanonicalRoughAdaptiveCoefficient ps U' a') +
              squareRootCanonicalRoughAdaptiveWeightedLedger R ps U' a') +
              squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U a +
              squareRootCanonicalRoughAdaptiveCoefficientMismatchMass R p U a := by
          rw [htail]
        _ = squareRootCanonicalRoughAdaptiveWeightedMass R
              (squareRootCanonicalRoughAdaptiveCarrier (p :: ps) U)
              (squareRootCanonicalRoughAdaptiveCoefficient (p :: ps) U a) +
              squareRootCanonicalRoughAdaptiveWeightedLedger R (p :: ps) U a := by
          simp only [squareRootCanonicalRoughAdaptiveCarrier,
            squareRootCanonicalRoughAdaptiveCoefficient,
            squareRootCanonicalRoughAdaptiveWeightedLedger,
            squareRootCanonicalRoughAdaptiveWeightedStepCorrection]
          dsimp [U', a']
          ring

/-- Unit initial coefficients specialize the exact iteration to the native
uncentered reciprocal correlation on the chosen carrier. -/
theorem sum_correlationReciprocal_eq_adaptiveWeightedUnitCarrier_add_ledger
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ) (U : Finset ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    (∑ n ∈ U, squareRootCanonicalRoughCorrelationReciprocalSummand R n) =
      squareRootCanonicalRoughAdaptiveWeightedMass R
        (squareRootCanonicalRoughAdaptiveCarrier ps U)
        (squareRootCanonicalRoughAdaptiveCoefficient ps U (fun _ => (1 : ℂ))) +
      squareRootCanonicalRoughAdaptiveWeightedLedger R ps U (fun _ => (1 : ℂ)) := by
  have h := adaptiveWeightedMass_eq_adaptiveCarrier_add_weightedLedger
    R hR ps U (fun _ => (1 : ℂ)) hprime
  simpa [squareRootCanonicalRoughAdaptiveWeightedMass] using h

/-! ## Actual descending zero-factor coefficients -/

/-- Raw zero-factor coefficients compose exactly along list append. -/
theorem squareRootCanonicalRoughAdaptiveRawCoefficient_append
    (ps qs : List ℕ) (U : Finset ℕ) (a : ℕ → ℂ) :
    squareRootCanonicalRoughAdaptiveRawCoefficient (ps ++ qs) U a =
      squareRootCanonicalRoughAdaptiveRawCoefficient qs
        (squareRootCanonicalRoughAdaptiveCarrier ps U)
        (squareRootCanonicalRoughAdaptiveRawCoefficient ps U a) := by
  induction ps generalizing U a with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.cons_append,
        squareRootCanonicalRoughAdaptiveRawCoefficient,
        squareRootCanonicalRoughAdaptiveCarrier]
      exact ih
        (U := squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (a := squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a)

/-- Once a raw zero-factor coefficient is zero, every later adaptive step keeps
it zero. -/
theorem squareRootCanonicalRoughAdaptiveRawCoefficient_eq_zero_of_eq_zero
    (ps : List ℕ) (U : Finset ℕ) (a : ℕ → ℂ) {n : ℕ}
    (ha : a n = 0) :
    squareRootCanonicalRoughAdaptiveRawCoefficient ps U a n = 0 := by
  induction ps generalizing U a with
  | nil =>
      simpa [squareRootCanonicalRoughAdaptiveRawCoefficient] using ha
  | cons p ps ih =>
      apply ih
        (U := squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (a := squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a)
      simp [squareRootCanonicalRoughAdaptiveRawNextCoefficient, ha]

/-- If a state is a parent at one concrete split point, its raw coefficient is
zero after that step and remains zero through the entire tail. -/
theorem squareRootCanonicalRoughAdaptiveRawCoefficient_eq_zero_of_parent_at_split
    (pre post : List ℕ) (U : Finset ℕ) (a : ℕ → ℂ)
    {q n : ℕ}
    (hn : n ∈ squareRootCanonicalRoughFreshPrimeParentsOn q
      (squareRootCanonicalRoughAdaptiveCarrier pre U)) :
    squareRootCanonicalRoughAdaptiveRawCoefficient
      (pre ++ q :: post) U a n = 0 := by
  rw [squareRootCanonicalRoughAdaptiveRawCoefficient_append]
  simp only [squareRootCanonicalRoughAdaptiveRawCoefficient]
  apply squareRootCanonicalRoughAdaptiveRawCoefficient_eq_zero_of_eq_zero
  simp [squareRootCanonicalRoughAdaptiveRawNextCoefficient, hn]

/-- **Four-corner descending coefficient kill.**  Suppose `q > p` is a physical
extension of the current `p`-child and every coordinate before `q` is strictly
larger than `q`.  On the literal full raw carrier all four corners
`c, c*p, c*q, c*p*q` survive that prefix.  Thus both `c` and `c*p` are parents
at the `q` step, receive coefficient zero simultaneously, and remain zero
through every later step. -/
theorem squareRootCanonicalRoughAdaptiveRawCoefficient_pair_eq_zero_of_larger_extension_split
    {R c p q : ℕ} (pre post : List ℕ)
    (hc : 0 < c) (hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hpq : p < q)
    (hupper : (c * p) * q ≤ squareRootEndpoint R)
    (hprime : ∀ r ∈ pre, r.Prime)
    (hlarger : ∀ r ∈ pre, q < r) :
    squareRootCanonicalRoughAdaptiveRawCoefficient
        (pre ++ q :: post) (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) c = 0 ∧
      squareRootCanonicalRoughAdaptiveRawCoefficient
        (pre ++ q :: post) (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) (c * p) = 0 := by
  let U0 : Finset ℕ := Finset.Icc 1 (squareRootEndpoint R)
  let V : Finset ℕ := squareRootCanonicalRoughAdaptiveCarrier pre U0
  have hcpPos : 0 < c * p := Nat.mul_pos hc hp.pos
  have hcqPos : 0 < c * q := Nat.mul_pos hc hq.pos
  have hcpqPos : 0 < (c * p) * q := Nat.mul_pos hcpPos hq.pos
  have hc_le_cp : c ≤ c * p := Nat.le_mul_of_pos_right c hp.pos
  have hcp_le_cpq : c * p ≤ (c * p) * q :=
    Nat.le_mul_of_pos_right (c * p) hq.pos
  have hcq_le_cpq : c * q ≤ (c * p) * q :=
    Nat.mul_le_mul_right q hc_le_cp
  have hcU0 : c ∈ U0 := by
    apply Finset.mem_Icc.mpr
    exact ⟨by omega, hc_le_cp.trans hcp_le_cpq |>.trans hupper⟩
  have hcpU0 : c * p ∈ U0 := by
    apply Finset.mem_Icc.mpr
    exact ⟨by omega, hcp_le_cpq.trans hupper⟩
  have hcqU0 : c * q ∈ U0 := by
    apply Finset.mem_Icc.mpr
    exact ⟨by omega, hcq_le_cpq.trans hupper⟩
  have hcpqU0 : (c * p) * q ∈ U0 := by
    apply Finset.mem_Icc.mpr
    exact ⟨by omega, hupper⟩
  have hlpfCP : canonicalLargestPrimeFactor (c * p) = p :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hp hrough
  have hroughQ : canonicalLargestPrimeFactor c < q := hrough.trans hpq
  have hlpfCQ : canonicalLargestPrimeFactor (c * q) = q :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hq hroughQ
  have hroughCPQ : canonicalLargestPrimeFactor (c * p) < q := by
    rw [hlpfCP]
    exact hpq
  have hlpfCPQ : canonicalLargestPrimeFactor ((c * p) * q) = q :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough hcpPos hq hroughCPQ
  have hcV : c ∈ V := by
    dsimp [V]
    apply mem_adaptiveCarrier_of_all_larger_primes pre hcU0 hprime
    intro r hr
    exact hroughQ.trans (hlarger r hr)
  have hcpV : c * p ∈ V := by
    dsimp [V]
    apply mem_adaptiveCarrier_of_all_larger_primes pre hcpU0 hprime
    intro r hr
    rw [hlpfCP]
    exact hpq.trans (hlarger r hr)
  have hcqV : c * q ∈ V := by
    dsimp [V]
    apply mem_adaptiveCarrier_of_all_larger_primes pre hcqU0 hprime
    intro r hr
    rw [hlpfCQ]
    exact hlarger r hr
  have hcpqV : (c * p) * q ∈ V := by
    dsimp [V]
    apply mem_adaptiveCarrier_of_all_larger_primes pre hcpqU0 hprime
    intro r hr
    rw [hlpfCPQ]
    exact hlarger r hr
  have hcParent : c ∈ squareRootCanonicalRoughFreshPrimeParentsOn q V := by
    apply mem_squareRootCanonicalRoughFreshPrimeParentsOn.mpr
    exact ⟨hcV, hc, hroughQ, hcqV⟩
  have hcpParent : c * p ∈ squareRootCanonicalRoughFreshPrimeParentsOn q V := by
    apply mem_squareRootCanonicalRoughFreshPrimeParentsOn.mpr
    exact ⟨hcpV, hcpPos, hroughCPQ, hcpqV⟩
  constructor
  · exact squareRootCanonicalRoughAdaptiveRawCoefficient_eq_zero_of_parent_at_split
      pre post U0 (fun _ => (1 : ℂ)) hcParent
  · exact squareRootCanonicalRoughAdaptiveRawCoefficient_eq_zero_of_parent_at_split
      pre post U0 (fun _ => (1 : ℂ)) hcpParent

/-- A prime prefix is complete and descending above `p` when every physically
relevant prime `q > p` occurs once after a prefix consisting only of strictly
larger prime coordinates.  The definition deliberately asks only for the split
property needed by the four-corner proof. -/
def SquareRootCanonicalRoughCompleteDescendingPrefix
    (R p : ℕ) (qs : List ℕ) : Prop :=
  (∀ r ∈ qs, r.Prime) ∧
    ∀ q : ℕ, q.Prime → p < q → q ≤ squareRootEndpoint R →
      ∃ pre post,
        qs = pre ++ q :: post ∧
          (∀ r ∈ pre, r.Prime) ∧
          (∀ r ∈ pre, q < r)

/-- **Actual evolved raw mismatch vanishes on a complete descending prefix.**
This is no longer the auxiliary threshold coefficient field.  The coefficient
is the literal recursive output of every earlier zero-factor step from unit
initial coefficients on the full raw carrier.  A nonzero child response supplies
a larger prime `q`; the complete descending prefix reaches that `q` while all
four arithmetic corners are still alive and zeroes both current endpoints.
If no such `q` exists, the child raw atom is already zero. -/
theorem squareRootCanonicalRoughAdaptiveRawMismatchMass_evolved_eq_zero_of_completeDescendingPrefix
    (R : ℕ) {p : ℕ} (qs : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs) :
    squareRootCanonicalRoughAdaptiveRawMismatchMass R p
        (squareRootCanonicalRoughAdaptiveCarrier qs
          (Finset.Icc 1 (squareRootEndpoint R)))
        (squareRootCanonicalRoughAdaptiveRawCoefficient qs
          (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))) = 0 := by
  unfold squareRootCanonicalRoughAdaptiveRawMismatchMass
  apply Finset.sum_eq_zero
  intro c hcParent
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
    ⟨_hcV, hcpos, hrough, _hcpV⟩
  by_cases hchild :
      squareRootCanonicalRoughHasPrimeExtensionAbove R p (c * p)
  · rcases hchild with ⟨q, hqPrime, hpq, hupper⟩
    have hcpPos : 0 < c * p := Nat.mul_pos hcpos hp.pos
    have hqProd : q ≤ q * (c * p) := Nat.le_mul_of_pos_right q hcpPos
    have hqUpper : q ≤ squareRootEndpoint R := by
      have hqProd' : q ≤ (c * p) * q := by
        simpa [Nat.mul_comm] using hqProd
      exact hqProd'.trans hupper
    rcases hcomplete.2 q hqPrime hpq hqUpper with
      ⟨pre, post, hsplit, hprePrime, hpreLarger⟩
    have hzero :=
      squareRootCanonicalRoughAdaptiveRawCoefficient_pair_eq_zero_of_larger_extension_split
        pre post hcpos hp hqPrime hrough hpq hupper hprePrime hpreLarger
    rw [← hsplit] at hzero
    rw [hzero.1, hzero.2]
    simp
  · have hraw :=
      squareRootCanonicalRoughRawCorrelationSummand_mul_freshPrime_eq_zero_of_no_extension
        hR hcpos hp hrough hchild
    rw [hraw]
    simp

end RHLean.Proof