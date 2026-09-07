import Mathlib
import RHLean.Proof.CanonicalRoughCriticalCorrelationContraction

/-!
# Critical scaled signed defect windows

An earlier layer recouples the canonical rough Euler compression to the RH-critical
uncentered reciprocal correlation and identifies the remaining quantitative
obligations as the transported survivor ledger and the scaled signed physical
defect floor.

This file sharpens the latter without replacing it by an unsigned support
estimate.

For one legal fresh-prime edge `c -> c*p`, write

```text
D_R(c,p) = mu(c)/(c*p) * (T + E - B),
```

where `T`, `E`, and `B` are the exact threshold-loss, top-escape, and birth
cardinalities.  Multiplying by `p` gives the real arithmetic target

```text
p * D_R(c,p) = (mu(c)/c) * (T + E - B).
```

The same identity survives summation over the complete physical parent carrier.
Thus the `p * ||D_p||` quantity used by the defect floor is exactly the
norm of one signed reciprocal Moebius boundary sum; the `T/E/B` signs remain
coupled before the norm.

The three physical channels are also localized in explicit reciprocal windows.
These inclusions are support information only.  They are deliberately not
followed by a triangle inequality over the three channel cardinalities, because
the repository already proves that unsigned boundary mass is too large to reach
the critical scale.

Finally, a post-root fresh prime is shown to provide no new contraction: once
`R < p`, the child has zero rough response and the scaled defect is exactly the
parent RH-critical reciprocal correlation.  Hence useful defect contraction
must be earned on sub-root primes; the root-crossing remainder belongs to the
frontier/survivor side.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughFreshPrimeDifference
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- The exact signed physical boundary scalar of one fresh-prime edge. -/
def squareRootCanonicalRoughFreshPrimeSignedBoundaryScalar
    (R c p : ℕ) : ℂ :=
  ((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℂ) +
    ((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℂ) -
    ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)

/-- **Scaled one-edge defect identity.**  Multiplying by the fresh prime removes
its reciprocal suppression and leaves exactly the reciprocal Moebius parent
weight times the intact signed physical boundary scalar. -/
theorem natCast_mul_squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect
    {R c p : ℕ} (hc : 0 < c) (hp : p.Prime) :
    (p : ℂ) * squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p =
      squareRootCanonicalRoughParityReciprocalSummand c *
        squareRootCanonicalRoughFreshPrimeSignedBoundaryScalar R c p := by
  have hc0 : (c : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hc)
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  unfold squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect
    squareRootCanonicalRoughParityReciprocalSummand
    squareRootCanonicalRoughFreshPrimeSignedBoundaryScalar
  push_cast
  field_simp [hc0, hp0]

/-- The signed scaled boundary mass of one prime on an arbitrary active
carrier.  No channel norm is taken inside this definition. -/
def squareRootCanonicalRoughFreshPrimeScaledSignedBoundaryMass
    (R p : ℕ) (U : Finset ℕ) : ℂ :=
  ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
    squareRootCanonicalRoughParityReciprocalSummand c *
      squareRootCanonicalRoughFreshPrimeSignedBoundaryScalar R c p

/-- **Carrier-level scaled defect identity.**  The aggregate signed boundary
mass is literally `p` times the exact physical defect layer used by an earlier layer. -/
theorem squareRootCanonicalRoughFreshPrimeScaledSignedBoundaryMass_eq
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (hp : p.Prime) :
    squareRootCanonicalRoughFreshPrimeScaledSignedBoundaryMass R p U =
      (p : ℂ) *
        squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U := by
  unfold squareRootCanonicalRoughFreshPrimeScaledSignedBoundaryMass
    squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hcParent
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
    ⟨_hcU, hcpos, _hrough, _hchild⟩
  exact
    (natCast_mul_squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect
      (R := R) hcpos hp).symm

/-- The scaled norm in the defect floor is exactly the norm of the intact
signed reciprocal boundary mass. -/
theorem norm_squareRootCanonicalRoughFreshPrimeScaledSignedBoundaryMass_eq
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (hp : p.Prime) :
    ‖squareRootCanonicalRoughFreshPrimeScaledSignedBoundaryMass R p U‖ =
      (p : ℝ) *
        ‖squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefectMass R p U‖ := by
  rw [squareRootCanonicalRoughFreshPrimeScaledSignedBoundaryMass_eq R U hp,
    norm_mul, Complex.norm_natCast]

/-! ## Exact reciprocal support windows -/

/-- A threshold loss lies above the root reciprocal cutoff of the parent and at
or below the newly adjoined prime. -/
theorem squareRootCanonicalRoughFreshThresholdLossBoundary_subset_Ioc
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughFreshThresholdLossBoundary R c p ⊆
      Finset.Ioc ((R - 1) / c) p := by
  intro q hq
  rcases
      (mem_squareRootCanonicalRoughFreshThresholdLossBoundary_iff
        hR hc hp hfresh).1 hq with
    ⟨_hqPrime, _hrough, hroot, _hupper, hqp⟩
  refine Finset.mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul hc).2 ?_, hqp⟩
  rw [Nat.mul_comm q c]
  omega

/-- A genuine top escape lies in the reciprocal band removed when multiplication
by `p` pushes the partner through the square endpoint. -/
theorem squareRootCanonicalRoughFreshTopEscapeBoundary_subset_Ioc
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughFreshTopEscapeBoundary R c p ⊆
      Finset.Ioc (squareRootEndpoint R / (p * c))
        (squareRootEndpoint R / c) := by
  intro q hq
  rcases
      (mem_squareRootCanonicalRoughFreshTopEscapeBoundary_iff
        hR hc hp hfresh).1 hq with
    ⟨_hqPrime, _hrough, _hroot, hupper, _hpq, hwall⟩
  have hpc : 0 < p * c := Nat.mul_pos hp.pos hc
  refine Finset.mem_Ioc.mpr
    ⟨(Nat.div_lt_iff_lt_mul hpc).2 ?_,
      (Nat.le_div_iff_mul_le hc).2 ?_⟩
  · rw [Nat.mul_comm q (p * c)]
    exact hwall
  · rw [Nat.mul_comm q c]
    exact hupper

/-- A birth lies in the reciprocal band that multiplication by `p` lifts across
the root. -/
theorem squareRootCanonicalRoughFreshBirthBoundary_subset_Ioc
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughFreshBirthBoundary R c p ⊆
      Finset.Ioc ((R - 1) / (p * c)) ((R - 1) / c) := by
  intro q hq
  rcases
      (mem_squareRootCanonicalRoughFreshBirthBoundary_iff
        hR hc hp hfresh).1 hq with
    ⟨_hqPrime, _hpq, hbelow, hroot, _hchildUpper⟩
  have hpc : 0 < p * c := Nat.mul_pos hp.pos hc
  refine Finset.mem_Ioc.mpr
    ⟨(Nat.div_lt_iff_lt_mul hpc).2 ?_,
      (Nat.le_div_iff_mul_le hc).2 ?_⟩
  · rw [Nat.mul_comm q (p * c)]
    omega
  · rw [Nat.mul_comm q c]
    omega

/-! ## Post-root no-contraction law -/

/-- A fresh child formed with a prime strictly above the root has zero
RH-critical reciprocal response. -/
theorem squareRootCanonicalRoughCorrelationReciprocalSummand_mul_freshPrime_eq_zero_of_rootPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hRp : R < p) :
    squareRootCanonicalRoughCorrelationReciprocalSummand R (c * p) = 0 := by
  have hcq : 0 < c * p := Nat.mul_pos hc hp.pos
  rw [squareRootCanonicalRoughCorrelationReciprocalSummand_eq_weighted_response_div
    R hcq]
  rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R (c * p) hR,
    squareRootCanonicalRoughPrimePartnerCount_mul_freshPrime_eq_zero_of_rootPrime
      hR hc hp hfresh hRp]
  simp

/-- **Post-root scaled-defect no-go.**  Once `p` is already above the root, the
child response is zero and the scaled physical defect is exactly the parent
RH-critical reciprocal correlation.  Such a prime cannot lower the defect
floor; it only restates the profile being bounded. -/
theorem natCast_mul_squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect_eq_parent_of_rootPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hRp : R < p) :
    (p : ℂ) * squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p =
      squareRootCanonicalRoughCorrelationReciprocalSummand R c := by
  have hchild :=
    squareRootCanonicalRoughCorrelationReciprocalSummand_mul_freshPrime_eq_zero_of_rootPrime
      hR hc hp hfresh hRp
  have hpair :=
    squareRootCanonicalRoughCorrelationReciprocalSummand_add_mul_freshPrime
      hR hc hp hfresh
  rw [hchild, add_zero, canonicalRoughEulerFactor_cast_complex] at hpair
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hD :
      squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p =
        squareRootCanonicalRoughCorrelationReciprocalSummand R c -
          (1 - 1 / (p : ℂ)) *
            squareRootCanonicalRoughCorrelationReciprocalSummand R c := by
    calc
      squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p =
          ((1 - 1 / (p : ℂ)) *
              squareRootCanonicalRoughCorrelationReciprocalSummand R c +
            squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect R c p) -
            (1 - 1 / (p : ℂ)) *
              squareRootCanonicalRoughCorrelationReciprocalSummand R c := by ring
      _ = squareRootCanonicalRoughCorrelationReciprocalSummand R c -
            (1 - 1 / (p : ℂ)) *
              squareRootCanonicalRoughCorrelationReciprocalSummand R c := by
        rw [← hpair]
  rw [hD]
  field_simp [hp0]
  ring

end RHLean.Proof
