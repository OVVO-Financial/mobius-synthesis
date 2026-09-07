import Mathlib
import RHLean.Arithmetic.PrimorialTruncatedWheelBoundary
import RHLean.Proof.CanonicalRoughCompleteSubrootDefectReduction

/-!
# Critical defect shells as truncated Euler-wheel increments

On a complete sub-root wheel the previous module removes threshold loss and
separates the remaining physical defect into post-root top escape minus
lower-root birth.  This file changes the order of summation one more time.

Fix the current fresh prime `p` and one partner prime `q`.  Summing the
reciprocal Mobius weights over all old Boolean faces turns either physical
channel into one shell of the old truncated wheel profile:

```text
T_{<p}(N) - T_{<p}(N / p).
```

For top escape, `N = X_R / q`; for birth, `N = (R-1) / q`.

The existing exact fresh-prime recurrence

```text
T_{P insert p}(N) = T_P(N) - (1/p) T_P(N/p)
```

then gives the decisive normalization

```text
(1/p) * (T_P(N) - T_P(N/p))
  = T_{P insert p}(N) - (1 - 1/p) * T_P(N).
```

Thus one physical defect shell is not an independent error: after restoring its
native `1/p` factor it is exactly the discrepancy between the *true next
truncated Euler cube* and the uniform Euler contraction used by the compressed
profile.  Transporting these discrepancies over successive primes is therefore
a telescoping problem, not a sum of absolute defect costs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open CanonicalRoughFreshPrimeDifference
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- The signed reciprocal weight of one Boolean face, in the real coordinate of
`primorialTruncatedSignedReciprocalCube`. -/
def canonicalRoughFaceReciprocalWeightReal (u : Finset ℕ) : ℝ :=
  ((booleanCubeSign u : ℤ) : ℝ) / (primeFaceProduct u : ℝ)

/-- **One truncated shell is exactly one Euler-step discrepancy.** -/
theorem primorialTruncatedSignedReciprocalCube_shell_div_prime_eq_insert_sub_euler
    {P : Finset ℕ} {p N : ℕ} (hpNot : p ∉ P) (hp : p.Prime) :
    (1 / (p : ℝ)) *
        (primorialTruncatedSignedReciprocalCube P N -
          primorialTruncatedSignedReciprocalCube P (N / p)) =
      primorialTruncatedSignedReciprocalCube (insert p P) N -
        (1 - 1 / (p : ℝ)) * primorialTruncatedSignedReciprocalCube P N := by
  rw [primorialTruncatedSignedReciprocalCube_insert hpNot hp]
  ring

/-- For a prime `p`, adjoining it to all earlier prime coordinates gives exactly
`primesUpTo p`. -/
theorem insert_freshPrime_primesUpTo_pred_eq
    {p : ℕ} (hp : p.Prime) :
    insert p (primesUpTo (p - 1)) = primesUpTo p := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_insert.mp hq with rfl | hqOld
    · exact mem_primesUpTo.mpr ⟨hp, le_rfl⟩
    · rcases mem_primesUpTo.mp hqOld with ⟨hqPrime, hqLe⟩
      exact mem_primesUpTo.mpr ⟨hqPrime, hqLe.trans (Nat.sub_le p 1)⟩
  · intro hq
    rcases mem_primesUpTo.mp hq with ⟨hqPrime, hqLe⟩
    by_cases hqp : q = p
    · simp [hqp]
    · have hqPred : q ≤ p - 1 := by omega
      exact Finset.mem_insert.mpr <| Or.inr <|
        mem_primesUpTo.mpr ⟨hqPrime, hqPred⟩

/-- Old-face contribution of one fixed partner to the top-escape channel. -/
def squareRootCanonicalRoughCompleteWheelTopEscapePartnerFaceMass
    (R p q : ℕ) : ℝ :=
  ∑ u ∈ (primesUpTo (p - 1)).powerset,
    if q ∈ squareRootCanonicalRoughFreshTopEscapeBoundary
        R (primeFaceProduct u) p then
      canonicalRoughFaceReciprocalWeightReal u
    else 0

/-- Old-face contribution of one fixed partner to the birth channel. -/
def squareRootCanonicalRoughCompleteWheelBirthPartnerFaceMass
    (R p q : ℕ) : ℝ :=
  ∑ u ∈ (primesUpTo (p - 1)).powerset,
    if q ∈ squareRootCanonicalRoughFreshBirthBoundary
        R (primeFaceProduct u) p then
      canonicalRoughFaceReciprocalWeightReal u
    else 0

/-- On a complete sub-root wheel, fixed post-root top escape is exactly the
reciprocal face shell

`X_R/(p*q) < P(u) <= X_R/q`.
-/
theorem squareRootCanonicalRoughCompleteWheelTopEscapePartnerFaceMass_eq_truncatedShell
    {R p q : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hq : q.Prime)
    (hqR : R < q)
    (hWheel : SquareRootCanonicalRoughCompleteWheelBelowRoot R p) :
    squareRootCanonicalRoughCompleteWheelTopEscapePartnerFaceMass R p q =
      primorialTruncatedSignedReciprocalCube
          (primesUpTo (p - 1)) (squareRootEndpoint R / q) -
        primorialTruncatedSignedReciprocalCube
          (primesUpTo (p - 1)) ((squareRootEndpoint R / q) / p) := by
  unfold squareRootCanonicalRoughCompleteWheelTopEscapePartnerFaceMass
    primorialTruncatedSignedReciprocalCube
    canonicalRoughFaceReciprocalWeightReal
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hcpos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset hu
  have hcfresh : canonicalLargestPrimeFactor (primeFaceProduct u) < p :=
    canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hp hu
  have hpcLt : p * primeFaceProduct u < R :=
    freshPrime_mul_oldFace_lt_root_of_completeWheel hp hu hWheel
  have hpq : p < q := by
    have hpLe : p ≤ p * primeFaceProduct u := by
      simpa using Nat.mul_le_mul_left p (Nat.succ_le_iff.mpr hcpos)
    exact hpLe.trans_lt (hpcLt.trans hqR)
  have hqRough : canonicalLargestPrimeFactor (primeFaceProduct u) < q :=
    hcfresh.trans hpq
  have hmem :
      q ∈ squareRootCanonicalRoughFreshTopEscapeBoundary
          R (primeFaceProduct u) p ↔
        (squareRootEndpoint R / q) / p < primeFaceProduct u ∧
          primeFaceProduct u ≤ squareRootEndpoint R / q := by
    constructor
    · intro hmem
      rcases
          (mem_squareRootCanonicalRoughFreshTopEscapeBoundary_iff
            hR hcpos hp hcfresh).1 hmem with
        ⟨_hqPrime, _hrough, _hroot, hupper, _hpq, hwall⟩
      have hupper' : primeFaceProduct u ≤ squareRootEndpoint R / q :=
        (Nat.le_div_iff_mul_le hq.pos).2 hupper
      have hfirst : squareRootEndpoint R / q < primeFaceProduct u * p := by
        apply (Nat.div_lt_iff_lt_mul hq.pos).2
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hwall
      have hlower :
          (squareRootEndpoint R / q) / p < primeFaceProduct u :=
        (Nat.div_lt_iff_lt_mul hp.pos).2 <| by
          simpa [Nat.mul_comm] using hfirst
      exact ⟨hlower, hupper'⟩
    · rintro ⟨hlower, hupper⟩
      have hupper' : primeFaceProduct u * q ≤ squareRootEndpoint R :=
        (Nat.le_div_iff_mul_le hq.pos).1 hupper
      have hfirst : squareRootEndpoint R / q < primeFaceProduct u * p :=
        (Nat.div_lt_iff_lt_mul hp.pos).1 hlower
      have hwall :
          squareRootEndpoint R < (p * primeFaceProduct u) * q := by
        have := (Nat.div_lt_iff_lt_mul hq.pos).1 hfirst
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
      have hroot : R ≤ primeFaceProduct u * q := by
        have hqLe : q ≤ primeFaceProduct u * q := by
          calc
            q = 1 * q := by simp
            _ ≤ primeFaceProduct u * q :=
              Nat.mul_le_mul_right q (Nat.succ_le_iff.mpr hcpos)
        exact hqR.le.trans hqLe
      exact
        (mem_squareRootCanonicalRoughFreshTopEscapeBoundary_iff
          hR hcpos hp hcfresh).2
          ⟨hq, hqRough, hroot, hupper', hpq, hwall⟩
  by_cases hupper : primeFaceProduct u ≤ squareRootEndpoint R / q
  · by_cases hlowerCut :
        primeFaceProduct u ≤ (squareRootEndpoint R / q) / p
    · have hnotShell :
          ¬ ((squareRootEndpoint R / q) / p < primeFaceProduct u ∧
            primeFaceProduct u ≤ squareRootEndpoint R / q) := by omega
      have hnotMem :
          q ∉ squareRootCanonicalRoughFreshTopEscapeBoundary
            R (primeFaceProduct u) p := by
        simpa [hmem] using hnotShell
      simp [hnotMem, hupper, hlowerCut]
    · have hlower :
          (squareRootEndpoint R / q) / p < primeFaceProduct u :=
        Nat.lt_of_not_ge hlowerCut
      have hmem' :
          q ∈ squareRootCanonicalRoughFreshTopEscapeBoundary
            R (primeFaceProduct u) p := hmem.2 ⟨hlower, hupper⟩
      simp [hmem', hupper, hlowerCut]
  · have hnotShell :
        ¬ ((squareRootEndpoint R / q) / p < primeFaceProduct u ∧
          primeFaceProduct u ≤ squareRootEndpoint R / q) := by
      intro hs
      exact hupper hs.2
    have hnotMem :
        q ∉ squareRootCanonicalRoughFreshTopEscapeBoundary
          R (primeFaceProduct u) p := by
      simpa [hmem] using hnotShell
    have hnotLowerCut :
        ¬ primeFaceProduct u ≤ (squareRootEndpoint R / q) / p := by
      intro hlowerCut
      exact hupper (hlowerCut.trans (Nat.div_le_self _ p))
    simp [hnotMem, hupper, hnotLowerCut]

/-- On a complete sub-root wheel, fixed lower-root birth is exactly the
reciprocal face shell

`(R-1)/(p*q) < P(u) <= (R-1)/q`.
-/
theorem squareRootCanonicalRoughCompleteWheelBirthPartnerFaceMass_eq_truncatedShell
    {R p q : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hqR : q < R)
    (hWheel : SquareRootCanonicalRoughCompleteWheelBelowRoot R p) :
    squareRootCanonicalRoughCompleteWheelBirthPartnerFaceMass R p q =
      primorialTruncatedSignedReciprocalCube
          (primesUpTo (p - 1)) ((R - 1) / q) -
        primorialTruncatedSignedReciprocalCube
          (primesUpTo (p - 1)) (((R - 1) / q) / p) := by
  unfold squareRootCanonicalRoughCompleteWheelBirthPartnerFaceMass
    primorialTruncatedSignedReciprocalCube
    canonicalRoughFaceReciprocalWeightReal
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hcpos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset hu
  have hcfresh : canonicalLargestPrimeFactor (primeFaceProduct u) < p :=
    canonicalLargestPrimeFactor_primeFaceProduct_lt_freshPrime hp hu
  have hpcLt : p * primeFaceProduct u < R :=
    freshPrime_mul_oldFace_lt_root_of_completeWheel hp hu hWheel
  have hmem :
      q ∈ squareRootCanonicalRoughFreshBirthBoundary
          R (primeFaceProduct u) p ↔
        ((R - 1) / q) / p < primeFaceProduct u ∧
          primeFaceProduct u ≤ (R - 1) / q := by
    constructor
    · intro hmem
      rcases
          (mem_squareRootCanonicalRoughFreshBirthBoundary_iff
            hR hcpos hp hcfresh).1 hmem with
        ⟨_hqPrime, _hpq, hbelow, hroot, _hchildUpper⟩
      have hupper : primeFaceProduct u * q ≤ R - 1 := by omega
      have hupper' : primeFaceProduct u ≤ (R - 1) / q :=
        (Nat.le_div_iff_mul_le hq.pos).2 hupper
      have hfirst : (R - 1) / q < primeFaceProduct u * p := by
        apply (Nat.div_lt_iff_lt_mul hq.pos).2
        have : R - 1 < (p * primeFaceProduct u) * q := by omega
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
      have hlower : ((R - 1) / q) / p < primeFaceProduct u :=
        (Nat.div_lt_iff_lt_mul hp.pos).2 <| by
          simpa [Nat.mul_comm] using hfirst
      exact ⟨hlower, hupper'⟩
    · rintro ⟨hlower, hupper⟩
      have hbelowLe : primeFaceProduct u * q ≤ R - 1 :=
        (Nat.le_div_iff_mul_le hq.pos).1 hupper
      have hbelow : primeFaceProduct u * q < R := by omega
      have hfirst : (R - 1) / q < primeFaceProduct u * p :=
        (Nat.div_lt_iff_lt_mul hp.pos).1 hlower
      have hrootPred : R - 1 < (p * primeFaceProduct u) * q := by
        have := (Nat.div_lt_iff_lt_mul hq.pos).1 hfirst
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
      have hroot : R ≤ (p * primeFaceProduct u) * q := by omega
      have hprod1 : (p * primeFaceProduct u) * q < R * q :=
        Nat.mul_lt_mul_of_pos_right hpcLt hq.pos
      have hprod2 : R * q < R * R :=
        Nat.mul_lt_mul_of_pos_left hqR (by omega)
      have hprod : (p * primeFaceProduct u) * q < R * R :=
        hprod1.trans hprod2
      have hchildUpper :
          (p * primeFaceProduct u) * q ≤ squareRootEndpoint R := by
        unfold squareRootEndpoint
        rw [pow_two]
        omega
      exact
        (mem_squareRootCanonicalRoughFreshBirthBoundary_iff
          hR hcpos hp hcfresh).2
          ⟨hq, hpq, hbelow, hroot, hchildUpper⟩
  by_cases hupper : primeFaceProduct u ≤ (R - 1) / q
  · by_cases hlowerCut : primeFaceProduct u ≤ ((R - 1) / q) / p
    · have hnotShell :
          ¬ (((R - 1) / q) / p < primeFaceProduct u ∧
            primeFaceProduct u ≤ (R - 1) / q) := by omega
      have hnotMem :
          q ∉ squareRootCanonicalRoughFreshBirthBoundary
            R (primeFaceProduct u) p := by
        simpa [hmem] using hnotShell
      simp [hnotMem, hupper, hlowerCut]
    · have hlower : ((R - 1) / q) / p < primeFaceProduct u :=
        Nat.lt_of_not_ge hlowerCut
      have hmem' :
          q ∈ squareRootCanonicalRoughFreshBirthBoundary
            R (primeFaceProduct u) p := hmem.2 ⟨hlower, hupper⟩
      simp [hmem', hupper, hlowerCut]
  · have hnotShell :
        ¬ (((R - 1) / q) / p < primeFaceProduct u ∧
          primeFaceProduct u ≤ (R - 1) / q) := by
      intro hs
      exact hupper hs.2
    have hnotMem :
        q ∉ squareRootCanonicalRoughFreshBirthBoundary
          R (primeFaceProduct u) p := by
      simpa [hmem] using hnotShell
    have hnotLowerCut :
        ¬ primeFaceProduct u ≤ ((R - 1) / q) / p := by
      intro hlowerCut
      exact hupper (hlowerCut.trans (Nat.div_le_self _ p))
    simp [hnotMem, hupper, hnotLowerCut]

/-- The fixed-partner top-escape shell, after restoring the native `1/p`, is
exactly the next truncated wheel minus the Euler-contracted old wheel. -/
theorem one_div_prime_mul_completeWheelTopEscapePartnerFaceMass_eq_next_sub_euler
    {R p q : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hq : q.Prime)
    (hqR : R < q)
    (hWheel : SquareRootCanonicalRoughCompleteWheelBelowRoot R p) :
    (1 / (p : ℝ)) *
        squareRootCanonicalRoughCompleteWheelTopEscapePartnerFaceMass R p q =
      primorialTruncatedSignedReciprocalCube
          (primesUpTo p) (squareRootEndpoint R / q) -
        (1 - 1 / (p : ℝ)) *
          primorialTruncatedSignedReciprocalCube
            (primesUpTo (p - 1)) (squareRootEndpoint R / q) := by
  rw [squareRootCanonicalRoughCompleteWheelTopEscapePartnerFaceMass_eq_truncatedShell
    hR hp hq hqR hWheel]
  rw [← insert_freshPrime_primesUpTo_pred_eq hp]
  exact primorialTruncatedSignedReciprocalCube_shell_div_prime_eq_insert_sub_euler
    (freshPrime_not_mem_primesUpTo_pred hp) hp

/-- The fixed-partner birth shell has the same exact Euler-step discrepancy
form at the lower-root cutoff `(R-1)/q`. -/
theorem one_div_prime_mul_completeWheelBirthPartnerFaceMass_eq_next_sub_euler
    {R p q : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hqR : q < R)
    (hWheel : SquareRootCanonicalRoughCompleteWheelBelowRoot R p) :
    (1 / (p : ℝ)) *
        squareRootCanonicalRoughCompleteWheelBirthPartnerFaceMass R p q =
      primorialTruncatedSignedReciprocalCube
          (primesUpTo p) ((R - 1) / q) -
        (1 - 1 / (p : ℝ)) *
          primorialTruncatedSignedReciprocalCube
            (primesUpTo (p - 1)) ((R - 1) / q) := by
  rw [squareRootCanonicalRoughCompleteWheelBirthPartnerFaceMass_eq_truncatedShell
    hR hp hq hpq hqR hWheel]
  rw [← insert_freshPrime_primesUpTo_pred_eq hp]
  exact primorialTruncatedSignedReciprocalCube_shell_div_prime_eq_insert_sub_euler
    (freshPrime_not_mem_primesUpTo_pred hp) hp

end RHLean.Proof
