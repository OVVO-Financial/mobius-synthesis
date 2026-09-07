import Mathlib
import RHLean.Proof.CanonicalRoughQuantitativeContraction

/-!
# Finite Abel return from the reciprocal profile to the covariance numerator

The reciprocal Euler compression works in the coordinate
`v_R(c) = S_R(c) / c`, where `S_R(c)` is the response-centered covariance
summand.  Every contraction statement proved on that carrier is a statement
about the *reciprocal-weighted* profile, whereas the canonical rough covariance
is the *unweighted* numerator `sum_c S_R(c)` divided by the cofactor population.

This file supplies the return trip, and it is exact.  Writing

```text
A_R(n) = sum_{c <= n} v_R(c)
```

for the compressed reciprocal profile, finite summation by parts gives the
identity

```text
sum_{c=1}^{N} S_R(c) = (N+1) * A_R(N) - sum_{n=1}^{N} A_R(n),
```

with no error term and no hypothesis whatsoever: it is the discrete Abel
transform of `S_R(c) = c * v_R(c)`.

The quantitative consequence is immediate.  A uniform bound `M` on the
compressed reciprocal profile over the whole cofactor range costs only the
length of that range:

```text
‖sum_{c=1}^{N} S_R(c)‖ <= (2N + 1) * M,
```

and since the canonical cofactor population is exactly the square-root endpoint
`X_R`, dividing by it turns any such uniform bound into the covariance estimate

```text
‖Cov_R‖ <= 3 * M.
```

So the reciprocal weight, which is what makes the Euler compression work at all,
costs nothing beyond an absolute constant on the way back.  What remains open is
only the input: a uniform bound `M` on the compressed reciprocal profile itself.

`CanonicalRoughQuantitativeContraction` already carries the profile itself and
an Abel reconstruction of the *numerator*.  The profile is reused from there
rather than redeclared.  What this file adds is the `Icc`-indexed form of the
transform, which needs no `range`/`Icc` bookkeeping at the call site, and the
final normalization step: the cofactor population is exactly `X_R`, so the
bound lands on the covariance itself rather than on its numerator.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughFreshPrimeDifference
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-! ## Endpoints of the compressed reciprocal profile

The profile itself is `squareRootCanonicalRoughReciprocalPrefix` from
`CanonicalRoughQuantitativeContraction`, reused here rather than redeclared.
Its inclusive form starts at index zero, which is harmless: the reciprocal
summand at zero divides by zero and so vanishes. -/

@[simp] theorem squareRootCanonicalRoughReciprocalPrefix_zero (R : ℕ) :
    squareRootCanonicalRoughReciprocalPrefix R 0 = 0 := by
  simp [squareRootCanonicalRoughReciprocalPrefix, inclusivePrefix,
    squareRootCanonicalRoughResponseCenteredReciprocalSummand]

theorem squareRootCanonicalRoughReciprocalPrefix_succ (R n : ℕ) :
    squareRootCanonicalRoughReciprocalPrefix R (n + 1) =
      squareRootCanonicalRoughReciprocalPrefix R n +
        squareRootCanonicalRoughResponseCenteredReciprocalSummand R (n + 1) := by
  simp [squareRootCanonicalRoughReciprocalPrefix, inclusivePrefix,
    Finset.sum_range_succ]

/-- **Finite Abel return (exact).**  Summation by parts expresses the unweighted
canonical rough covariance numerator entirely in terms of the compressed
reciprocal profile.  The identity is exact and unconditional. -/
theorem sum_squareRootCanonicalRoughResponseCenteredSummand_eq_abel (R N : ℕ) :
    (∑ c ∈ Finset.Icc 1 N, squareRootCanonicalRoughResponseCenteredSummand R c) =
      ((N : ℂ) + 1) * squareRootCanonicalRoughReciprocalPrefix R N -
        ∑ n ∈ Finset.Icc 1 N, squareRootCanonicalRoughReciprocalPrefix R n := by
  induction N with
  | zero =>
      rw [Finset.Icc_eq_empty (by omega : ¬(1 : ℕ) ≤ 0)]
      simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1),
        Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1), ih,
        squareRootCanonicalRoughReciprocalPrefix_succ]
      have hS : squareRootCanonicalRoughResponseCenteredSummand R (N + 1) =
          ((N : ℂ) + 1) *
            squareRootCanonicalRoughResponseCenteredReciprocalSummand R (N + 1) := by
        have h := natCast_mul_squareRootCanonicalRoughResponseCenteredReciprocalSummand
          R (show 0 < N + 1 by omega)
        push_cast at h
        exact h.symm
      rw [hS]
      push_cast
      ring

/-- **Quantitative Abel return.**  A uniform bound on the compressed reciprocal
profile over an initial range returns a bound on the unweighted covariance
numerator that costs only the length of that range. -/
theorem norm_sum_squareRootCanonicalRoughResponseCenteredSummand_le
    (R N : ℕ) (M : ℝ)
    (hM : ∀ n, n ≤ N → ‖squareRootCanonicalRoughReciprocalPrefix R n‖ ≤ M) :
    ‖∑ c ∈ Finset.Icc 1 N, squareRootCanonicalRoughResponseCenteredSummand R c‖ ≤
      (2 * (N : ℝ) + 1) * M := by
  have hnormN : ‖((N : ℂ) + 1)‖ = (N : ℝ) + 1 := by
    have hcast : ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_natCast]
    norm_cast
  have hprefix :
      ‖∑ n ∈ Finset.Icc 1 N, squareRootCanonicalRoughReciprocalPrefix R n‖ ≤
        (N : ℝ) * M := by
    refine le_trans (norm_sum_le _ _) ?_
    calc
      (∑ n ∈ Finset.Icc 1 N, ‖squareRootCanonicalRoughReciprocalPrefix R n‖) ≤
          ∑ _n ∈ Finset.Icc 1 N, M := by
            refine Finset.sum_le_sum ?_
            intro n hn
            exact hM n (Finset.mem_Icc.mp hn).2
      _ = (N : ℝ) * M := by
            rw [Finset.sum_const, Nat.card_Icc]
            simp
  have hhead :
      ‖((N : ℂ) + 1) * squareRootCanonicalRoughReciprocalPrefix R N‖ ≤
        ((N : ℝ) + 1) * M := by
    rw [norm_mul, hnormN]
    exact mul_le_mul_of_nonneg_left (hM N le_rfl) (by positivity)
  rw [sum_squareRootCanonicalRoughResponseCenteredSummand_eq_abel R N]
  calc
    ‖((N : ℂ) + 1) * squareRootCanonicalRoughReciprocalPrefix R N -
        ∑ n ∈ Finset.Icc 1 N, squareRootCanonicalRoughReciprocalPrefix R n‖ ≤
        ‖((N : ℂ) + 1) * squareRootCanonicalRoughReciprocalPrefix R N‖ +
          ‖∑ n ∈ Finset.Icc 1 N, squareRootCanonicalRoughReciprocalPrefix R n‖ :=
      norm_sub_le _ _
    _ ≤ ((N : ℝ) + 1) * M + (N : ℝ) * M := add_le_add hhead hprefix
    _ = (2 * (N : ℝ) + 1) * M := by ring

/-- The canonical cofactor population is exactly the square-root endpoint. -/
theorem squareRootCanonicalRoughCofactorCard_eq_squareRootEndpoint (R : ℕ) :
    squareRootCanonicalRoughCofactorCard R = squareRootEndpoint R := by
  unfold squareRootCanonicalRoughCofactorCard
  rw [Nat.card_Icc]
  omega

/-- **Finite Abel return to the covariance.**  Any uniform bound on the
compressed reciprocal profile over the canonical cofactor range yields a bound
on the unweighted canonical rough covariance, losing only the absolute factor
three.  This is the missing passage from the reciprocal carrier, where the Euler
compression contracts, back to the covariance the criterion is stated about. -/
theorem norm_squareRootCanonicalRoughCovariance_le_of_reciprocalPrefix_bound
    (R : ℕ) (hR : 2 ≤ R) (M : ℝ)
    (hM : ∀ n, n ≤ squareRootEndpoint R →
      ‖squareRootCanonicalRoughReciprocalPrefix R n‖ ≤ M) :
    ‖squareRootCanonicalRoughCovariance R‖ ≤ 3 * M := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (Nat.zero_le _))
  have hXpos : 0 < squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : 4 ≤ R ^ 2 := by nlinarith
    omega
  have hX1n : 1 ≤ squareRootEndpoint R := by omega
  have hXposR : (0 : ℝ) < (squareRootEndpoint R : ℝ) := by exact_mod_cast hXpos
  have hX1 : (1 : ℝ) ≤ (squareRootEndpoint R : ℝ) := by exact_mod_cast hX1n
  have hcardEq := squareRootCanonicalRoughCofactorCard_eq_squareRootEndpoint R
  have hkey :=
    squareRootCanonicalRoughCofactorCard_mul_covariance_eq_sum_responseCentered R hR
  have hnorm :
      (squareRootEndpoint R : ℝ) * ‖squareRootCanonicalRoughCovariance R‖ =
        ‖∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          squareRootCanonicalRoughResponseCenteredSummand R c‖ := by
    rw [← hkey, norm_mul, Complex.norm_natCast, hcardEq]
  have hbound := norm_sum_squareRootCanonicalRoughResponseCenteredSummand_le
    R (squareRootEndpoint R) M hM
  rw [← hnorm] at hbound
  refine le_of_mul_le_mul_left ?_ hXposR
  calc
    (squareRootEndpoint R : ℝ) * ‖squareRootCanonicalRoughCovariance R‖ ≤
        (2 * (squareRootEndpoint R : ℝ) + 1) * M := hbound
    _ ≤ (squareRootEndpoint R : ℝ) * (3 * M) := by
        have hprod : 0 ≤ M * ((squareRootEndpoint R : ℝ) - 1) :=
          mul_nonneg hM0 (by linarith)
        nlinarith [hprod]

end RHLean.Proof
