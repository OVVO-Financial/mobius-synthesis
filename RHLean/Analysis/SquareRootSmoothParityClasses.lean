import Mathlib
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm

/-!
# Parity classes of the complete smooth mass, and the residual gap to RH scale

The sign of a smooth squarefree source is parity-determined: `mu(m) = (-1)^k` for
`k` distinct primes, and adjoining a fresh top prime flips it
(`canonicalMoebiusWeight_mul_prime_eq_neg_of_rough`).  So the smooth population
carries mandatory cancellation and can never be a same-sign pile.  This module
records what that mechanism does and does not buy.

## The complete smooth mass in parity-class form

Combining the positive-orientation collapse with the born-smooth reciprocal
form, the prime-indexed Mertens prefix transform cancels exactly and leaves

```text
squareRootSmoothMass (R-1) = 1 - sum_{q <= R, q prime} Rough(q, floor(X/q)),
```

with `Rough(q,B) = sum_{c <= B, P+(c) < q} mu(c)`.  Each fibre is the signed
count of the parity classes of the `q`-rough pool truncated at the reciprocal
cutoff, so this is exactly the parity-class statement for the complete smooth
mass, with no norm taken.

## What the parity mechanism does not buy

The complete smooth mass is *not* the square-prefix RH residual, and is not at
square-root scale.  Because `X = R^2 - 1`, every source below `R^2` has at most
one prime factor above `R`, so

```text
squarePrefixMertens (R-1) = squareRootSmoothMass (R-1) - squareRootTransportPrimeFirst R,
```

and the complete smooth mass carries the whole transport drift.  The signed
residual that *is* at square-root scale is the matched one, obtained after the
orientation split removes the positive-orientation part:

```text
squarePrefixMertens (R-1)
  = squareRootPositiveSmoothMass R + squareRootMatchedBornSmoothTransport R.
```

That identity is already in the repository.  What this module adds is the
consequence for the criterion: the matched bound alone does not reach the
square-prefix Mertens value.  It needs the positive-orientation mass to be at
the same scale, and that mass is exactly

```text
squareRootPositiveSmoothMass R = - sum_{q <= R, q prime} M(q-1),
```

the parity-class balance of the small-prime pool itself.  The final theorem
proves that the two RH-scale statements together bound the square-prefix Mertens
Gram, making the remaining gap explicit rather than implicit.

No analytic estimate is proved or assumed.  The auxiliary statement is a named
proposition, and the combination theorem is a hypothetical implication.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The small-prime part of the unified reciprocal transform: one rough Möbius
prefix at the reciprocal cutoff for every prime up to `R`. -/
def squareRootSmallPrimeReciprocalTransform (R : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 2 R,
    if q.Prime then
      roughCofactorMobiusPrefixMass q (squareRootEndpoint R / q)
    else 0

/-- **Parity-class form of the complete smooth mass.**  The prime-indexed
Mertens prefix transform carried by the positive orientation cancels exactly
against the one carried by the born orientation, leaving the complete smooth
mass as the unit source minus the small-prime reciprocal transform. -/
theorem squareRootSmoothMass_eq_one_sub_smallPrimeReciprocalTransform
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootSmoothMass (R - 1) =
      1 - squareRootSmallPrimeReciprocalTransform R := by
  rw [squareRootSmoothMass_eq_positive_add_bornSmooth R (by omega),
    squareRootPositiveSmoothMass_eq_neg_primeMertensTransform R (by omega),
    squareRootBornSmoothMass_eq_one_sub_reciprocalTransform R hR,
    squareRootBornSmoothReciprocalTransform_eq_low_sub_primeMertens R]
  unfold squareRootSmallPrimeReciprocalTransform
  ring

/-- The RH-scale statement for the positive-orientation mass, i.e. for the
parity-class balance of the small-prime pool on its own.  Named proposition
only; nothing here asserts or assumes it. -/
def SquareRootPositiveSmoothBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
        ‖squareRootPositiveSmoothMass R‖ ^ 2 ≤ C * Real.rpow (R : ℝ) (2 + ε)

/-- The same statement written on the collapsed prime-indexed Mertens prefix
transform, which is what the positive-orientation mass equals. -/
theorem squareRootPositiveSmoothBounded_iff_primeMertensTransformBounded :
    SquareRootPositiveSmoothBoundedStatement ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ R : ℕ, 2 ≤ R →
            ‖squareRootPositiveSmoothPrimeMertensTransform R‖ ^ 2 ≤
              C * Real.rpow (R : ℝ) (2 + ε) := by
  unfold SquareRootPositiveSmoothBoundedStatement
  constructor
  · intro h ε hε
    obtain ⟨C, hC0, hC⟩ := h ε hε
    refine ⟨C, hC0, fun R hR => ?_⟩
    have hcollapse :=
      squareRootPositiveSmoothMass_eq_neg_primeMertensTransform R (by omega)
    have hval := hC R hR
    rw [hcollapse, norm_neg] at hval
    exact hval
  · intro h ε hε
    obtain ⟨C, hC0, hC⟩ := h ε hε
    refine ⟨C, hC0, fun R hR => ?_⟩
    have hcollapse :=
      squareRootPositiveSmoothMass_eq_neg_primeMertensTransform R (by omega)
    rw [hcollapse, norm_neg]
    exact hC R hR

/-- **The residual gap.**  The square-prefix RH criterion on the matched object
does not by itself bound the square-prefix Mertens value: the positive
orientation has to be at the same scale too.  Given both, the square-prefix
Mertens Gram is bounded at RH scale.

This is a hypothetical implication.  Neither hypothesis is proved or assumed
anywhere in the repository. -/
theorem squarePrefixMertensGram_bounded_of_matched_and_positiveSmooth
    (hmatched : SquareRootMatchedTransportBoundedStatement)
    (hpositive : SquareRootPositiveSmoothBoundedStatement) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ R : ℕ, 2 ≤ R →
          ‖RHLean.Analysis.squarePrefixMertens (R - 1)‖ ^ 2 ≤
            C * Real.rpow (R : ℝ) (2 + ε) := by
  intro ε hε
  obtain ⟨C₁, hC₁0, hC₁⟩ := hmatched ε hε
  obtain ⟨C₂, hC₂0, hC₂⟩ := hpositive ε hε
  refine ⟨2 * C₁ + 2 * C₂, by linarith, ?_⟩
  intro R hR
  have hsplit :=
    squarePrefixMertens_eq_positiveSmooth_add_matched R (by omega)
  have hposNorm : 0 ≤ ‖squareRootPositiveSmoothMass R‖ := norm_nonneg _
  have hmatNorm : 0 ≤ ‖squareRootMatchedBornSmoothTransport R‖ := norm_nonneg _
  have htri :
      ‖RHLean.Analysis.squarePrefixMertens (R - 1)‖ ≤
        ‖squareRootPositiveSmoothMass R‖ +
          ‖squareRootMatchedBornSmoothTransport R‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  have hsq :
      ‖RHLean.Analysis.squarePrefixMertens (R - 1)‖ ^ 2 ≤
        2 * ‖squareRootPositiveSmoothMass R‖ ^ 2 +
          2 * ‖squareRootMatchedBornSmoothTransport R‖ ^ 2 := by
    nlinarith [norm_nonneg (RHLean.Analysis.squarePrefixMertens (R - 1)),
      sq_nonneg (‖squareRootPositiveSmoothMass R‖ -
        ‖squareRootMatchedBornSmoothTransport R‖)]
  have hmatBound := hC₁ R hR
  have hposBound := hC₂ R hR
  nlinarith [hsq, hmatBound, hposBound]

end RHLean.Proof
