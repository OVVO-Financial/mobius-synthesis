import RHLean.Analysis.DistinguishedPrimeTransitionSupport
import RHLean.Analysis.SquarePrefixMertensBridge

/-!
# Mertens energy criterion

This module now also records the exact two-real-variable quadratic closure of
the distinguished-prime rank-one channel.  For a positive Lyapunov weight `r`,
strict domination of the output quadratic by the weighted input quadratic on
every nonzero real vector is the Rayleigh-quotient statement that the largest
generalized eigenvalue is below `1`.

The arithmetic content is concentrated in one scalar threshold.  When
`beta, gamma > 0`, such a positive weight exists exactly when
`alpha + beta * gamma < 1`.  For the complex restricted-prime coefficient we
take `alpha = ‖a‖`.
-/

noncomputable section

namespace RHLean.Analysis

/-- Weighted real input quadratic for the reduced two-scalar channel. -/
def restrictedPrimeRealQuadraticInput (r x y : ℝ) : ℝ :=
  x ^ 2 + r * y ^ 2

/-- Worst-phase radial output quadratic.  Here `alpha` is the modulus of the
inactive-to-inactive complex coefficient. -/
def restrictedPrimeRealQuadraticOutput
    (alpha beta gamma r x y : ℝ) : ℝ :=
  (alpha * x + beta * y) ^ 2 + r * gamma ^ 2 * x ^ 2

/-- Strict quadratic contraction at level `1`.  For `r > 0`, this is exactly the
statement that the largest generalized eigenvalue of the output quadratic
relative to `diag(1,r)` is strictly below `1`. -/
def RestrictedPrimeRealQuadraticContraction
    (alpha beta gamma r : ℝ) : Prop :=
  ∀ x y : ℝ, x ≠ 0 ∨ y ≠ 0 →
    restrictedPrimeRealQuadraticOutput alpha beta gamma r x y <
      restrictedPrimeRealQuadraticInput r x y

/-- The symmetrizing Lyapunov weight `r = beta / gamma` gives strict quadratic
contraction as soon as the scalar threshold is subunit.  The proof is the exact
sum-of-squares completion of the two-by-two real quadratic form. -/
theorem restrictedPrimeRealQuadraticContraction_symmetrizingWeight
    (alpha beta gamma : ℝ)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 < beta)
    (hgamma : 0 < gamma)
    (hscalar : alpha + beta * gamma < 1) :
    RestrictedPrimeRealQuadraticContraction
      alpha beta gamma (beta / gamma) := by
  intro x y hxy
  unfold restrictedPrimeRealQuadraticOutput restrictedPrimeRealQuadraticInput
  have ht : 0 < beta * gamma := mul_pos hbeta hgamma
  have ht_one : beta * gamma < 1 := by nlinarith
  have hone : 0 < 1 - beta * gamma := by linarith
  have hminus : 0 < 1 - beta * gamma - alpha := by linarith
  have hplus : 0 < 1 - beta * gamma + alpha := by nlinarith
  have hdisc : 0 < (1 - beta * gamma) ^ 2 - alpha ^ 2 := by
    nlinarith [mul_pos hminus hplus]
  by_cases hx : x = 0
  · subst x
    have hy : y ≠ 0 := by simpa using hxy
    have hy2 : 0 < y ^ 2 := by positivity
    have hcoef : beta ^ 2 < beta / gamma := by
      rw [lt_div_iff₀ hgamma]
      nlinarith [mul_lt_mul_of_pos_left ht_one hbeta]
    nlinarith [mul_lt_mul_of_pos_right hcoef hy2]
  · have hx2 : 0 < x ^ 2 := by positivity
    have hnonneg :
        0 ≤ (beta * (1 - beta * gamma) * y -
          alpha * (beta * gamma) * x) ^ 2 :=
      sq_nonneg _
    have hpositive :
        0 < (beta * gamma) *
          (((1 - beta * gamma) ^ 2 - alpha ^ 2) * x ^ 2) :=
      mul_pos ht (mul_pos hdisc hx2)
    have hrhs :
        0 < (beta * (1 - beta * gamma) * y -
              alpha * (beta * gamma) * x) ^ 2 +
            (beta * gamma) *
              (((1 - beta * gamma) ^ 2 - alpha ^ 2) * x ^ 2) :=
      add_pos_of_nonneg_of_pos hnonneg hpositive
    have hidentity :
        (1 - beta * gamma) * (beta * gamma) *
            (x ^ 2 + (beta / gamma) * y ^ 2 -
              ((alpha * x + beta * y) ^ 2 +
                (beta / gamma) * gamma ^ 2 * x ^ 2)) =
          (beta * (1 - beta * gamma) * y -
              alpha * (beta * gamma) * x) ^ 2 +
            (beta * gamma) *
              (((1 - beta * gamma) ^ 2 - alpha ^ 2) * x ^ 2) := by
      field_simp [ne_of_gt hgamma]
      ring
    have hprod :
        0 < (1 - beta * gamma) * (beta * gamma) *
          (x ^ 2 + (beta / gamma) * y ^ 2 -
            ((alpha * x + beta * y) ^ 2 +
              (beta / gamma) * gamma ^ 2 * x ^ 2)) := by
      rw [hidentity]
      exact hrhs
    have hmult : 0 < (1 - beta * gamma) * (beta * gamma) :=
      mul_pos hone ht
    have hdiff :
        0 < x ^ 2 + (beta / gamma) * y ^ 2 -
          ((alpha * x + beta * y) ^ 2 +
            (beta / gamma) * gamma ^ 2 * x ^ 2) :=
      pos_of_mul_pos_right hprod hmult.le
    linarith

/-- **Scalar norm criterion for the real quadratic closure.**  If
`beta, gamma > 0`, there is a positive Lyapunov weight whose largest generalized
eigenvalue is below `1` if and only if `‖a‖ + beta * gamma < 1`.

The reverse implication uses the explicit symmetrizing weight `beta / gamma`.
For necessity, test the quadratic contraction on the nonzero vector
`(x,y) = (1,gamma)`; the weighted terms cancel and leave exactly the scalar
threshold. -/
theorem restrictedPrimeRealQuadraticContraction_iff_scalarNorm
    (a : ℂ) (beta gamma : ℝ)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    (∃ r : ℝ, 0 < r ∧
      RestrictedPrimeRealQuadraticContraction ‖a‖ beta gamma r) ↔
        ‖a‖ + beta * gamma < 1 := by
  constructor
  · rintro ⟨r, _hr, hcontract⟩
    have htest := hcontract 1 gamma (Or.inl one_ne_zero)
    unfold restrictedPrimeRealQuadraticOutput
      restrictedPrimeRealQuadraticInput at htest
    have hsum_nonneg : 0 ≤ ‖a‖ + beta * gamma :=
      add_nonneg (norm_nonneg a) (mul_pos hbeta hgamma).le
    nlinarith
  · intro hscalar
    refine ⟨beta / gamma, div_pos hbeta hgamma, ?_⟩
    exact restrictedPrimeRealQuadraticContraction_symmetrizingWeight
      ‖a‖ beta gamma (norm_nonneg a) hbeta hgamma hscalar

end RHLean.Analysis
