import RHLean.Analysis.NativePNTQuantitativeStatements
import RHLean.Analysis.NativePNTQuadraticBudget
import RHLean.Analysis.NativePNTSquarePrefixQuadraticBudget

/-!
# Retain the contracted PNT slope through the Axer transfer

The existing Axer bridge is usually consumed only as `M(N) = o(N)`.  Dividing
its calibrated estimate by `N log N` keeps the actual PNT slope visible in a
finite normalized Mertens bound.  Combining this with the new quadratic PNT
iteration budgets makes the contraction quantitative all the way to `M(N)/N`.
-/

noncomputable section

namespace RHLean.Analysis

/-- An affine Chebyshev envelope with slope `alpha` gives a finite normalized
Mertens bound with the same leading coefficient. -/
theorem nativeMertens_abs_div_le_of_affineEnvelope
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (henv : nativePNTHasAffineEnvelope alpha) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N →
      |nativeMertensSummatory N| / (N : ℝ) ≤
        alpha + (alpha + D + 2) / Real.log (N : ℝ) := by
  rcases nativeMertens_abs_mul_log_le_of_affineEnvelope
      alpha halpha henv with ⟨D, hD, hbound⟩
  refine ⟨D, hD, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [div_le_iff₀ hNpos]
  apply (mul_le_mul_iff_right₀ hlogpos).mp
  calc
    Real.log (N : ℝ) * |nativeMertensSummatory N| =
        |nativeMertensSummatory N| * Real.log (N : ℝ) := by ring
    _ ≤ alpha * (N : ℝ) * (1 + Real.log (N : ℝ)) +
          (D + 2) * (N : ℝ) := hbound N hN
    _ = Real.log (N : ℝ) *
          ((alpha + (alpha + D + 2) / Real.log (N : ℝ)) * (N : ℝ)) := by
      field_simp [ne_of_gt hlogpos]; ring

/-- Every original-path cubic iterate gives a strictly tighter finite normalized
Mertens coefficient. -/
theorem nativeMertens_abs_div_le_cubicSlope (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N →
      |nativeMertensSummatory N| / (N : ℝ) ≤
        nativePNTCubicSlope k +
          (nativePNTCubicSlope k + D + 2) / Real.log (N : ℝ) := by
  exact nativeMertens_abs_div_le_of_affineEnvelope
    (nativePNTCubicSlope k)
    (nativePNTCubicSlope_spec k).1.le
    (nativePNTCubicSlope_spec k).2.2

/-- The normalized Mertens bound inherits the sharper original-path
`eta^(-2)` PNT iteration budget. -/
theorem nativeMertens_abs_div_le_of_quadratic_budget
    (eta : ℝ) (heta : 0 < eta) (n : ℕ)
    (hbudget :
      1 < 2 * nativePNTCubicConstant * (n : ℝ) * eta ^ 2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N →
      |nativeMertensSummatory N| / (N : ℝ) ≤
        eta + (eta + D + 2) / Real.log (N : ℝ) := by
  exact nativeMertens_abs_div_le_of_affineEnvelope eta heta.le
    (nativePNTHasAffineEnvelope_of_quadratic_budget eta heta n hbudget)

/-- The same normalized Mertens contraction can be driven entirely by the
rederived square-prefix PNT path. -/
theorem nativeMertens_abs_div_le_of_squarePrefix_quadratic_budget
    (eta : ℝ) (heta : 0 < eta) (n : ℕ)
    (hbudget :
      1 < 2 * nativePNTSquarePrefixRederivedCubicConstant *
        (n : ℝ) * eta ^ 2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N →
      |nativeMertensSummatory N| / (N : ℝ) ≤
        eta + (eta + D + 2) / Real.log (N : ℝ) := by
  exact nativeMertens_abs_div_le_of_affineEnvelope eta heta.le
    (nativePNTSquarePrefixRederivedHasAffineEnvelope_of_quadratic_budget
      eta heta n hbudget)

end RHLean.Analysis
