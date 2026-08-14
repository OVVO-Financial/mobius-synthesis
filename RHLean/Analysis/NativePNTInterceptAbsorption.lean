import Mathlib

/-!
# Algebraic absorption for one native PNT intercept step

These lemmas separate the pure lower-order algebra from the arithmetic PNT
recurrence.  They are the two inequalities responsible for the onset cost in
the explicit intercept propagation.
-/

noncomputable section

namespace RHLean.Analysis

/-- The lower-order affine terms are absorbed by `3 * delta * N * L^2` once
`L >= 1` and the calibrated coefficient is at most `3 * delta * L`. -/
theorem nativePNTCubicStep_overhead_le
    (alpha D delta x L : ℝ)
    (halpha : 0 ≤ alpha) (hD : 0 ≤ D)
    (hx1 : 1 ≤ x) (hL1 : 1 ≤ L)
    (hC : 3000 * alpha + 784 * D + 3000 ≤ 3 * delta * L) :
    alpha * x * (1000 * L + 2000) +
        D * (2 * x * L + 182 * x + 600) +
        3000 * x * L ≤
      3 * delta * x * L ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hB0 : 0 ≤ 2000 * alpha + 782 * D := by positivity
  have hBLe :
      2000 * alpha + 782 * D ≤
        (2000 * alpha + 782 * D) * L := by
    have h := mul_le_mul_of_nonneg_left hL1 hB0
    simpa using h
  have hinner :
      alpha * (1000 * L + 2000) +
          D * (2 * L + 782) + 3000 * L ≤
        3 * delta * L ^ 2 := by
    have hleft :
        alpha * (1000 * L + 2000) +
            D * (2 * L + 782) + 3000 * L ≤
          (3000 * alpha + 784 * D + 3000) * L := by
      nlinarith [hBLe]
    have hright := mul_le_mul_of_nonneg_right hC hL0
    calc
      alpha * (1000 * L + 2000) +
            D * (2 * L + 782) + 3000 * L ≤
          (3000 * alpha + 784 * D + 3000) * L := hleft
      _ ≤ (3 * delta * L) * L := hright
      _ = 3 * delta * L ^ 2 := by ring
  have hD600 : D * 600 ≤ D * 600 * x := by
    have h600D : 0 ≤ D * 600 := by positivity
    have h := mul_le_mul_of_nonneg_left hx1 h600D
    simpa [mul_assoc] using h
  have hinnerX := mul_le_mul_of_nonneg_left hinner hx0
  have hreshape :
      alpha * x * (1000 * L + 2000) +
          D * (2 * x * L + 182 * x + 600) +
          3000 * x * L ≤
        x *
          (alpha * (1000 * L + 2000) +
            D * (2 * L + 782) + 3000 * L) := by
    nlinarith [hD600]
  calc
    alpha * x * (1000 * L + 2000) +
          D * (2 * x * L + 182 * x + 600) +
          3000 * x * L ≤
        x *
          (alpha * (1000 * L + 2000) +
            D * (2 * L + 782) + 3000 * L) := hreshape
    _ ≤ x * (3 * delta * L ^ 2) := hinnerX
    _ = 3 * delta * x * L ^ 2 := by ring

/-- A good-mass lower bound converts directly into four copies of the cubic
slope decrement. -/
theorem nativePNTCubicStep_deficit_le
    (alpha beta c delta x L mass : ℝ)
    (hab : 0 ≤ alpha - beta) (hx : 0 ≤ x)
    (hgood : c * L ^ 2 ≤ mass)
    (hdelta : delta = (alpha - beta) * c / 4) :
    -(alpha - beta) * x * mass ≤
      -4 * delta * x * L ^ 2 := by
  have hcoef0 : 0 ≤ (alpha - beta) * x :=
    mul_nonneg hab hx
  have hmul := mul_le_mul_of_nonneg_left hgood hcoef0
  calc
    -(alpha - beta) * x * mass =
        -((alpha - beta) * x * mass) := by ring
    _ ≤ -((alpha - beta) * x * (c * L ^ 2)) :=
      neg_le_neg hmul
    _ = -4 * delta * x * L ^ 2 := by
      rw [hdelta]
      ring

end RHLean.Analysis
