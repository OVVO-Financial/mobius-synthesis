import Mathlib
import RHLean.Analysis.PrimeWheelCoconductorTailBound

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

private theorem norm_sq_sub_le_two (x y : ℂ) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm := norm_sub_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x - y‖ := norm_nonneg (x - y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Exact subtraction form of the low-plus-tail decomposition.

This is the co-conductor analogue of the earlier geometric complement step:
once the ambient prefix and the complementary tail are controlled, the low
co-conductor sector is obtained by subtraction rather than by a second analytic
decomposition. -/
theorem primeWheelCoconductorLowPart_eq_spectralPrefix_sub_tail
    (W : PrimeWheelFiniteSystem) (x D : ℕ) :
    primeWheelCoconductorLowPart W x D =
      W.spectralPrefix x - primeWheelCoconductorTail W x D := by
  rw [spectralPrefix_eq_coconductorLowPart_add_tail]
  ring

/-- Pointwise norm transfer through the subtraction bridge. -/
theorem norm_primeWheelCoconductorLowPart_le_spectralPrefix_add_tail
    (W : PrimeWheelFiniteSystem) (x D : ℕ) :
    ‖primeWheelCoconductorLowPart W x D‖ ≤
      ‖W.spectralPrefix x‖ + ‖primeWheelCoconductorTail W x D‖ := by
  rw [primeWheelCoconductorLowPart_eq_spectralPrefix_sub_tail]
  exact norm_sub_le _ _

/-- Squared-energy form of the subtraction bridge.  No low-tail cross-term
estimate is required. -/
theorem norm_sq_primeWheelCoconductorLowPart_le_two_spectralPrefix_add_tail
    (W : PrimeWheelFiniteSystem) (x D : ℕ) :
    ‖primeWheelCoconductorLowPart W x D‖ ^ 2 ≤
      2 * ‖W.spectralPrefix x‖ ^ 2 +
        2 * ‖primeWheelCoconductorTail W x D‖ ^ 2 := by
  rw [primeWheelCoconductorLowPart_eq_spectralPrefix_sub_tail]
  exact norm_sq_sub_le_two _ _

/-- Abstract bound transfer in the manuscript's `S = A - T` form.  Any
independent ambient-prefix bound and tail bound immediately control the low
co-conductor sector; no packetwise low-sector estimate is needed. -/
theorem norm_sq_primeWheelCoconductorLowPart_le_of_ambient_tail_bounds
    (W : PrimeWheelFiniteSystem) (x D : ℕ)
    (ambientBound tailBound : ℝ)
    (hambient : ‖W.spectralPrefix x‖ ^ 2 ≤ ambientBound)
    (htail : ‖primeWheelCoconductorTail W x D‖ ^ 2 ≤ tailBound) :
    ‖primeWheelCoconductorLowPart W x D‖ ^ 2 ≤
      2 * ambientBound + 2 * tailBound := by
  calc
    ‖primeWheelCoconductorLowPart W x D‖ ^ 2 ≤
        2 * ‖W.spectralPrefix x‖ ^ 2 +
          2 * ‖primeWheelCoconductorTail W x D‖ ^ 2 :=
      norm_sq_primeWheelCoconductorLowPart_le_two_spectralPrefix_add_tail W x D
    _ ≤ 2 * ambientBound + 2 * tailBound := by
      nlinarith

end RHLean.Analysis
