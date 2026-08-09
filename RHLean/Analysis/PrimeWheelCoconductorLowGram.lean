import Mathlib
import RHLean.Analysis.PrimeWheelCoconductorGram
import RHLean.Analysis.PrimeWheelCoconductorTail

open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Divisor packets retained in the low co-conductor sector. -/
def primeWheelLowCoconductorDivisors
    (W : PrimeWheelFiniteSystem) (D : ℕ) : Finset ℕ :=
  (primeWheelCoconductorDivisors W).filter fun d => d ≤ D

/-- Exact divisor-packet expansion of the low co-conductor sector.  This is a
finite reindexing identity only; no estimate or orthogonality is used. -/
theorem primeWheelCoconductorLowPart_eq_sum_coconductorComponents
    (W : PrimeWheelFiniteSystem) (x D : ℕ) :
    primeWheelCoconductorLowPart W x D =
      ∑ d ∈ primeWheelLowCoconductorDivisors W D,
        primeWheelCoconductorComponent W x d := by
  classical
  unfold primeWheelCoconductorLowPart primeWheelLowCoconductorDivisors
    primeWheelCoconductorDivisors primeWheelCoconductorComponent
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hdvd : additiveCoconductor r ∣ W.modulus :=
    additiveCoconductor_dvd_modulus r
  have hle : additiveCoconductor r ≤ W.modulus :=
    additiveCoconductor_le_modulus r
  by_cases hlow : additiveCoconductor r ≤ D
  · have hmem :
        additiveCoconductor r ∈
          ((Finset.range (W.modulus + 1)).filter
            (fun d => d ∣ W.modulus)).filter (fun d => d ≤ D) := by
      simp [Finset.mem_range, Nat.lt_succ_iff, hle, hdvd, hlow]
    simp [hlow, hmem]
  · have hnotmem :
        additiveCoconductor r ∉
          ((Finset.range (W.modulus + 1)).filter
            (fun d => d ∣ W.modulus)).filter (fun d => d ≤ D) := by
      simp [Finset.mem_range, Nat.lt_succ_iff, hle, hdvd, hlow]
    simp [hlow, hnotmem]

/-- Signed Gram energy of the complete low co-conductor sector. -/
def primeWheelCoconductorLowGram
    (W : PrimeWheelFiniteSystem) (x D : ℕ) : ℂ :=
  primeWheelCoconductorLowPart W x D *
    conj (primeWheelCoconductorLowPart W x D)

/-- Exact signed double-packet expansion of the low sector.  Every diagonal and
cross-co-conductor interaction is retained.  In particular, this theorem does
not replace the signed sum by a sum of packet absolute values. -/
theorem primeWheelCoconductorLowGram_eq_sum_coconductorGramBlocks
    (W : PrimeWheelFiniteSystem) (x D : ℕ) :
    primeWheelCoconductorLowGram W x D =
      ∑ d ∈ primeWheelLowCoconductorDivisors W D,
        ∑ d' ∈ primeWheelLowCoconductorDivisors W D,
          primeWheelCoconductorGramBlock W x d d' := by
  unfold primeWheelCoconductorLowGram
  rw [primeWheelCoconductorLowPart_eq_sum_coconductorComponents]
  rw [map_sum]
  unfold primeWheelCoconductorGramBlock
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]

end RHLean.Analysis
