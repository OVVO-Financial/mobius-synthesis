import Mathlib
import RHLean.Analysis.PrimeWheelCoconductorGram

open scoped BigOperators
open AddChar

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- The primitive-side contribution from additive co-conductors at most `D`. -/
def primeWheelCoconductorLowPart
    (W : PrimeWheelFiniteSystem) (x D : ℕ) : ℂ :=
  ∑ r : ZMod W.modulus,
    if additiveCoconductor r ≤ D then W.spectralPrefixAtom x r else 0

/-- The high-co-conductor tail.  Since every additive co-conductor divides the
ambient modulus, this is exactly the sum of the packets indexed by divisors
`d ∣ W.modulus` with `D < d`. -/
def primeWheelCoconductorTail
    (W : PrimeWheelFiniteSystem) (x D : ℕ) : ℂ :=
  ∑ r : ZMod W.modulus,
    if D < additiveCoconductor r then W.spectralPrefixAtom x r else 0

/-- Exact low-plus-tail decomposition of the complete pinned spectral prefix. -/
theorem spectralPrefix_eq_coconductorLowPart_add_tail
    (W : PrimeWheelFiniteSystem) (x D : ℕ) :
    W.spectralPrefix x =
      primeWheelCoconductorLowPart W x D +
        primeWheelCoconductorTail W x D := by
  classical
  rw [W.spectralPrefix_eq_sum_atoms]
  unfold primeWheelCoconductorLowPart primeWheelCoconductorTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hlow : additiveCoconductor r ≤ D
  · have hnotTail : ¬D < additiveCoconductor r := Nat.not_lt_of_ge hlow
    simp [hlow, hnotTail]
  · have htail : D < additiveCoconductor r := Nat.lt_of_not_ge hlow
    simp [hlow, htail]

/-- The summed Ramanujan kernel of the complete high-co-conductor tail.  Keeping
this sum intact preserves cancellation between distinct high co-conductors. -/
def primeWheelCoconductorTailKernel
    (W : PrimeWheelFiniteSystem) (D : ℕ)
    (z : ZMod W.modulus) : ℂ :=
  ∑ r : ZMod W.modulus,
    if D < additiveCoconductor r then
      ZMod.stdAddChar (z * r)
    else 0

/-- Exact physical-space formula for the summed high-co-conductor tail.  The
high packets are combined inside one kernel before any absolute value is taken. -/
theorem primeWheelCoconductorTail_eq_ramanujanTailKernel
    (W : PrimeWheelFiniteSystem) (x D : ℕ) :
    primeWheelCoconductorTail W x D =
      ((W.modulus : ℂ)⁻¹) *
        ∑ a : ZMod W.modulus,
          ∑ b : ZMod W.modulus,
            W.torusJointField a * W.torusPrefixWindow x b *
              primeWheelCoconductorTailKernel W D (b - a) := by
  classical
  unfold primeWheelCoconductorTail
  calc
    (∑ r : ZMod W.modulus,
        if D < additiveCoconductor r then W.spectralPrefixAtom x r else 0) =
        ((W.modulus : ℂ)⁻¹) *
          ∑ r : ZMod W.modulus,
            if D < additiveCoconductor r then
              W.jointSpectrum r * W.prefixWindowSpectrum x (-r)
            else 0 := by
      unfold spectralPrefixAtom
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases htail : D < additiveCoconductor r
      · simp [htail, mul_assoc]
      · simp [htail]
    _ = ((W.modulus : ℂ)⁻¹) *
        ∑ r : ZMod W.modulus,
          ∑ a : ZMod W.modulus,
            ∑ b : ZMod W.modulus,
              if D < additiveCoconductor r then
                (ZMod.stdAddChar (-(a * r)) * W.torusJointField a) *
                  (ZMod.stdAddChar (-(b * (-r))) * W.torusPrefixWindow x b)
              else 0 := by
      congr 1
      unfold jointSpectrum prefixWindowSpectrum
      simp only [ZMod.dft_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases htail : D < additiveCoconductor r
      · simp only [htail, if_true]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
      · simp [htail]
    _ = ((W.modulus : ℂ)⁻¹) *
        ∑ a : ZMod W.modulus,
          ∑ b : ZMod W.modulus,
            ∑ r : ZMod W.modulus,
              if D < additiveCoconductor r then
                (ZMod.stdAddChar (-(a * r)) * W.torusJointField a) *
                  (ZMod.stdAddChar (-(b * (-r))) * W.torusPrefixWindow x b)
              else 0 := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ((W.modulus : ℂ)⁻¹) *
        ∑ a : ZMod W.modulus,
          ∑ b : ZMod W.modulus,
            W.torusJointField a * W.torusPrefixWindow x b *
              primeWheelCoconductorTailKernel W D (b - a) := by
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      unfold primeWheelCoconductorTailKernel
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases htail : D < additiveCoconductor r
      · simp only [htail, if_true]
        have hchar :
            ZMod.stdAddChar (-(a * r)) *
                ZMod.stdAddChar (-(b * (-r))) =
              ZMod.stdAddChar ((b - a) * r) := by
          rw [← map_add_eq_mul]
          congr 1
          ring
        calc
          (ZMod.stdAddChar (-(a * r)) * W.torusJointField a) *
                (ZMod.stdAddChar (-(b * (-r))) * W.torusPrefixWindow x b) =
              W.torusJointField a * W.torusPrefixWindow x b *
                (ZMod.stdAddChar (-(a * r)) *
                  ZMod.stdAddChar (-(b * (-r)))) := by ring
          _ = W.torusJointField a * W.torusPrefixWindow x b *
                ZMod.stdAddChar ((b - a) * r) := by rw [hchar]
      · simp [htail]

/-- Shifted interval response of the summed high-co-conductor kernel.  An
absolute tail estimate should bound this object before pairing it with the
prime-wheel field. -/
def primeWheelCoconductorTailWindowResponse
    (W : PrimeWheelFiniteSystem) (x D : ℕ)
    (a : ZMod W.modulus) : ℂ :=
  ∑ b : ZMod W.modulus,
    W.torusPrefixWindow x b *
      primeWheelCoconductorTailKernel W D (b - a)

/-- The exact tail formula with all interval cancellation packaged inside the
shifted kernel response. -/
theorem primeWheelCoconductorTail_eq_jointField_pairing
    (W : PrimeWheelFiniteSystem) (x D : ℕ) :
    primeWheelCoconductorTail W x D =
      ((W.modulus : ℂ)⁻¹) *
        ∑ a : ZMod W.modulus,
          W.torusJointField a *
            primeWheelCoconductorTailWindowResponse W x D a := by
  rw [primeWheelCoconductorTail_eq_ramanujanTailKernel]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  unfold primeWheelCoconductorTailWindowResponse
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

end RHLean.Analysis
