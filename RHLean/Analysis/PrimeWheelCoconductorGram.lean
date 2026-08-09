import Mathlib
import RHLean.Analysis.PrimeWheelFourierReduction

open scoped BigOperators ComplexConjugate
open AddChar

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Co-conductor of an additive frequency: the common divisor retained by the
frequency and the ambient modulus.  In particular the zero frequency has
co-conductor equal to the full modulus. -/
def additiveCoconductor
    {N : ℕ} [NeZero N] (r : ZMod N) : ℕ :=
  Nat.gcd r.val N

@[simp] theorem additiveCoconductor_zero
    {N : ℕ} [NeZero N] :
    additiveCoconductor (0 : ZMod N) = N := by
  simp [additiveCoconductor]

/-- Every additive co-conductor divides the ambient modulus. -/
theorem additiveCoconductor_dvd_modulus
    {N : ℕ} [NeZero N] (r : ZMod N) :
    additiveCoconductor r ∣ N := by
  exact Nat.gcd_dvd_right r.val N

/-- Every additive co-conductor lies between zero and the ambient modulus. -/
theorem additiveCoconductor_le_modulus
    {N : ℕ} [NeZero N] (r : ZMod N) :
    additiveCoconductor r ≤ N := by
  exact Nat.gcd_le_right r.val (Nat.pos_of_neZero N)

/-- The finite set of divisors that can index co-conductor packets. -/
def primeWheelCoconductorDivisors
    (W : PrimeWheelFiniteSystem) : Finset ℕ :=
  (Finset.range (W.modulus + 1)).filter fun d => d ∣ W.modulus

/-- The pinned-prefix contribution carried by one additive co-conductor. -/
def primeWheelCoconductorComponent
    (W : PrimeWheelFiniteSystem) (x d : ℕ) : ℂ :=
  ∑ r : ZMod W.modulus,
    if d = additiveCoconductor r then W.spectralPrefixAtom x r else 0

/-- The complete pinned spectral prefix is the sum of its co-conductor
components over the divisors of the modulus.  This is an exact finite
partition and uses no estimate or orthogonality. -/
theorem spectralPrefix_eq_sum_coconductorComponents
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    W.spectralPrefix x =
      ∑ d ∈ primeWheelCoconductorDivisors W,
        primeWheelCoconductorComponent W x d := by
  classical
  rw [W.spectralPrefix_eq_sum_atoms]
  unfold primeWheelCoconductorDivisors primeWheelCoconductorComponent
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hdvd : additiveCoconductor r ∣ W.modulus :=
    additiveCoconductor_dvd_modulus r
  have hle : additiveCoconductor r ≤ W.modulus :=
    additiveCoconductor_le_modulus r
  have hmem :
      additiveCoconductor r ∈
        (Finset.range (W.modulus + 1)).filter
          (fun d => d ∣ W.modulus) := by
    simp [Finset.mem_range, Nat.lt_succ_iff, hle, hdvd]
  simp [hmem]

/-- Full interaction between two co-conductor components.  No cross-packet
term is discarded. -/
def primeWheelCoconductorGramBlock
    (W : PrimeWheelFiniteSystem) (x d d' : ℕ) : ℂ :=
  primeWheelCoconductorComponent W x d *
    conj (primeWheelCoconductorComponent W x d')

/-- Exact co-conductor-pair decomposition of the complete signed pinned-prefix
Gram energy. -/
theorem intervalGramEnergy_eq_sum_coconductorGramBlocks
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    W.intervalGramEnergy x =
      ∑ d ∈ primeWheelCoconductorDivisors W,
        ∑ d' ∈ primeWheelCoconductorDivisors W,
          primeWheelCoconductorGramBlock W x d d' := by
  rw [W.intervalGramEnergy_eq_mul_conj,
    spectralPrefix_eq_sum_coconductorComponents]
  rw [map_sum]
  unfold primeWheelCoconductorGramBlock
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]

/-- Ramanujan kernel attached to one co-conductor packet.  It is the complete
additive-character sum over frequencies whose gcd with the modulus is `d`. -/
def primeWheelRamanujanKernel
    (W : PrimeWheelFiniteSystem) (d : ℕ)
    (z : ZMod W.modulus) : ℂ :=
  ∑ r : ZMod W.modulus,
    if d = additiveCoconductor r then
      ZMod.stdAddChar (z * r)
    else 0

/-- Exact physical-space Ramanujan-kernel formula for one co-conductor packet.
The arithmetic field and the pinned interval window remain separate, and the
kernel depends only on their displacement `b-a`. -/
theorem primeWheelCoconductorComponent_eq_ramanujanKernel
    (W : PrimeWheelFiniteSystem) (x d : ℕ) :
    primeWheelCoconductorComponent W x d =
      ((W.modulus : ℂ)⁻¹) *
        ∑ a : ZMod W.modulus,
          ∑ b : ZMod W.modulus,
            W.torusJointField a * W.torusPrefixWindow x b *
              primeWheelRamanujanKernel W d (b - a) := by
  classical
  unfold primeWheelCoconductorComponent
  calc
    (∑ r : ZMod W.modulus,
        if d = additiveCoconductor r then W.spectralPrefixAtom x r else 0) =
        ((W.modulus : ℂ)⁻¹) *
          ∑ r : ZMod W.modulus,
            if d = additiveCoconductor r then
              W.jointSpectrum r * W.prefixWindowSpectrum x (-r)
            else 0 := by
      unfold spectralPrefixAtom
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hcond : d = additiveCoconductor r
      · simp [hcond, mul_assoc]
      · simp [hcond]
    _ = ((W.modulus : ℂ)⁻¹) *
        ∑ r : ZMod W.modulus,
          ∑ a : ZMod W.modulus,
            ∑ b : ZMod W.modulus,
              if d = additiveCoconductor r then
                (ZMod.stdAddChar (-(a * r)) * W.torusJointField a) *
                  (ZMod.stdAddChar (-(b * (-r))) * W.torusPrefixWindow x b)
              else 0 := by
      congr 1
      unfold jointSpectrum prefixWindowSpectrum
      simp only [ZMod.dft_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hcond : d = additiveCoconductor r
      · simp only [hcond, if_true]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
      · simp [hcond]
    _ = ((W.modulus : ℂ)⁻¹) *
        ∑ a : ZMod W.modulus,
          ∑ b : ZMod W.modulus,
            ∑ r : ZMod W.modulus,
              if d = additiveCoconductor r then
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
              primeWheelRamanujanKernel W d (b - a) := by
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      unfold primeWheelRamanujanKernel
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hcond : d = additiveCoconductor r
      · simp only [hcond, if_true]
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
      · simp [hcond]

end RHLean.Analysis
