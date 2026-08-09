import Mathlib
import RHLean.Analysis.PrimeWheelCoconductorLowGram
import RHLean.Analysis.PrimeWheelHarmonicCriterion

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Reduced modulus attached to a co-conductor packet. -/
def primeWheelReducedModulusOfCoconductor
    (W : PrimeWheelFiniteSystem) (d : ℕ) : ℕ :=
  W.modulus / d

/-- Away from the zero frequency, the reduced additive conductor is exactly the
ambient modulus divided by the additive co-conductor. -/
theorem reducedAdditiveConductor_eq_modulus_div_additiveCoconductor
    {N : ℕ} [NeZero N] (r : ZMod N) (hr : r ≠ 0) :
    reducedAdditiveConductor r = N / additiveCoconductor r := by
  simp [reducedAdditiveConductor, additiveCoconductor, hr]

/-- A proper co-conductor packet cannot contain the zero frequency. -/
theorem ne_zero_of_coconductor_lt_modulus
    (W : PrimeWheelFiniteSystem) {d : ℕ}
    (r : ZMod W.modulus)
    (hd : d = additiveCoconductor r)
    (hdlt : d < W.modulus) :
    r ≠ 0 := by
  intro hr
  subst r
  rw [additiveCoconductor_zero] at hd
  omega

/-- Every frequency in a proper `d`-packet has reduced additive conductor
`Q / d`.  This is the exact reduced-modulus label needed before introducing a
primitive residue parameter. -/
theorem reducedAdditiveConductor_eq_reducedModulus_of_coconductor
    (W : PrimeWheelFiniteSystem) {d : ℕ}
    (r : ZMod W.modulus)
    (hd : d = additiveCoconductor r)
    (hdlt : d < W.modulus) :
    reducedAdditiveConductor r =
      primeWheelReducedModulusOfCoconductor W d := by
  have hr : r ≠ 0 :=
    ne_zero_of_coconductor_lt_modulus W r hd hdlt
  rw [reducedAdditiveConductor_eq_modulus_div_additiveCoconductor r hr]
  unfold primeWheelReducedModulusOfCoconductor
  rw [← hd]

/-- The exact two-term summand obtained by pairing a frequency with its
additive inverse.  The packet tests are kept on the corresponding frequency,
so no gcd-negation lemma or cancellation estimate is hidden in the definition. -/
def primeWheelCoconductorPairedAtom
    (W : PrimeWheelFiniteSystem) (x d : ℕ)
    (r : ZMod W.modulus) : ℂ :=
  (if d = additiveCoconductor r then W.spectralPrefixAtom x r else 0) +
    (if d = additiveCoconductor (-r) then
      W.spectralPrefixAtom x (-r) else 0)

/-- Negation swaps the two terms of the paired atom exactly. -/
@[simp] theorem primeWheelCoconductorPairedAtom_neg
    (W : PrimeWheelFiniteSystem) (x d : ℕ)
    (r : ZMod W.modulus) :
    primeWheelCoconductorPairedAtom W x d (-r) =
      primeWheelCoconductorPairedAtom W x d r := by
  simp [primeWheelCoconductorPairedAtom, add_comm]

private theorem sum_neg_reindex
    (W : PrimeWheelFiniteSystem)
    (f : ZMod W.modulus → ℂ) :
    (∑ r : ZMod W.modulus, f (-r)) =
      ∑ r : ZMod W.modulus, f r := by
  simpa using
    (Equiv.sum_comp (Equiv.neg (ZMod W.modulus)) f)

/-- The complete paired `d`-packet sum. -/
def primeWheelCoconductorPairedSum
    (W : PrimeWheelFiniteSystem) (x d : ℕ) : ℂ :=
  ∑ r : ZMod W.modulus,
    primeWheelCoconductorPairedAtom W x d r

/-- Exact involutive pairing identity: summing the `r,-r` paired atoms counts
one co-conductor component twice.  No triangle inequality, orthogonality, or
analytic cancellation is used. -/
theorem primeWheelCoconductorPairedSum_eq_two_mul_component
    (W : PrimeWheelFiniteSystem) (x d : ℕ) :
    primeWheelCoconductorPairedSum W x d =
      2 * primeWheelCoconductorComponent W x d := by
  classical
  unfold primeWheelCoconductorPairedSum
    primeWheelCoconductorPairedAtom
    primeWheelCoconductorComponent
  rw [Finset.sum_add_distrib]
  have hneg :
      (∑ r : ZMod W.modulus,
        if d = additiveCoconductor (-r) then
          W.spectralPrefixAtom x (-r)
        else 0) =
      ∑ r : ZMod W.modulus,
        if d = additiveCoconductor r then
          W.spectralPrefixAtom x r
        else 0 := by
    simpa using
      (sum_neg_reindex W
        (fun r : ZMod W.modulus =>
          if d = additiveCoconductor r then
            W.spectralPrefixAtom x r
          else 0))
  rw [hneg]
  ring

private theorem coconductorAtom_eq_reducedModulusSupport
    (W : PrimeWheelFiniteSystem) (x : ℕ) {d : ℕ}
    (r : ZMod W.modulus)
    (hdlt : d < W.modulus) :
    (if d = additiveCoconductor r then
        W.spectralPrefixAtom x r
      else 0) =
      if primeWheelReducedModulusOfCoconductor W d =
          reducedAdditiveConductor r then
        if d = additiveCoconductor r then
          W.spectralPrefixAtom x r
        else 0
      else 0 := by
  by_cases hr : d = additiveCoconductor r
  · have hq :
        primeWheelReducedModulusOfCoconductor W d =
          reducedAdditiveConductor r :=
      (reducedAdditiveConductor_eq_reducedModulus_of_coconductor
        W r hr hdlt).symm
    rw [if_pos hr, if_pos hq]
  · simp [hr]

/-- On a proper packet, every active half of the paired summand carries the
same reduced-modulus label `Q / d`.  This theorem records the label without yet
claiming a quotient-level primitive-residue bijection. -/
theorem primeWheelCoconductorPairedAtom_reducedModulus_support
    (W : PrimeWheelFiniteSystem) (x : ℕ) {d : ℕ}
    (r : ZMod W.modulus)
    (hdlt : d < W.modulus) :
    primeWheelCoconductorPairedAtom W x d r =
      (if primeWheelReducedModulusOfCoconductor W d =
            reducedAdditiveConductor r then
        if d = additiveCoconductor r then
          W.spectralPrefixAtom x r
        else 0
      else 0) +
      (if primeWheelReducedModulusOfCoconductor W d =
            reducedAdditiveConductor (-r) then
        if d = additiveCoconductor (-r) then
          W.spectralPrefixAtom x (-r)
        else 0
      else 0) := by
  unfold primeWheelCoconductorPairedAtom
  exact congrArg₂ (fun a b : ℂ => a + b)
    (coconductorAtom_eq_reducedModulusSupport W x r hdlt)
    (coconductorAtom_eq_reducedModulusSupport W x (-r) hdlt)

end RHLean.Analysis
