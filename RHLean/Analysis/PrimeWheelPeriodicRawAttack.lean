import RHLean.Arithmetic.PrimeProductLowerBound
import RHLean.Analysis.PhysicalDegreeOneLeastSquareChannels
import RHLean.Analysis.PrimeWheelRawPeriod
import RHLean.Analysis.PrimeWheelPeriodicRawBridge
import RHLean.Analysis.PrimeWheelLocalSpectrum
import RHLean.Analysis.PrimeWheelPeriodicRawConductorResponse
import RHLean.Analysis.PrimeWheelRawUnitOrbit
import RHLean.Analysis.PrimeWheelRawShellConstancy
import RHLean.Analysis.RamanujanDivisorBoundary
import RHLean.Analysis.PrimeWheelRamanujanIdentification
import RHLean.Analysis.PrimeWheelRamanujanBoundaryReduction
import RHLean.Analysis.PrimeWheelRawConductorCoefficient
import RHLean.Analysis.PrimeWheelRawConductorWeight
import RHLean.Analysis.PrimeWheelFullConductorRecombination
import RHLean.Analysis.SmallModulusResonance

/-!
# Periodic-raw conductor attack umbrella

This module collects the exact reductions that replace the oversized zero-padded
raw torus by the natural square-sensitive CRT period on every primorial block
from `k = 2` onward, while preserving the historical corrected residual exactly.

The current layer exposes the exact local `p^2` Fourier trichotomy, the signed
reduced-conductor response, unit-orbit invariance and shell constancy of the
actual periodic raw spectrum, and the identification of every occupied reduced-
conductor character kernel with the classical divisor-form Ramanujan sum.
For every conductor `q > 1`, both the raw interval and every shifted smooth
interval have their common bulk term cancelled exactly, leaving only finite
Möbius-weighted divisor-residue boundary defects.  The remaining common raw
shell Fourier coefficient is also eliminated: it is an exact finite arithmetic
divisor-tail sum indexed by the three local exponents `0,1,2`.

The normalized raw conductor coefficient has an exact local product law.
First-power conductor coordinates cost at most `2/p`, square coordinates cost
exactly `1/p^2`, and the total absolute mass over all exponent patterns is the
finite Euler product `prod_p (1 + 1/p^2)`.  A marked generating identity isolates
the wheel primes not dividing the pinned primorial lower endpoint.  These are
finite structural diagnostics only: they do not by themselves bound the signed
`q > 1` packet.

The full-conductor recombination restores the conductor-one shell before any
norm is taken.  Conductor one is proved to be exactly the additive zero
frequency; the historical corrected residual is then written as that zero atom
plus the explicit divisor-boundary packets over all divisor conductors `q > 1`.
Accordingly, the nonzero response and the `q > 1` packet are auxiliary exact
coordinates, not standalone RH-scale obligations.  The critical path remains
the full corrected residual with zero, raw, and smooth cancellation preserved.

The final lemmas below record two small-modulus diagnostics for that critical
path.  The isolated prime-`3` slot DFT cancels exactly, but restoring the
physical prime-`2` slot factors `1,-1,1` leaves a coherent nonzero residue.  In
the original Möbius coordinates the same phenomenon is an exact dyadic scale
descent: one complete `D9` increment splits into twelve odd terms at the current
scale minus six odd terms at half scale.  Thus the prime-`2` contribution is not
a positive error term to bound separately; it is a signed renormalization term.

The last two theorems recombine the three linear transition modes with the
entire least-square channel sum before applying this dyadic scale descent.  They
are the exact proof-side bridge to the combined signed target; no channelwise
absolute value is introduced.

No analytic estimate is claimed here.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- The prime-`2` local comb factor attached to physical slot `j`. -/
def physicalPrimeTwoSlotWeight (j : ℕ) : ℤ :=
  localPrimeComb 2 j

@[simp] theorem physicalPrimeTwoSlotWeight_one :
    physicalPrimeTwoSlotWeight 1 = 1 := by
  norm_num [physicalPrimeTwoSlotWeight, localPrimeComb]

@[simp] theorem physicalPrimeTwoSlotWeight_two :
    physicalPrimeTwoSlotWeight 2 = -1 := by
  norm_num [physicalPrimeTwoSlotWeight, localPrimeComb]

@[simp] theorem physicalPrimeTwoSlotWeight_three :
    physicalPrimeTwoSlotWeight 3 = 1 := by
  norm_num [physicalPrimeTwoSlotWeight, localPrimeComb]

/-- On the actual physical sites `4k+j`, the prime-`2` local factors are
respectively `1,-1,1`. -/
theorem localPrimeComb_two_physical_slots (k : ℕ) :
    localPrimeComb 2 (4 * k + 1) = 1 ∧
      localPrimeComb 2 (4 * k + 2) = -1 ∧
      localPrimeComb 2 (4 * k + 3) = 1 := by
  constructor
  · simp [localPrimeComb, pow_two, Nat.dvd_iff_mod_eq_zero,
      Nat.add_mod, Nat.mul_mod]
  · constructor
    · simp [localPrimeComb, pow_two, Nat.dvd_iff_mod_eq_zero,
        Nat.add_mod, Nat.mul_mod]
    · simp [localPrimeComb, pow_two, Nat.dvd_iff_mod_eq_zero,
        Nat.add_mod, Nat.mul_mod]

/-- Restoring the physical prime-`2` factors breaks the isolated cube-root
cancellation: the weighted phase sum is exactly `-2` times the middle phase. -/
theorem physicalPrimeTwoWeightedPrimeThreePhase_sum_eq
    (r : ZMod 9) (hr0 : r ≠ 0) (hr3 : 3 ∣ r.val) :
    ((physicalPrimeTwoSlotWeight 1 : ℤ) : ℂ) *
          physicalPrimeThreeSlotPhase 1 r +
        ((physicalPrimeTwoSlotWeight 2 : ℤ) : ℂ) *
          physicalPrimeThreeSlotPhase 2 r +
        ((physicalPrimeTwoSlotWeight 3 : ℤ) : ℂ) *
          physicalPrimeThreeSlotPhase 3 r =
      (-2 : ℂ) * physicalPrimeThreeSlotPhase 2 r := by
  have hphase := physicalPrimeThreeSlotPhase_sum_eq_zero r hr0 hr3
  simp only [physicalPrimeTwoSlotWeight_one,
    physicalPrimeTwoSlotWeight_two, physicalPrimeTwoSlotWeight_three,
    Int.cast_one, Int.cast_neg]
  calc
    1 * physicalPrimeThreeSlotPhase 1 r +
          (-1) * physicalPrimeThreeSlotPhase 2 r +
          1 * physicalPrimeThreeSlotPhase 3 r =
      (physicalPrimeThreeSlotPhase 1 r +
          physicalPrimeThreeSlotPhase 2 r +
          physicalPrimeThreeSlotPhase 3 r) -
        2 * physicalPrimeThreeSlotPhase 2 r := by ring
    _ = (-2 : ℂ) * physicalPrimeThreeSlotPhase 2 r := by
      rw [hphase]
      ring

/-- The actual shifted prime-`3` DFT with its physical prime-`2` slot factor
restored. -/
def physicalPrimeTwoWeightedPrimeThreeLocalRawSlotSpectrum
    (j : ℕ) (r : ZMod 9) : ℂ :=
  ((physicalPrimeTwoSlotWeight j : ℤ) : ℂ) *
    physicalPrimeThreeLocalRawSlotSpectrum j r

/-- **Exact raw obstruction at conductor three.**  The isolated shifted
prime-`3` DFTs cancel, but after the physical prime-`2` factors are restored the
three-slot raw contribution is the coherent residue `10 * phase₂`, not zero.
Any proof of the full physical bound must therefore cancel this term inside the
joint signed `raw - 2 * smooth` conductor packet (possibly together with other
conductor channels) before taking norms. -/
theorem physicalPrimeTwoWeightedPrimeThreeLocalRawSlotSpectrum_sum_eq
    (r : ZMod 9) (hr0 : r ≠ 0) (hr3 : 3 ∣ r.val) :
    physicalPrimeTwoWeightedPrimeThreeLocalRawSlotSpectrum 1 r +
        physicalPrimeTwoWeightedPrimeThreeLocalRawSlotSpectrum 2 r +
        physicalPrimeTwoWeightedPrimeThreeLocalRawSlotSpectrum 3 r =
      (10 : ℂ) * physicalPrimeThreeSlotPhase 2 r := by
  unfold physicalPrimeTwoWeightedPrimeThreeLocalRawSlotSpectrum
  rw [physicalPrimeThreeLocalRawSlotSpectrum_eq_mode,
    physicalPrimeThreeLocalRawSlotSpectrum_eq_mode,
    physicalPrimeThreeLocalRawSlotSpectrum_eq_mode]
  rw [physicalPrimeThreeLocalRawMode_eq_neg_five r hr0 hr3]
  have hweighted :=
    physicalPrimeTwoWeightedPrimeThreePhase_sum_eq r hr0 hr3
  calc
    ((physicalPrimeTwoSlotWeight 1 : ℤ) : ℂ) *
          (physicalPrimeThreeSlotPhase 1 r * (-5 : ℂ)) +
        ((physicalPrimeTwoSlotWeight 2 : ℤ) : ℂ) *
          (physicalPrimeThreeSlotPhase 2 r * (-5 : ℂ)) +
        ((physicalPrimeTwoSlotWeight 3 : ℤ) : ℂ) *
          (physicalPrimeThreeSlotPhase 3 r * (-5 : ℂ)) =
      (((physicalPrimeTwoSlotWeight 1 : ℤ) : ℂ) *
          physicalPrimeThreeSlotPhase 1 r +
        ((physicalPrimeTwoSlotWeight 2 : ℤ) : ℂ) *
          physicalPrimeThreeSlotPhase 2 r +
        ((physicalPrimeTwoSlotWeight 3 : ℤ) : ℂ) *
          physicalPrimeThreeSlotPhase 3 r) * (-5 : ℂ) := by ring
    _ = (10 : ℂ) * physicalPrimeThreeSlotPhase 2 r := by
      rw [hweighted]
      ring

/-- Twelve odd current-scale terms in one complete `D9` increment. -/
def physicalD9DyadicOuterBlock (L : ℕ) : ℤ :=
  (μ (4 * (9 * L + 2) + 1) + μ (4 * (9 * L + 2) + 3)) +
  (μ (4 * (9 * L + 3) + 1) + μ (4 * (9 * L + 3) + 3)) +
  (μ (4 * (9 * L + 4) + 1) + μ (4 * (9 * L + 4) + 3)) +
  (μ (4 * (9 * L + 5) + 1) + μ (4 * (9 * L + 5) + 3)) +
  (μ (4 * (9 * L + 6) + 1) + μ (4 * (9 * L + 6) + 3)) +
  (μ (4 * (9 * L + 7) + 1) + μ (4 * (9 * L + 7) + 3))

/-- Six odd terms at exactly half the physical scale in one complete `D9`
increment. -/
def physicalD9DyadicInnerBlock (L : ℕ) : ℤ :=
  μ (2 * (9 * L + 2) + 1) +
  μ (2 * (9 * L + 3) + 1) +
  μ (2 * (9 * L + 4) + 1) +
  μ (2 * (9 * L + 5) + 1) +
  μ (2 * (9 * L + 6) + 1) +
  μ (2 * (9 * L + 7) + 1)

/-- One complete nine-edge `D9` increment is exactly the six destination
four-cells. -/
theorem physicalD9_nine_step_eq_six_fourSlotCells (L : ℕ) :
    physicalD9 (9 * (L + 1)) - physicalD9 (9 * L) =
      fourSlotCellSum (9 * L + 2) +
      fourSlotCellSum (9 * L + 3) +
      fourSlotCellSum (9 * L + 4) +
      fourSlotCellSum (9 * L + 5) +
      fourSlotCellSum (9 * L + 6) +
      fourSlotCellSum (9 * L + 7) := by
  rw [physicalD9_nine_step_recurrence]
  rw [show 36 * L + 32 = 4 * (9 * L + 8) by ring,
    show 36 * L + 8 = 4 * (9 * L + 2) by ring]
  rw [moebiusPositivePrefix_four_mul_eq_fourSlotCellSum,
    moebiusPositivePrefix_four_mul_eq_fourSlotCellSum]
  have hprefix :
      (∑ k ∈ Finset.range (9 * L + 8), fourSlotCellSum k) =
        (∑ k ∈ Finset.range (9 * L + 2), fourSlotCellSum k) +
          fourSlotCellSum (9 * L + 2) +
          fourSlotCellSum (9 * L + 3) +
          fourSlotCellSum (9 * L + 4) +
          fourSlotCellSum (9 * L + 5) +
          fourSlotCellSum (9 * L + 6) +
          fourSlotCellSum (9 * L + 7) := by
    rw [show 9 * L + 8 = (9 * L + 7) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 7 = (9 * L + 6) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 6 = (9 * L + 5) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 5 = (9 * L + 4) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 4 = (9 * L + 3) + 1 by omega,
      Finset.sum_range_succ]
    rw [show 9 * L + 3 = (9 * L + 2) + 1 by omega,
      Finset.sum_range_succ]
  rw [hprefix]
  ring

/-- **Dyadic renormalization of the prime-three defect block.**  The current
scale second-slot terms are not discarded or bounded absolutely; Möbius
doubling sends them with the opposite sign to an exact half-scale block. -/
theorem physicalD9_nine_step_dyadic_compression (L : ℕ) :
    physicalD9 (9 * (L + 1)) - physicalD9 (9 * L) =
      physicalD9DyadicOuterBlock L - physicalD9DyadicInnerBlock L := by
  rw [physicalD9_nine_step_eq_six_fourSlotCells]
  simp only [fourSlotCellSum_eq]
  unfold physicalD9DyadicOuterBlock physicalD9DyadicInnerBlock
  ring

/-- **Exact recombination of all Mertens-visible physical channels.**  The
three degree-one transition modes and the entire disjoint least-square defect
partition recombine before any norm into the unweighted destination four-cell
sum.  This is the signed form of the target quantity. -/
theorem physicalCombinedLinearChannels_eq_destinationFourSlotSum
    (K : ℕ) :
    physicalTransitionTa K + physicalTransitionTb K + physicalTransitionTc K +
        (∑ p ∈ physicalLeastSquarePrimes K,
          physicalLeastSquareChannel K p) =
      ∑ k ∈ Finset.range K, fourSlotCellSum (k + 1) := by
  rw [← physicalTransitionD_eq_sum_leastSquareChannels]
  rw [← physicalDegreeOneT_eq_linearTransitionMoments]
  rw [physicalDegreeOneT_eq_leastSquareNoneSum,
    physicalTransitionD_eq_leastSquareSupportedSum]
  have hpart := Finset.sum_filter_add_sum_filter_not
    (Finset.range K)
    (fun k => physicalLeastOddSquarePrime k = none)
    physicalDefectEdgeValue
  calc
    (∑ k ∈ Finset.range K with physicalLeastOddSquarePrime k = none,
        physicalDefectEdgeValue k) +
        (∑ k ∈ Finset.range K with physicalLeastOddSquarePrime k ≠ none,
          physicalDefectEdgeValue k) =
      ∑ k ∈ Finset.range K, physicalDefectEdgeValue k := by
        simpa using hpart
    _ = ∑ k ∈ Finset.range K, fourSlotCellSum (k + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact physicalDefectEdgeValue_eq_fourSlotCellSum k

/-- **Combined signed dyadic scale descent.**  After all transition and
least-square channels have been recombined, the prime-`2` cell compression is
applied once to the whole object.  The result is a current-scale odd sum minus
a half-scale odd sum; no `D_{p^2}` term is bounded separately. -/
theorem physicalCombinedLinearChannels_eq_dyadicScaleDescent
    (K : ℕ) :
    physicalTransitionTa K + physicalTransitionTb K + physicalTransitionTc K +
        (∑ p ∈ physicalLeastSquarePrimes K,
          physicalLeastSquareChannel K p) =
      (∑ k ∈ Finset.range K,
        (μ (4 * (k + 1) + 1) + μ (4 * (k + 1) + 3))) -
      ∑ k ∈ Finset.range K, μ (2 * (k + 1) + 1) := by
  rw [physicalCombinedLinearChannels_eq_destinationFourSlotSum]
  calc
    (∑ k ∈ Finset.range K, fourSlotCellSum (k + 1)) =
        ∑ k ∈ Finset.range K,
          ((μ (4 * (k + 1) + 1) + μ (4 * (k + 1) + 3)) -
            μ (2 * (k + 1) + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [fourSlotCellSum_eq]
      ring
    _ =
        (∑ k ∈ Finset.range K,
          (μ (4 * (k + 1) + 1) + μ (4 * (k + 1) + 3))) -
        ∑ k ∈ Finset.range K, μ (2 * (k + 1) + 1) := by
      rw [Finset.sum_sub_distrib]

end RHLean.Analysis
