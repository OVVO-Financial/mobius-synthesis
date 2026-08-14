import Mathlib
import RHLean.Analysis.PrimeSieveClassicalDyadicVariation

/-!
# Classical Mobius--chord dispersion for the reciprocal prime discrepancy

The preceding classical-variation layer rewrites the packet-energy input in
terms of dyadic quadratic variation of the clipped classical discrepancy

`D(d) = pi(max y (floor (x / d))) - Li(max y (floor (x / d)))`.

This module performs the matching exact change of coordinates on the remaining
Mobius-dispersion input.  The boundary-free Abel potential is already known to
vanish outside its dyadic block and to equal the classical chord residual on the
block.  Consequently both the block contribution and the full mean-zero wavelet
error are literally Mobius pairings against classical `pi - Li` chord residuals.

No Mobius cancellation estimate is proved here.  The point is to expose the
remaining signed analytic input in the same classical coordinate as the
quadratic-variation premise, and to preserve the stronger block-local route
introduced in the classical-variation attack.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- Mobius pairing against the classical chord residual on one occupied dyadic
reciprocal block. -/
def primeSieveDyadicBlockMobiusChordContribution
    (y x j : ℕ) : ℂ :=
  ∑ d ∈ primeSieveDyadicBlock y x j,
    (((μ d : ℤ) : ℂ)) * primeSieveDyadicChordResidual y x j d

/-- Classical chord energy carried by one dyadic reciprocal block. -/
def primeSieveDyadicBlockChordEnergy (y x j : ℕ) : ℝ :=
  ∑ d ∈ primeSieveDyadicBlock y x j,
    ‖primeSieveDyadicChordResidual y x j d‖ ^ 2

/-- On an occupied block, the boundary-free Abel contribution is exactly the
Mobius pairing against the classical chord residual. -/
theorem primeSieveDyadicBlockWaveletMertensContribution_eq_mobiusChordContribution
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    primeSieveDyadicBlockWaveletMertensContribution y x j =
      primeSieveDyadicBlockMobiusChordContribution y x j := by
  rw [primeSieveDyadicBlockWaveletMertensContribution_eq_boundaryFreeAbel hj]
  calc
    (∑ d ∈ primeSieveQuotientSupport y x,
        (((μ d : ℤ) : ℂ)) * primeSieveDyadicBlockAbelPotential y x j d) =
      ∑ d ∈ primeSieveQuotientSupport y x,
        if d ∈ primeSieveDyadicBlock y x j then
          (((μ d : ℤ) : ℂ)) * primeSieveDyadicBlockAbelPotential y x j d
        else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hdB : d ∈ primeSieveDyadicBlock y x j
          · simp [hdB]
          · have hz := primeSieveDyadicBlockAbelPotential_eq_zero_of_not_mem
              hj hd hdB
            simp [hdB, hz]
    _ = ∑ d ∈ primeSieveDyadicBlock y x j,
          (((μ d : ℤ) : ℂ)) * primeSieveDyadicBlockAbelPotential y x j d := by
          rw [← Finset.sum_filter]
          have hfilter :
              (primeSieveQuotientSupport y x).filter
                  (fun d => d ∈ primeSieveDyadicBlock y x j) =
                primeSieveDyadicBlock y x j := by
            ext d
            simp [mem_primeSieveDyadicBlock]
          rw [hfilter]
    _ = primeSieveDyadicBlockMobiusChordContribution y x j := by
          unfold primeSieveDyadicBlockMobiusChordContribution
          apply Finset.sum_congr rfl
          intro d hdB
          rw [primeSieveDyadicBlockAbelPotential_eq_chordResidual hdB]

/-- On an occupied block, Abel-potential energy is exactly classical chord
energy. -/
theorem primeSieveDyadicBlockAbelPotentialEnergy_eq_chordEnergy
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    primeSieveDyadicBlockAbelPotentialEnergy y x j =
      primeSieveDyadicBlockChordEnergy y x j := by
  unfold primeSieveDyadicBlockAbelPotentialEnergy
    primeSieveDyadicBlockChordEnergy
  calc
    (∑ d ∈ primeSieveQuotientSupport y x,
        ‖primeSieveDyadicBlockAbelPotential y x j d‖ ^ 2) =
      ∑ d ∈ primeSieveQuotientSupport y x,
        if d ∈ primeSieveDyadicBlock y x j then
          ‖primeSieveDyadicBlockAbelPotential y x j d‖ ^ 2
        else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hdB : d ∈ primeSieveDyadicBlock y x j
          · simp [hdB]
          · have hz := primeSieveDyadicBlockAbelPotential_eq_zero_of_not_mem
              hj hd hdB
            simp [hdB, hz]
    _ = ∑ d ∈ primeSieveDyadicBlock y x j,
          ‖primeSieveDyadicBlockAbelPotential y x j d‖ ^ 2 := by
          rw [← Finset.sum_filter]
          have hfilter :
              (primeSieveQuotientSupport y x).filter
                  (fun d => d ∈ primeSieveDyadicBlock y x j) =
                primeSieveDyadicBlock y x j := by
            ext d
            simp [mem_primeSieveDyadicBlock]
          rw [hfilter]
    _ = ∑ d ∈ primeSieveDyadicBlock y x j,
          ‖primeSieveDyadicChordResidual y x j d‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro d hdB
          rw [primeSieveDyadicBlockAbelPotential_eq_chordResidual hdB]

/-- Full Mobius pairing against the classical dyadic chord field. -/
def primeSieveDyadicMobiusChordSum (y x : ℕ) : ℂ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    primeSieveDyadicBlockMobiusChordContribution y x j

/-- The complete mean-zero dyadic prime error is exactly the classical
Mobius--chord pairing. -/
theorem primeSieveDyadicWaveletPNTError_eq_mobiusChordSum
    (y x : ℕ) :
    primeSieveDyadicWaveletPNTError y x =
      primeSieveDyadicMobiusChordSum y x := by
  rw [primeSieveDyadicWaveletPNTError_eq_sum_blockContributions]
  unfold primeSieveDyadicMobiusChordSum
  apply Finset.sum_congr rfl
  intro j hj
  exact
    primeSieveDyadicBlockWaveletMertensContribution_eq_mobiusChordContribution hj

/-- Global Mobius dispersion stated entirely in the classical chord coordinate. -/
def DyadicMobiusChordDispersionBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        ‖primeSieveDyadicMobiusChordSum
            (primorialPNTPrimeSieveCutoff k) x‖ ^ 2 ≤
          C * Real.rpow ((x : ℝ) + 1) ε *
            primeSieveDyadicChordEnergy
              (primorialPNTPrimeSieveCutoff k) x

/-- The classical Mobius--chord dispersion statement is exactly equivalent to
the existing global boundary-free Abel dispersion statement. -/
theorem dyadicMobiusChordDispersionBlockBounded_iff_mobiusDispersion :
    DyadicMobiusChordDispersionBlockBoundedStatement ↔
      DyadicMobiusDispersionBlockBoundedStatement := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hCb⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro k x hk hlow hup
    rw [primeSieveDyadicWaveletPNTError_eq_mobiusChordSum,
      primeSieveDyadicAbelPotentialEnergy_eq_chordEnergy]
    exact hCb k x hk hlow hup
  · intro h ε hε
    obtain ⟨C, hC, hCb⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro k x hk hlow hup
    rw [← primeSieveDyadicWaveletPNTError_eq_mobiusChordSum,
      ← primeSieveDyadicAbelPotentialEnergy_eq_chordEnergy]
    exact hCb k x hk hlow hup

/-- Block-local Mobius dispersion stated entirely in the classical chord
coordinate. -/
def DyadicBlockwiseMobiusChordDispersionBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x j : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        j ∈ primeSieveDyadicBlockIndices
          (primorialPNTPrimeSieveCutoff k) x →
        ‖primeSieveDyadicBlockMobiusChordContribution
            (primorialPNTPrimeSieveCutoff k) x j‖ ^ 2 ≤
          C * Real.rpow ((x : ℝ) + 1) ε *
            primeSieveDyadicBlockChordEnergy
              (primorialPNTPrimeSieveCutoff k) x j

/-- Blockwise classical chord dispersion is exactly equivalent to the blockwise
boundary-free Abel formulation. -/
theorem dyadicBlockwiseMobiusChordDispersionBlockBounded_iff_blockwiseMobiusDispersion :
    DyadicBlockwiseMobiusChordDispersionBlockBoundedStatement ↔
      DyadicBlockwiseMobiusDispersionBlockBoundedStatement := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hCb⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro k x j hk hlow hup hj
    rw [primeSieveDyadicBlockWaveletMertensContribution_eq_mobiusChordContribution hj,
      primeSieveDyadicBlockAbelPotentialEnergy_eq_chordEnergy hj]
    exact hCb k x j hk hlow hup hj
  · intro h ε hε
    obtain ⟨C, hC, hCb⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro k x j hk hlow hup hj
    rw [← primeSieveDyadicBlockWaveletMertensContribution_eq_mobiusChordContribution hj,
      ← primeSieveDyadicBlockAbelPotentialEnergy_eq_chordEnergy hj]
    exact hCb k x j hk hlow hup hj

/-- The stronger blockwise classical chord-dispersion premise implies global
classical Mobius--chord dispersion, with only the subpolynomial block-count loss
already proved in the preceding layer. -/
theorem dyadicMobiusChordDispersionBlockBounded_of_blockwiseChord
    (hD : DyadicBlockwiseMobiusChordDispersionBlockBoundedStatement) :
    DyadicMobiusChordDispersionBlockBoundedStatement := by
  apply dyadicMobiusChordDispersionBlockBounded_iff_mobiusDispersion.mpr
  apply dyadicMobiusDispersionBlockBounded_of_blockwise
  exact
    dyadicBlockwiseMobiusChordDispersionBlockBounded_iff_blockwiseMobiusDispersion.mp hD

/-- RH route with the packet input and the global dispersion input both stated
in classical `pi - Li` chord geometry. -/
theorem riemannHypothesis_of_baseEightClippedVariationMobiusChordPackage
    (hC : DyadicCoherentChannelRHScale)
    (hQ : DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement)
    (hD : DyadicMobiusChordDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_baseEightClippedDiscrepancyQuadraticVariationChordPackage hC hQ
  exact dyadicMobiusChordDispersionBlockBounded_iff_mobiusDispersion.mp hD

/-- Stronger localized RH route: classical dyadic quadratic variation together
with blockwise classical Mobius--chord dispersion suffices, since the logarithmic
number of occupied blocks is absorbed into an epsilon. -/
theorem riemannHypothesis_of_baseEightClippedVariationBlockwiseMobiusChordPackage
    (hC : DyadicCoherentChannelRHScale)
    (hQ : DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement)
    (hD : DyadicBlockwiseMobiusChordDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_baseEightClippedDiscrepancyVariationBlockwiseMobiusPackage
    hC hQ
  exact
    dyadicBlockwiseMobiusChordDispersionBlockBounded_iff_blockwiseMobiusDispersion.mp hD

end RHLean.Analysis
