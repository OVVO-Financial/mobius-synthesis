import Mathlib
import RHLean.Analysis.PrimeWheelHarmonicCriterion
import RHLean.Analysis.PrimeWheelCoconductorGram
import RHLean.Analysis.PrimeWheelCoconductorTail
import RHLean.Analysis.PrimeWheelCoconductorTailBound
import RHLean.Analysis.PrimeWheelCoconductorLowGram
import RHLean.Analysis.PrimeWheelCoconductorResiduePairing
import RHLean.Analysis.PrimeWheelCoconductorSubtractionBridge

open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- The pinned-prefix contribution carried by one reduced additive conductor.
The sum is over the complete finite torus; frequencies outside the selected
conductor are set to zero. -/
def primeWheelConductorComponent
    (W : PrimeWheelFiniteSystem) (x q : ℕ) : ℂ :=
  ∑ r : ZMod W.modulus,
    if q = reducedAdditiveConductor r then W.spectralPrefixAtom x r else 0

/-- The complete pinned spectral prefix is the sum of its conductor components.
No estimate or orthogonality is used: this is an exact finite partition. -/
theorem spectralPrefix_eq_sum_conductorComponents
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    W.spectralPrefix x =
      ∑ q ∈ Finset.range (W.modulus + 1),
        primeWheelConductorComponent W x q := by
  classical
  rw [W.spectralPrefix_eq_sum_atoms]
  unfold primeWheelConductorComponent
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hcond : reducedAdditiveConductor r ≤ W.modulus := by
    unfold reducedAdditiveConductor
    split_ifs
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt W.modulus_pos)
    · exact Nat.div_le_self _ _
  have hmem : reducedAdditiveConductor r ∈ Finset.range (W.modulus + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hcond)
  simp [hmem]

/-- Full interaction between two reduced-conductor components.  In particular,
`q ≠ q'` terms are retained rather than discarded or assumed orthogonal. -/
def primeWheelConductorGramBlock
    (W : PrimeWheelFiniteSystem) (x q q' : ℕ) : ℂ :=
  primeWheelConductorComponent W x q *
    conj (primeWheelConductorComponent W x q')

/-- Exact conductor-pair decomposition of the complete signed pinned-prefix
Gram energy.  This retains every cross-frequency and cross-conductor term. -/
theorem intervalGramEnergy_eq_sum_conductorGramBlocks
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    W.intervalGramEnergy x =
      ∑ q ∈ Finset.range (W.modulus + 1),
        ∑ q' ∈ Finset.range (W.modulus + 1),
          primeWheelConductorGramBlock W x q q' := by
  rw [W.intervalGramEnergy_eq_mul_conj,
    spectralPrefix_eq_sum_conductorComponents]
  rw [map_sum]
  unfold primeWheelConductorGramBlock
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]

end RHLean.Analysis
