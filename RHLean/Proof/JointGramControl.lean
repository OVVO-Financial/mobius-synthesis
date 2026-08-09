import Mathlib
import RHLean.Proof.ActualForcingEstimates
import RHLean.Proof.ActualResidualDecomposition
import RHLean.Proof.HeightShellGram

noncomputable section

open scoped BigOperators InnerProductSpace

namespace RHLean.Analysis

/-- The two rows retained in the joint Gram index: resonant and nonresonant. -/
abbrev ActualResidualRow := Fin 2

/-- The resonant row label. -/
def actualResonantRow : ActualResidualRow := 0

/-- The nonresonant row label. -/
def actualNonresonantRow : ActualResidualRow := 1

/--
One packet contribution in a selected residual row. The resonant row is the
scale-dependent extraction of the packet. The nonresonant row is its exact
algebraic remainder. No orthogonality or Pythagorean identity is used.
-/
def actualJointRowPacket
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel)
    (denominatorMode : ℕ) (row : ActualResidualRow) : ℂ :=
  if row = actualResonantRow then
    skeleton.extraction M
      (actualResidualPacket data shell channel denominatorMode)
  else
    actualResidualPacket data shell channel denominatorMode -
      skeleton.extraction M
        (actualResidualPacket data shell channel denominatorMode)

/-- The two row contributions recombine exactly to the original packet. -/
theorem actualJointRowPacket_recombine
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel)
    (denominatorMode : ℕ) :
    actualJointRowPacket skeleton M data shell channel denominatorMode
        actualResonantRow +
      actualJointRowPacket skeleton M data shell channel denominatorMode
        actualNonresonantRow =
    actualResidualPacket data shell channel denominatorMode := by
  simp [actualJointRowPacket, actualResonantRow, actualNonresonantRow]

/-- Summing over the two explicit residual rows recovers the original packet. -/
theorem sum_actualJointRowPacket
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel)
    (denominatorMode : ℕ) :
    (∑ row : ActualResidualRow,
      actualJointRowPacket skeleton M data shell channel denominatorMode row) =
      actualResidualPacket data shell channel denominatorMode := by
  rw [Fin.sum_univ_two]
  exact actualJointRowPacket_recombine
    skeleton M data shell channel denominatorMode

/--
The complete finite joint index. Height shell, cofactor channel, denominator
mode, and residual row remain separate coordinates. Membership in the actual
cofactor and denominator-mode sets is carried by subtype fields.
-/
abbrev ActualJointGramIndex
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M) :=
  Fin data.shellCount ×
    {channel : ActualCofactorChannel // channel ∈ data.cofactorChannels} ×
      {denominatorMode : ℕ // denominatorMode ∈ data.denominatorModes} ×
        ActualResidualRow

/-- The actual complex contribution attached to one complete joint index. -/
def actualJointGramEntry
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (index : ActualJointGramIndex data) : ℂ :=
  actualJointRowPacket skeleton M data
    index.1.1 index.2.1.1 index.2.2.1.1 index.2.2.2

/-- Every complete joint index is enumerated exactly once by a finite ordinal. -/
noncomputable def actualJointGramEquivFin
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M) :
    ActualJointGramIndex data ≃
      Fin (Fintype.card (ActualJointGramIndex data)) :=
  Fintype.equivFin _

/-- The complete joint index occupying an enumerated Gram position. -/
noncomputable def actualJointGramEnumeratedIndex
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M)
    (index : Fin (Fintype.card (ActualJointGramIndex data))) :
    ActualJointGramIndex data :=
  (actualJointGramEquivFin data).symm index

/--
The natural-number sequence used by the compiled height-shell Gram theorem.
Only positions below the exact joint cardinality are nonzero.
-/
noncomputable def actualJointGramEnumeratedEntry
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (index : ℕ) : ℂ :=
  if hindex : index < Fintype.card (ActualJointGramIndex data) then
    actualJointGramEntry skeleton M data
      (actualJointGramEnumeratedIndex data ⟨index, hindex⟩)
  else
    0

/-- The cardinality of the complete shell/cofactor/mode/row joint index. -/
def actualJointGramCard
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M) : ℕ :=
  Fintype.card (ActualJointGramIndex data)

/-- The full signed sum of all enumerated joint contributions. -/
noncomputable def actualJointGramSum
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) : ℂ :=
  heightShellSum
    (actualJointGramEnumeratedEntry skeleton M data)
    (actualJointGramCard data)

/-- The complete diagonal energy of the joint index. -/
noncomputable def actualJointGramDiagonalEnergy
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) : ℝ :=
  heightShellDiagonalEnergy
    (actualJointGramEnumeratedEntry skeleton M data)
    (actualJointGramCard data)

/--
The complete signed off-diagonal Gram sum. Since the enumerated index contains
all four coordinates, this one object retains cross-shell, cross-cofactor,
cross-row, and cross-denominator-mode interactions.
-/
noncomputable def actualJointGramOffDiagonal
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) : ℝ :=
  heightShellOffDiagonalGram (𝕜 := ℂ)
    (actualJointGramEnumeratedEntry skeleton M data)
    (actualJointGramCard data)

/-- The full signed joint Gram expression. -/
noncomputable def actualJointGramEnergy
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) : ℝ :=
  actualJointGramDiagonalEnergy skeleton M data +
    2 * actualJointGramOffDiagonal skeleton M data

/--
Reindexing the finite ordinal enumeration gives the sum over the complete joint
index without changing any contribution.
-/
theorem actualJointGramSum_eq_fintypeSum
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) :
    actualJointGramSum skeleton M data =
      ∑ index : ActualJointGramIndex data,
        actualJointGramEntry skeleton M data index := by
  classical
  calc
    actualJointGramSum skeleton M data =
        ∑ index : Fin (actualJointGramCard data),
          actualJointGramEntry skeleton M data
            (actualJointGramEnumeratedIndex data index) := by
      unfold actualJointGramSum heightShellSum
      rw [← Fin.sum_univ_eq_sum_range]
      apply Fintype.sum_congr
      intro index
      have hindex :
          (index : ℕ) < Fintype.card (ActualJointGramIndex data) := by
        simpa [actualJointGramCard] using index.isLt
      unfold actualJointGramEnumeratedEntry
      split
      · apply congrArg (actualJointGramEntry skeleton M data)
        apply congrArg (fun i => (actualJointGramEquivFin data).symm i)
        exact Fin.ext rfl
      · rename_i hnot
        exact (hnot hindex).elim
    _ = ∑ index : ActualJointGramIndex data,
          actualJointGramEntry skeleton M data index := by
      exact (Fintype.sum_equiv
        (actualJointGramEquivFin data)
        (fun index : ActualJointGramIndex data =>
          actualJointGramEntry skeleton M data index)
        (fun index : Fin (actualJointGramCard data) =>
          actualJointGramEntry skeleton M data
            (actualJointGramEnumeratedIndex data index))
        (by
          intro index
          simp [actualJointGramEnumeratedIndex])).symm

/-- The complete joint-index sum is exactly the actual residual. -/
theorem actualJointGramFintypeSum_eq_actualResidual
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) :
    (∑ index : ActualJointGramIndex data,
      actualJointGramEntry skeleton M data index) =
      actualResidual data := by
  classical
  simp_rw [Fintype.sum_prod_type]
  simp only [actualJointGramEntry]
  simp_rw [sum_actualJointRowPacket]
  calc
    (∑ shell : Fin data.shellCount,
      ∑ channel : {channel : ActualCofactorChannel //
          channel ∈ data.cofactorChannels},
        ∑ denominatorMode : {denominatorMode : ℕ //
            denominatorMode ∈ data.denominatorModes},
          actualResidualPacket data shell channel denominatorMode) =
        ∑ shell : Fin data.shellCount,
          actualResidualShell data shell := by
      apply Fintype.sum_congr
      intro shell
      unfold actualResidualShell
      simp only [Finset.univ_eq_attach]
      rw [Finset.sum_attach
        (f := fun channel =>
          ∑ denominatorMode ∈ data.denominatorModes.attach,
            actualResidualPacket data shell channel denominatorMode)]
      apply Finset.sum_congr rfl
      intro channel _
      rw [Finset.sum_attach
        (f := fun denominatorMode =>
          actualResidualPacket data shell channel denominatorMode)]
    _ = actualResidual data := by
      simpa [actualResidual, heightShellSum] using
        (Fin.sum_univ_eq_sum_range
          (actualResidualShell data) data.shellCount)

/-- The enumerated complete joint sum is exactly the actual residual. -/
theorem actualJointGramSum_eq_actualResidual
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) :
    actualJointGramSum skeleton M data = actualResidual data := by
  rw [actualJointGramSum_eq_fintypeSum]
  exact actualJointGramFintypeSum_eq_actualResidual skeleton M data

/--
Exact full signed joint Gram identity for the actual residual. Every interaction
between distinct complete joint indices remains in the off-diagonal term.
-/
theorem actualResidual_energy_eq_jointGram
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M) :
    ‖actualResidual data‖ ^ 2 =
      actualJointGramEnergy skeleton M data := by
  rw [← actualJointGramSum_eq_actualResidual skeleton M data]
  exact energy_sum_heightShells
    (𝕜 := ℂ)
    (actualJointGramEnumeratedEntry skeleton M data)
    (actualJointGramCard data)

/--
A bound on the single full signed joint Gram expression controls the actual
residual energy. No separate positive estimate of any shell, cofactor, row, or
mode is required.
-/
theorem actualResidual_energy_le_of_jointGram_control
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (bound : ℝ)
    (hcontrol : actualJointGramEnergy skeleton M data ≤ bound) :
    ‖actualResidual data‖ ^ 2 ≤ bound := by
  rw [actualResidual_energy_eq_jointGram skeleton M data]
  exact hcontrol

/--
The recursive target for later checked or analytic control. The parent energy,
contraction coefficient, and forcing remain explicit; the hypothesis is on the
single signed joint Gram quantity rather than on its components separately.
-/
def ActualJointGramRecurrenceControl
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (rho parentEnergy forcing : ℝ) : Prop :=
  actualJointGramEnergy skeleton M data ≤
    rho * parentEnergy + forcing

/-- A recursive joint Gram control immediately gives the corresponding residual bound. -/
theorem actualResidual_energy_le_of_jointGram_recurrence
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (rho parentEnergy forcing : ℝ)
    (hcontrol : ActualJointGramRecurrenceControl
      skeleton M data rho parentEnergy forcing) :
    ‖actualResidual data‖ ^ 2 ≤ rho * parentEnergy + forcing := by
  exact actualResidual_energy_le_of_jointGram_control
    skeleton M data (rho * parentEnergy + forcing) hcontrol

end RHLean.Analysis