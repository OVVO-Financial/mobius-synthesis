import Mathlib
import RHLean.Proof.JointGramControl
import RHLean.Proof.CompleteHighFamilyDecomposition

noncomputable section

open scoped BigOperators InnerProductSpace

namespace RHLean.Proof

/-- Away from a channel's assigned source shell, every concrete transport packet
vanishes. The packet window remains present; only the explicit shell amplitude is
zero. -/
theorem actualResidualPacket_squarePrefixHighTransportData_offShell
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n shell : ℕ)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (modeLabel : ℕ)
    (hshell : shell ≠ squarePrefixHighShell channel) :
    RHLean.Analysis.actualResidualPacket
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        shell channel modeLabel = 0 := by
  unfold RHLean.Analysis.actualResidualPacket RHLean.Kernel.packet
  apply Finset.sum_eq_zero
  intro packetIndex _
  simp [RHLean.Analysis.actualResidualEntry,
    squarePrefixHighTransportData,
    squarePrefixHighTransportAmplitude,
    hshell]

/-- The complete retained Farey-mode sum for one shell and channel is exactly the
channel contribution at its source shell and zero at every other shell. -/
theorem squarePrefixHighTransportModeSum_eq
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n shell : ℕ)
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    (∑ modeLabel ∈ fareyModeLabels (cutoff M),
      RHLean.Analysis.actualResidualPacket
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        shell channel modeLabel) =
      if shell = squarePrefixHighShell channel then
        squarePrefixHighChannelModeContribution
          cutoff M hcutoff Λ n channel
      else
        0 := by
  classical
  by_cases hshell : shell = squarePrefixHighShell channel
  · subst shell
    simp [squarePrefixHighChannelModeContribution]
  · rw [if_neg hshell]
    apply Finset.sum_eq_zero
    intro modeLabel _
    exact actualResidualPacket_squarePrefixHighTransportData_offShell
      cutoff M hcutoff Λ n shell channel modeLabel hshell

/-- The concrete transport residual is exactly the complete high-family
once-per-channel, all-mode contribution from the finite decomposition layer. -/
theorem actualResidual_squarePrefixHighTransportData_eq_familyContribution
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) :
    RHLean.Analysis.actualResidual
        (squarePrefixHighTransportData cutoff M hcutoff Λ n) =
      squarePrefixHighTransportFamilyContribution
        cutoff M hcutoff Λ n := by
  classical
  unfold RHLean.Analysis.actualResidual RHLean.Analysis.heightShellSum
    RHLean.Analysis.actualResidualShell
    squarePrefixHighTransportFamilyContribution
  change (∑ shell ∈ Finset.range (squarePrefixEntryShellCount n),
    ∑ channel ∈ squarePrefixHighHeightChannels Λ n,
      ∑ modeLabel ∈ fareyModeLabels (cutoff M),
        RHLean.Analysis.actualResidualPacket
          (squarePrefixHighTransportData cutoff M hcutoff Λ n)
          shell channel modeLabel) = _
  simp_rw [squarePrefixHighTransportModeSum_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro channel hchannel
  have hmem : squarePrefixHighShell channel ∈
      Finset.range (squarePrefixEntryShellCount n) :=
    Finset.mem_range.mpr (squarePrefixHighShell_lt_shellCount hchannel)
  rw [Finset.sum_eq_single (squarePrefixHighShell channel)]
  · simp
  · intro shell _ hne
    simp [hne]
  · intro hnot
    exact (hnot hmem).elim

/-- The concrete complete-family joint Gram energy, with shell, cofactor channel,
Farey mode, and resonant/nonresonant row retained as separate coordinates. -/
noncomputable def squarePrefixHighFullFamilyJointGramEnergy
    (skeleton : RHLean.Analysis.ResonantProjectionSkeleton ℂ ℂ)
    (M : ℕ) (hcutoff : 0 < skeleton.cutoff M)
    (Λ : ℝ) (n : ℕ) : ℝ :=
  RHLean.Analysis.actualJointGramEnergy skeleton M
    (squarePrefixHighTransportData skeleton.cutoff M hcutoff Λ n)

/-- Exact concrete full-family signed Gram identity. Every cross-shell,
cross-channel, cross-mode, and cross-row interaction remains in the single joint
Gram expression. -/
theorem squarePrefixHighTransportFamily_energy_eq_jointGram
    (skeleton : RHLean.Analysis.ResonantProjectionSkeleton ℂ ℂ)
    (M : ℕ) (hcutoff : 0 < skeleton.cutoff M)
    (Λ : ℝ) (n : ℕ) :
    ‖squarePrefixHighTransportFamilyContribution
        skeleton.cutoff M hcutoff Λ n‖ ^ 2 =
      squarePrefixHighFullFamilyJointGramEnergy
        skeleton M hcutoff Λ n := by
  unfold squarePrefixHighFullFamilyJointGramEnergy
  rw [← actualResidual_squarePrefixHighTransportData_eq_familyContribution]
  exact RHLean.Analysis.actualResidual_energy_eq_jointGram skeleton M
    (squarePrefixHighTransportData skeleton.cutoff M hcutoff Λ n)

/-- The defect-minus-child-correction-plus-unpaired recombination has the same
exact full joint Gram energy. The norm is taken only after all three signed
families have been recombined. -/
theorem squarePrefixHighFullDecomposition_energy_eq_jointGram
    (skeleton : RHLean.Analysis.ResonantProjectionSkeleton ℂ ℂ)
    (M : ℕ) (hcutoff : 0 < skeleton.cutoff M)
    (Λ : ℝ) (n : ℕ) :
    ‖(squarePrefixHighRetainedDefectContribution
          skeleton.cutoff M hcutoff Λ n -
        squarePrefixHighRetainedChildCorrection
          skeleton.cutoff M hcutoff Λ n) +
      squarePrefixHighUnpairedModeContribution
        skeleton.cutoff M hcutoff Λ n‖ ^ 2 =
      squarePrefixHighFullFamilyJointGramEnergy
        skeleton M hcutoff Λ n := by
  rw [← squarePrefixHighTransportFamilyContribution_eq_full_decomposition]
  exact squarePrefixHighTransportFamily_energy_eq_jointGram
    skeleton M hcutoff Λ n

/-- The remaining pointwise analytic obligation at one scale and square-prefix
endpoint. This is a proposition about the single complete signed Gram quantity,
not a list of separate positive component bounds. -/
def SquarePrefixHighFullFamilyJointGramEstimateAt
    (skeleton : RHLean.Analysis.ResonantProjectionSkeleton ℂ ℂ)
    (M : ℕ) (hcutoff : 0 < skeleton.cutoff M)
    (Λ : ℝ) (n : ℕ) (bound : ℝ) : Prop :=
  squarePrefixHighFullFamilyJointGramEnergy
    skeleton M hcutoff Λ n ≤ bound

/-- A concrete full-family joint Gram estimate gives the corresponding complete
high-family energy bound without discarding any cross interaction. -/
theorem squarePrefixHighTransportFamily_energy_le_of_jointGramEstimate
    (skeleton : RHLean.Analysis.ResonantProjectionSkeleton ℂ ℂ)
    (M : ℕ) (hcutoff : 0 < skeleton.cutoff M)
    (Λ : ℝ) (n : ℕ) (bound : ℝ)
    (hestimate : SquarePrefixHighFullFamilyJointGramEstimateAt
      skeleton M hcutoff Λ n bound) :
    ‖squarePrefixHighTransportFamilyContribution
        skeleton.cutoff M hcutoff Λ n‖ ^ 2 ≤ bound := by
  rw [squarePrefixHighTransportFamily_energy_eq_jointGram]
  exact hestimate

/-- Uniform concrete control of the complete signed joint Gram family. The
analytic proof of this proposition is intentionally not supplied by the exact
recombination layer. -/
def SquarePrefixHighFullFamilyJointGramBoundedBy
    (skeleton : RHLean.Analysis.ResonantProjectionSkeleton ℂ ℂ)
    (Λ : ℝ) (bound : ℕ → ℕ → ℝ) : Prop :=
  ∀ M n, ∀ hcutoff : 0 < skeleton.cutoff M,
    SquarePrefixHighFullFamilyJointGramEstimateAt
      skeleton M hcutoff Λ n (bound M n)

/-- Uniform joint Gram control transfers directly to the complete concrete
high-family energy. -/
theorem squarePrefixHighTransportFamily_energy_le_of_uniform_jointGramControl
    (skeleton : RHLean.Analysis.ResonantProjectionSkeleton ℂ ℂ)
    (Λ : ℝ) (bound : ℕ → ℕ → ℝ)
    (hcontrol : SquarePrefixHighFullFamilyJointGramBoundedBy
      skeleton Λ bound)
    (M n : ℕ) (hcutoff : 0 < skeleton.cutoff M) :
    ‖squarePrefixHighTransportFamilyContribution
        skeleton.cutoff M hcutoff Λ n‖ ^ 2 ≤ bound M n := by
  exact squarePrefixHighTransportFamily_energy_le_of_jointGramEstimate
    skeleton M hcutoff Λ n (bound M n) (hcontrol M n hcutoff)

end RHLean.Proof
