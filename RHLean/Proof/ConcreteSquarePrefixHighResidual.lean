import Mathlib
import RHLean.Proof.FareyModesAndTransportWindows

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The exact zero rational mode `(0,1)`, encoded by the compiled pairing map. -/
def zeroFareyModeLabel : ℕ :=
  Nat.pair 0 1

@[simp] theorem unpair_zeroFareyModeLabel :
    Nat.unpair zeroFareyModeLabel = (0, 1) := by
  simp [zeroFareyModeLabel]

/-- Every positive Farey cutoff contains the exact zero mode. -/
theorem zeroFareyModeLabel_mem (R : ℕ) (hR : 0 < R) :
    zeroFareyModeLabel ∈ fareyModeLabels R := by
  have hR1 : 1 ≤ R := by omega
  rw [mem_fareyModeLabels]
  simp [mem_fareyModePairs, hR1]

/-- Product fibers are pairwise disjoint because an ordered pair has one exact product. -/
theorem orderedCoprimeFactorPairs_pairwiseDisjoint (Q : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range (Q + 1)))
      orderedCoprimeFactorPairs := by
  intro m _ m' _ hne
  change Disjoint (orderedCoprimeFactorPairs m) (orderedCoprimeFactorPairs m')
  rw [Finset.disjoint_left]
  intro p hp hp'
  have hprod := product_eq_of_mem_orderedCoprimeFactorPairs hp
  have hprod' := product_eq_of_mem_orderedCoprimeFactorPairs hp'
  exact hne (hprod.symm.trans hprod')

/-- The existing nested high-height expansion is exactly the sum over the finite
high ordered-pair support. No product fiber or ordered orientation is removed. -/
theorem squarePrefixHighHeightExpansionRat_eq_pairSum
    (Λ : ℝ) (n : ℕ) :
    squarePrefixHighHeightExpansionRat Λ n =
      ∑ p ∈ squarePrefixHighHeightPairs Λ n,
        (((μ p.1 : ℤ) : ℚ)) *
          normalizedChannelAmplitudeRat (actualChannelOfPair p) := by
  classical
  unfold squarePrefixHighHeightExpansionRat squarePrefixHighHeightPairs
    squarePrefixCofactorPairs
  rw [← Finset.sum_biUnion
    (orderedCoprimeFactorPairs_pairwiseDisjoint
      (RHLean.Analysis.squarePrefixEndpoint n))]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hlow : IsLowHeightPair Λ n p
  · simp [hlow]
  · simp [hlow]

/-- Complex form of the exact finite high ordered-pair sum. -/
theorem squarePrefixHighHeightExpansion_eq_pairSum
    (Λ : ℝ) (n : ℕ) :
    squarePrefixHighHeightExpansion Λ n =
      ∑ p ∈ squarePrefixHighHeightPairs Λ n,
        (((μ p.1 : ℤ) : ℂ)) *
          normalizedChannelAmplitude (actualChannelOfPair p) := by
  have hrat := squarePrefixHighHeightExpansionRat_eq_pairSum Λ n
  have hcast := congrArg (fun x : ℚ => (x : ℂ)) hrat
  simpa [squarePrefixHighHeightExpansion, normalizedChannelAmplitude] using hcast

/-- Reindex the exact high ordered-pair sum by the injective concrete channel map. -/
theorem squarePrefixHighHeightExpansion_eq_channelSum
    (Λ : ℝ) (n : ℕ) :
    squarePrefixHighHeightExpansion Λ n =
      ∑ channel ∈ squarePrefixHighHeightChannels Λ n,
        (((μ channel.lowerCofactor : ℤ) : ℂ)) *
          normalizedChannelAmplitude channel := by
  rw [squarePrefixHighHeightExpansion_eq_pairSum]
  unfold squarePrefixHighHeightChannels
  rw [Finset.sum_image actualChannelOfPair_injective.injOn]
  rfl

/-- The exact source shell is the square block in which the ordered product enters. -/
def squarePrefixHighShell
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℕ :=
  orderedChannelEntryShell channel

/-- Exact singleton packet start for signal realization. This is deliberately
separate from the transport-window start used by the later dynamical layer. -/
def squarePrefixHighSourcePacketStart
    (_shell : ℕ) (channel : RHLean.Analysis.ActualCofactorChannel)
    (_modeLabel : ℕ) : ℕ :=
  squarePrefixHighShell channel

/-- Every exact source-entry packet has one index, including ordered channels whose
transport interval is empty. -/
def squarePrefixHighSourcePacketLength
    (_shell : ℕ) (_channel : RHLean.Analysis.ActualCofactorChannel)
    (_modeLabel : ℕ) : ℕ :=
  1

/-- The source-entry packet is exactly the singleton containing its entry shell. -/
theorem squarePrefixHighSourcePacket_range
    (shell : ℕ) (channel : RHLean.Analysis.ActualCofactorChannel)
    (modeLabel : ℕ) :
    Finset.Ico (squarePrefixHighSourcePacketStart shell channel modeLabel)
        (squarePrefixHighSourcePacketStart shell channel modeLabel +
          squarePrefixHighSourcePacketLength shell channel modeLabel) =
      {squarePrefixHighShell channel} := by
  ext k
  simp [squarePrefixHighSourcePacketStart,
    squarePrefixHighSourcePacketLength, squarePrefixHighShell]

/-- Exact packet-indexed amplitude for the signal realization. The channel
coefficient appears once: in its entry shell, at the zero Farey mode, and at the
singleton source index. Nonzero rational modes remain in the finite support but
carry zero amplitude at this exact, untransformed signal layer. -/
def squarePrefixHighResidualAmplitude
    (shell : ℕ) (channel : RHLean.Analysis.ActualCofactorChannel)
    (modeLabel packetIndex : ℕ) : ℂ :=
  if shell = squarePrefixHighShell channel ∧
      modeLabel = zeroFareyModeLabel ∧
      packetIndex = squarePrefixHighShell channel then
    normalizedChannelAmplitude channel
  else
    0

/-- Concrete residual data for the exact high-height square-prefix signal. The
entry-block shell choice is finite, the complete reduced Farey support is retained,
and every ordered high channel is represented without collapsing orientations. -/
noncomputable def squarePrefixHighResidualData
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) : RHLean.Analysis.ActualResidualData cutoff M where
  shellCount := squarePrefixEntryShellCount n
  cofactorChannels := squarePrefixHighHeightChannels Λ n
  denominatorModes := fareyModeLabels (cutoff M)
  mode := fareyResonantMode cutoff M hcutoff
  packetStart := squarePrefixHighSourcePacketStart
  packetLength := squarePrefixHighSourcePacketLength
  amplitude := squarePrefixHighResidualAmplitude

@[simp] theorem zeroFareyMode_numerator
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M) :
    (fareyResonantMode cutoff M hcutoff zeroFareyModeLabel).numerator = 0 := by
  rw [fareyResonantMode_numerator_of_mem cutoff M hcutoff
    (zeroFareyModeLabel_mem (cutoff M) hcutoff)]
  simp

/-- The exact zero Farey mode has constant quadratic phase one. -/
@[simp] theorem resonantQuadraticMode_zeroFareyMode
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (u : ℤ) :
    RHLean.Analysis.resonantQuadraticMode
        (fareyResonantMode cutoff M hcutoff zeroFareyModeLabel) u = 1 := by
  unfold RHLean.Analysis.resonantQuadraticMode
  rw [zeroFareyMode_numerator]
  simp [RHLean.QuadraticPrimePhase.quadraticPhase,
    RHLean.QuadraticPrimePhase.additiveCharacter]

/-- Every retained high channel has its concrete entry shell inside the declared
finite shell range. -/
theorem squarePrefixHighShell_lt_shellCount
    {Λ : ℝ} {n : ℕ}
    {channel : RHLean.Analysis.ActualCofactorChannel}
    (hchannel : channel ∈ squarePrefixHighHeightChannels Λ n) :
    squarePrefixHighShell channel < squarePrefixEntryShellCount n := by
  classical
  rcases Finset.mem_image.mp hchannel with ⟨p, hp, rfl⟩
  exact orderedChannelEntryShell_lt_squarePrefixEntryShellCount
    (Finset.mem_filter.mp hp).1

/-- A one-point fixed packet evaluates to its unique entry. -/
theorem packet_length_one
    {R : Type*} [AddCommMonoid R]
    (x : ℕ → R) (u : ℕ) :
    RHLean.Kernel.packet x u 1 = x u := by
  simp [RHLean.Kernel.packet]

/-- Every concrete packet is either its exact normalized channel coefficient in the
assigned entry shell and zero mode, or zero. -/
theorem squarePrefixHighResidualPacket_eq
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n shell : ℕ)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (modeLabel : ℕ) :
    RHLean.Analysis.actualResidualPacket
        (squarePrefixHighResidualData cutoff M hcutoff Λ n)
        shell channel modeLabel =
      if shell = squarePrefixHighShell channel ∧
          modeLabel = zeroFareyModeLabel then
        (((μ channel.lowerCofactor : ℤ) : ℂ)) *
          normalizedChannelAmplitude channel
      else
        0 := by
  classical
  unfold RHLean.Analysis.actualResidualPacket
  change RHLean.Kernel.packet
      (RHLean.Analysis.actualResidualEntry
        (squarePrefixHighResidualData cutoff M hcutoff Λ n)
        shell channel modeLabel)
      (squarePrefixHighShell channel) 1 = _
  rw [packet_length_one]
  unfold RHLean.Analysis.actualResidualEntry
    squarePrefixHighResidualData
    squarePrefixHighResidualAmplitude
  by_cases hshell : shell = squarePrefixHighShell channel
  · by_cases hmode : modeLabel = zeroFareyModeLabel
    · subst shell
      subst modeLabel
      simp
    · simp [hshell, hmode]
  · simp [hshell]

/-- The complete retained Farey-mode sum for one shell and channel keeps exactly
the zero-mode source coefficient. -/
theorem squarePrefixHighModeSum_eq
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n shell : ℕ)
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    (∑ modeLabel ∈ fareyModeLabels (cutoff M),
      RHLean.Analysis.actualResidualPacket
        (squarePrefixHighResidualData cutoff M hcutoff Λ n)
        shell channel modeLabel) =
      if shell = squarePrefixHighShell channel then
        (((μ channel.lowerCofactor : ℤ) : ℂ)) *
          normalizedChannelAmplitude channel
      else
        0 := by
  classical
  by_cases hshell : shell = squarePrefixHighShell channel
  · rw [if_pos hshell]
    rw [Finset.sum_eq_single zeroFareyModeLabel]
    · rw [squarePrefixHighResidualPacket_eq]
      simp [hshell]
    · intro modeLabel _ hne
      rw [squarePrefixHighResidualPacket_eq]
      simp [hshell, hne]
    · intro hnot
      exact (hnot (zeroFareyModeLabel_mem (cutoff M) hcutoff)).elim
  · rw [if_neg hshell]
    apply Finset.sum_eq_zero
    intro modeLabel _
    rw [squarePrefixHighResidualPacket_eq]
    simp [hshell]

/-- The concrete residual equals the exact signed sum over all high channels. -/
theorem actualResidual_squarePrefixHighResidualData_eq_channelSum
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) :
    RHLean.Analysis.actualResidual
        (squarePrefixHighResidualData cutoff M hcutoff Λ n) =
      ∑ channel ∈ squarePrefixHighHeightChannels Λ n,
        (((μ channel.lowerCofactor : ℤ) : ℂ)) *
          normalizedChannelAmplitude channel := by
  classical
  unfold RHLean.Analysis.actualResidual RHLean.Analysis.heightShellSum
    RHLean.Analysis.actualResidualShell
  change (∑ shell ∈ Finset.range (squarePrefixEntryShellCount n),
    ∑ channel ∈ squarePrefixHighHeightChannels Λ n,
      ∑ modeLabel ∈ fareyModeLabels (cutoff M),
        RHLean.Analysis.actualResidualPacket
          (squarePrefixHighResidualData cutoff M hcutoff Λ n)
          shell channel modeLabel) = _
  simp_rw [squarePrefixHighModeSum_eq]
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

/-- Exact high-sector recombination through the concrete `ActualResidualData`
constructor. This is a signal identity, not an energy estimate or a major-arc
cancellation theorem. -/
theorem actualResidual_squarePrefixHighResidualData_eq_highHeightExpansion
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) :
    RHLean.Analysis.actualResidual
        (squarePrefixHighResidualData cutoff M hcutoff Λ n) =
      squarePrefixHighHeightExpansion Λ n := by
  rw [actualResidual_squarePrefixHighResidualData_eq_channelSum]
  exact (squarePrefixHighHeightExpansion_eq_channelSum Λ n).symm

end RHLean.Proof
