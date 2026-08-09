import Mathlib
import RHLean.Proof.ConcreteSquarePrefixHighResidual
import RHLean.Proof.NormalizedCofactorTripling

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Complex coefficient compatibility with the `ActualResidualData` convention. -/
theorem lowerMoebius_mul_normalizedChannelAmplitude
    (c q : ℕ) :
    (((μ c : ℤ) : ℂ)) *
        normalizedChannelAmplitude
          { lowerCofactor := c, upperFactor := q } =
      normalizedCofactorWeight c q := by
  simpa [normalizedChannelAmplitude, normalizedCofactorWeight] using
    congrArg (fun x : ℚ => (x : ℂ))
      (lowerMoebius_mul_normalizedChannelAmplitudeRat c q)

/-- Channel-valued form of the exact coefficient compatibility theorem. -/
theorem lowerMoebius_mul_normalizedChannelAmplitude_of_channel
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    (((μ channel.lowerCofactor : ℤ) : ℂ)) *
        normalizedChannelAmplitude channel =
      normalizedCofactorWeight
        channel.lowerCofactor channel.upperFactor := by
  rcases channel with ⟨c, q⟩
  exact lowerMoebius_mul_normalizedChannelAmplitude c q

/-- Reassociate the explicit lower Möbius factor before applying coefficient compatibility. -/
theorem lowerMoebius_mul_normalizedChannelAmplitude_mul
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (z w : ℂ) :
    ((((μ channel.lowerCofactor : ℤ) : ℂ)) *
        (normalizedChannelAmplitude channel * z)) * w =
      (normalizedCofactorWeight
          channel.lowerCofactor channel.upperFactor * z) * w := by
  calc
    ((((μ channel.lowerCofactor : ℤ) : ℂ)) *
        (normalizedChannelAmplitude channel * z)) * w =
      (((((μ channel.lowerCofactor : ℤ) : ℂ)) *
          normalizedChannelAmplitude channel) * z) * w := by
        ring
    _ = (normalizedCofactorWeight
          channel.lowerCofactor channel.upperFactor * z) * w := by
        rw [lowerMoebius_mul_normalizedChannelAmplitude_of_channel]

/-- The full normalized Farey transport entry before finite packet summation. -/
def normalizedFareyTransportEntry
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (packetIndex : ℕ) : ℂ :=
  normalizedCofactorWeight channel.lowerCofactor channel.upperFactor *
    fareyChannelPhase mode channel *
      RHLean.Analysis.resonantQuadraticMode mode (packetIndex : ℤ)

/-- The exact contiguous transport packet on `[⌊√(cq)⌋,q-1)`. -/
def normalizedFareyTransportPacket
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  RHLean.Kernel.packet
    (normalizedFareyTransportEntry mode channel)
    (orderedChannelEntryShell channel)
    (orderedChannelTransitionIndex channel - orderedChannelEntryShell channel)

/-- Interval-sum form of the exact normalized transport packet. -/
theorem normalizedFareyTransportPacket_eq_intervalSum
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    normalizedFareyTransportPacket mode channel =
      ∑ packetIndex ∈ Finset.Ico (orderedChannelEntryShell channel)
          (orderedChannelTransitionIndex channel),
        normalizedFareyTransportEntry mode channel packetIndex := by
  unfold normalizedFareyTransportPacket
  simpa [orderedTransportPacketStart, orderedTransportPacketLength] using
    orderedTransportPacket_eq_intervalSum
      (normalizedFareyTransportEntry mode channel) 0 channel 0

/-- Transport amplitude for the concrete high-height dynamical packet data. -/
def squarePrefixHighTransportAmplitude
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (shell : ℕ) (channel : RHLean.Analysis.ActualCofactorChannel)
    (modeLabel _packetIndex : ℕ) : ℂ :=
  if shell = squarePrefixHighShell channel then
    normalizedChannelAmplitude channel *
      fareyChannelPhase
        (fareyResonantMode cutoff M hcutoff modeLabel) channel
  else
    0

/-- Concrete high-height transport data, distinct from the singleton exact-signal data. -/
noncomputable def squarePrefixHighTransportData
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) : RHLean.Analysis.ActualResidualData cutoff M where
  shellCount := squarePrefixEntryShellCount n
  cofactorChannels := squarePrefixHighHeightChannels Λ n
  denominatorModes := fareyModeLabels (cutoff M)
  mode := fareyResonantMode cutoff M hcutoff
  packetStart := orderedTransportPacketStart
  packetLength := orderedTransportPacketLength
  amplitude := squarePrefixHighTransportAmplitude cutoff M hcutoff

/-- At its assigned source shell, the concrete transport entry is exact. -/
theorem actualResidualEntry_squarePrefixHighTransportData_ownShell
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (modeLabel packetIndex : ℕ) :
    RHLean.Analysis.actualResidualEntry
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        (squarePrefixHighShell channel) channel modeLabel packetIndex =
      normalizedFareyTransportEntry
        (fareyResonantMode cutoff M hcutoff modeLabel)
        channel packetIndex := by
  unfold RHLean.Analysis.actualResidualEntry
    squarePrefixHighTransportData
    squarePrefixHighTransportAmplitude
    normalizedFareyTransportEntry
  simp only [ite_true]
  exact lowerMoebius_mul_normalizedChannelAmplitude_mul
    channel
    (fareyChannelPhase
      (fareyResonantMode cutoff M hcutoff modeLabel) channel)
    (RHLean.Analysis.resonantQuadraticMode
      (fareyResonantMode cutoff M hcutoff modeLabel) (packetIndex : ℤ))

/-- At its source shell, an actual transport packet is the normalized packet. -/
theorem actualResidualPacket_squarePrefixHighTransportData_ownShell
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (modeLabel : ℕ) :
    RHLean.Analysis.actualResidualPacket
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        (squarePrefixHighShell channel) channel modeLabel =
      normalizedFareyTransportPacket
        (fareyResonantMode cutoff M hcutoff modeLabel) channel := by
  unfold RHLean.Analysis.actualResidualPacket normalizedFareyTransportPacket
  change RHLean.Kernel.packet
      (RHLean.Analysis.actualResidualEntry
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        (squarePrefixHighShell channel) channel modeLabel)
      (orderedChannelEntryShell channel)
      (orderedChannelTransitionIndex channel - orderedChannelEntryShell channel) = _
  unfold RHLean.Kernel.packet
  apply Finset.sum_congr rfl
  intro packetIndex _
  exact actualResidualEntry_squarePrefixHighTransportData_ownShell
    cutoff M hcutoff Λ n channel modeLabel packetIndex

/-- The explicit phase multiplier relating `(3c,q)` to `(c,q)`. -/
def triplingPhaseTransport
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  RHLean.QuadraticPrimePhase.quadraticPhase
    (-8 * mode.numerator) (mode.denominator : ℤ)
    (channel.lowerCofactor : ℤ)

/-- Channel-phase transport with no Möbius sign inserted into the phase. -/
theorem fareyChannelPhase_tripled_eq_transport_mul
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    fareyChannelPhase mode (tripledCofactorChannel channel) =
      triplingPhaseTransport mode channel * fareyChannelPhase mode channel := by
  simpa [triplingPhaseTransport] using fareyChannelPhase_tripled mode channel

/-- Tripling cannot move a channel to an earlier entry shell. -/
theorem orderedChannelEntryShell_le_tripled
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    orderedChannelEntryShell channel ≤
      orderedChannelEntryShell (tripledCofactorChannel channel) := by
  unfold orderedChannelEntryShell tripledCofactorChannel
  apply Nat.sqrt_le_sqrt
  calc
    channel.lowerCofactor * channel.upperFactor ≤
        3 * (channel.lowerCofactor * channel.upperFactor) := by omega
    _ = (3 * channel.lowerCofactor) * channel.upperFactor := by
      simp [Nat.mul_assoc]

/-- Tripling leaves the transition index unchanged. -/
@[simp] theorem orderedChannelTransitionIndex_tripled
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    orderedChannelTransitionIndex (tripledCofactorChannel channel) =
      orderedChannelTransitionIndex channel := by
  rfl

/-- The finite base-channel prefix removed by the later tripled entry shell. -/
def triplingBoundaryPacket
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  ∑ packetIndex ∈ Finset.Ico (orderedChannelEntryShell channel)
      (min (orderedChannelEntryShell (tripledCofactorChannel channel))
        (orderedChannelTransitionIndex channel)),
    normalizedFareyTransportEntry mode channel packetIndex

/-- The base profile restricted to the exact window shared with the tripled channel. -/
def triplingTransportedBasePacket
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  ∑ packetIndex ∈
      Finset.Ico (orderedChannelEntryShell (tripledCofactorChannel channel))
        (orderedChannelTransitionIndex channel),
    normalizedFareyTransportEntry mode channel packetIndex

/-- The full base packet is boundary prefix plus common transport window. -/
theorem normalizedFareyTransportPacket_eq_boundary_add_common
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    normalizedFareyTransportPacket mode channel =
      triplingBoundaryPacket mode channel +
        triplingTransportedBasePacket mode channel := by
  rw [normalizedFareyTransportPacket_eq_intervalSum]
  unfold triplingBoundaryPacket triplingTransportedBasePacket
  have hstart := orderedChannelEntryShell_le_tripled channel
  rw [← Finset.sum_union]
  · congr 1
    ext packetIndex
    simp
    omega
  · rw [Finset.disjoint_left]
    intro packetIndex hboundary hcommon
    simp only [Finset.mem_Ico] at hboundary hcommon
    omega

/-- Pointwise phase-aligned child-plus-twice-parent cancellation. -/
theorem normalizedFareyTransportEntry_phaseAligned_cancel
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (packetIndex : ℕ)
    (h3 : ¬ 3 ∣ channel.lowerCofactor * channel.upperFactor) :
    triplingPhaseTransport mode channel *
        normalizedFareyTransportEntry mode channel packetIndex +
      2 * normalizedFareyTransportEntry mode
        (tripledCofactorChannel channel) packetIndex = 0 := by
  change
    triplingPhaseTransport mode channel *
        (normalizedCofactorWeight channel.lowerCofactor channel.upperFactor *
          fareyChannelPhase mode channel *
          RHLean.Analysis.resonantQuadraticMode mode (packetIndex : ℤ)) +
      2 *
        (normalizedCofactorWeight (3 * channel.lowerCofactor) channel.upperFactor *
          fareyChannelPhase mode (tripledCofactorChannel channel) *
          RHLean.Analysis.resonantQuadraticMode mode (packetIndex : ℤ)) = 0
  rw [normalized_tripling_scaling
      channel.lowerCofactor channel.upperFactor h3,
    fareyChannelPhase_tripled_eq_transport_mul]
  ring

/-- Unaligned pointwise cancellation leaves the exact phase defect. -/
theorem normalizedFareyTransportEntry_add_two_tripled_eq_phaseDefect
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (packetIndex : ℕ)
    (h3 : ¬ 3 ∣ channel.lowerCofactor * channel.upperFactor) :
    normalizedFareyTransportEntry mode channel packetIndex +
      2 * normalizedFareyTransportEntry mode
        (tripledCofactorChannel channel) packetIndex =
      (1 - triplingPhaseTransport mode channel) *
        normalizedFareyTransportEntry mode channel packetIndex := by
  have hcancel := normalizedFareyTransportEntry_phaseAligned_cancel
    mode channel packetIndex h3
  linear_combination hcancel

/-- Summed phase-aligned cancellation on the common packet window. -/
theorem triplingTransportedBasePacket_phaseAligned_cancel
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (h3 : ¬ 3 ∣ channel.lowerCofactor * channel.upperFactor) :
    triplingPhaseTransport mode channel *
        triplingTransportedBasePacket mode channel +
      2 * normalizedFareyTransportPacket mode
        (tripledCofactorChannel channel) = 0 := by
  rw [normalizedFareyTransportPacket_eq_intervalSum]
  unfold triplingTransportedBasePacket
  simp only [orderedChannelTransitionIndex_tripled]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro packetIndex _
  exact normalizedFareyTransportEntry_phaseAligned_cancel
    mode channel packetIndex h3

/-- Summed unaligned common-window identity. -/
theorem triplingTransportedBasePacket_add_two_tripled_eq_phaseDefect
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (h3 : ¬ 3 ∣ channel.lowerCofactor * channel.upperFactor) :
    triplingTransportedBasePacket mode channel +
      2 * normalizedFareyTransportPacket mode
        (tripledCofactorChannel channel) =
      (1 - triplingPhaseTransport mode channel) *
        triplingTransportedBasePacket mode channel := by
  rw [normalizedFareyTransportPacket_eq_intervalSum]
  unfold triplingTransportedBasePacket
  simp only [orderedChannelTransitionIndex_tripled]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro packetIndex _
  exact normalizedFareyTransportEntry_add_two_tripled_eq_phaseDefect
    mode channel packetIndex h3

/-- Boundary plus phase mismatch: the complete signed tripling defect. -/
def triplingSignedDefect
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  triplingBoundaryPacket mode channel +
    (1 - triplingPhaseTransport mode channel) *
      triplingTransportedBasePacket mode channel

/-- Full signed packet identity with every boundary and phase term retained. -/
theorem normalizedFareyTransportPacket_add_two_tripled_eq_signedDefect
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (h3 : ¬ 3 ∣ channel.lowerCofactor * channel.upperFactor) :
    normalizedFareyTransportPacket mode channel +
      2 * normalizedFareyTransportPacket mode
        (tripledCofactorChannel channel) =
      triplingSignedDefect mode channel := by
  rw [normalizedFareyTransportPacket_eq_boundary_add_common]
  calc
    (triplingBoundaryPacket mode channel +
        triplingTransportedBasePacket mode channel) +
        2 * normalizedFareyTransportPacket mode
          (tripledCofactorChannel channel) =
      triplingBoundaryPacket mode channel +
        (triplingTransportedBasePacket mode channel +
          2 * normalizedFareyTransportPacket mode
            (tripledCofactorChannel channel)) := by ring
    _ = triplingSignedDefect mode channel := by
      rw [triplingTransportedBasePacket_add_two_tripled_eq_phaseDefect
        mode channel h3]
      rfl

/-- A retained concrete tripling pair. -/
structure SquarePrefixHighTriplingPair (Λ : ℝ) (n : ℕ) where
  base : RHLean.Analysis.ActualCofactorChannel
  newPrime : ¬ 3 ∣ base.lowerCofactor * base.upperFactor
  base_mem : base ∈ squarePrefixHighHeightChannels Λ n
  tripled_mem : tripledCofactorChannel base ∈
    squarePrefixHighHeightChannels Λ n

/-- The base shell of a retained pair is in the finite shell range. -/
theorem SquarePrefixHighTriplingPair.baseShell_lt
    {Λ : ℝ} {n : ℕ} (pair : SquarePrefixHighTriplingPair Λ n) :
    squarePrefixHighShell pair.base < squarePrefixEntryShellCount n :=
  squarePrefixHighShell_lt_shellCount pair.base_mem

/-- The tripled shell of a retained pair is in the finite shell range. -/
theorem SquarePrefixHighTriplingPair.tripledShell_lt
    {Λ : ℝ} {n : ℕ} (pair : SquarePrefixHighTriplingPair Λ n) :
    squarePrefixHighShell (tripledCofactorChannel pair.base) <
      squarePrefixEntryShellCount n :=
  squarePrefixHighShell_lt_shellCount pair.tripled_mem

/-- Full signed defect through the concrete transport-data packet interface. -/
theorem actualResidualPacket_squarePrefixHighTransportData_tripling_signedDefect
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) (pair : SquarePrefixHighTriplingPair Λ n)
    (modeLabel : ℕ) :
    RHLean.Analysis.actualResidualPacket
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        (squarePrefixHighShell pair.base) pair.base modeLabel +
      2 * RHLean.Analysis.actualResidualPacket
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        (squarePrefixHighShell (tripledCofactorChannel pair.base))
        (tripledCofactorChannel pair.base) modeLabel =
      triplingSignedDefect
        (fareyResonantMode cutoff M hcutoff modeLabel) pair.base := by
  rw [actualResidualPacket_squarePrefixHighTransportData_ownShell,
    actualResidualPacket_squarePrefixHighTransportData_ownShell]
  exact normalizedFareyTransportPacket_add_two_tripled_eq_signedDefect
    (fareyResonantMode cutoff M hcutoff modeLabel)
    pair.base pair.newPrime

/-- Complete signed child-plus-twice-parent contribution over all retained modes. -/
def squarePrefixHighTriplingModeContribution
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) (pair : SquarePrefixHighTriplingPair Λ n) : ℂ :=
  ∑ modeLabel ∈ fareyModeLabels (cutoff M),
    (RHLean.Analysis.actualResidualPacket
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        (squarePrefixHighShell pair.base) pair.base modeLabel +
      2 * RHLean.Analysis.actualResidualPacket
        (squarePrefixHighTransportData cutoff M hcutoff Λ n)
        (squarePrefixHighShell (tripledCofactorChannel pair.base))
        (tripledCofactorChannel pair.base) modeLabel)

/-- Complete retained-mode defect sum for one tripling pair. -/
def squarePrefixHighTriplingModeDefect
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    {Λ : ℝ} {n : ℕ} (pair : SquarePrefixHighTriplingPair Λ n) : ℂ :=
  ∑ modeLabel ∈ fareyModeLabels (cutoff M),
    triplingSignedDefect
      (fareyResonantMode cutoff M hcutoff modeLabel) pair.base

/-- Exact all-mode signed defect identity. -/
theorem squarePrefixHighTriplingModeContribution_eq_defect
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) (pair : SquarePrefixHighTriplingPair Λ n) :
    squarePrefixHighTriplingModeContribution
        cutoff M hcutoff Λ n pair =
      squarePrefixHighTriplingModeDefect cutoff M hcutoff pair := by
  unfold squarePrefixHighTriplingModeContribution
    squarePrefixHighTriplingModeDefect
  apply Finset.sum_congr rfl
  intro modeLabel _
  exact actualResidualPacket_squarePrefixHighTransportData_tripling_signedDefect
    cutoff M hcutoff Λ n pair modeLabel

/-- Energy after the complete signed mode recombination. -/
theorem squarePrefixHighTriplingModeContribution_energy_eq_defect
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) (pair : SquarePrefixHighTriplingPair Λ n) :
    ‖squarePrefixHighTriplingModeContribution
        cutoff M hcutoff Λ n pair‖ ^ 2 =
      ‖squarePrefixHighTriplingModeDefect cutoff M hcutoff pair‖ ^ 2 := by
  rw [squarePrefixHighTriplingModeContribution_eq_defect]

end RHLean.Proof
