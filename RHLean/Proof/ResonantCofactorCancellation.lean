import Mathlib
import RHLean.Proof.ActualResidualDecomposition

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- The complex scalar attached to the exact Möbius weight of a cofactor. -/
def moebiusScalar (n : ℕ) : ℂ :=
  ((μ n : ℤ) : ℂ)

/-- Möbius doubling gives an exact complex sign reversal for every odd cofactor. -/
theorem moebiusScalar_two_mul_of_odd (a : ℕ) (ha : Odd a) :
    moebiusScalar (2 * a) = -moebiusScalar a := by
  simp [moebiusScalar, RHLean.Arithmetic.moebius_two_mul_of_odd a ha]

/--
A candidate cancellation pair consists of a base cofactor and its doubled
cofactor, with the upper factor kept fixed and visible.
-/
structure CofactorDoublingPair where
  baseCofactor : ℕ
  upperFactor : ℕ
  deriving DecidableEq

/-- The odd/base channel of a cofactor-doubling pair. -/
def baseCofactorChannel (pair : CofactorDoublingPair) : ActualCofactorChannel where
  lowerCofactor := pair.baseCofactor
  upperFactor := pair.upperFactor

/-- The doubled channel of a cofactor-doubling pair. -/
def doubledCofactorChannel (pair : CofactorDoublingPair) : ActualCofactorChannel where
  lowerCofactor := 2 * pair.baseCofactor
  upperFactor := pair.upperFactor

/--
The packet entry before its Möbius weight is applied. The complex quadratic
phase is still the exact actual phase, with denominator mode and packet index
unchanged and canonical modulus `2r` inherited from `resonantQuadraticMode`.
-/
def actualResidualUnweightedEntry
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel)
    (denominatorMode packetIndex : ℕ) : ℂ :=
  data.amplitude shell channel denominatorMode packetIndex *
    resonantQuadraticMode
      (data.mode denominatorMode) (packetIndex : ℤ)

/-- The fixed packet formed from the actual entry with only its Möbius weight removed. -/
def actualResidualUnweightedPacket
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel)
    (denominatorMode : ℕ) : ℂ :=
  RHLean.Kernel.packet
    (actualResidualUnweightedEntry data shell channel denominatorMode)
    (data.packetStart shell channel denominatorMode)
    (data.packetLength shell channel denominatorMode)

/-- Every actual packet entry is its exact Möbius scalar times the unweighted entry. -/
theorem actualResidualEntry_eq_moebiusScalar_mul_unweighted
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel)
    (denominatorMode packetIndex : ℕ) :
    actualResidualEntry data shell channel denominatorMode packetIndex =
      moebiusScalar channel.lowerCofactor *
        actualResidualUnweightedEntry
          data shell channel denominatorMode packetIndex := by
  simp [actualResidualEntry, actualResidualUnweightedEntry, moebiusScalar, mul_assoc]

/-- Every actual fixed packet factors by its exact Möbius scalar. -/
theorem actualResidualPacket_eq_moebiusScalar_mul_unweighted
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel)
    (denominatorMode : ℕ) :
    actualResidualPacket data shell channel denominatorMode =
      moebiusScalar channel.lowerCofactor *
        actualResidualUnweightedPacket data shell channel denominatorMode := by
  simp [actualResidualPacket, actualResidualUnweightedPacket,
    RHLean.Kernel.packet, actualResidualEntry_eq_moebiusScalar_mul_unweighted,
    Finset.mul_sum]

/-- The scale-`M` extraction of one actual cofactor/denominator packet. -/
def resonantActualResidualPacket
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel)
    (denominatorMode : ℕ) : ℂ :=
  skeleton.extraction M
    (actualResidualPacket data shell channel denominatorMode)

/-- The scale-`M` extraction of the corresponding unweighted packet profile. -/
def resonantUnweightedResidualPacket
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel)
    (denominatorMode : ℕ) : ℂ :=
  skeleton.extraction M
    (actualResidualUnweightedPacket data shell channel denominatorMode)

/-- Linear extraction preserves the explicit Möbius scalar factor. -/
theorem resonantActualResidualPacket_eq_moebiusScalar_smul_unweighted
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel)
    (denominatorMode : ℕ) :
    resonantActualResidualPacket skeleton M data shell channel denominatorMode =
      moebiusScalar channel.lowerCofactor •
        resonantUnweightedResidualPacket
          skeleton M data shell channel denominatorMode := by
  unfold resonantActualResidualPacket resonantUnweightedResidualPacket
  rw [actualResidualPacket_eq_moebiusScalar_mul_unweighted]
  change skeleton.extraction M
      (moebiusScalar channel.lowerCofactor •
        actualResidualUnweightedPacket data shell channel denominatorMode) =
    moebiusScalar channel.lowerCofactor •
      skeleton.extraction M
        (actualResidualUnweightedPacket data shell channel denominatorMode)
  exact (skeleton.extraction M).map_smul _ _

/--
Explicit compatibility data for one actual odd/doubled cofactor pair in one
height shell. Both channels must occur in the actual cofactor set. For every
retained denominator mode, packet start, packet length, and the full
packet-indexed amplitude agree. No cancellation, smallness, or norm estimate is
hidden in the structure.
-/
structure MöbiusCofactorPairCompatibility
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M)
    (shell : ℕ) (pair : CofactorDoublingPair) : Prop where
  baseOdd : Odd pair.baseCofactor
  base_mem : baseCofactorChannel pair ∈ data.cofactorChannels
  doubled_mem : doubledCofactorChannel pair ∈ data.cofactorChannels
  packetStart_eq :
    ∀ denominatorMode ∈ data.denominatorModes,
      data.packetStart shell (baseCofactorChannel pair) denominatorMode =
        data.packetStart shell (doubledCofactorChannel pair) denominatorMode
  packetLength_eq :
    ∀ denominatorMode ∈ data.denominatorModes,
      data.packetLength shell (baseCofactorChannel pair) denominatorMode =
        data.packetLength shell (doubledCofactorChannel pair) denominatorMode
  amplitude_eq :
    ∀ denominatorMode ∈ data.denominatorModes, ∀ packetIndex,
      data.amplitude shell (baseCofactorChannel pair)
          denominatorMode packetIndex =
        data.amplitude shell (doubledCofactorChannel pair)
          denominatorMode packetIndex

/-- Compatible paired channels have exactly the same unweighted actual packet. -/
theorem actualResidualUnweightedPacket_base_eq_doubled
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M)
    (shell : ℕ) (pair : CofactorDoublingPair)
    (hcompat : MöbiusCofactorPairCompatibility data shell pair)
    (denominatorMode : ℕ) (hmode : denominatorMode ∈ data.denominatorModes) :
    actualResidualUnweightedPacket data shell
        (baseCofactorChannel pair) denominatorMode =
      actualResidualUnweightedPacket data shell
        (doubledCofactorChannel pair) denominatorMode := by
  unfold actualResidualUnweightedPacket RHLean.Kernel.packet
  rw [hcompat.packetStart_eq denominatorMode hmode,
    hcompat.packetLength_eq denominatorMode hmode]
  apply Finset.sum_congr rfl
  intro packetIndex _
  simp [actualResidualUnweightedEntry,
    hcompat.amplitude_eq denominatorMode hmode packetIndex]

/-- Compatible paired channels have the same extracted unweighted resonant profile. -/
theorem resonantUnweightedResidualPacket_base_eq_doubled
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (shell : ℕ) (pair : CofactorDoublingPair)
    (hcompat : MöbiusCofactorPairCompatibility data shell pair)
    (denominatorMode : ℕ) (hmode : denominatorMode ∈ data.denominatorModes) :
    resonantUnweightedResidualPacket skeleton M data shell
        (baseCofactorChannel pair) denominatorMode =
      resonantUnweightedResidualPacket skeleton M data shell
        (doubledCofactorChannel pair) denominatorMode := by
  unfold resonantUnweightedResidualPacket
  rw [actualResidualUnweightedPacket_base_eq_doubled
    data shell pair hcompat denominatorMode hmode]

/--
For each retained denominator mode, a compatible odd/doubled cofactor pair
cancels exactly after scale-dependent resonant extraction. The denominator mode
is not summed away or bounded independently.
-/
theorem resonantActualResidualPacket_pair_cancel
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (shell : ℕ) (pair : CofactorDoublingPair)
    (hcompat : MöbiusCofactorPairCompatibility data shell pair)
    (denominatorMode : ℕ) (hmode : denominatorMode ∈ data.denominatorModes) :
    resonantActualResidualPacket skeleton M data shell
        (baseCofactorChannel pair) denominatorMode +
      resonantActualResidualPacket skeleton M data shell
        (doubledCofactorChannel pair) denominatorMode = 0 := by
  rw [resonantActualResidualPacket_eq_moebiusScalar_smul_unweighted,
    resonantActualResidualPacket_eq_moebiusScalar_smul_unweighted,
    resonantUnweightedResidualPacket_base_eq_doubled
      skeleton M data shell pair hcompat denominatorMode hmode]
  simp only [baseCofactorChannel, doubledCofactorChannel]
  rw [moebiusScalar_two_mul_of_odd pair.baseCofactor hcompat.baseOdd]
  simp

/-- The actual joint denominator-mode contribution of one cofactor channel. -/
def actualCofactorModeContribution
    {cutoff : ℕ → ℕ} {M : ℕ}
    (data : ActualResidualData cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel) : ℂ :=
  ∑ denominatorMode ∈ data.denominatorModes,
    actualResidualPacket data shell channel denominatorMode

/-- The resonant extraction of one actual cofactor channel with all modes retained jointly. -/
def resonantActualCofactorContribution
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel) : ℂ :=
  skeleton.extraction M
    (actualCofactorModeContribution data shell channel)

/-- Linearity expands a cofactor contribution into the exact sum of extracted mode packets. -/
theorem resonantActualCofactorContribution_eq_sum_packets
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (shell : ℕ) (channel : ActualCofactorChannel) :
    resonantActualCofactorContribution skeleton M data shell channel =
      ∑ denominatorMode ∈ data.denominatorModes,
        resonantActualResidualPacket
          skeleton M data shell channel denominatorMode := by
  simp [resonantActualCofactorContribution, actualCofactorModeContribution,
    resonantActualResidualPacket]

/--
The complete joint denominator-mode contributions of a compatible cofactor pair
cancel exactly. This is a signed cofactor interaction, not a modewise norm bound.
-/
theorem resonantActualCofactorPair_cancel
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (shell : ℕ) (pair : CofactorDoublingPair)
    (hcompat : MöbiusCofactorPairCompatibility data shell pair) :
    resonantActualCofactorContribution skeleton M data shell
        (baseCofactorChannel pair) +
      resonantActualCofactorContribution skeleton M data shell
        (doubledCofactorChannel pair) = 0 := by
  rw [resonantActualCofactorContribution_eq_sum_packets,
    resonantActualCofactorContribution_eq_sum_packets,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro denominatorMode hmode
  exact resonantActualResidualPacket_pair_cancel
    skeleton M data shell pair hcompat denominatorMode hmode

/-- The signed resonant contribution of a finite family of certified cofactor pairs. -/
def resonantActualCofactorPairFamilyContribution
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (shell : ℕ) (pairs : Finset CofactorDoublingPair) : ℂ :=
  ∑ pair ∈ pairs,
    (resonantActualCofactorContribution skeleton M data shell
        (baseCofactorChannel pair) +
      resonantActualCofactorContribution skeleton M data shell
        (doubledCofactorChannel pair))

/--
Every finite family of explicitly compatible odd/doubled cofactor pairs has
zero total resonant contribution. No claim is made that the actual channel set
is exhausted by such pairs, and no unpaired, endpoint, boundary, or low-height
term is discarded.
-/
theorem resonantActualCofactorPairFamilyContribution_eq_zero
    (skeleton : ResonantProjectionSkeleton ℂ ℂ) (M : ℕ)
    (data : ActualResidualData skeleton.cutoff M)
    (shell : ℕ) (pairs : Finset CofactorDoublingPair)
    (hcompat :
      ∀ pair ∈ pairs, MöbiusCofactorPairCompatibility data shell pair) :
    resonantActualCofactorPairFamilyContribution
      skeleton M data shell pairs = 0 := by
  unfold resonantActualCofactorPairFamilyContribution
  apply Finset.sum_eq_zero
  intro pair hpair
  exact resonantActualCofactorPair_cancel
    skeleton M data shell pair (hcompat pair hpair)

end RHLean.Analysis
