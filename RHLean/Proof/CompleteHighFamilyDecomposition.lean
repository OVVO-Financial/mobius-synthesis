import Mathlib
import RHLean.Proof.TriplingPacketTransport

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- Retained high channels that introduce a genuinely new factor `3` and whose
tripled child remains in the same finite high-height support. -/
def squarePrefixHighTriplingBases (Λ : ℝ) (n : ℕ) :
    Finset RHLean.Analysis.ActualCofactorChannel :=
  (squarePrefixHighHeightChannels Λ n).filter fun channel =>
    (¬ 3 ∣ channel.lowerCofactor * channel.upperFactor) ∧
      tripledCofactorChannel channel ∈ squarePrefixHighHeightChannels Λ n

@[simp] theorem mem_squarePrefixHighTriplingBases
    {Λ : ℝ} {n : ℕ}
    {channel : RHLean.Analysis.ActualCofactorChannel} :
    channel ∈ squarePrefixHighTriplingBases Λ n ↔
      channel ∈ squarePrefixHighHeightChannels Λ n ∧
        (¬ 3 ∣ channel.lowerCofactor * channel.upperFactor) ∧
          tripledCofactorChannel channel ∈
            squarePrefixHighHeightChannels Λ n := by
  simp [squarePrefixHighTriplingBases]

/-- Tripling the lower cofactor is injective on concrete ordered channels. -/
theorem tripledCofactorChannel_injective :
    Function.Injective tripledCofactorChannel := by
  intro channel channel' h
  have hc := congrArg RHLean.Analysis.ActualCofactorChannel.lowerCofactor h
  have hq := congrArg RHLean.Analysis.ActualCofactorChannel.upperFactor h
  change 3 * channel.lowerCofactor = 3 * channel'.lowerCofactor at hc
  change channel.upperFactor = channel'.upperFactor at hq
  cases channel with
  | mk c q =>
      cases channel' with
      | mk c' q' =>
          simp only at hc hq
          have hcc : c = c' := by omega
          subst c'
          subst q'
          rfl

/-- The finite set of retained tripled children. -/
def squarePrefixHighTriplingChildren (Λ : ℝ) (n : ℕ) :
    Finset RHLean.Analysis.ActualCofactorChannel :=
  (squarePrefixHighTriplingBases Λ n).image tripledCofactorChannel

@[simp] theorem mem_squarePrefixHighTriplingChildren
    {Λ : ℝ} {n : ℕ}
    {channel : RHLean.Analysis.ActualCofactorChannel} :
    channel ∈ squarePrefixHighTriplingChildren Λ n ↔
      ∃ base ∈ squarePrefixHighTriplingBases Λ n,
        tripledCofactorChannel base = channel := by
  simp [squarePrefixHighTriplingChildren]

/-- Every retained base belongs to the original high support. -/
theorem squarePrefixHighTriplingBases_subset
    (Λ : ℝ) (n : ℕ) :
    squarePrefixHighTriplingBases Λ n ⊆
      squarePrefixHighHeightChannels Λ n := by
  intro channel hchannel
  exact (mem_squarePrefixHighTriplingBases.mp hchannel).1

/-- Every retained child belongs to the original high support. -/
theorem squarePrefixHighTriplingChildren_subset
    (Λ : ℝ) (n : ℕ) :
    squarePrefixHighTriplingChildren Λ n ⊆
      squarePrefixHighHeightChannels Λ n := by
  intro channel hchannel
  rcases Finset.mem_image.mp hchannel with ⟨base, hbase, rfl⟩
  exact (mem_squarePrefixHighTriplingBases.mp hbase).2.2

/-- A new-prime base cannot itself be a tripled child: every child product is
already divisible by `3`. -/
theorem squarePrefixHighTriplingBases_disjoint_children
    (Λ : ℝ) (n : ℕ) :
    Disjoint (squarePrefixHighTriplingBases Λ n)
      (squarePrefixHighTriplingChildren Λ n) := by
  rw [Finset.disjoint_left]
  intro channel hbase hchild
  rcases Finset.mem_image.mp hchild with ⟨parent, hparent, htripled⟩
  subst channel
  have hnew := (mem_squarePrefixHighTriplingBases.mp hbase).2.1
  apply hnew
  refine ⟨parent.lowerCofactor * parent.upperFactor, ?_⟩
  simp [tripledCofactorChannel, Nat.mul_assoc]

/-- Channels covered by retained tripling pairs. -/
def squarePrefixHighTriplingCovered (Λ : ℝ) (n : ℕ) :
    Finset RHLean.Analysis.ActualCofactorChannel :=
  squarePrefixHighTriplingBases Λ n ∪
    squarePrefixHighTriplingChildren Λ n

/-- Every paired base or child remains in the original high support. -/
theorem squarePrefixHighTriplingCovered_subset
    (Λ : ℝ) (n : ℕ) :
    squarePrefixHighTriplingCovered Λ n ⊆
      squarePrefixHighHeightChannels Λ n := by
  intro channel hchannel
  rcases Finset.mem_union.mp hchannel with hbase | hchild
  · exact squarePrefixHighTriplingBases_subset Λ n hbase
  · exact squarePrefixHighTriplingChildren_subset Λ n hchild

/-- Every high channel not covered by a retained pair is kept explicitly. -/
def squarePrefixHighUnpairedChannels (Λ : ℝ) (n : ℕ) :
    Finset RHLean.Analysis.ActualCofactorChannel :=
  squarePrefixHighHeightChannels Λ n \
    squarePrefixHighTriplingCovered Λ n

@[simp] theorem mem_squarePrefixHighUnpairedChannels
    {Λ : ℝ} {n : ℕ}
    {channel : RHLean.Analysis.ActualCofactorChannel} :
    channel ∈ squarePrefixHighUnpairedChannels Λ n ↔
      channel ∈ squarePrefixHighHeightChannels Λ n ∧
        channel ∉ squarePrefixHighTriplingCovered Λ n := by
  simp [squarePrefixHighUnpairedChannels]

/-- Paired channels and explicitly unpaired channels are disjoint. -/
theorem squarePrefixHighTriplingCovered_disjoint_unpaired
    (Λ : ℝ) (n : ℕ) :
    Disjoint (squarePrefixHighTriplingCovered Λ n)
      (squarePrefixHighUnpairedChannels Λ n) := by
  rw [Finset.disjoint_left]
  intro channel hcovered hunpaired
  exact (mem_squarePrefixHighUnpairedChannels.mp hunpaired).2 hcovered

/-- The retained bases, retained children, and unpaired channels cover the exact
finite high-height support with no duplication. -/
theorem squarePrefixHighTriplingCovered_union_unpaired
    (Λ : ℝ) (n : ℕ) :
    squarePrefixHighTriplingCovered Λ n ∪
        squarePrefixHighUnpairedChannels Λ n =
      squarePrefixHighHeightChannels Λ n := by
  ext channel
  constructor
  · intro hchannel
    rcases Finset.mem_union.mp hchannel with hcovered | hunpaired
    · exact squarePrefixHighTriplingCovered_subset Λ n hcovered
    · exact (mem_squarePrefixHighUnpairedChannels.mp hunpaired).1
  · intro hhigh
    by_cases hcovered : channel ∈ squarePrefixHighTriplingCovered Λ n
    · exact Finset.mem_union_left _ hcovered
    · exact Finset.mem_union_right _
        (mem_squarePrefixHighUnpairedChannels.mpr ⟨hhigh, hcovered⟩)

/-- An unpaired channel is not silently discarded: either its product already
contains `3`, or its tripled child exits the finite high support; in addition it
is not the retained child of any new-prime base. -/
theorem squarePrefixHighUnpairedChannels_reason
    {Λ : ℝ} {n : ℕ}
    {channel : RHLean.Analysis.ActualCofactorChannel}
    (hchannel : channel ∈ squarePrefixHighUnpairedChannels Λ n) :
    (3 ∣ channel.lowerCofactor * channel.upperFactor ∨
        tripledCofactorChannel channel ∉
          squarePrefixHighHeightChannels Λ n) ∧
      channel ∉ squarePrefixHighTriplingChildren Λ n := by
  have hhigh := (mem_squarePrefixHighUnpairedChannels.mp hchannel).1
  have hnotCovered := (mem_squarePrefixHighUnpairedChannels.mp hchannel).2
  have hnotBase : channel ∉ squarePrefixHighTriplingBases Λ n := by
    intro hbase
    exact hnotCovered (Finset.mem_union_left _ hbase)
  have hnotChild : channel ∉ squarePrefixHighTriplingChildren Λ n := by
    intro hchild
    exact hnotCovered (Finset.mem_union_right _ hchild)
  refine ⟨?_, hnotChild⟩
  by_cases h3 : 3 ∣ channel.lowerCofactor * channel.upperFactor
  · exact Or.inl h3
  · right
    intro htripled
    exact hnotBase
      (mem_squarePrefixHighTriplingBases.mpr ⟨hhigh, h3, htripled⟩)

/-- Generic exact sum decomposition over the complete high support. Each paired
channel occurs once, and every unmatched channel remains in the final sum. -/
theorem sum_squarePrefixHighHeightChannels_eq_pairs_add_unpaired
    {R : Type*} [AddCommMonoid R]
    (Λ : ℝ) (n : ℕ)
    (f : RHLean.Analysis.ActualCofactorChannel → R) :
    (∑ channel ∈ squarePrefixHighHeightChannels Λ n, f channel) =
      (∑ base ∈ squarePrefixHighTriplingBases Λ n,
        (f base + f (tripledCofactorChannel base))) +
      ∑ channel ∈ squarePrefixHighUnpairedChannels Λ n, f channel := by
  rw [← squarePrefixHighTriplingCovered_union_unpaired Λ n]
  rw [Finset.sum_union
    (squarePrefixHighTriplingCovered_disjoint_unpaired Λ n)]
  unfold squarePrefixHighTriplingCovered
  rw [Finset.sum_union
    (squarePrefixHighTriplingBases_disjoint_children Λ n)]
  unfold squarePrefixHighTriplingChildren
  rw [Finset.sum_image tripledCofactorChannel_injective.injOn]
  rw [Finset.sum_add_distrib]

/-- All retained Farey-mode packets of one concrete high channel, summed jointly
before any norm is taken. -/
def squarePrefixHighChannelModeContribution
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ)
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  ∑ modeLabel ∈ fareyModeLabels (cutoff M),
    RHLean.Analysis.actualResidualPacket
      (squarePrefixHighTransportData cutoff M hcutoff Λ n)
      (squarePrefixHighShell channel) channel modeLabel

/-- Exact all-mode transport contribution of the complete high family. -/
def squarePrefixHighTransportFamilyContribution
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) : ℂ :=
  ∑ channel ∈ squarePrefixHighHeightChannels Λ n,
    squarePrefixHighChannelModeContribution
      cutoff M hcutoff Λ n channel

/-- Raw once-per-channel contribution of every retained base/child pair. -/
def squarePrefixHighRetainedPairContribution
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) : ℂ :=
  ∑ base ∈ squarePrefixHighTriplingBases Λ n,
    (squarePrefixHighChannelModeContribution
        cutoff M hcutoff Λ n base +
      squarePrefixHighChannelModeContribution
        cutoff M hcutoff Λ n (tripledCofactorChannel base))

/-- Joint all-mode contribution of every explicitly unpaired high channel. -/
def squarePrefixHighUnpairedModeContribution
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) : ℂ :=
  ∑ channel ∈ squarePrefixHighUnpairedChannels Λ n,
    squarePrefixHighChannelModeContribution
      cutoff M hcutoff Λ n channel

/-- The complete high-family transport contribution is exactly paired channels
plus the explicit unpaired remainder. -/
theorem squarePrefixHighTransportFamilyContribution_eq_pair_add_unpaired
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) :
    squarePrefixHighTransportFamilyContribution
        cutoff M hcutoff Λ n =
      squarePrefixHighRetainedPairContribution
          cutoff M hcutoff Λ n +
        squarePrefixHighUnpairedModeContribution
          cutoff M hcutoff Λ n := by
  unfold squarePrefixHighTransportFamilyContribution
    squarePrefixHighRetainedPairContribution
    squarePrefixHighUnpairedModeContribution
  exact sum_squarePrefixHighHeightChannels_eq_pairs_add_unpaired
    Λ n (squarePrefixHighChannelModeContribution cutoff M hcutoff Λ n)

/-- All-mode signed defect attached to one retained base channel. -/
def squarePrefixHighTriplingBaseModeDefect
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (base : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  ∑ modeLabel ∈ fareyModeLabels (cutoff M),
    triplingSignedDefect
      (fareyResonantMode cutoff M hcutoff modeLabel) base

/-- The weighted `base + 2 * child` relation holds jointly over every retained
Farey mode for each concrete retained base. -/
theorem squarePrefixHighChannelModeContribution_add_two_tripled_eq_defect
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ)
    (base : RHLean.Analysis.ActualCofactorChannel)
    (hbase : base ∈ squarePrefixHighTriplingBases Λ n) :
    squarePrefixHighChannelModeContribution
        cutoff M hcutoff Λ n base +
      2 * squarePrefixHighChannelModeContribution
        cutoff M hcutoff Λ n (tripledCofactorChannel base) =
      squarePrefixHighTriplingBaseModeDefect
        cutoff M hcutoff base := by
  unfold squarePrefixHighChannelModeContribution
    squarePrefixHighTriplingBaseModeDefect
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro modeLabel _
  let pair : SquarePrefixHighTriplingPair Λ n :=
    { base := base
      newPrime := (mem_squarePrefixHighTriplingBases.mp hbase).2.1
      base_mem := (mem_squarePrefixHighTriplingBases.mp hbase).1
      tripled_mem := (mem_squarePrefixHighTriplingBases.mp hbase).2.2 }
  simpa [pair] using
    actualResidualPacket_squarePrefixHighTransportData_tripling_signedDefect
      cutoff M hcutoff Λ n pair modeLabel

/-- A raw once-per-channel pair is the signed defect minus the extra child copy.
This records the exact multiplicity correction forced by the `base + 2*child`
tripling law. -/
theorem squarePrefixHighChannelModeContribution_add_tripled_eq_defect_sub_tripled
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ)
    (base : RHLean.Analysis.ActualCofactorChannel)
    (hbase : base ∈ squarePrefixHighTriplingBases Λ n) :
    squarePrefixHighChannelModeContribution
        cutoff M hcutoff Λ n base +
      squarePrefixHighChannelModeContribution
        cutoff M hcutoff Λ n (tripledCofactorChannel base) =
      squarePrefixHighTriplingBaseModeDefect cutoff M hcutoff base -
        squarePrefixHighChannelModeContribution
          cutoff M hcutoff Λ n (tripledCofactorChannel base) := by
  have hweighted :=
    squarePrefixHighChannelModeContribution_add_two_tripled_eq_defect
      cutoff M hcutoff Λ n base hbase
  linear_combination hweighted

/-- Sum of all retained pair defects. -/
def squarePrefixHighRetainedDefectContribution
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) : ℂ :=
  ∑ base ∈ squarePrefixHighTriplingBases Λ n,
    squarePrefixHighTriplingBaseModeDefect cutoff M hcutoff base

/-- The one-copy child correction converting weighted signed defects back to the
raw once-per-channel high-family sum. -/
def squarePrefixHighRetainedChildCorrection
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) : ℂ :=
  ∑ base ∈ squarePrefixHighTriplingBases Λ n,
    squarePrefixHighChannelModeContribution
      cutoff M hcutoff Λ n (tripledCofactorChannel base)

/-- Exact aggregate multiplicity correction for the retained pair family. -/
theorem squarePrefixHighRetainedPairContribution_eq_defect_sub_childCorrection
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) :
    squarePrefixHighRetainedPairContribution
        cutoff M hcutoff Λ n =
      squarePrefixHighRetainedDefectContribution
          cutoff M hcutoff Λ n -
        squarePrefixHighRetainedChildCorrection
          cutoff M hcutoff Λ n := by
  unfold squarePrefixHighRetainedPairContribution
    squarePrefixHighRetainedDefectContribution
    squarePrefixHighRetainedChildCorrection
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro base hbase
  exact
    squarePrefixHighChannelModeContribution_add_tripled_eq_defect_sub_tripled
      cutoff M hcutoff Λ n base hbase

/-- Complete exact high-family identity: retained signed defects, the explicit
one-copy child multiplicity correction, and every unmatched channel. No term or
cross-mode interaction is discarded. -/
theorem squarePrefixHighTransportFamilyContribution_eq_full_decomposition
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (Λ : ℝ) (n : ℕ) :
    squarePrefixHighTransportFamilyContribution
        cutoff M hcutoff Λ n =
      (squarePrefixHighRetainedDefectContribution
          cutoff M hcutoff Λ n -
        squarePrefixHighRetainedChildCorrection
          cutoff M hcutoff Λ n) +
      squarePrefixHighUnpairedModeContribution
        cutoff M hcutoff Λ n := by
  rw [squarePrefixHighTransportFamilyContribution_eq_pair_add_unpaired]
  rw [squarePrefixHighRetainedPairContribution_eq_defect_sub_childCorrection]

end RHLean.Proof
