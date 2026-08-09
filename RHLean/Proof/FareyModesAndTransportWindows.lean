import Mathlib
import RHLean.Analysis.SquarePrefixHeightPartition

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- Reduced rational major-arc pairs `(a,r)` with `0 ≤ a < r ≤ R` and
`Nat.Coprime a r`. The zero mode occurs exactly as `(0,1)`. -/
def fareyModePairs (R : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range R).product (Finset.Icc 1 R)).filter fun p =>
    p.1 < p.2 ∧ Nat.Coprime p.1 p.2

@[simp] theorem mem_fareyModePairs
    {R : ℕ} {p : ℕ × ℕ} :
    p ∈ fareyModePairs R ↔
      p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
        1 ≤ p.2 ∧ p.2 ≤ R := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpProduct, hlt, hcop⟩
    rcases Finset.mem_product.mp hpProduct with ⟨ha, hr⟩
    rcases Finset.mem_Icc.mp hr with ⟨hrpos, hrle⟩
    exact ⟨hlt, hcop, hrpos, hrle⟩
  · rintro ⟨hlt, hcop, hrpos, hrle⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_Icc.mpr ⟨hrpos, hrle⟩⟩,
      hlt, hcop⟩
    exact Finset.mem_range.mpr (lt_of_lt_of_le hlt hrle)

/-- Canonical natural-number labels for the finite Farey mode set. -/
def fareyModeLabels (R : ℕ) : Finset ℕ :=
  (fareyModePairs R).image fun p => Nat.pair p.1 p.2

/-- Membership in the encoded support is exactly membership of the decoded pair. -/
theorem mem_fareyModeLabels
    {R label : ℕ} :
    label ∈ fareyModeLabels R ↔
      Nat.unpair label ∈ fareyModePairs R := by
  constructor
  · intro hlabel
    rcases Finset.mem_image.mp hlabel with ⟨p, hp, hpair⟩
    have hunpair : Nat.unpair label = p := by
      rw [← hpair]
      simp
    simpa [hunpair] using hp
  · intro hp
    apply Finset.mem_image.mpr
    refine ⟨Nat.unpair label, hp, ?_⟩
    exact Nat.pair_unpair label

/-- The total mode map required by `ActualResidualData`. On valid Farey labels it
returns the decoded reduced mode; outside the retained support it uses the harmless
fallback `(0,1)`. The positivity premise is unavoidable because
`ResonantModeIndex` requires a positive denominator bounded by the cutoff. -/
noncomputable def fareyResonantMode
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    (label : ℕ) : RHLean.Analysis.ResonantModeIndex cutoff M := by
  classical
  by_cases hlabel : Nat.unpair label ∈ fareyModePairs (cutoff M)
  · have hmem := mem_fareyModePairs.mp hlabel
    exact
      { numerator := (Nat.unpair label).1
        denominator := (Nat.unpair label).2
        denominator_pos := hmem.2.2.1
        denominator_le_cutoff := hmem.2.2.2 }
  · exact
      { numerator := 0
        denominator := 1
        denominator_pos := by omega
        denominator_le_cutoff := hcutoff }

/-- A retained Farey label decodes to its exact integer numerator. -/
theorem fareyResonantMode_numerator_of_mem
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    {label : ℕ} (hlabel : label ∈ fareyModeLabels (cutoff M)) :
    (fareyResonantMode cutoff M hcutoff label).numerator =
      ((Nat.unpair label).1 : ℤ) := by
  have hp := mem_fareyModeLabels.mp hlabel
  simp [fareyResonantMode, hp]

/-- A retained Farey label decodes to its exact positive denominator. -/
theorem fareyResonantMode_denominator_of_mem
    (cutoff : ℕ → ℕ) (M : ℕ) (hcutoff : 0 < cutoff M)
    {label : ℕ} (hlabel : label ∈ fareyModeLabels (cutoff M)) :
    (fareyResonantMode cutoff M hcutoff label).denominator =
      (Nat.unpair label).2 := by
  have hp := mem_fareyModeLabels.mp hlabel
  simp [fareyResonantMode, hp]

/-- The exact squared-complex rational phase of one cofactor channel at a
retained rational mode. -/
def fareyChannelPhase
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  RHLean.Analysis.resonantQuadraticMode mode (channel.upperFactor : ℤ) *
    RHLean.QuadraticPrimePhase.quadraticPhase
      (-mode.numerator) (mode.denominator : ℤ)
      (channel.lowerCofactor : ℤ)

/-- Tripling acts on the lower cofactor while retaining the upper factor. -/
def tripledCofactorChannel
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    RHLean.Analysis.ActualCofactorChannel where
  lowerCofactor := 3 * channel.lowerCofactor
  upperFactor := channel.upperFactor

/-- Quadratic phases are multiplicative in the numerator. -/
theorem quadraticPhase_add_numerator (a b r u : ℤ) :
    RHLean.QuadraticPrimePhase.quadraticPhase (a + b) r u =
      RHLean.QuadraticPrimePhase.quadraticPhase a r u *
        RHLean.QuadraticPrimePhase.quadraticPhase b r u := by
  unfold RHLean.QuadraticPrimePhase.quadraticPhase
    RHLean.QuadraticPrimePhase.additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Scaling the phase input by `3` multiplies its numerator by `9`. -/
theorem quadraticPhase_three_mul (a r u : ℤ) :
    RHLean.QuadraticPrimePhase.quadraticPhase a r (3 * u) =
      RHLean.QuadraticPrimePhase.quadraticPhase (9 * a) r u := by
  unfold RHLean.QuadraticPrimePhase.quadraticPhase
  congr 1
  ring

/-- Exact Farey-mode transport under `(c,q) ↦ (3c,q)`. The rational mode and
its denominator are unchanged; the entire change is the explicit cofactor phase
`quadraticPhase (-8a) r c`. No Möbius sign is inserted here. -/
theorem fareyChannelPhase_tripled
    {cutoff : ℕ → ℕ} {M : ℕ}
    (mode : RHLean.Analysis.ResonantModeIndex cutoff M)
    (channel : RHLean.Analysis.ActualCofactorChannel) :
    fareyChannelPhase mode (tripledCofactorChannel channel) =
      RHLean.QuadraticPrimePhase.quadraticPhase
          (-8 * mode.numerator) (mode.denominator : ℤ)
          (channel.lowerCofactor : ℤ) *
        fareyChannelPhase mode channel := by
  have hcofactor :
      RHLean.QuadraticPrimePhase.quadraticPhase
          (-mode.numerator) (mode.denominator : ℤ)
          (3 * (channel.lowerCofactor : ℤ)) =
        RHLean.QuadraticPrimePhase.quadraticPhase
            (-8 * mode.numerator) (mode.denominator : ℤ)
            (channel.lowerCofactor : ℤ) *
          RHLean.QuadraticPrimePhase.quadraticPhase
            (-mode.numerator) (mode.denominator : ℤ)
            (channel.lowerCofactor : ℤ) := by
    rw [quadraticPhase_three_mul]
    rw [show 9 * (-mode.numerator) =
      (-8 * mode.numerator) + (-mode.numerator) by ring]
    exact quadraticPhase_add_numerator
      (-8 * mode.numerator) (-mode.numerator)
      (mode.denominator : ℤ) (channel.lowerCofactor : ℤ)
  unfold fareyChannelPhase tripledCofactorChannel
  simp only
  push_cast
  rw [hcofactor]
  ring

/-- Exact source-entry shell `e(cq)=⌊√(cq)⌋`. This is the manuscript's square
block assignment, not an invented high-height shell partition. -/
def orderedChannelEntryShell
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℕ :=
  Nat.sqrt (channel.lowerCofactor * channel.upperFactor)

/-- Exact smoothness-transition index `h(c,q)=q-1` for the ordered channel. -/
def orderedChannelTransitionIndex
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℕ :=
  channel.upperFactor - 1

/-- Exact start field for the contiguous transport packet. -/
def orderedTransportPacketStart
    (_shell : ℕ) (channel : RHLean.Analysis.ActualCofactorChannel)
    (_modeLabel : ℕ) : ℕ :=
  orderedChannelEntryShell channel

/-- Exact length field for the contiguous transport packet. Natural subtraction
automatically gives length zero to channels that enter after their transition. -/
def orderedTransportPacketLength
    (_shell : ℕ) (channel : RHLean.Analysis.ActualCofactorChannel)
    (_modeLabel : ℕ) : ℕ :=
  orderedChannelTransitionIndex channel - orderedChannelEntryShell channel

/-- The fixed-packet interval is exactly the manuscript interval
`[⌊√(cq)⌋,q-1)`, including the empty-window case. -/
theorem orderedTransportPacket_range
    (shell : ℕ) (channel : RHLean.Analysis.ActualCofactorChannel)
    (modeLabel : ℕ) :
    Finset.Ico (orderedTransportPacketStart shell channel modeLabel)
        (orderedTransportPacketStart shell channel modeLabel +
          orderedTransportPacketLength shell channel modeLabel) =
      Finset.Ico (orderedChannelEntryShell channel)
        (orderedChannelTransitionIndex channel) := by
  ext k
  simp [orderedTransportPacketStart, orderedTransportPacketLength,
    orderedChannelEntryShell, orderedChannelTransitionIndex]
  omega

/-- The corresponding fixed packet is exactly the sum over the contiguous
transport interval. -/
theorem orderedTransportPacket_eq_intervalSum
    {R : Type*} [AddCommMonoid R]
    (x : ℕ → R) (shell : ℕ)
    (channel : RHLean.Analysis.ActualCofactorChannel)
    (modeLabel : ℕ) :
    RHLean.Kernel.packet x
        (orderedTransportPacketStart shell channel modeLabel)
        (orderedTransportPacketLength shell channel modeLabel) =
      ∑ k ∈ Finset.Ico (orderedChannelEntryShell channel)
          (orderedChannelTransitionIndex channel), x k := by
  unfold RHLean.Kernel.packet
  rw [orderedTransportPacket_range]

/-- The finite square-prefix shell count covering entry blocks `0,…,n`. -/
def squarePrefixEntryShellCount (n : ℕ) : ℕ :=
  n + 1

/-- Every retained normalized ordered channel at square prefix `n` has its entry
shell inside the concrete finite shell range. -/
theorem orderedChannelEntryShell_lt_squarePrefixEntryShellCount
    {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ squarePrefixCofactorPairs n) :
    orderedChannelEntryShell (actualChannelOfPair p) <
      squarePrefixEntryShellCount n := by
  classical
  unfold squarePrefixCofactorPairs at hp
  rcases Finset.mem_biUnion.mp hp with ⟨m, hm, hpFiber⟩
  have hprod := product_eq_of_mem_orderedCoprimeFactorPairs hpFiber
  have hm_lt : m < RHLean.Analysis.squarePrefixEndpoint n + 1 :=
    Finset.mem_range.mp hm
  rw [RHLean.Analysis.squarePrefixEndpoint_add_one] at hm_lt
  unfold orderedChannelEntryShell squarePrefixEntryShellCount
  simp only [actualChannelOfPair_lowerCofactor,
    actualChannelOfPair_upperFactor]
  rw [hprod]
  exact Nat.sqrt_lt'.2 hm_lt

end RHLean.Proof
