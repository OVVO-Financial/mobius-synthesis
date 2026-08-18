import Mathlib
import RHLean.Analysis.PrimeSieveDyadicChordEnergy

/-!
# Signed sibling packets for the dyadic prime-discrepancy chord

An earlier layer identified the boundary-free Abel coefficient field with the secant-chord
residual of the clipped classical discrepancy

`D(d) = pi(max y (x / d)) - Li(max y (x / d))`.

This module exposes the signed interval coordinate carried by that chord geometry.
For an interval `[a,b]` and an interior split `m`, define the sibling packet

`B(a,m,b) = (b-m) * (D(m)-D(a)) - (m-a) * (D(b)-D(m))`.

The packet is exactly the scaled deviation of `D(m)` from the chord joining the
endpoints.  More importantly, the already-proved reciprocal telescope identifies
it with a signed imbalance between the two child interval discrepancy masses:

`B = (m-a) * sum_[m,b) Delta_d - (b-m) * sum_[a,m) Delta_d`.

Thus no triangle split of `pi` and `Li` is introduced.  At the full occupied
dyadic block, normalizing this packet by the block width recovers the chord
residual pointwise.  Consequently the full root-packet energy is exactly the
chord energy, and the existing RH reduction can be restated directly
in this signed sibling-packet coordinate.

The generic interval packet is deliberately defined for arbitrary `a <= m <= b`.
That is the exact algebra needed for later recursive midpoint / Faber--Schauder
refinement without changing the signed arithmetic object.

No analytic estimate is proved here.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- Signed left-versus-right packet of the clipped classical prime discrepancy.
The coefficients are the opposite child lengths, so the packet vanishes on every
affine function of the reciprocal coordinate. -/
def primeSieveSignedSiblingPacket (y x a m b : ℕ) : ℂ :=
  (((b - m : ℕ) : ℂ) *
      (primeSieveDyadicClippedDiscrepancy y x m -
        primeSieveDyadicClippedDiscrepancy y x a)) -
    (((m - a : ℕ) : ℂ) *
      (primeSieveDyadicClippedDiscrepancy y x b -
        primeSieveDyadicClippedDiscrepancy y x m))

/-- The same packet written as the scaled deviation from the endpoint chord.
This division-free form is useful over `ℂ` and avoids introducing any positivity
hypothesis into the definition. -/
def primeSieveScaledSiblingChordDeviation (y x a m b : ℕ) : ℂ :=
  (((b - a : ℕ) : ℂ) * primeSieveDyadicClippedDiscrepancy y x m) -
    (((b - m : ℕ) : ℂ) * primeSieveDyadicClippedDiscrepancy y x a) -
    (((m - a : ℕ) : ℂ) * primeSieveDyadicClippedDiscrepancy y x b)

/-- Pure finite geometry: the signed sibling packet is exactly the scaled chord
deviation at the split point. -/
theorem primeSieveSignedSiblingPacket_eq_scaledChordDeviation
    {y x a m b : ℕ} (ham : a ≤ m) (hmb : m ≤ b) :
    primeSieveSignedSiblingPacket y x a m b =
      primeSieveScaledSiblingChordDeviation y x a m b := by
  have hsplit : b - a = (b - m) + (m - a) := by omega
  unfold primeSieveSignedSiblingPacket primeSieveScaledSiblingChordDeviation
  rw [hsplit]
  push_cast
  ring

/-- Exact arithmetic form of the packet.  On any reciprocal-support subinterval,
the two endpoint differences telescope to the signed prime-count-minus-Li masses
of the two children. -/
theorem primeSieveSignedSiblingPacket_eq_weighted_intervalDiscrepancies
    {y x a m b : ℕ}
    (ha : 1 ≤ a) (ham : a ≤ m) (hmb : m ≤ b)
    (hb : b ≤ x / (y + 1) + 1) :
    primeSieveSignedSiblingPacket y x a m b =
      (((m - a : ℕ) : ℂ) *
        (∑ d ∈ Finset.Ico m b,
          primeSieveReciprocalPrimeDiscrepancy y x d)) -
      (((b - m : ℕ) : ℂ) *
        (∑ d ∈ Finset.Ico a m,
          primeSieveReciprocalPrimeDiscrepancy y x d)) := by
  have hm1 : 1 ≤ m := ha.trans ham
  have hleft := sum_primeSieveReciprocalPrimeDiscrepancy_Ico_eq
    (y := y) (x := x) ha ham (hmb.trans hb)
  have hright := sum_primeSieveReciprocalPrimeDiscrepancy_Ico_eq
    (y := y) (x := x) hm1 hmb hb
  unfold primeSieveSignedSiblingPacket
  rw [hleft, hright]
  ring

/-- Width-normalized sibling packet.  At the root interval of an occupied dyadic
block this is exactly the chord residual. -/
def primeSieveSignedSiblingPacketResidual (y x a m b : ℕ) : ℂ :=
  (((b - a : ℕ) : ℂ)⁻¹) * primeSieveSignedSiblingPacket y x a m b

/-- On an occupied block, the unnormalized root packet is the block width
times the chord residual at the chosen reciprocal index. -/
theorem primeSieveDyadicRootPacket_eq_width_mul_chordResidual
    {y x j d : ℕ}
    (hj : j ∈ primeSieveDyadicBlockIndices y x)
    (hdB : d ∈ primeSieveDyadicBlock y x j) :
    primeSieveSignedSiblingPacket y x
        (primeSieveDyadicBlockLeft j) d
        (primeSieveDyadicBlockRight y x j + 1) =
      (((primeSieveDyadicBlockRight y x j + 1 -
          primeSieveDyadicBlockLeft j : ℕ) : ℂ) *
        primeSieveDyadicChordResidual y x j d) := by
  have hsec := card_mul_primeSieveDyadicBlockMean_eq_secantDrop hj
  have hcard := card_primeSieveDyadicBlock hj
  rw [hcard] at hsec
  have hdE := hdB
  rw [primeSieveDyadicBlock_eq_explicitIcc] at hdE
  rcases Finset.mem_Icc.mp hdE with ⟨hleftd, hdright⟩
  have hsplit :
      primeSieveDyadicBlockRight y x j + 1 - primeSieveDyadicBlockLeft j =
        (primeSieveDyadicBlockRight y x j + 1 - d) +
          (d - primeSieveDyadicBlockLeft j) := by
    omega
  calc
    primeSieveSignedSiblingPacket y x
        (primeSieveDyadicBlockLeft j) d
        (primeSieveDyadicBlockRight y x j + 1) =
      (((primeSieveDyadicBlockRight y x j + 1 -
          primeSieveDyadicBlockLeft j : ℕ) : ℂ) *
        (primeSieveDyadicClippedDiscrepancy y x d -
          primeSieveDyadicClippedDiscrepancy y x
            (primeSieveDyadicBlockLeft j))) +
      (((d - primeSieveDyadicBlockLeft j : ℕ) : ℂ) *
        (primeSieveDyadicClippedDiscrepancy y x
            (primeSieveDyadicBlockLeft j) -
          primeSieveDyadicClippedDiscrepancy y x
            (primeSieveDyadicBlockRight y x j + 1))) := by
        unfold primeSieveSignedSiblingPacket
        rw [hsplit]
        push_cast
        ring
    _ = (((primeSieveDyadicBlockRight y x j + 1 -
          primeSieveDyadicBlockLeft j : ℕ) : ℂ) *
        primeSieveDyadicChordResidual y x j d) := by
        unfold primeSieveDyadicChordResidual
        rw [← hsec]
        ring

/-- Pointwise recovery of the chord coordinate from the signed root packet. -/
theorem primeSieveDyadicRootPacketResidual_eq_chordResidual
    {y x j d : ℕ}
    (hj : j ∈ primeSieveDyadicBlockIndices y x)
    (hdB : d ∈ primeSieveDyadicBlock y x j) :
    primeSieveSignedSiblingPacketResidual y x
        (primeSieveDyadicBlockLeft j) d
        (primeSieveDyadicBlockRight y x j + 1) =
      primeSieveDyadicChordResidual y x j d := by
  have hle := primeSieveDyadicBlockLeft_le_right_of_mem_indices hj
  have hwidthNat :
      0 < primeSieveDyadicBlockRight y x j + 1 -
        primeSieveDyadicBlockLeft j := by omega
  have hwidth :
      ((((primeSieveDyadicBlockRight y x j + 1 -
        primeSieveDyadicBlockLeft j : ℕ) : ℂ))) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hwidthNat)
  unfold primeSieveSignedSiblingPacketResidual
  rw [primeSieveDyadicRootPacket_eq_width_mul_chordResidual hj hdB]
  simp [hwidth]

/-- Energy of the width-normalized root sibling packets over all occupied
dyadic reciprocal blocks. -/
def primeSieveDyadicSignedRootPacketEnergy (y x : ℕ) : ℝ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    ∑ d ∈ primeSieveDyadicBlock y x j,
      ‖primeSieveSignedSiblingPacketResidual y x
          (primeSieveDyadicBlockLeft j) d
          (primeSieveDyadicBlockRight y x j + 1)‖ ^ 2

/-- Exact energy preservation: the signed root-packet energy is literally the
prime-discrepancy chord energy. -/
theorem primeSieveDyadicSignedRootPacketEnergy_eq_chordEnergy
    (y x : ℕ) :
    primeSieveDyadicSignedRootPacketEnergy y x =
      primeSieveDyadicChordEnergy y x := by
  classical
  unfold primeSieveDyadicSignedRootPacketEnergy primeSieveDyadicChordEnergy
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro d hdB
  rw [primeSieveDyadicRootPacketResidual_eq_chordResidual hj hdB]

/-- Critical block-uniform energy target expressed entirely in the signed sibling
packet coordinate.  It is equivalent to the chord-energy target. -/
def DyadicSignedRootPacketEnergyBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveDyadicSignedRootPacketEnergy
            (primorialPNTPrimeSieveCutoff k) x ≤
          C * Real.rpow ((x : ℝ) + 1) (1 + ε)

/-- The signed packet target is exactly equivalent to the chord target. -/
theorem dyadicSignedRootPacketEnergyBlockBounded_iff_chordEnergyBlockBounded :
    DyadicSignedRootPacketEnergyBlockBoundedStatement ↔
      DyadicPrimeDiscrepancyChordEnergyBlockBoundedStatement := by
  constructor
  · intro hP ε hε
    obtain ⟨C, hC, hPb⟩ := hP ε hε
    refine ⟨C, hC, ?_⟩
    intro k x hk hlow hup
    rw [← primeSieveDyadicSignedRootPacketEnergy_eq_chordEnergy]
    exact hPb k x hk hlow hup
  · intro hE ε hε
    obtain ⟨C, hC, hEb⟩ := hE ε hε
    refine ⟨C, hC, ?_⟩
    intro k x hk hlow hup
    rw [primeSieveDyadicSignedRootPacketEnergy_eq_chordEnergy]
    exact hEb k x hk hlow hup

/-- The complete reduction stated in the signed sibling-packet coordinate.
Future multiscale refinements only need to prove the packet-energy hypothesis;
the downstream RH architecture is unchanged. -/
theorem riemannHypothesis_of_dyadicSignedPacketAnalyticPackage
    (hC : DyadicCoherentChannelRHScale)
    (hP : DyadicSignedRootPacketEnergyBlockBoundedStatement)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_dyadicChordAnalyticPackage hC
  · exact dyadicSignedRootPacketEnergyBlockBounded_iff_chordEnergyBlockBounded.mp hP
  · exact hD

end RHLean.Analysis
