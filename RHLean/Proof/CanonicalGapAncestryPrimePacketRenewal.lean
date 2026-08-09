import RHLean.Proof.CanonicalGapAncestryPrimePacketScales

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapAncestryPrimePackets

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge
open CanonicalGapAncestryHighRealization
open CanonicalGapAncestryProjectedRenewal

/-!
# Exact two-parameter packet renewal

This module applies the packet projectors to the projected ancestry renewal and
pushes the resulting identities through the square-root clock and window paths.
-/

/-! ## Projected-renewal packets -/

/-- The two projected successor populations retained as one signed field. -/
def sourceProjectedSuccessorField (Λ : ℝ) (B : ℕ) :
    SourceIndex B → ℤ :=
  sourceLowToHighSuccessorField Λ B + sourceHighToHighSuccessorField Λ B

/-- The projected renewal with both successor populations recombined. -/
theorem sourceHighField_eq_root_sub_projectedSuccessor
    (Λ : ℝ) (B : ℕ) :
    sourceHighField Λ B =
      sourceHighRootField Λ B - sourceProjectedSuccessorField Λ B := by
  rw [sourceHighField_eq_projectedRenewal]
  unfold sourceProjectedSuccessorField
  abel

/-- One `q`-scale packet of the projected root field. -/
def sourceHighRootQPacketField (Λ : ℝ) (B k : ℕ) :
    SourceIndex B → ℤ :=
  sourceQPacketField B k (sourceHighRootField Λ B)

/-- One `(p,q)`-scale packet of the complete projected successor field. -/
def sourceProjectedSuccessorPQPacketField
    (Λ : ℝ) (B j k : ℕ) : SourceIndex B → ℤ :=
  sourceQPPacketField B j k (sourceProjectedSuccessorField Λ B)

/-- Exact recombination of the projected root packets. -/
theorem sourceHighRootField_eq_qPacket_sum
    (Λ : ℝ) (B : ℕ) :
    sourceHighRootField Λ B =
      ∑ k ∈ Finset.range (B + 1), sourceHighRootQPacketField Λ B k := by
  exact sourceField_eq_qPacket_sum B (sourceHighRootField Λ B)

/-- Exact recombination of the projected successor packets. -/
theorem sourceProjectedSuccessorField_eq_qpPacket_sum
    (Λ : ℝ) (B : ℕ) :
    sourceProjectedSuccessorField Λ B =
      ∑ k ∈ Finset.range (B + 1),
        ∑ j ∈ Finset.range (B + 1),
          sourceProjectedSuccessorPQPacketField Λ B j k := by
  exact sourceField_eq_qpPacket_sum B (sourceProjectedSuccessorField Λ B)

/-- The projected successor field vanishes away from smooth children. -/
theorem sourceProjectedSuccessorField_eq_zero_of_not_smooth
    (Λ : ℝ) (B : ℕ) (s : SourceIndex B)
    (hs : ¬ SmoothOriented s) :
    sourceProjectedSuccessorField Λ B s = 0 := by
  have hparent : sourceParent s = none :=
    (sourceParent_eq_none_iff s).2 hs
  unfold sourceProjectedSuccessorField sourceLowToHighSuccessorField
    sourceHighToHighSuccessorField sourceLowField sourceHighField
  simp [sourceHighProjector, successorOperator, boundedSourceFlow, hparent]

/-- The projected successor packets have exact triangular support `j ≤ k`. -/
theorem sourceProjectedSuccessorPQPacketField_eq_zero_of_k_lt_j
    {Λ : ℝ} {B j k : ℕ} (hjk : k < j) :
    sourceProjectedSuccessorPQPacketField Λ B j k = 0 := by
  exact sourceQPPacketField_eq_zero_of_k_lt_j
    (sourceProjectedSuccessorField Λ B)
    (sourceProjectedSuccessorField_eq_zero_of_not_smooth Λ B) hjk

/-- Exact field-level two-parameter packet renewal. -/
theorem sourceHighField_eq_primePacketRenewal
    (Λ : ℝ) (B : ℕ) :
    sourceHighField Λ B =
      (∑ k ∈ Finset.range (B + 1), sourceHighRootQPacketField Λ B k) -
        ∑ k ∈ Finset.range (B + 1),
          ∑ j ∈ Finset.range (B + 1),
            sourceProjectedSuccessorPQPacketField Λ B j k := by
  rw [sourceHighField_eq_root_sub_projectedSuccessor,
    sourceHighRootField_eq_qPacket_sum,
    sourceProjectedSuccessorField_eq_qpPacket_sum]

/-! ## Clock pushforward and window paths -/

/-- Clock-pushed projected root packet. -/
def sourceHighRootQPacketPrefix
    (Λ : ℝ) (B k x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x (sourceHighRootQPacketField Λ B k)

/-- Clock-pushed complete projected successor packet. -/
def sourceProjectedSuccessorPQPacketPrefix
    (Λ : ℝ) (B j k x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x
    (sourceProjectedSuccessorPQPacketField Λ B j k)

/-- Exact packet renewal after the native square-root clock pushforward. -/
theorem sourceHighPrefix_eq_primePacketRenewal
    (Λ : ℝ) (B x : ℕ) :
    sourceHighPrefix Λ B x =
      (∑ k ∈ Finset.range (B + 1), sourceHighRootQPacketPrefix Λ B k x) -
        ∑ k ∈ Finset.range (B + 1),
          ∑ j ∈ Finset.range (B + 1),
            sourceProjectedSuccessorPQPacketPrefix Λ B j k x := by
  unfold sourceHighRootQPacketPrefix sourceProjectedSuccessorPQPacketPrefix
  change clockPushforward (sourceClock B) x (sourceHighField Λ B) = _
  rw [sourceHighField_eq_primePacketRenewal, map_sub, map_sum, map_sum]
  apply congrArg₂ Sub.sub rfl
  apply Finset.sum_congr rfl
  intro k _hk
  rw [map_sum]

/-- Actual projected root packet path in a translated window. -/
def sourceHighRootQPacketWindowPath
    (Λ : ℝ) (B k N : ℕ) : ℕ → ℤ := fun r =>
  sourceHighRootQPacketPrefix Λ B k (N + r)

/-- Actual complete projected successor packet path in a translated window. -/
def sourceProjectedSuccessorPQPacketWindowPath
    (Λ : ℝ) (B j k N : ℕ) : ℕ → ℤ := fun r =>
  sourceProjectedSuccessorPQPacketPrefix Λ B j k (N + r)

/-- Exact fibered packet renewal on an actual translated window. -/
theorem sourceHighWindowPath_eq_primePacketRenewal
    (Λ : ℝ) (B N : ℕ) :
    sourceHighWindowPath Λ B N = fun r =>
      ∑ k ∈ Finset.range (B + 1),
        (sourceHighRootQPacketWindowPath Λ B k N r -
          ∑ j ∈ Finset.range (B + 1),
            sourceProjectedSuccessorPQPacketWindowPath Λ B j k N r) := by
  funext r
  unfold sourceHighWindowPath sourceHighRootQPacketWindowPath
    sourceProjectedSuccessorPQPacketWindowPath
  rw [Finset.sum_sub_distrib]
  exact sourceHighPrefix_eq_primePacketRenewal Λ B (N + r)

end CanonicalGapAncestryPrimePackets

end RHLean.Proof
