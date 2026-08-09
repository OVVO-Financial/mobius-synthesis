import RHLean.Proof.CanonicalGapAncestryPrimePacketRenewal

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
# Fibrewise packet renewal

`CanonicalGapAncestryPrimePacketRenewal` proves the packet renewal only after
summing over the distinguished-prime scale `k`.  This module proves it one `k` at a
time, which is the object a `q`-fibre diagnostic actually measures.

Two generic lemmas do the work, and neither uses successor or ancestry arithmetic:

* `sourceQPacketField_eq_qpPacket_sum` — a single `q`-packet refines into its
  `(j,k)` packets, for an arbitrary field.  Both projectors classify a source by its
  own scales, so this is `Finset.sum_eq_single` against
  `sourceStrippedPrimeDyadicScale_lt_bound`.
* `sourceQPacketField_sub` — the projector is additive.

In particular the parent map's preservation of the distinguished prime
(`sourcePrime_parentIndex`) is *not* needed here.  It is the right way to read the
renewal as motion down one fixed `q`-fibre, but the identity below is pure algebra.
-/

/-! ## Generic refinement and linearity of the `q`-projector -/

/-- One distinguished-prime packet refines exactly into its `(j,k)` packets.
Holds for an arbitrary source field. -/
theorem sourceQPacketField_eq_qpPacket_sum
    (B k : ℕ) (f : SourceIndex B → ℤ) :
    sourceQPacketField B k f =
      ∑ j ∈ Finset.range (B + 1), sourceQPPacketField B j k f := by
  classical
  funext s
  simp only [Finset.sum_apply]
  by_cases hk : sourcePrimeDyadicScale s = k
  · have hj : sourceStrippedPrimeDyadicScale s ∈ Finset.range (B + 1) :=
      Finset.mem_range.mpr (sourceStrippedPrimeDyadicScale_lt_bound s)
    rw [Finset.sum_eq_single (sourceStrippedPrimeDyadicScale s)]
    · simp [sourceQPacketField, sourceQPPacketField, hk]
    · intro j _hj hne
      have hne' : sourceStrippedPrimeDyadicScale s ≠ j := Ne.symm hne
      simp [sourceQPPacketField, hne']
    · intro hnot
      exact (hnot hj).elim
  · have hzero : ∀ j ∈ Finset.range (B + 1), sourceQPPacketField B j k f s = 0 := by
      intro j _hj
      simp [sourceQPPacketField, hk]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    simp [sourceQPacketField, hk]

/-- The `q`-projector is additive on differences. -/
theorem sourceQPacketField_sub
    (B k : ℕ) (f g : SourceIndex B → ℤ) :
    sourceQPacketField B k (f - g) =
      sourceQPacketField B k f - sourceQPacketField B k g := by
  funext s
  by_cases hk : sourcePrimeDyadicScale s = k <;>
    simp [sourceQPacketField, hk]

/-! ## The fibrewise renewal identity -/

/-- One distinguished-prime packet of the projected high field. -/
def sourceHighQPacketField (Λ : ℝ) (B k : ℕ) : SourceIndex B → ℤ :=
  sourceQPacketField B k (sourceHighField Λ B)

/-- **Fibrewise packet renewal.**  For each `k` separately, the high field's
`q`-packet is the projected root packet minus the successor packets in that fibre.
`CanonicalGapAncestryPrimePacketRenewal` proves this only after summing over `k`. -/
theorem sourceHighQPacketField_eq_root_sub_successorPackets
    (Λ : ℝ) (B k : ℕ) :
    sourceHighQPacketField Λ B k =
      sourceHighRootQPacketField Λ B k -
        ∑ j ∈ Finset.range (B + 1),
          sourceProjectedSuccessorPQPacketField Λ B j k := by
  unfold sourceHighQPacketField sourceHighRootQPacketField
    sourceProjectedSuccessorPQPacketField
  rw [sourceHighField_eq_root_sub_projectedSuccessor, sourceQPacketField_sub,
    sourceQPacketField_eq_qpPacket_sum B k (sourceProjectedSuccessorField Λ B)]

/-! ## Pushforward to prefixes and window paths -/

/-- Clock-pushed `q`-packet of the projected high field. -/
def sourceHighQPacketPrefix (Λ : ℝ) (B k x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x (sourceHighQPacketField Λ B k)

/-- Fibrewise renewal after the square-root clock pushforward. -/
theorem sourceHighQPacketPrefix_eq_root_sub_successorPackets
    (Λ : ℝ) (B k x : ℕ) :
    sourceHighQPacketPrefix Λ B k x =
      sourceHighRootQPacketPrefix Λ B k x -
        ∑ j ∈ Finset.range (B + 1),
          sourceProjectedSuccessorPQPacketPrefix Λ B j k x := by
  unfold sourceHighQPacketPrefix sourceHighRootQPacketPrefix
    sourceProjectedSuccessorPQPacketPrefix
  rw [sourceHighQPacketField_eq_root_sub_successorPackets, map_sub, map_sum]

/-- Actual `q`-packet path of the projected high field in a translated window. -/
def sourceHighQPacketWindowPath (Λ : ℝ) (B k N : ℕ) : ℕ → ℤ := fun r =>
  sourceHighQPacketPrefix Λ B k (N + r)

/-- Fibrewise renewal on an actual translated window.  This is the object a
`q`-fibre square-function diagnostic measures. -/
theorem sourceHighQPacketWindowPath_eq_root_sub_successorPackets
    (Λ : ℝ) (B k N : ℕ) :
    sourceHighQPacketWindowPath Λ B k N = fun r =>
      sourceHighRootQPacketWindowPath Λ B k N r -
        ∑ j ∈ Finset.range (B + 1),
          sourceProjectedSuccessorPQPacketWindowPath Λ B j k N r := by
  funext r
  unfold sourceHighQPacketWindowPath sourceHighRootQPacketWindowPath
    sourceProjectedSuccessorPQPacketWindowPath
  exact sourceHighQPacketPrefix_eq_root_sub_successorPackets Λ B k (N + r)

/-- The fibrewise identities recombine to the existing summed renewal, so nothing
here replaces `sourceHighField_eq_primePacketRenewal`; it refines it. -/
theorem sourceHighField_eq_qPacketField_sum (Λ : ℝ) (B : ℕ) :
    sourceHighField Λ B =
      ∑ k ∈ Finset.range (B + 1), sourceHighQPacketField Λ B k := by
  unfold sourceHighQPacketField
  exact sourceField_eq_qPacket_sum B (sourceHighField Λ B)

end CanonicalGapAncestryPrimePackets

end RHLean.Proof
