import RHLean.Analysis.OutsidePrimeLeastSquareMaximalWheel
import RHLean.Proof.ExceptionalSignedPacketIdentification

/-!
# Exceptional partition of the complete outside-square deletion parent

The maximal-wheel blocker proves that, under its finite certificate, no generic
least-square owner `q >= 11` can occur in the complete square-block interior.
Because every physical square contact is odd, the only possible complete owners
are therefore `3`, `5`, and `7`.

This file packages that fact at the exact carrier and signed-mass levels.  It is
bookkeeping only: the observable remains the selected-prime degree-one field
used by the outside-prime deletion decomposition.  No identification with the
true Möbius observable is made here.  That separation is deliberate, because
the remaining selected-prime / Möbius first-power parity transfer is the genuine
parent-side seam.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Every complete least-square deletion cell has one of the three exceptional
physical owners once the maximal-wheel blocker certificate is available. -/
theorem squareBlockOutsidePrimeLeastComplete_owner_exceptional
    {P : Finset ℕ} {R k : ℕ}
    (hcert : OutsidePrimeGenericBlockerCertificate R P)
    (hk : k ∈ squareBlockOutsidePrimeLeastCompleteCells P R) :
    physicalLeastOddSquarePrime k = some 3 ∨
      physicalLeastOddSquarePrime k = some 5 ∨
        physicalLeastOddSquarePrime k = some 7 := by
  have hkDel : k ∈ squareBlockOutsidePrimeDeletionCells P R :=
    (Finset.mem_filter.mp hk).1
  obtain ⟨q, hqOwner⟩ := outsidePrimeDeletion_leastSquare_exists hkDel
  have hqLt : q < 11 :=
    outsidePrimeLeastComplete_owner_lt_eleven_of_certificate
      hcert hk hqOwner
  have hqHit := physicalLeastOddSquarePrime_some_spec hqOwner
  have hqPrime : q.Prime := hqHit.1
  have hqOdd : q % 2 = 1 := physicalSquarePrimeAtEdge_odd hqHit
  have hqTwo : 2 ≤ q := hqPrime.two_le
  have hqNeNine : q ≠ 9 := by
    intro h
    subst q
    norm_num at hqPrime
  have hcases : q = 3 ∨ q = 5 ∨ q = 7 := by
    omega
  rcases hcases with rfl | rfl | rfl
  · exact Or.inl hqOwner
  · exact Or.inr (Or.inl hqOwner)
  · exact Or.inr (Or.inr hqOwner)

/-- The complete deletion carrier is exactly the disjoint union of the three
exceptional least-owner fibres. -/
theorem squareBlockOutsidePrimeLeastCompleteCells_eq_exceptionalOwners
    {P : Finset ℕ} {R : ℕ}
    (hcert : OutsidePrimeGenericBlockerCertificate R P) :
    squareBlockOutsidePrimeLeastCompleteCells P R =
      exceptionalCompleteOwnerCells P R 3 ∪
        (exceptionalCompleteOwnerCells P R 5 ∪
          exceptionalCompleteOwnerCells P R 7) := by
  ext k
  constructor
  · intro hk
    rcases squareBlockOutsidePrimeLeastComplete_owner_exceptional hcert hk with
      h3 | h5 | h7
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hk, h3⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hk, h5⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hk, h7⟩))
  · intro hk
    rcases Finset.mem_union.mp hk with h3 | h57
    · exact (Finset.mem_filter.mp h3).1
    · rcases Finset.mem_union.mp h57 with h5 | h7
      · exact (Finset.mem_filter.mp h5).1
      · exact (Finset.mem_filter.mp h7).1

/-- Distinct least-owner fibres are disjoint before any observable is summed. -/
theorem exceptionalCompleteOwnerCells_disjoint
    (P : Finset ℕ) (R : ℕ) {q r : ℕ} (hqr : q ≠ r) :
    Disjoint (exceptionalCompleteOwnerCells P R q)
      (exceptionalCompleteOwnerCells P R r) := by
  apply Finset.disjoint_left.mpr
  intro k hkq hkr
  have hq := (Finset.mem_filter.mp hkq).2
  have hr := (Finset.mem_filter.mp hkr).2
  have hsome : some q = some r := hq.symm.trans hr
  exact hqr (Option.some.inj hsome)

/-- Selected-prime signed mass carried by one exceptional complete owner.  This
is intentionally not the true Möbius source packet. -/
def exceptionalCompleteOwnerSelectedPacket
    (P : Finset ℕ) (R q : ℕ) : ℝ :=
  ∑ k ∈ exceptionalCompleteOwnerCells P R q,
    selectedDegreeOneProjection P k

/-- Under the blocker certificate, the complete outside-square deletion mass is
exactly the sum of the selected-prime masses on owners `3`, `5`, and `7`. -/
theorem squareBlockOutsidePrimeLeastCompleteT_eq_exceptionalSelectedPackets
    {P : Finset ℕ} {R : ℕ}
    (hcert : OutsidePrimeGenericBlockerCertificate R P) :
    squareBlockOutsidePrimeLeastCompleteT P R =
      exceptionalCompleteOwnerSelectedPacket P R 3 +
        exceptionalCompleteOwnerSelectedPacket P R 5 +
          exceptionalCompleteOwnerSelectedPacket P R 7 := by
  let A := exceptionalCompleteOwnerCells P R 3
  let B := exceptionalCompleteOwnerCells P R 5
  let C := exceptionalCompleteOwnerCells P R 7
  have hBC : Disjoint B C := by
    dsimp [B, C]
    exact exceptionalCompleteOwnerCells_disjoint P R (by norm_num)
  have hA_BC : Disjoint A (B ∪ C) := by
    apply Finset.disjoint_left.mpr
    intro k hkA hkBC
    rcases Finset.mem_union.mp hkBC with hkB | hkC
    · exact (Finset.disjoint_left.mp
        (exceptionalCompleteOwnerCells_disjoint P R (by norm_num : 3 ≠ 5)))
          hkA hkB
    · exact (Finset.disjoint_left.mp
        (exceptionalCompleteOwnerCells_disjoint P R (by norm_num : 3 ≠ 7)))
          hkA hkC
  unfold squareBlockOutsidePrimeLeastCompleteT
    exceptionalCompleteOwnerSelectedPacket
  rw [squareBlockOutsidePrimeLeastCompleteCells_eq_exceptionalOwners hcert]
  change (∑ k ∈ A ∪ (B ∪ C), selectedDegreeOneProjection P k) = _
  rw [Finset.sum_union hA_BC, Finset.sum_union hBC]
  ring

/-- **Exact selected deletion-parent normal form.**  One square block's entire
outside-square deletion term is the three exceptional complete owner packets
plus the already-defined aggregate incomplete-super-orbit endpoint.  No norm,
triangle inequality, or selected-to-Möbius substitution enters. -/
theorem squareBlockOutsidePrimeDeletionT_eq_exceptionalSelected_add_endpoint
    {P : Finset ℕ} {R : ℕ}
    (hcert : OutsidePrimeGenericBlockerCertificate R P) :
    outsidePrimeDeletionT P (threeSlotSquareBlockTransitionCells R) =
      exceptionalCompleteOwnerSelectedPacket P R 3 +
        exceptionalCompleteOwnerSelectedPacket P R 5 +
          exceptionalCompleteOwnerSelectedPacket P R 7 +
            squareBlockOutsidePrimeLeastEndpointT P R := by
  rw [squareBlockOutsidePrimeDeletionT_eq_complete_add_endpoint,
    squareBlockOutsidePrimeLeastCompleteT_eq_exceptionalSelectedPackets hcert]

end RHLean.Proof
