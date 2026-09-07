import Mathlib
import RHLean.Proof.SquareRootLowPrimeStructuralKey
import RHLean.Proof.SquareRootLowPrimeResponseSeatAtomEquiv

/-!
# Deep processed seats are exactly response seats

The complete processed-seat carrier contains both the shallow creation side and
the deep response side.  Once the cofactor owner lies strictly above the packet
cutoff `K`, there is no coordinate ambiguity: the processed cofactor is owned by
its canonical largest prime in `(K,U]`, and the literal seat bound is exactly
the response-seat bound.

Thus the deep non-head part of the processed carrier is definitionally the
existing owned response-seat universe, after proving the arithmetic owner
membership.  This is the bridge used by the `BornExit` branch of the final
no-liberty classifier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Non-head processed seats whose canonical prime owner is genuinely above
`K`. -/
def squareRootLowPrimeProcessedDeepSeatAtoms
    (R K j U : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeProcessedSeatAtoms R K j U).filter fun z =>
    K < canonicalLargestPrimeFactor z.1

@[simp] theorem mem_squareRootLowPrimeProcessedDeepSeatAtoms
    {R K j U : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeProcessedDeepSeatAtoms R K j U ↔
      z ∈ squareRootLowPrimeProcessedSeatAtoms R K j U ∧
        K < canonicalLargestPrimeFactor z.1 := by
  simp [squareRootLowPrimeProcessedDeepSeatAtoms]

private theorem squareRootLowPrimeProcessedDeepCofactor_mem_ownedSigned
    {R K U c : ℕ} (hK : 1 ≤ K)
    (hc : c ∈ squareRootLowPrimeProcessedSignedCofactors R U)
    (hdeep : K < canonicalLargestPrimeFactor c) :
    c ∈ squareRootLowPrimeOwnedSignedCofactors R K U := by
  rcases Finset.mem_filter.mp hc with ⟨hcRange, hlpfU, hmu⟩
  have hcOne := (Finset.mem_Icc.mp hcRange).1
  have hcGt : 1 < c := by
    by_contra hnot
    have hcEq : c = 1 := by omega
    subst c
    simp [canonicalLargestPrimeFactor] at hdeep
    omega
  have hpPrime : (canonicalLargestPrimeFactor c).Prime :=
    canonicalLargestPrimeFactor_prime hcGt
  have hpFresh : canonicalLargestPrimeFactor c ∈
      squareRootLowPrimeFreshPrimeSet K U := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hdeep, hlpfU⟩, hpPrime⟩
  have hcFresh : c ∈ squareRootLowPrimeBornFreshCofactors R
      (canonicalLargestPrimeFactor c) := by
    exact Finset.mem_filter.mpr ⟨hcRange, rfl⟩
  have habs : |μ c| ≤ 1 :=
    ArithmeticFunction.abs_moebius_le_one (n := c)
  have hbounds : -(1 : ℤ) ≤ μ c ∧ μ c ≤ 1 :=
    abs_le.mp habs
  have hsign : μ c = 1 ∨ μ c = -1 := by
    omega
  unfold squareRootLowPrimeOwnedSignedCofactors
  rcases hsign with hpos | hneg
  · apply Finset.mem_union.mpr
    left
    unfold squareRootLowPrimeOwnedBadCofactors
    apply Finset.mem_biUnion.mpr
    refine ⟨canonicalLargestPrimeFactor c, hpFresh, ?_⟩
    exact Finset.mem_filter.mpr ⟨hcFresh, hpos⟩
  · apply Finset.mem_union.mpr
    right
    unfold squareRootLowPrimeOwnedDeletionCofactors
    apply Finset.mem_biUnion.mpr
    refine ⟨canonicalLargestPrimeFactor c, hpFresh, ?_⟩
    exact Finset.mem_filter.mpr ⟨hcFresh, hneg⟩

private theorem squareRootLowPrimeOwnedSignedCofactor_mem_processed
    {R K U c : ℕ}
    (hc : c ∈ squareRootLowPrimeOwnedSignedCofactors R K U) :
    c ∈ squareRootLowPrimeProcessedSignedCofactors R U ∧
      K < canonicalLargestPrimeFactor c := by
  have hcResponse : c ∈ squareRootLowPrimeOwnedResponseCofactors R K U := by
    simpa [squareRootLowPrimeOwnedSignedCofactors,
      squareRootLowPrimeOwnedResponseCofactors] using hc
  have hpFresh :=
    canonicalLargestPrimeFactor_mem_freshPrimeSet_of_mem_ownedResponseCofactors
      hcResponse
  have hpData := Finset.mem_filter.mp hpFresh
  have hpIoc := Finset.mem_Ioc.mp hpData.1
  have hcRange : c ∈ Finset.Icc 1 (squareRootEndpoint R) := by
    rcases Finset.mem_union.mp hc with hbad | hdel
    · unfold squareRootLowPrimeOwnedBadCofactors at hbad
      rcases Finset.mem_biUnion.mp hbad with ⟨p, _hp, hcp⟩
      unfold squareRootLowPrimeBadCofactors at hcp
      have hcFresh := (Finset.mem_filter.mp hcp).1
      exact (Finset.mem_filter.mp hcFresh).1
    · unfold squareRootLowPrimeOwnedDeletionCofactors at hdel
      rcases Finset.mem_biUnion.mp hdel with ⟨p, _hp, hcp⟩
      unfold squareRootLowPrimeDeletionCofactors at hcp
      have hcFresh := (Finset.mem_filter.mp hcp).1
      exact (Finset.mem_filter.mp hcFresh).1
  have hsign := squareRootLowPrimeOwnedResponseCofactor_moebius_eq_one_or_neg_one
    hcResponse
  have hmu : μ c ≠ 0 := by
    rcases hsign with h | h <;> omega
  constructor
  · unfold squareRootLowPrimeProcessedSignedCofactors
    exact Finset.mem_filter.mpr ⟨hcRange, hpIoc.2, hmu⟩
  · exact hpIoc.1

/-- **Exact deep-carrier identity.**  Under the natural positive packet cutoff,
the deep processed seats are literally the existing owned response-seat
carrier. -/
theorem squareRootLowPrimeProcessedDeepSeatAtoms_eq_ownedResponseSeatCarrier
    {R K j U : ℕ} (hK : 1 ≤ K) :
    squareRootLowPrimeProcessedDeepSeatAtoms R K j U =
      squareRootLowPrimeOwnedResponseSeatCarrier R K j U := by
  ext z
  constructor
  · intro hz
    rcases mem_squareRootLowPrimeProcessedDeepSeatAtoms.mp hz with
      ⟨hzProcessed, hdeep⟩
    rcases mem_squareRootLowPrimeProcessedSeatAtoms.mp hzProcessed with
      ⟨hcProcessed, hs⟩
    have hcOwned :=
      squareRootLowPrimeProcessedDeepCofactor_mem_ownedSigned hK hcProcessed hdeep
    exact mem_squareRootLowPrimeOwnedResponseSeatCarrier_iff.mpr ⟨hcOwned, hs⟩
  · intro hz
    rcases mem_squareRootLowPrimeOwnedResponseSeatCarrier_iff.mp hz with
      ⟨hcOwned, hs⟩
    rcases squareRootLowPrimeOwnedSignedCofactor_mem_processed hcOwned with
      ⟨hcProcessed, hdeep⟩
    exact mem_squareRootLowPrimeProcessedDeepSeatAtoms.mpr
      ⟨mem_squareRootLowPrimeProcessedSeatAtoms.mpr ⟨hcProcessed, hs⟩, hdeep⟩

/-- Membership form convenient for a deep processed state `some (c,s)`. -/
theorem squareRootLowPrimeProcessedSeat_mem_ownedResponseSeatCarrier_of_deep
    {R K j U c s : ℕ} (hK : 1 ≤ K)
    (hx : some (c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hdeep : K < canonicalLargestPrimeFactor c) :
    (c, s) ∈ squareRootLowPrimeOwnedResponseSeatCarrier R K j U := by
  have hz : (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hx
  rw [← squareRootLowPrimeProcessedDeepSeatAtoms_eq_ownedResponseSeatCarrier hK]
  exact mem_squareRootLowPrimeProcessedDeepSeatAtoms.mpr ⟨hz, hdeep⟩

end RHLean.Proof
