import Mathlib
import RHLean.Proof.SquareRootLowPrimeDeepProcessedSeatBridge
import RHLean.Proof.SquareRootLowPrimeNoLibertyBoundaryHome
import RHLean.Proof.SquareRootLowPrimeFirstOwnerFalloutWidth

/-!
# Literal BornExit branch of the no-liberty classifier

The deep part of the processed-seat carrier is exactly the existing response
seat carrier.  Therefore a deep processed seat has a canonical literal response
atom `(c,q)`, obtained from the already-proved increasing seat/partner order
rather than from a cardinality equivalence.

If that atom has no successor, it is already one of the final BornExit boundary
cells.  This file proves the three facts required by the eventual classifier:
membership, injectivity, and exact native-weight preservation.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Read a deep processed seat as its unique literal response atom. -/
noncomputable def squareRootLowPrimeProcessedDeepSeatResponseAtom
    (R K j U : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K)
    (z : ℕ × ℕ)
    (hz : some z ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hdeep : K < canonicalLargestPrimeFactor z.1) : ℕ × ℕ :=
  (squareRootLowPrimeOwnedResponseSeatAtomEquiv R K j U hR
    ⟨z, squareRootLowPrimeProcessedSeat_mem_ownedResponseSeatCarrier_of_deep
      hK hz hdeep⟩ : ℕ × ℕ)

/-- The recovered atom lies in the actual response-atom carrier. -/
theorem squareRootLowPrimeProcessedDeepSeatResponseAtom_mem
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K)
    {z : ℕ × ℕ}
    (hz : some z ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hdeep : K < canonicalLargestPrimeFactor z.1) :
    squareRootLowPrimeProcessedDeepSeatResponseAtom
        R K j U hR hK z hz hdeep ∈
      squareRootLowPrimeOwnedResponseAtoms R K U := by
  exact (squareRootLowPrimeOwnedResponseSeatAtomEquiv R K j U hR
    ⟨z, squareRootLowPrimeProcessedSeat_mem_ownedResponseSeatCarrier_of_deep
      hK hz hdeep⟩).property

/-- The response-atom equivalence preserves the processed cofactor literally. -/
@[simp] theorem squareRootLowPrimeProcessedDeepSeatResponseAtom_fst
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K)
    {z : ℕ × ℕ}
    (hz : some z ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hdeep : K < canonicalLargestPrimeFactor z.1) :
    (squareRootLowPrimeProcessedDeepSeatResponseAtom
        R K j U hR hK z hz hdeep).1 = z.1 := by
  simp [squareRootLowPrimeProcessedDeepSeatResponseAtom]

/-- Literal atom recovery is injective on deep processed seats.  No target
cardinality argument is used: this is injectivity of the canonical seat/partner
equivalence itself. -/
theorem squareRootLowPrimeProcessedDeepSeatResponseAtom_injective
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K)
    {z w : ℕ × ℕ}
    (hz : some z ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hw : some w ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hzDeep : K < canonicalLargestPrimeFactor z.1)
    (hwDeep : K < canonicalLargestPrimeFactor w.1)
    (hEq : squareRootLowPrimeProcessedDeepSeatResponseAtom
          R K j U hR hK z hz hzDeep =
        squareRootLowPrimeProcessedDeepSeatResponseAtom
          R K j U hR hK w hw hwDeep) :
    z = w := by
  let ez : ↥(squareRootLowPrimeOwnedResponseSeatCarrier R K j U) :=
    ⟨z, squareRootLowPrimeProcessedSeat_mem_ownedResponseSeatCarrier_of_deep
      hK hz hzDeep⟩
  let ew : ↥(squareRootLowPrimeOwnedResponseSeatCarrier R K j U) :=
    ⟨w, squareRootLowPrimeProcessedSeat_mem_ownedResponseSeatCarrier_of_deep
      hK hw hwDeep⟩
  have hAtoms :
      squareRootLowPrimeOwnedResponseSeatAtomEquiv R K j U hR ez =
        squareRootLowPrimeOwnedResponseSeatAtomEquiv R K j U hR ew := by
    apply Subtype.ext
    simpa [squareRootLowPrimeProcessedDeepSeatResponseAtom, ez, ew] using hEq
  have hSeats : ez = ew :=
    (squareRootLowPrimeOwnedResponseSeatAtomEquiv R K j U hR).injective hAtoms
  exact congrArg Subtype.val hSeats

/-- The BornExit constructor inside the final tagged boundary. -/
def squareRootLowPrimeBornExitBoundaryTag
    (a : ℕ × ℕ) : SquareRootLowPrimeProcessedSeatNoLibertyState :=
  .inr (.inr (.inl a))

/-- A recovered no-successor atom lands literally in the BornExit summand of the
final boundary. -/
theorem squareRootLowPrimeProcessedDeepSeatResponseAtom_bornExit_mem_boundary
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K)
    {z : ℕ × ℕ}
    (hz : some z ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hdeep : K < canonicalLargestPrimeFactor z.1)
    (hborn : squareRootLowPrimeProcessedDeepSeatResponseAtom
        R K j U hR hK z hz hdeep ∈
      squareRootLowPrimeBornNoSuccessorAtoms R K U) :
    squareRootLowPrimeBornExitBoundaryTag
        (squareRootLowPrimeProcessedDeepSeatResponseAtom
          R K j U hR hK z hz hdeep) ∈
      squareRootLowPrimeProcessedSeatNoLibertyBoundary R K j U := by
  simpa [squareRootLowPrimeBornExitBoundaryTag,
    squareRootLowPrimeProcessedSeatNoLibertyBoundary] using hborn

/-- The BornExit tag has exactly the native processed-seat weight. -/
theorem squareRootLowPrimeProcessedDeepSeatResponseAtom_bornExit_weight_eq
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hUR : U < R)
    {z : ℕ × ℕ}
    (hz : some z ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hdeep : K < canonicalLargestPrimeFactor z.1) :
    squareRootLowPrimeNoLibertyBoundaryWeight
        (squareRootLowPrimeBornExitBoundaryTag
          (squareRootLowPrimeProcessedDeepSeatResponseAtom
            R K j U hR hK z hz hdeep)) =
      squareRootLowPrimeProcessedSeatWeightReal (some z) := by
  let a := squareRootLowPrimeProcessedDeepSeatResponseAtom
    R K j U hR hK z hz hdeep
  have ha : a ∈ squareRootLowPrimeOwnedResponseAtoms R K U := by
    simpa [a] using squareRootLowPrimeProcessedDeepSeatResponseAtom_mem
      hR hK hz hdeep
  have haData := squareRootLowPrimeOwnedResponseAtom_data ha
  have hqPrime : a.2.Prime :=
    prime_of_mem_squareRootLowPrimeDeepPartnerSet haData.2.2.2
  have hrough : canonicalLargestPrimeFactor a.1 < a.2 :=
    canonicalLargestPrimeFactor_lt_partner_of_ownedResponseAtom hUR ha
  have hqFresh : ¬ a.2 ∣ a.1 :=
    squareRootLowPrimePrime_fresh_of_lpf_lt haData.1 hqPrime hrough
  have hmu : μ (a.1 * a.2) = -μ a.1 := by
    simpa [Nat.mul_comm] using
      (moebius_prime_mul_eq_neg_of_not_dvd hqPrime hqFresh)
  have hfst : a.1 = z.1 := by
    simp [a]
  change ((μ (a.1 * a.2) : ℤ) : ℝ) = ((-μ z.1 : ℤ) : ℝ)
  rw [hmu, hfst]

/-- Within the BornExit branch, equal tagged endpoints recover equal processed
seats.  Cross-branch injectivity will later be automatic from the `Sum` tags. -/
theorem squareRootLowPrimeProcessedDeepSeat_bornExitTag_injective
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K)
    {z w : ℕ × ℕ}
    (hz : some z ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hw : some w ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hzDeep : K < canonicalLargestPrimeFactor z.1)
    (hwDeep : K < canonicalLargestPrimeFactor w.1)
    (hEq :
      squareRootLowPrimeBornExitBoundaryTag
          (squareRootLowPrimeProcessedDeepSeatResponseAtom
            R K j U hR hK z hz hzDeep) =
        squareRootLowPrimeBornExitBoundaryTag
          (squareRootLowPrimeProcessedDeepSeatResponseAtom
            R K j U hR hK w hw hwDeep)) :
    z = w := by
  have hAtom :
      squareRootLowPrimeProcessedDeepSeatResponseAtom
          R K j U hR hK z hz hzDeep =
        squareRootLowPrimeProcessedDeepSeatResponseAtom
          R K j U hR hK w hw hwDeep := by
    simpa [squareRootLowPrimeBornExitBoundaryTag] using hEq
  exact squareRootLowPrimeProcessedDeepSeatResponseAtom_injective
    hR hK hz hw hzDeep hwDeep hAtom

end RHLean.Proof
