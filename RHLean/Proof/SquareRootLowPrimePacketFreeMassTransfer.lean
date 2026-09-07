import Mathlib
import RHLean.Proof.SquareRootLowPrimePartialEndpointCarrier
import RHLean.Proof.SquareRootBornPostTailLowPrimeCollapse
import RHLean.Proof.LowPrimeFreshLayerBridge

/-!
# The partial packet cancels out of the mass-transfer identity

`squareRootLowPrimeRunningImbalance` is by definition `1 - RunningLowPrimeResponse`,
and the running response is the full cofactor response restricted to
`P+(c) <= p`.  Writing `Above` for the complementary part, the exact
BornPostTail response identity gives

`runningImbalance = BornPostTail + Above`,

and `squareRootBornPostTail_eq_matched_sub_partial` gives
`BornPostTail = matched - V`.  Hence

`runningImbalance = matched - V + Above`.

The compressed packet block of the tagged boundary contributes exactly `-V`.
So `V` occurs once on each side of the mass-transfer identity, with the same
sign, and **cancels**.  What remains is packet-free:

`Re(matched) + Re(Above) = 1 + BornExitMass + RootEqualityMass`.

Note also that `Above` does not depend on `j`: it ranges over cofactors with
`P+(c) > p`, and at the canonical cutoff `p = R - sqrt R > K` every such `c`
exceeds `K`, so `squareRootBornPostTailHighResponse` takes its `c > K` branch,
which is `squareRootPostRootPrimePrefixCard R c` alone.  Nothing on the left
reintroduces the packet.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The part of the cofactor response lying strictly above the running cutoff. -/
def squareRootBornPostTailAboveCutoffResponse
    (R K j p : ℕ) : ℂ :=
  (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
      if canonicalLargestPrimeFactor c ≤ p then 0
      else canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)) +
  (∑ c ∈ Finset.Icc 1 (R - 1),
      if canonicalLargestPrimeFactor c ≤ p then 0
      else canonicalMoebiusWeight c *
        (squareRootBornPostTailHighResponse R K j c : ℂ))

/-- Splitting the response at the cutoff is exact. -/
theorem squareRootBornPostTailRunningLowPrimeResponse_add_aboveCutoff
    (R K j p : ℕ) :
    squareRootBornPostTailRunningLowPrimeResponse R K j p +
        squareRootBornPostTailAboveCutoffResponse R K j p =
      (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)) +
        (∑ c ∈ Finset.Icc 1 (R - 1),
          canonicalMoebiusWeight c *
            (squareRootBornPostTailHighResponse R K j c : ℂ)) := by
  classical
  have hborn :
      (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          if canonicalLargestPrimeFactor c ≤ p then
            canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)
          else 0) +
        (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          if canonicalLargestPrimeFactor c ≤ p then 0
          else canonicalMoebiusWeight c *
            (squareRootBornPartnerCount R c : ℂ)) =
      ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _hc
    by_cases hle : canonicalLargestPrimeFactor c ≤ p <;> simp [hle]
  have hhigh :
      (∑ c ∈ Finset.Icc 1 (R - 1),
          if canonicalLargestPrimeFactor c ≤ p then
            canonicalMoebiusWeight c *
              (squareRootBornPostTailHighResponse R K j c : ℂ)
          else 0) +
        (∑ c ∈ Finset.Icc 1 (R - 1),
          if canonicalLargestPrimeFactor c ≤ p then 0
          else canonicalMoebiusWeight c *
            (squareRootBornPostTailHighResponse R K j c : ℂ)) =
      ∑ c ∈ Finset.Icc 1 (R - 1),
        canonicalMoebiusWeight c *
          (squareRootBornPostTailHighResponse R K j c : ℂ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _hc
    by_cases hle : canonicalLargestPrimeFactor c ≤ p <;> simp [hle]
  unfold squareRootBornPostTailRunningLowPrimeResponse
    squareRootBornPostTailAboveCutoffResponse
  rw [← hborn, ← hhigh]
  ring

/-- The running imbalance is the BornPostTail object plus the above-cutoff
response.  Nothing is estimated: this is the exact split of the response sum. -/
theorem squareRootLowPrimeRunningImbalance_eq_bornPostTail_add_aboveCutoff
    (R K j p : ℕ) (hR : 2 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeRunningImbalance R K j p =
      squareRootBornPostTail R K j +
        squareRootBornPostTailAboveCutoffResponse R K j p := by
  have hsplit :=
    squareRootBornPostTailRunningLowPrimeResponse_add_aboveCutoff R K j p
  rw [squareRootBornPostTail_eq_one_sub_weighted_response R K j hR hK hKR hj]
  unfold squareRootLowPrimeRunningImbalance
  linear_combination -hsplit

/-- **The packet enters the running imbalance exactly once, with the same sign
as the compressed boundary block.** -/
theorem squareRootLowPrimeRunningImbalance_eq_matched_sub_packet_add_aboveCutoff
    (R K j p : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeRunningImbalance R K j p =
      squareRootMatchedBornSmoothTransport R -
          ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) +
        squareRootBornPostTailAboveCutoffResponse R K j p := by
  rw [squareRootLowPrimeRunningImbalance_eq_bornPostTail_add_aboveCutoff
      R K j p (by omega) hK hKR hj,
    squareRootBornPostTail_eq_matched_sub_partial R K j hR]

/-- Real form of the same split. -/
theorem squareRootLowPrimeRunningImbalanceReal_eq_matched_sub_packet_add_aboveCutoff
    (R K j p : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootLowPrimeRunningImbalanceReal R K j p =
      (squareRootMatchedBornSmoothTransport R).re -
          ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
        (squareRootBornPostTailAboveCutoffResponse R K j p).re := by
  unfold squareRootLowPrimeRunningImbalanceReal
  rw [squareRootLowPrimeRunningImbalance_eq_matched_sub_packet_add_aboveCutoff
    R K j p hR hK hKR hj]
  simp

/-- **The packet cancels.**  The mass-transfer identity is equivalent to a
packet-free identity on the original matched born/transport channel. -/
theorem squareRootLowPrimeMassTransfer_iff_packetFree
    (R K j p : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    (squareRootLowPrimeRunningImbalanceReal R K j p =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K p +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) ↔
      ((squareRootMatchedBornSmoothTransport R).re +
          (squareRootBornPostTailAboveCutoffResponse R K j p).re =
        1 + squareRootLowPrimeBornExitBoundaryMassReal R K p +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) := by
  rw [squareRootLowPrimeRunningImbalanceReal_eq_matched_sub_packet_add_aboveCutoff
    R K j p hR hK hKR hj]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- **The whole remaining programme, packet-free.**  At the canonical terminal
cutoff, the `4R` bound follows from one identity in which the crossing packet
does not appear. -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_four_root_of_packetFree
    {R K j : ℕ} (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (h : (squareRootMatchedBornSmoothTransport R).re +
        (squareRootBornPostTailAboveCutoffResponse R K j
          (squareRootBornPostTailLowPrimeCutoff R)).re =
      1 + squareRootLowPrimeBornExitBoundaryMassReal R K
            (squareRootBornPostTailLowPrimeCutoff R) +
        squareRootLowPrimeRootEqualityBoundaryMassReal R) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤ 4 * (R : ℝ) := by
  refine abs_squareRootLowPrimeRunningImbalanceReal_le_four_root_of_closedForm
    (by omega) hKR hV0 hVK ?_
  exact (squareRootLowPrimeMassTransfer_iff_packetFree R K j
    (squareRootBornPostTailLowPrimeCutoff R) hR hK hKR hj).mpr h

/-! ## The boundary machinery is not on the critical path

The identity `Re(matched) + Re(Above) = 1 + BornExitMass + RootEqualityMass` is
not weaker than the `4R` conclusion.  The repository already bounds both
right-hand blocks — `squareRootLowPrimeBornNoSuccessorAtoms_card_le_two_root`
gives `|BornExitMass| ≤ 2R` and `abs_squareRootLowPrimeGoRootEqualityDefectMass_le_root`
gives `|RootEqualityMass| ≤ R` — so the identity immediately yields
`|Re(matched) + Re(Above)| ≤ 1 + 3R`.  An identity with that much metric content
cannot be produced by rearranging identities that do not already have it.

Conversely the repository *already* proves that the running imbalance sits
within `R + K` of the matched channel.  Taking real parts, that alone reduces
the whole `4R` bound to a bound on `Re(matched)` — no boundary, no packet, no
classifier, no mass transfer, no four tags. -/

/-- **`4R` from a bound on the matched channel alone.** -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_four_root_of_matched_re_bound
    {R K j : ℕ} (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (hmatched :
      |(squareRootMatchedBornSmoothTransport R).re| ≤ 3 * (R : ℝ) - (K : ℝ)) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤ 4 * (R : ℝ) := by
  have hnorm :=
    norm_squareRootLowPrimeRunningImbalance_sub_matched_le_root_add_depth
      R K j hR hK hKR hj hV0 hVK
  have hre :
      |(squareRootLowPrimeRunningImbalance R K j
            (squareRootBornPostTailLowPrimeCutoff R) -
          squareRootMatchedBornSmoothTransport R).re| ≤ (R : ℝ) + (K : ℝ) :=
    le_trans (Complex.abs_re_le_norm _) hnorm
  have hsplit :
      (squareRootLowPrimeRunningImbalance R K j
            (squareRootBornPostTailLowPrimeCutoff R) -
          squareRootMatchedBornSmoothTransport R).re =
        squareRootLowPrimeRunningImbalanceReal R K j
            (squareRootBornPostTailLowPrimeCutoff R) -
          (squareRootMatchedBornSmoothTransport R).re := by
    unfold squareRootLowPrimeRunningImbalanceReal
    simp
  rw [hsplit] at hre
  have h1 := abs_le.mp hre
  have h2 := abs_le.mp hmatched
  rw [abs_le]
  constructor <;> linarith

end RHLean.Proof
