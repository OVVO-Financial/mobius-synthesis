import Mathlib
import RHLean.Analysis.SquareRootPostCrossingRenewal
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm

/-!
# Low-prime collapse of the born post-crossing tail

This module keeps the born-smooth population and the raw post-crossing high-prime
remainder in one cofactor coordinate before taking any norm.

For a crossing layer `K` with `j` already-admitted prime seats, define the
born post-tail

`BPT = bornSmooth + rawPostCrossingTail`.

The first exact step is a cofactor-response identity

`BPT = 1 - sum_c mu(c) * Resp(c)`.

The high part of `Resp(c)` is written in Abel-prefix coordinates.  For `c <= K`
it contains the unfilled part of layer `K` plus the complete deeper prime prefix;
for `c > K` it is simply the post-root prime prefix at the reciprocal cutoff
`floor(X_R/c)`.

The later section cuts the cofactor coordinate at
`P_R = R - floor(sqrt R)`.  The purpose of this file is to make that reduction
an exact finite theorem rather than a numerical observation.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- The signed object isolated in the finite BornPostTail diagnostic. -/
def squareRootBornPostTail (R K j : ℕ) : ℂ :=
  squareRootBornSmoothMass R + squareRootPostCrossingRawTransportTail R K j

/-- The born post-tail differs from the original matched born/transport channel
only by the already-shallow partial crossing packet. -/
theorem squareRootBornPostTail_eq_matched_sub_partial
    (R K j : ℕ) (hR : 3 ≤ R) :
    squareRootBornPostTail R K j =
      squareRootMatchedBornSmoothTransport R -
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) := by
  unfold squareRootBornPostTail squareRootMatchedBornSmoothTransport
    squareRootPostCrossingRawTransportTail
  rw [squareRootTruncatedUpperMiddlePacket_full_eq_neg_transport R hR]
  ring

/-! ## Honest natural partner counts -/

/-- Born-smooth prime partners of a fixed canonical cofactor. -/
def squareRootBornPartnerSet (R c : ℕ) : Finset ℕ :=
  (Finset.Icc 2 R).filter fun q =>
    q.Prime ∧ canonicalLargestPrimeFactor c < q ∧
      q ≤ c ∧ c * q ≤ squareRootEndpoint R

/-- Honest cardinality of the born partner set. -/
def squareRootBornPartnerCount (R c : ℕ) : ℕ :=
  (squareRootBornPartnerSet R c).card

/-- Honest cardinality of the clipped post-root prime prefix used in the Abel
form of the remaining high-prime response. -/
def squareRootPostRootPrimePrefixCard (R d : ℕ) : ℕ :=
  ((Finset.Ioc R (max R (squareRootEndpoint R / d))).filter Nat.Prime).card

/-- The natural prefix cardinality casts to the existing complex Abel prefix. -/
theorem squareRootPostRootPrimePrefixCard_cast
    (R d : ℕ) :
    ((squareRootPostRootPrimePrefixCard R d : ℕ) : ℂ) =
      squareRootPostRootPrimePrefix R d := by
  classical
  let U := max R (squareRootEndpoint R / d)
  have hRU : R ≤ U := le_max_left _ _
  have hset :
      (Finset.Ioc 0 U).filter Nat.Prime =
        (Finset.Ioc 0 R).filter Nat.Prime ∪
          (Finset.Ioc R U).filter Nat.Prime := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_filter.mp hq with ⟨hqIoc, hqPrime⟩
      rcases Finset.mem_Ioc.mp hqIoc with ⟨hq0, hqU⟩
      by_cases hqR : q ≤ R
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr
            ⟨Finset.mem_Ioc.mpr ⟨hq0, hqR⟩, hqPrime⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr
            ⟨Finset.mem_Ioc.mpr ⟨Nat.lt_of_not_ge hqR, hqU⟩, hqPrime⟩)
    · intro hq
      rcases Finset.mem_union.mp hq with hq | hq
      · rcases Finset.mem_filter.mp hq with ⟨hqIoc, hqPrime⟩
        rcases Finset.mem_Ioc.mp hqIoc with ⟨hq0, hqR⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr ⟨hq0, hqR.trans hRU⟩, hqPrime⟩
      · rcases Finset.mem_filter.mp hq with ⟨hqIoc, hqPrime⟩
        rcases Finset.mem_Ioc.mp hqIoc with ⟨hqR, hqU⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr ⟨by omega, hqU⟩, hqPrime⟩
  have hdisj :
      Disjoint ((Finset.Ioc 0 R).filter Nat.Prime)
        ((Finset.Ioc R U).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    rcases Finset.mem_filter.mp hq1 with ⟨hq1Ioc, _⟩
    rcases Finset.mem_filter.mp hq2 with ⟨hq2Ioc, _⟩
    rcases Finset.mem_Ioc.mp hq1Ioc with ⟨_, hq1R⟩
    rcases Finset.mem_Ioc.mp hq2Ioc with ⟨hq2R, _⟩
    omega
  have hcard := congrArg Finset.card hset
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  have hcardC := congrArg (fun n : ℕ => (n : ℂ)) hcard
  push_cast at hcardC
  unfold squareRootPostRootPrimePrefixCard squareRootPostRootPrimePrefix
  change
    ((((Finset.Ioc R U).filter Nat.Prime).card : ℕ) : ℂ) =
      primeSievePrefixPrimeCount U - primeSievePrefixPrimeCount R
  rw [primeSievePrefixPrimeCount_eq_card,
    primeSievePrefixPrimeCount_eq_card]
  rw [hcardC]
  ring

/-- Natural high-prime response of one cofactor after the crossing packet has
stopped inside layer `K`.  The hypothesis `j <= N_R(K)` is imposed only when
this value is related to the complex packet, so the definition itself remains
total. -/
def squareRootBornPostTailHighResponse
    (R K j c : ℕ) : ℕ :=
  if c ≤ K then
    (squareRootReciprocalPrimeLayerCard R K - j) +
      squareRootPostRootPrimePrefixCard R (K + 1)
  else
    squareRootPostRootPrimePrefixCard R c

/-- Complete honest cofactor response: born partners plus still-unprocessed
post-root partners. -/
def squareRootBornPostTailResponse
    (R K j c : ℕ) : ℕ :=
  squareRootBornPartnerCount R c +
    squareRootBornPostTailHighResponse R K j c

/-- Complex cast of the high response in the exact Abel coordinates. -/
theorem squareRootBornPostTailHighResponse_cast
    {R K j c : ℕ}
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    ((squareRootBornPostTailHighResponse R K j c : ℕ) : ℂ) =
      if c ≤ K then
        ((squareRootReciprocalPrimeLayerCard R K : ℕ) : ℂ) - (j : ℂ) +
          squareRootPostRootPrimePrefix R (K + 1)
      else
        squareRootPostRootPrimePrefix R c := by
  unfold squareRootBornPostTailHighResponse
  by_cases hcK : c ≤ K
  · rw [if_pos hcK, if_pos hcK]
    rw [Nat.cast_add, Nat.cast_sub hj,
      squareRootPostRootPrimePrefixCard_cast]
  · rw [if_neg hcK, if_neg hcK,
      squareRootPostRootPrimePrefixCard_cast]

/-! ## Born side in cofactor-response form -/

/-- The canonical born pair mass is the negative cofactor-weighted partner
cardinality. -/
theorem squareRootBornSmoothPairSourceMass_eq_neg_weighted_partnerCount
    (R : ℕ) :
    squareRootBornSmoothPairSourceMass R =
      -∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ) := by
  classical
  unfold squareRootBornSmoothPairSourceMass squareRootBornSmoothPairSet
  rw [Finset.sum_filter]
  calc
    (∑ qc ∈ (Finset.Icc 2 R).product
          (Finset.Icc 1 (squareRootEndpoint R)),
        if qc.1.Prime ∧ canonicalLargestPrimeFactor qc.2 < qc.1 ∧
            qc.1 ≤ qc.2 ∧ qc.2 * qc.1 ≤ squareRootEndpoint R then
          canonicalMoebiusWeight (qc.2 * qc.1)
        else 0) =
      ∑ q ∈ Finset.Icc 2 R,
        ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          if q.Prime ∧ canonicalLargestPrimeFactor c < q ∧
              q ≤ c ∧ c * q ≤ squareRootEndpoint R then
            canonicalMoebiusWeight (c * q)
          else 0 := by
      simpa only using
        (Finset.sum_product
          (s := Finset.Icc 2 R)
          (t := Finset.Icc 1 (squareRootEndpoint R))
          (f := fun qc : ℕ × ℕ =>
            if qc.1.Prime ∧ canonicalLargestPrimeFactor qc.2 < qc.1 ∧
                qc.1 ≤ qc.2 ∧ qc.2 * qc.1 ≤ squareRootEndpoint R then
              canonicalMoebiusWeight (qc.2 * qc.1)
            else 0))
    _ = ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        ∑ q ∈ Finset.Icc 2 R,
          if q.Prime ∧ canonicalLargestPrimeFactor c < q ∧
              q ≤ c ∧ c * q ≤ squareRootEndpoint R then
            canonicalMoebiusWeight (c * q)
          else 0 := by rw [Finset.sum_comm]
    _ = ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        -(canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hcpos : 0 < c := by
        have := (Finset.mem_Icc.mp hc).1
        omega
      unfold squareRootBornPartnerCount squareRootBornPartnerSet
      rw [← Finset.sum_filter]
      calc
        (∑ q ∈ (Finset.Icc 2 R).filter (fun q =>
            q.Prime ∧ canonicalLargestPrimeFactor c < q ∧
              q ≤ c ∧ c * q ≤ squareRootEndpoint R),
            canonicalMoebiusWeight (c * q)) =
          ∑ q ∈ (Finset.Icc 2 R).filter (fun q =>
            q.Prime ∧ canonicalLargestPrimeFactor c < q ∧
              q ≤ c ∧ c * q ≤ squareRootEndpoint R),
            -canonicalMoebiusWeight c := by
          apply Finset.sum_congr rfl
          intro q hq
          have hdata := (Finset.mem_filter.mp hq).2
          exact canonicalMoebiusWeight_mul_prime_eq_neg_of_rough
            hcpos hdata.1 hdata.2.1
        _ = -(canonicalMoebiusWeight c *
            (((Finset.Icc 2 R).filter (fun q =>
              q.Prime ∧ canonicalLargestPrimeFactor c < q ∧
                q ≤ c ∧ c * q ≤ squareRootEndpoint R)).card : ℂ)) := by
          simp [mul_comm]
    _ = -∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ) := by
      rw [Finset.sum_neg_distrib]

/-- Born-smooth mass, including the exceptional unit source, in the exact
cofactor-response form used by the BornPostTail gate. -/
theorem squareRootBornSmoothMass_eq_one_sub_weighted_partnerCount
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootBornSmoothMass R =
      1 - ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ) := by
  rw [squareRootBornSmoothMass_eq_one_add_sourceMass R hR,
    squareRootBornSmoothSourceMass_eq_pairSourceMass R,
    squareRootBornSmoothPairSourceMass_eq_neg_weighted_partnerCount]
  ring

/-! ## Raw post-crossing side in cofactor-response form -/

/-- The raw post-crossing tail is the negative Möbius-weighted high response.
This is exactly the existing Abel cap, now Fubini-read by its cofactor index. -/
theorem squareRootPostCrossingRawTransportTail_eq_neg_weighted_highResponse
    (R K j : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootPostCrossingRawTransportTail R K j =
      -∑ c ∈ Finset.Icc 1 (R - 1),
        canonicalMoebiusWeight c *
          (squareRootBornPostTailHighResponse R K j c : ℂ) := by
  have hN :
      ((squareRootReciprocalPrimeLayerCard R K : ℕ) : ℂ) =
        squareRootPostRootPrimePrefix R K -
          squareRootPostRootPrimePrefix R (K + 1) := by
    rw [← squareRootReciprocalPrimeCount_eq_layerCard]
    exact squareRoot_reciprocalPrimeCount_eq_postRootPrefix_diff
      hR hK hKR
  have hsplit :
      Finset.Icc 1 (R - 1) =
        Finset.Icc 1 K ∪ Finset.Icc (K + 1) (R - 1) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj :
      Disjoint (Finset.Icc 1 K) (Finset.Icc (K + 1) (R - 1)) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    simp only [Finset.mem_Icc] at hc1 hc2
    omega
  have hlow :
      (∑ c ∈ Finset.Icc 1 K,
        canonicalMoebiusWeight c *
          (squareRootBornPostTailHighResponse R K j c : ℂ)) =
        mertensSummatory K *
          (((squareRootReciprocalPrimeLayerCard R K : ℕ) : ℂ) - (j : ℂ) +
            squareRootPostRootPrimePrefix R (K + 1)) := by
    have hsum :
        (∑ c ∈ Finset.Icc 1 K, canonicalMoebiusWeight c) =
          mertensSummatory K := by
      rw [← cofactorMobiusPrefixMass_eq_mertensSummatory K]
      rfl
    calc
      (∑ c ∈ Finset.Icc 1 K,
        canonicalMoebiusWeight c *
          (squareRootBornPostTailHighResponse R K j c : ℂ)) =
        ∑ c ∈ Finset.Icc 1 K,
          canonicalMoebiusWeight c *
            (((squareRootReciprocalPrimeLayerCard R K : ℕ) : ℂ) - (j : ℂ) +
              squareRootPostRootPrimePrefix R (K + 1)) := by
          apply Finset.sum_congr rfl
          intro c hc
          have hcK : c ≤ K := (Finset.mem_Icc.mp hc).2
          rw [squareRootBornPostTailHighResponse_cast hj, if_pos hcK]
      _ = mertensSummatory K *
          (((squareRootReciprocalPrimeLayerCard R K : ℕ) : ℂ) - (j : ℂ) +
            squareRootPostRootPrimePrefix R (K + 1)) := by
          rw [← Finset.sum_mul, hsum]
  have hhigh :
      (∑ c ∈ Finset.Icc (K + 1) (R - 1),
        canonicalMoebiusWeight c *
          (squareRootBornPostTailHighResponse R K j c : ℂ)) =
        ∑ c ∈ Finset.Icc (K + 1) (R - 1),
          canonicalMoebiusWeight c * squareRootPostRootPrimePrefix R c := by
    apply Finset.sum_congr rfl
    intro c hc
    have hcK : ¬ c ≤ K := by
      have := (Finset.mem_Icc.mp hc).1
      omega
    rw [squareRootBornPostTailHighResponse_cast hj, if_neg hcK]
  rw [squareRootPostCrossingRawTransportTail_eq_remainingAbelCap
    R K j hR hK hKR]
  unfold squareRootPostCrossingRemainingAbelCap
  rw [hsplit, Finset.sum_union hdisj, hlow, hhigh, hN]
  simp [canonicalMoebiusWeight]
  ring

/-- Exact cofactor-response identity for the BornPostTail object.  The unit
source is explicit; no mean-zero assumption or norm split occurs. -/
theorem squareRootBornPostTail_eq_one_sub_weighted_response
    (R K j : ℕ) (hR : 2 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootBornPostTail R K j =
      1 -
        (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)) -
        (∑ c ∈ Finset.Icc 1 (R - 1),
          canonicalMoebiusWeight c *
            (squareRootBornPostTailHighResponse R K j c : ℂ)) := by
  unfold squareRootBornPostTail
  rw [squareRootBornSmoothMass_eq_one_sub_weighted_partnerCount R hR,
    squareRootPostCrossingRawTransportTail_eq_neg_weighted_highResponse
      R K j (by omega) hK hKR hj]
  ring

/-! ## The near-root low-prime cutoff -/

/-- Process all prime coordinates up to `R - floor(sqrt R)`. -/
def squareRootBornPostTailLowPrimeCutoff (R : ℕ) : ℕ :=
  R - Nat.sqrt R

private theorem sqrt_ge_four_of_sixteen_le
    {R : ℕ} (hR : 16 ≤ R) : 4 ≤ Nat.sqrt R := by
  by_contra h
  have hs : Nat.sqrt R ≤ 3 := by omega
  have hlt := Nat.lt_succ_sqrt' R
  have hsq : (Nat.sqrt R + 1) ^ 2 ≤ 16 := by nlinarith
  nlinarith

private theorem four_mul_sqrt_le
    {R : ℕ} (hR : 16 ≤ R) : 4 * Nat.sqrt R ≤ R := by
  have hs4 := sqrt_ge_four_of_sixteen_le hR
  have hsquare : (Nat.sqrt R) ^ 2 ≤ R := Nat.sqrt_le' R
  nlinarith

/-- The low-prime cutoff still lies well above half the root. -/
theorem squareRootBornPostTailLowPrimeCutoff_two_mul_gt_root
    {R : ℕ} (hR : 16 ≤ R) :
    R < 2 * squareRootBornPostTailLowPrimeCutoff R := by
  unfold squareRootBornPostTailLowPrimeCutoff
  have h4 := four_mul_sqrt_le hR
  have hsR : Nat.sqrt R ≤ R := by nlinarith [Nat.sqrt_le' R]
  omega

/-- Two low-prime-cutoff factors already exceed the complete square endpoint. -/
theorem squareRootBornPostTailLowPrimeCutoff_two_sq_gt_endpoint
    {R : ℕ} (hR : 16 ≤ R) :
    squareRootEndpoint R <
      2 * (squareRootBornPostTailLowPrimeCutoff R) ^ 2 := by
  let s := Nat.sqrt R
  let P := squareRootBornPostTailLowPrimeCutoff R
  have hs4 : 4 ≤ s := by simpa [s] using sqrt_ge_four_of_sixteen_le hR
  have h4s : 4 * s ≤ R := by simpa [s] using four_mul_sqrt_le hR
  have hsR : s ≤ R := by nlinarith [Nat.sqrt_le' R]
  have hPs : P + s = R := by
    dsimp [P, squareRootBornPostTailLowPrimeCutoff, s]
    omega
  have hthree : 3 * R ≤ 4 * P := by omega
  have hsq := Nat.mul_le_mul hthree hthree
  have hsq' : 9 * R ^ 2 ≤ 16 * P ^ 2 := by
    nlinarith [hsq]
  have hR2pos : 0 < R ^ 2 := by positivity
  have h8lt : 8 * R ^ 2 < 9 * R ^ 2 := by nlinarith
  have h16 : 8 * R ^ 2 < 16 * P ^ 2 := h8lt.trans_le hsq'
  have htarget : R ^ 2 < 2 * P ^ 2 := by omega
  have hXlt : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    exact Nat.sub_lt (by positivity) (by norm_num)
  exact hXlt.trans htarget

/-- A low-prime-cutoff factor times a post-root factor already exceeds the
square endpoint. -/
theorem squareRootBornPostTailLowPrimeCutoff_two_mul_root_gt_endpoint
    {R : ℕ} (hR : 16 ≤ R) :
    squareRootEndpoint R <
      2 * squareRootBornPostTailLowPrimeCutoff R * R := by
  let P := squareRootBornPostTailLowPrimeCutoff R
  have hroot : R < 2 * P := by
    simpa [P] using squareRootBornPostTailLowPrimeCutoff_two_mul_gt_root hR
  have hRpos : 0 < R := by omega
  have hmul := Nat.mul_lt_mul_of_pos_right hroot hRpos
  have htarget : R ^ 2 < 2 * P * R := by
    simpa [pow_two, Nat.mul_assoc] using hmul
  have hXlt : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    exact Nat.sub_lt (by positivity) (by norm_num)
  exact hXlt.trans htarget

end RHLean.Proof
