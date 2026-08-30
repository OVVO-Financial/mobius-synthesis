import Mathlib
import RHLean.Proof.SquareRootBornPostTailLowPrimeCollapse

/-!
# Near-root remainder after the BornPostTail low-prime cutoff

This module continues the exact cofactor-response reduction from
`SquareRootBornPostTailLowPrimeCollapse`.

Write

`P_R = R - floor(sqrt R)`.

After the low-prime coordinates through `P_R` have been separated, the born
complement vanishes exactly.  On the post-root side, every remaining cofactor
with largest prime factor above `P_R` is itself a prime in `(P_R,R)`.  There are
at most `sqrt R` such cofactor seats, and every one sees at most `sqrt R`
post-root prime seats.  Because every surviving cofactor is prime, its Mobius
weight is exactly `-1`; the boundary remainder is therefore a positive natural
cardinality, not a triangle-inequality estimate.

The resulting bound is the elementary finite estimate

`||nearRootRemainder|| <= R`.

No PNT estimate, RH hypothesis, density model, independence assumption, or
Mertens bound occurs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

private theorem two_mul_canonicalLargestPrimeFactor_le_of_lt
    {c : ℕ} (hc : 1 < c)
    (hlt : canonicalLargestPrimeFactor c < c) :
    2 * canonicalLargestPrimeFactor c ≤ c := by
  have hdvd := canonicalLargestPrimeFactor_dvd hc
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    by_contra hk0
    have hk0' : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [hk0', mul_zero] at hk
    omega
  have hkone : k ≠ 1 := by
    intro hk1
    rw [hk1, mul_one] at hk
    omega
  have hk2 : 2 ≤ k := by omega
  calc
    2 * canonicalLargestPrimeFactor c ≤
        k * canonicalLargestPrimeFactor c :=
      Nat.mul_le_mul_right (canonicalLargestPrimeFactor c) hk2
    _ = canonicalLargestPrimeFactor c * k := by rw [Nat.mul_comm]
    _ = c := hk.symm

/-- If the largest prime factor of a cofactor lies beyond the low-prime cutoff,
that cofactor has no born-smooth partner at all.  This is exact vanishing, not
a smallness estimate. -/
theorem squareRootBornPartnerCount_eq_zero_of_lowPrimeCutoff_lt_lpf
    {R c : ℕ} (hR : 16 ≤ R)
    (hcP : squareRootBornPostTailLowPrimeCutoff R <
      canonicalLargestPrimeFactor c) :
    squareRootBornPartnerCount R c = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  rw [Finset.eq_empty_iff_forall_notMem]
  intro q hq
  rw [squareRootBornPartnerSet, Finset.mem_filter] at hq
  obtain ⟨hqRange, hqPrime, hpq, hqc, hcqX⟩ := hq
  have hcgt : 1 < c := lt_of_lt_of_le hqPrime.one_lt hqc
  have hpc : canonicalLargestPrimeFactor c < c := hpq.trans_le hqc
  have h2p : 2 * canonicalLargestPrimeFactor c ≤ c :=
    two_mul_canonicalLargestPrimeFactor_le_of_lt hcgt hpc
  have hPq : squareRootBornPostTailLowPrimeCutoff R < q := hcP.trans hpq
  have hlow :
      2 * (squareRootBornPostTailLowPrimeCutoff R) ^ 2 < c * q := by
    nlinarith
  have hgeom := squareRootBornPostTailLowPrimeCutoff_two_sq_gt_endpoint hR
  omega

/-- Cofactors in the high response whose largest prime coordinate has not yet
been processed at `P_R`. -/
def squareRootBornPostTailHighComplementCofactors (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (R - 1)).filter fun c =>
    squareRootBornPostTailLowPrimeCutoff R < canonicalLargestPrimeFactor c

@[simp] theorem mem_squareRootBornPostTailHighComplementCofactors
    {R c : ℕ} :
    c ∈ squareRootBornPostTailHighComplementCofactors R ↔
      1 ≤ c ∧ c ≤ R - 1 ∧
        squareRootBornPostTailLowPrimeCutoff R <
          canonicalLargestPrimeFactor c := by
  simp only [squareRootBornPostTailHighComplementCofactors,
    Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- High-complement rigidity: above `P_R`, a cofactor below `R` cannot retain a
proper largest-prime-factor quotient.  It is itself prime, and lies in the
near-root interval `(P_R,R)`. -/
theorem squareRootBornPostTailHighComplement_prime
    {R c : ℕ} (hR : 16 ≤ R)
    (hc : c ∈ squareRootBornPostTailHighComplementCofactors R) :
    c.Prime ∧ squareRootBornPostTailLowPrimeCutoff R < c ∧ c < R := by
  rcases mem_squareRootBornPostTailHighComplementCofactors.mp hc with
    ⟨hc1, hcR, hcP⟩
  let P := squareRootBornPostTailLowPrimeCutoff R
  have hRP : R < 2 * P := by
    simpa [P] using squareRootBornPostTailLowPrimeCutoff_two_mul_gt_root hR
  have hP1 : 1 < P := by omega
  have hcgt : 1 < c := by
    by_contra h
    have hcnot : ¬ 1 < c := by omega
    have hlpf : canonicalLargestPrimeFactor c = 1 := by
      simp [canonicalLargestPrimeFactor, hcnot]
    rw [hlpf] at hcP
    omega
  have hpPrime := canonicalLargestPrimeFactor_prime hcgt
  have hpDvd := canonicalLargestPrimeFactor_dvd hcgt
  have hpLeC : canonicalLargestPrimeFactor c ≤ c :=
    Nat.le_of_dvd (by omega) hpDvd
  have hpEq : canonicalLargestPrimeFactor c = c := by
    apply le_antisymm hpLeC
    by_contra hcp
    have hpLtC : canonicalLargestPrimeFactor c < c := by omega
    have h2p : 2 * canonicalLargestPrimeFactor c ≤ c :=
      two_mul_canonicalLargestPrimeFactor_le_of_lt hcgt hpLtC
    have hPp : P < canonicalLargestPrimeFactor c := by simpa [P] using hcP
    have hR2p : R < 2 * canonicalLargestPrimeFactor c := by omega
    omega
  have hcPrime : c.Prime := by simpa [hpEq] using hpPrime
  exact ⟨hcPrime, by simpa [hpEq] using hcP, by omega⟩

/-- The reciprocal cutoff of every unprocessed cofactor is already at most
`R + floor(sqrt R)`. -/
theorem squareRootBornPostTail_reciprocalCutoff_le_root_add_sqrt
    {R d : ℕ} (hR : 16 ≤ R)
    (hdP : squareRootBornPostTailLowPrimeCutoff R < d) :
    squareRootEndpoint R / d ≤ R + Nat.sqrt R := by
  let s := Nat.sqrt R
  let P := squareRootBornPostTailLowPrimeCutoff R
  have hsR : s ≤ R := by nlinarith [Nat.sqrt_le' R]
  have hPs : P + s = R := by
    dsimp [P, squareRootBornPostTailLowPrimeCutoff, s]
    omega
  have hd : P + 1 ≤ d := by simpa [P] using hdP
  have hbase : R ^ 2 ≤ (R + s) * (P + 1) := by
    nlinarith [Nat.sqrt_le' R]
  have hmono : (R + s) * (P + 1) ≤ (R + s) * d :=
    Nat.mul_le_mul_left (R + s) hd
  have hX : squareRootEndpoint R ≤ (R + s) * d := by
    have hXR : squareRootEndpoint R < R ^ 2 := by
      unfold squareRootEndpoint
      exact Nat.sub_lt (by positivity) (by norm_num)
    exact (Nat.le_of_lt hXR).trans (hbase.trans hmono)
  have hdpos : 0 < d := by omega
  apply (Nat.div_le_iff_le_mul hdpos).2
  have hX' : squareRootEndpoint R ≤ d * (R + Nat.sqrt R) := by
    simpa [s, Nat.mul_comm] using hX
  have htail :
      d * (R + Nat.sqrt R) ≤ (R + Nat.sqrt R) * d + d - 1 := by
    rw [Nat.mul_comm d (R + Nat.sqrt R)]
    omega
  exact hX'.trans htail

/-- Every post-root prefix seen by an unprocessed cofactor contains at most
`floor(sqrt R)` primes. -/
theorem squareRootPostRootPrimePrefixCard_le_sqrt_of_lowPrimeCutoff_lt
    {R d : ℕ} (hR : 16 ≤ R)
    (hdP : squareRootBornPostTailLowPrimeCutoff R < d) :
    squareRootPostRootPrimePrefixCard R d ≤ Nat.sqrt R := by
  classical
  let U := max R (squareRootEndpoint R / d)
  have hdiv :=
    squareRootBornPostTail_reciprocalCutoff_le_root_add_sqrt hR hdP
  have hU : U ≤ R + Nat.sqrt R := by
    dsimp [U]
    exact max_le (by omega) hdiv
  unfold squareRootPostRootPrimePrefixCard
  change ((Finset.Ioc R U).filter Nat.Prime).card ≤ Nat.sqrt R
  have hsub :
      (Finset.Ioc R U).filter Nat.Prime ⊆
        Finset.Ioc R (R + Nat.sqrt R) := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqIoc, _⟩
    rcases Finset.mem_Ioc.mp hqIoc with ⟨hRq, hqU⟩
    exact Finset.mem_Ioc.mpr ⟨hRq, hqU.trans hU⟩
  have hcard := Finset.card_le_card hsub
  have hIoc :
      (Finset.Ioc R (R + Nat.sqrt R)).card = Nat.sqrt R := by
    rw [Nat.card_Ioc]
    omega
  simpa [hIoc] using hcard

/-- Natural Abel telescope: one reciprocal layer plus the deeper post-root
prefix is exactly the prefix at the current reciprocal depth. -/
theorem squareRootReciprocalPrimeLayerCard_add_postRootPrimePrefixCard
    (R K : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootReciprocalPrimeLayerCard R K +
        squareRootPostRootPrimePrefixCard R (K + 1) =
      squareRootPostRootPrimePrefixCard R K := by
  have hC :
      ((squareRootReciprocalPrimeLayerCard R K : ℕ) : ℂ) =
        ((squareRootPostRootPrimePrefixCard R K : ℕ) : ℂ) -
          ((squareRootPostRootPrimePrefixCard R (K + 1) : ℕ) : ℂ) := by
    rw [squareRootPostRootPrimePrefixCard_cast,
      squareRootPostRootPrimePrefixCard_cast]
    rw [← squareRootReciprocalPrimeCount_eq_layerCard]
    exact squareRoot_reciprocalPrimeCount_eq_postRootPrefix_diff hR hK hKR
  have hsumC :
      (((squareRootReciprocalPrimeLayerCard R K +
          squareRootPostRootPrimePrefixCard R (K + 1) : ℕ)) : ℂ) =
        ((squareRootPostRootPrimePrefixCard R K : ℕ) : ℂ) := by
    push_cast
    linear_combination hC
  exact_mod_cast hsumC

/-- Pointwise near-root bound for the still-unprocessed high response.  The
partially filled crossing layer is kept together with every deeper layer, and
is bounded only after the exact natural Abel telescope above. -/
theorem squareRootBornPostTailHighResponse_le_sqrt
    {R K j c : ℕ} (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hcP : squareRootBornPostTailLowPrimeCutoff R < c) :
    squareRootBornPostTailHighResponse R K j c ≤ Nat.sqrt R := by
  unfold squareRootBornPostTailHighResponse
  by_cases hcK : c ≤ K
  · rw [if_pos hcK]
    have hPK : squareRootBornPostTailLowPrimeCutoff R < K :=
      hcP.trans_le hcK
    have hprefix :=
      squareRootPostRootPrimePrefixCard_le_sqrt_of_lowPrimeCutoff_lt
        hR hPK
    have htel :=
      squareRootReciprocalPrimeLayerCard_add_postRootPrimePrefixCard
        R K (by omega) hK hKR
    omega
  · rw [if_neg hcK]
    exact squareRootPostRootPrimePrefixCard_le_sqrt_of_lowPrimeCutoff_lt
      hR hcP

/-! ## Cardinality of the near-root boundary -/

/-- The unprocessed high cofactors occupy at most `floor(sqrt R)` integer
seats. -/
theorem squareRootBornPostTailHighComplementCofactors_card_le_sqrt
    {R : ℕ} (hR : 16 ≤ R) :
    (squareRootBornPostTailHighComplementCofactors R).card ≤ Nat.sqrt R := by
  classical
  let P := squareRootBornPostTailLowPrimeCutoff R
  have hsub :
      squareRootBornPostTailHighComplementCofactors R ⊆
        Finset.Ioc P (R - 1) := by
    intro c hc
    have hrigid := squareRootBornPostTailHighComplement_prime hR hc
    have hmem := mem_squareRootBornPostTailHighComplementCofactors.mp hc
    exact Finset.mem_Ioc.mpr ⟨by simpa [P] using hrigid.2.1, hmem.2.1⟩
  have hcard := Finset.card_le_card hsub
  have hsR : Nat.sqrt R ≤ R := by nlinarith [Nat.sqrt_le' R]
  have hPs : P + Nat.sqrt R = R := by
    dsimp [P, squareRootBornPostTailLowPrimeCutoff]
    omega
  have hIoc : (Finset.Ioc P (R - 1)).card ≤ Nat.sqrt R := by
    rw [Nat.card_Ioc]
    omega
  exact hcard.trans hIoc

/-- Natural cardinality carried by the near-root high complement. -/
def squareRootBornPostTailNearRootRemainderCount
    (R K j : ℕ) : ℕ :=
  ∑ c ∈ squareRootBornPostTailHighComplementCofactors R,
    squareRootBornPostTailHighResponse R K j c

/-- The near-root response count is at most `R`; it is a rectangle of at most
`sqrt R` cofactor seats by at most `sqrt R` post-root prime seats. -/
theorem squareRootBornPostTailNearRootRemainderCount_le_root
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootBornPostTailNearRootRemainderCount R K j ≤ R := by
  classical
  unfold squareRootBornPostTailNearRootRemainderCount
  have hsum :
      (∑ c ∈ squareRootBornPostTailHighComplementCofactors R,
        squareRootBornPostTailHighResponse R K j c) ≤
      ∑ _c ∈ squareRootBornPostTailHighComplementCofactors R,
        Nat.sqrt R := by
    apply Finset.sum_le_sum
    intro c hc
    have hcP := (squareRootBornPostTailHighComplement_prime hR hc).2.1
    exact squareRootBornPostTailHighResponse_le_sqrt hR hK hKR hj hcP
  have hcard := squareRootBornPostTailHighComplementCofactors_card_le_sqrt hR
  calc
    (∑ c ∈ squareRootBornPostTailHighComplementCofactors R,
        squareRootBornPostTailHighResponse R K j c) ≤
        ∑ _c ∈ squareRootBornPostTailHighComplementCofactors R,
          Nat.sqrt R := hsum
    _ = (squareRootBornPostTailHighComplementCofactors R).card * Nat.sqrt R := by
      simp
    _ ≤ Nat.sqrt R * Nat.sqrt R :=
      Nat.mul_le_mul_right (Nat.sqrt R) hcard
    _ ≤ R := by simpa [pow_two] using Nat.sqrt_le' R

private theorem canonicalMoebiusWeight_eq_neg_one_of_mem_highComplement
    {R c : ℕ} (hR : 16 ≤ R)
    (hc : c ∈ squareRootBornPostTailHighComplementCofactors R) :
    canonicalMoebiusWeight c = -1 := by
  have hcPrime := (squareRootBornPostTailHighComplement_prime hR hc).1
  unfold canonicalMoebiusWeight
  rw [ArithmeticFunction.moebius_apply_prime hcPrime]
  norm_num

/-- The signed high-complement sum is exactly minus its natural response
cardinality.  No absolute value has been taken. -/
theorem squareRootBornPostTailHighComplementWeighted_eq_neg_count
    (R K j : ℕ) (hR : 16 ≤ R) :
    (∑ c ∈ squareRootBornPostTailHighComplementCofactors R,
      canonicalMoebiusWeight c *
        (squareRootBornPostTailHighResponse R K j c : ℂ)) =
      -((squareRootBornPostTailNearRootRemainderCount R K j : ℕ) : ℂ) := by
  classical
  unfold squareRootBornPostTailNearRootRemainderCount
  calc
    (∑ c ∈ squareRootBornPostTailHighComplementCofactors R,
      canonicalMoebiusWeight c *
        (squareRootBornPostTailHighResponse R K j c : ℂ)) =
      ∑ c ∈ squareRootBornPostTailHighComplementCofactors R,
        -((squareRootBornPostTailHighResponse R K j c : ℕ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [canonicalMoebiusWeight_eq_neg_one_of_mem_highComplement hR hc]
          ring
    _ = -∑ c ∈ squareRootBornPostTailHighComplementCofactors R,
        ((squareRootBornPostTailHighResponse R K j c : ℕ) : ℂ) := by
          rw [Finset.sum_neg_distrib]
    _ = -((∑ c ∈ squareRootBornPostTailHighComplementCofactors R,
        squareRootBornPostTailHighResponse R K j c : ℕ) : ℂ) := by
          push_cast
          rfl

/-- Positive complex form of the near-root remainder. -/
def squareRootBornPostTailNearRootRemainder
    (R K j : ℕ) : ℂ :=
  ((squareRootBornPostTailNearRootRemainderCount R K j : ℕ) : ℂ)

/-- The near-root remainder satisfies the stronger bound `<= R`. -/
theorem squareRootBornPostTailNearRootRemainder_norm_le_root
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    ‖squareRootBornPostTailNearRootRemainder R K j‖ ≤ (R : ℝ) := by
  have hcount := squareRootBornPostTailNearRootRemainderCount_le_root
    R K j hR hK hKR hj
  have hreal :
      (squareRootBornPostTailNearRootRemainderCount R K j : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hcount
  unfold squareRootBornPostTailNearRootRemainder
  simpa using hreal

/-! ## Exact processed-response split -/

/-- The part of the complete BornPostTail response whose largest-prime
coordinate has already been processed through `P_R`. -/
def squareRootBornPostTailLowPrimeProcessedResponse
    (R K j : ℕ) : ℂ :=
  (∑ c ∈ (Finset.Icc 1 (squareRootEndpoint R)).filter (fun c =>
      canonicalLargestPrimeFactor c ≤ squareRootBornPostTailLowPrimeCutoff R),
      canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)) +
  (∑ c ∈ (Finset.Icc 1 (R - 1)).filter (fun c =>
      canonicalLargestPrimeFactor c ≤ squareRootBornPostTailLowPrimeCutoff R),
      canonicalMoebiusWeight c *
        (squareRootBornPostTailHighResponse R K j c : ℂ))

private theorem squareRootBornPostTailBornWeighted_eq_lowPrimeProcessed
    (R : ℕ) (hR : 16 ≤ R) :
    (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
      canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)) =
    ∑ c ∈ (Finset.Icc 1 (squareRootEndpoint R)).filter (fun c =>
      canonicalLargestPrimeFactor c ≤ squareRootBornPostTailLowPrimeCutoff R),
      canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ) := by
  classical
  let S := Finset.Icc 1 (squareRootEndpoint R)
  let pred : ℕ → Prop := fun c =>
    canonicalLargestPrimeFactor c ≤ squareRootBornPostTailLowPrimeCutoff R
  let f : ℕ → ℂ := fun c =>
    canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)
  have hsplit := Finset.sum_filter_add_sum_filter_not S pred f
  have hzero : (∑ c ∈ S.filter (fun c => ¬ pred c), f c) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    have hnot := (Finset.mem_filter.mp hc).2
    have hcP : squareRootBornPostTailLowPrimeCutoff R <
        canonicalLargestPrimeFactor c := by
      exact Nat.lt_of_not_ge hnot
    dsimp [f]
    rw [squareRootBornPartnerCount_eq_zero_of_lowPrimeCutoff_lt_lpf hR hcP]
    simp
  have hres : (∑ c ∈ S, f c) = ∑ c ∈ S.filter pred, f c := by
    rw [← hsplit, hzero, add_zero]
  simpa [S, pred, f] using hres

private theorem squareRootBornPostTailHighWeighted_eq_processed_add_complement
    (R K j : ℕ) :
    (∑ c ∈ Finset.Icc 1 (R - 1),
      canonicalMoebiusWeight c *
        (squareRootBornPostTailHighResponse R K j c : ℂ)) =
    (∑ c ∈ (Finset.Icc 1 (R - 1)).filter (fun c =>
      canonicalLargestPrimeFactor c ≤ squareRootBornPostTailLowPrimeCutoff R),
      canonicalMoebiusWeight c *
        (squareRootBornPostTailHighResponse R K j c : ℂ)) +
    (∑ c ∈ squareRootBornPostTailHighComplementCofactors R,
      canonicalMoebiusWeight c *
        (squareRootBornPostTailHighResponse R K j c : ℂ)) := by
  classical
  let S := Finset.Icc 1 (R - 1)
  let pred : ℕ → Prop := fun c =>
    canonicalLargestPrimeFactor c ≤ squareRootBornPostTailLowPrimeCutoff R
  let f : ℕ → ℂ := fun c =>
    canonicalMoebiusWeight c *
      (squareRootBornPostTailHighResponse R K j c : ℂ)
  have hsplit := Finset.sum_filter_add_sum_filter_not S pred f
  have hcomp : S.filter (fun c => ¬ pred c) =
      squareRootBornPostTailHighComplementCofactors R := by
    ext c
    simp only [S, pred, squareRootBornPostTailHighComplementCofactors,
      Finset.mem_filter, Finset.mem_Icc]
    omega
  have hres :
      (∑ c ∈ S, f c) =
        (∑ c ∈ S.filter pred, f c) +
          ∑ c ∈ squareRootBornPostTailHighComplementCofactors R, f c := by
    rw [← hsplit, hcomp]
  simpa [S, pred, f] using hres

/-- **Low-prime collapse of the BornPostTail gate.**  After every largest-prime
coordinate through `P_R = R - floor(sqrt R)` is retained in one processed
response, the entire born complement vanishes and the only remaining term is a
positive near-root cardinality. -/
theorem squareRootBornPostTail_eq_one_sub_lowPrimeProcessedResponse_add_nearRootRemainder
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootBornPostTail R K j =
      1 - squareRootBornPostTailLowPrimeProcessedResponse R K j +
        squareRootBornPostTailNearRootRemainder R K j := by
  rw [squareRootBornPostTail_eq_one_sub_weighted_response
    R K j (by omega) hK hKR hj]
  rw [squareRootBornPostTailBornWeighted_eq_lowPrimeProcessed R hR]
  rw [squareRootBornPostTailHighWeighted_eq_processed_add_complement]
  rw [squareRootBornPostTailHighComplementWeighted_eq_neg_count R K j hR]
  unfold squareRootBornPostTailLowPrimeProcessedResponse
    squareRootBornPostTailNearRootRemainder
  ring

/-- The remainder in the exact low-prime collapse is `O(R)` with constant one;
in particular it satisfies the originally targeted `2R` bound. -/
theorem squareRootBornPostTailNearRootRemainder_norm_le_two_root
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    ‖squareRootBornPostTailNearRootRemainder R K j‖ ≤ 2 * (R : ℝ) := by
  have h := squareRootBornPostTailNearRootRemainder_norm_le_root
    R K j hR hK hKR hj
  nlinarith

end RHLean.Proof
