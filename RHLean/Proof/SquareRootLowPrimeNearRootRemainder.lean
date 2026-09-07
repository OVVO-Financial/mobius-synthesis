import Mathlib
import RHLean.Proof.SquareRootLowPrimePacketFreeMassTransfer

/-!
# The above-cutoff response is the negative near-root remainder

At the canonical cutoff `U = R - sqrt R` the above-cutoff response collapses
completely.

* **The born complement vanishes.**  If `P = P+(c) > U` then either `c = P`,
  in which case a born partner would need `P < q <= c = P`; or `c >= 2P`, in
  which case `c*q > 2P^2 > 2U^2 > X_R`, and the born partner condition
  `c*q <= X_R` fails.  The two cutoff inequalities
  `..._two_sq_gt_endpoint` supply exactly this.
* **The high complement is a set of primes with uniform Möbius sign.**  If
  `c <= R-1` and `P+(c) > U` then `c >= 2P > 2U > R` is impossible, so `c = P`
  is prime and `mu c = -1`.  Since `c > U >= K`, the high response takes its
  `c > K` branch, which is the post-root prime prefix alone.

Hence at the cutoff

`Above = - NearRootRemainder`,

with `NearRootRemainder` a nonnegative sum of post-root prime prefix counts over
the primes in `(U, R-1]`.  In particular `Above` does not depend on `j`, so the
packet-free target shortens to

`Re(matched) - NearRootRemainder = 1 + BornExitMass + RootEqualityMass`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- A prime is its own canonical largest prime factor. -/
theorem canonicalLargestPrimeFactor_of_prime {p : ℕ} (hp : p.Prime) :
    canonicalLargestPrimeFactor p = p := by
  have h1 : 1 < p := hp.one_lt
  have hdvd := canonicalLargestPrimeFactor_dvd h1
  have hprime := canonicalLargestPrimeFactor_prime h1
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd h hprime.one_lt.ne'
  · exact h

/-- Above the cutoff the born partner set is empty. -/
theorem squareRootBornPartnerCount_eq_zero_of_lpf_gt_cutoff
    {R c : ℕ} (hR : 16 ≤ R)
    (_hcX : c ≤ squareRootEndpoint R)
    (hlpf : squareRootBornPostTailLowPrimeCutoff R <
      canonicalLargestPrimeFactor c) :
    squareRootBornPartnerCount R c = 0 := by
  classical
  have hURoot : R < 2 * squareRootBornPostTailLowPrimeCutoff R :=
    squareRootBornPostTailLowPrimeCutoff_two_mul_gt_root hR
  have hUsq : squareRootEndpoint R <
      2 * (squareRootBornPostTailLowPrimeCutoff R) ^ 2 :=
    squareRootBornPostTailLowPrimeCutoff_two_sq_gt_endpoint hR
  have hU1 : 1 < squareRootBornPostTailLowPrimeCutoff R := by omega
  have hc1 : 1 < c := by
    by_contra hcle
    have hPeq : canonicalLargestPrimeFactor c = 1 := by
      unfold canonicalLargestPrimeFactor
      rw [dif_neg hcle]
    omega
  have hPprime : (canonicalLargestPrimeFactor c).Prime :=
    canonicalLargestPrimeFactor_prime hc1
  have hPdvd : canonicalLargestPrimeFactor c ∣ c :=
    canonicalLargestPrimeFactor_dvd hc1
  unfold squareRootBornPartnerCount
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨_hqIcc, hqPrime, hqRough, hqLe, hqProd⟩
  rcases hPdvd with ⟨m, hm⟩
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, Nat.mul_zero] at hm
    omega
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · have hme : m = 1 := by omega
    rw [hme, Nat.mul_one] at hm
    omega
  · have hPpos : 0 < canonicalLargestPrimeFactor c := hPprime.pos
    have hcP : 2 * canonicalLargestPrimeFactor c ≤ c := by
      have h2m :
          canonicalLargestPrimeFactor c * 2 ≤
            canonicalLargestPrimeFactor c * m :=
        Nat.mul_le_mul (le_refl _) hm2
      calc 2 * canonicalLargestPrimeFactor c
          = canonicalLargestPrimeFactor c * 2 := by ring
        _ ≤ canonicalLargestPrimeFactor c * m := h2m
        _ = c := hm.symm
    have hq1 : canonicalLargestPrimeFactor c + 1 ≤ q := hqRough
    have hUP : (squareRootBornPostTailLowPrimeCutoff R) ^ 2 ≤
        (canonicalLargestPrimeFactor c) ^ 2 :=
      Nat.pow_le_pow_left (le_of_lt hlpf) 2
    have hstep : 2 * (canonicalLargestPrimeFactor c) ^ 2 < c * q := by
      calc 2 * (canonicalLargestPrimeFactor c) ^ 2
          < 2 * canonicalLargestPrimeFactor c *
              (canonicalLargestPrimeFactor c + 1) := by nlinarith [hPpos]
        _ ≤ c * q := Nat.mul_le_mul hcP hq1
    linarith

/-- Above the cutoff a cofactor at most `R-1` is a near-root prime. -/
theorem prime_of_le_pred_root_of_lpf_gt_cutoff
    {R c : ℕ} (hR : 16 ≤ R) (hcR : c ≤ R - 1)
    (hlpf : squareRootBornPostTailLowPrimeCutoff R <
      canonicalLargestPrimeFactor c) :
    c.Prime ∧ squareRootBornPostTailLowPrimeCutoff R < c := by
  classical
  have hURoot : R < 2 * squareRootBornPostTailLowPrimeCutoff R :=
    squareRootBornPostTailLowPrimeCutoff_two_mul_gt_root hR
  have hU1 : 1 < squareRootBornPostTailLowPrimeCutoff R := by omega
  have hc1 : 1 < c := by
    by_contra hcle
    have hPeq : canonicalLargestPrimeFactor c = 1 := by
      unfold canonicalLargestPrimeFactor
      rw [dif_neg hcle]
    omega
  have hPprime : (canonicalLargestPrimeFactor c).Prime :=
    canonicalLargestPrimeFactor_prime hc1
  have hPdvd : canonicalLargestPrimeFactor c ∣ c :=
    canonicalLargestPrimeFactor_dvd hc1
  rcases hPdvd with ⟨m, hm⟩
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, Nat.mul_zero] at hm
    omega
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · have hme : m = 1 := by omega
    rw [hme, Nat.mul_one] at hm
    refine ⟨?_, ?_⟩
    · rw [hm]
      exact hPprime
    · omega
  · exfalso
    have hPpos : 0 < canonicalLargestPrimeFactor c := hPprime.pos
    have hcP : 2 * canonicalLargestPrimeFactor c ≤ c := by
      have h2m :
          canonicalLargestPrimeFactor c * 2 ≤
            canonicalLargestPrimeFactor c * m :=
        Nat.mul_le_mul (le_refl _) hm2
      calc 2 * canonicalLargestPrimeFactor c
          = canonicalLargestPrimeFactor c * 2 := by ring
        _ ≤ canonicalLargestPrimeFactor c * m := h2m
        _ = c := hm.symm
    omega

/-- The cofactors surviving the cutoff complement below the root. -/
def squareRootLowPrimeNearRootPrimeSet (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (R - 1)).filter fun c =>
    ¬ canonicalLargestPrimeFactor c ≤ squareRootBornPostTailLowPrimeCutoff R

/-- The nonnegative near-root remainder. -/
def squareRootLowPrimeNearRootRemainder (R : ℕ) : ℕ :=
  ∑ p ∈ squareRootLowPrimeNearRootPrimeSet R,
    squareRootPostRootPrimePrefixCard R p

/-- Every member of the near-root set is a prime strictly above the cutoff. -/
theorem mem_squareRootLowPrimeNearRootPrimeSet_prime
    {R c : ℕ} (hR : 16 ≤ R)
    (hc : c ∈ squareRootLowPrimeNearRootPrimeSet R) :
    c.Prime ∧ squareRootBornPostTailLowPrimeCutoff R < c := by
  rcases Finset.mem_filter.mp hc with ⟨hcIcc, hlpf⟩
  exact prime_of_le_pred_root_of_lpf_gt_cutoff hR (Finset.mem_Icc.mp hcIcc).2
    (by omega)

/-- **The above-cutoff response is the negative near-root remainder.** -/
theorem squareRootBornPostTailAboveCutoffResponse_at_cutoff
    {R K j : ℕ} (hR : 16 ≤ R)
    (hKU : K ≤ squareRootBornPostTailLowPrimeCutoff R) :
    squareRootBornPostTailAboveCutoffResponse R K j
        (squareRootBornPostTailLowPrimeCutoff R) =
      -((squareRootLowPrimeNearRootRemainder R : ℕ) : ℂ) := by
  classical
  have hborn :
      (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        if canonicalLargestPrimeFactor c ≤
            squareRootBornPostTailLowPrimeCutoff R then 0
        else canonicalMoebiusWeight c *
          (squareRootBornPartnerCount R c : ℂ)) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    by_cases hle : canonicalLargestPrimeFactor c ≤
        squareRootBornPostTailLowPrimeCutoff R
    · rw [if_pos hle]
    · rw [if_neg hle]
      rw [squareRootBornPartnerCount_eq_zero_of_lpf_gt_cutoff hR
        (Finset.mem_Icc.mp hc).2 (by omega)]
      simp
  have hfilter :
      (∑ c ∈ Finset.Icc 1 (R - 1),
        if canonicalLargestPrimeFactor c ≤
            squareRootBornPostTailLowPrimeCutoff R then 0
        else canonicalMoebiusWeight c *
          (squareRootBornPostTailHighResponse R K j c : ℂ)) =
      ∑ c ∈ squareRootLowPrimeNearRootPrimeSet R,
        canonicalMoebiusWeight c *
          (squareRootBornPostTailHighResponse R K j c : ℂ) := by
    unfold squareRootLowPrimeNearRootPrimeSet
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _hc
    by_cases hle : canonicalLargestPrimeFactor c ≤
        squareRootBornPostTailLowPrimeCutoff R <;> simp [hle]
  have hterms :
      (∑ c ∈ squareRootLowPrimeNearRootPrimeSet R,
        canonicalMoebiusWeight c *
          (squareRootBornPostTailHighResponse R K j c : ℂ)) =
      (-1 : ℂ) * ∑ c ∈ squareRootLowPrimeNearRootPrimeSet R,
        (squareRootPostRootPrimePrefixCard R c : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    obtain ⟨hcPrime, hcU⟩ := mem_squareRootLowPrimeNearRootPrimeSet_prime hR hc
    have hcK : ¬ c ≤ K := by omega
    have hmu : canonicalMoebiusWeight c = (-1 : ℂ) := by
      unfold canonicalMoebiusWeight
      rw [ArithmeticFunction.moebius_apply_prime hcPrime]
      norm_num
    have hhigh : squareRootBornPostTailHighResponse R K j c =
        squareRootPostRootPrimePrefixCard R c := by
      unfold squareRootBornPostTailHighResponse
      rw [if_neg hcK]
    rw [hmu, hhigh]
  unfold squareRootBornPostTailAboveCutoffResponse
  rw [hborn, hfilter, hterms]
  unfold squareRootLowPrimeNearRootRemainder
  push_cast
  ring

/-- **Packet-free target, with `Above` eliminated.** -/
theorem squareRootLowPrimeMassTransfer_iff_nearRoot
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hKU : K ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    (squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K
            (squareRootBornPostTailLowPrimeCutoff R) +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) ↔
      ((squareRootMatchedBornSmoothTransport R).re -
          ((squareRootLowPrimeNearRootRemainder R : ℕ) : ℝ) =
        1 + squareRootLowPrimeBornExitBoundaryMassReal R K
              (squareRootBornPostTailLowPrimeCutoff R) +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) := by
  have habove := squareRootBornPostTailAboveCutoffResponse_at_cutoff
    (R := R) (K := K) (j := j) (by omega) hKU
  have hre :
      (squareRootBornPostTailAboveCutoffResponse R K j
          (squareRootBornPostTailLowPrimeCutoff R)).re =
        -((squareRootLowPrimeNearRootRemainder R : ℕ) : ℝ) := by
    rw [habove]
    simp
  rw [squareRootLowPrimeMassTransfer_iff_packetFree R K j
    (squareRootBornPostTailLowPrimeCutoff R) (by omega) hK hKR hj, hre]
  constructor
  · intro h
    linarith
  · intro h
    linarith

end RHLean.Proof
