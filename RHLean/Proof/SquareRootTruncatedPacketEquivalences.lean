import Mathlib
import RHLean.Proof.LargePrimeTerminalFlipLayers

/-!
# Truncated square-root packet equivalences

The truncated upper/middle packet introduced in `LargePrimeTerminalFlipLayers`
keeps the upper `k = 1` block and the first reciprocal middle layers inside one
signed object

`U_R(K) = - sum_{1 <= k <= K} N_R(k) M(k)`.

This module identifies that *same* incomplete object with several existing
post-square-root representations.  The key square-endpoint fact is that the
reciprocal depth `K` and the high-prime cutoff

`Q_R(K) = floor((R^2-1)/(K+1))`

are exact inverse coordinates while `K+1 < R`.  Consequently the packet is the
negative prime tail above `Q_R(K)`, and, because that cutoff is still above the
square root, it is also the ordinary Mobius mass of the unresolved sources
whose canonical largest prime has not yet acted.

No estimate, asymptotic statement, PNT input, or RH hypothesis is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- **Exact square-root reciprocal involution.**  Below the root, the truncated
prime cutoff `Q = floor(X_R/(K+1))` has quotient-support top exactly `K`:

`floor(X_R/(Q+1)) = K`.

The point is special to the square endpoint.  The inequality `K+1 < R` implies
`(K+1)^2 <= X_R`, hence `K+1 <= Q`; Euclidean division then traps `X_R`
between `K(Q+1)` and `(K+1)(Q+1)`. -/
theorem squareRootTruncatedPrimeCutoff_inverse
    {R K : ℕ} (hK : K + 1 < R) :
    squareRootEndpoint R /
        (squareRootTruncatedPrimeCutoff R K + 1) = K := by
  have hsqLt : (K + 1) ^ 2 < R ^ 2 :=
    Nat.pow_lt_pow_left hK (by omega)
  have hsqLe :
      (K + 1) * (K + 1) ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    rw [pow_two] at hsqLt
    omega
  have hQge : K + 1 ≤ squareRootTruncatedPrimeCutoff R K := by
    unfold squareRootTruncatedPrimeCutoff
    exact (Nat.le_div_iff_mul_le (by omega : 0 < K + 1)).2 hsqLe
  have hlo :
      K * (squareRootTruncatedPrimeCutoff R K + 1) ≤
        squareRootEndpoint R := by
    calc
      K * (squareRootTruncatedPrimeCutoff R K + 1) =
          K * squareRootTruncatedPrimeCutoff R K + K := by ring
      _ ≤ K * squareRootTruncatedPrimeCutoff R K +
          squareRootTruncatedPrimeCutoff R K :=
        Nat.add_le_add_left (by omega) _
      _ = (K + 1) * squareRootTruncatedPrimeCutoff R K := by ring
      _ ≤ squareRootEndpoint R := by
        unfold squareRootTruncatedPrimeCutoff
        simpa [Nat.mul_comm] using
          Nat.div_mul_le_self (squareRootEndpoint R) (K + 1)
  have hhi :
      squareRootEndpoint R <
        (K + 1) * (squareRootTruncatedPrimeCutoff R K + 1) := by
    have h :=
      Nat.lt_mul_div_succ (squareRootEndpoint R) (by omega : 0 < K + 1)
    simpa [squareRootTruncatedPrimeCutoff, Nat.mul_comm] using h
  exact Nat.div_eq_of_lt_le hlo hhi

/-- The quotient support at the truncated high-prime cutoff is literally the
first `K` reciprocal layers. -/
theorem primeSieveQuotientSupport_truncatedPrimeCutoff_eq_Icc
    {R K : ℕ} (hK : K + 1 < R) :
    primeSieveQuotientSupport (squareRootTruncatedPrimeCutoff R K)
        (squareRootEndpoint R) =
      Finset.Icc 1 K := by
  unfold primeSieveQuotientSupport
  rw [squareRootTruncatedPrimeCutoff_inverse hK]

/-- Inside the first `K` layers, replacing the root cutoff `R` by the common
truncated cutoff `Q_R(K)` does not change any reciprocal interval.  The lower
reciprocal endpoint is already at least `Q_R(K) > R`. -/
theorem primeSieveReciprocalInterval_truncatedPrimeCutoff_eq_root
    {R K d : ℕ} (hR : 1 ≤ R) (hK : K + 1 < R)
    (hd : d ∈ Finset.Icc 1 K) :
    primeSieveReciprocalInterval (squareRootTruncatedPrimeCutoff R K)
        (squareRootEndpoint R) d =
      primeSieveReciprocalInterval R (squareRootEndpoint R) d := by
  rcases Finset.mem_Icc.mp hd with ⟨hd1, hdK⟩
  have hQpost : R < squareRootTruncatedPrimeCutoff R K :=
    squareRoot_root_lt_truncatedPrimeCutoff hR hK
  have hQle :
      squareRootTruncatedPrimeCutoff R K ≤
        squareRootEndpoint R / (d + 1) := by
    unfold squareRootTruncatedPrimeCutoff
    exact Nat.div_le_div_left (by omega) (by omega)
  have hRle : R ≤ squareRootEndpoint R / (d + 1) :=
    hQpost.le.trans hQle
  unfold primeSieveReciprocalInterval primeSieveReciprocalLower
  rw [max_eq_right hQle, max_eq_right hRle]

/-- Cardinal/indicator form of the same interval identification. -/
theorem primeSieveReciprocalPrimeCount_truncatedPrimeCutoff_eq_root
    {R K d : ℕ} (hR : 1 ≤ R) (hK : K + 1 < R)
    (hd : d ∈ Finset.Icc 1 K) :
    primeSieveReciprocalPrimeCount (squareRootTruncatedPrimeCutoff R K)
        (squareRootEndpoint R) d =
      primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d := by
  unfold primeSieveReciprocalPrimeCount
  rw [primeSieveReciprocalInterval_truncatedPrimeCutoff_eq_root hR hK hd]

/-- **Prime-first form of the truncated packet.**  The upper block plus the
first `K` middle layers is exactly the *negative* post-`Q_R(K)` Mertens prime
tail.  This is the same signed object, not a new decomposition. -/
theorem squareRootTruncatedUpperMiddlePacket_eq_neg_mertensPrimeTail
    (R K : ℕ) (hR : 1 ≤ R) (hK : K + 1 < R) :
    squareRootTruncatedUpperMiddlePacket R K =
      -primeSieveMertensPrimeTail (squareRootTruncatedPrimeCutoff R K)
        (squareRootEndpoint R) := by
  rw [primeSieveMertensPrimeTail_eq_reciprocalPrimeTail]
  unfold squareRootTruncatedUpperMiddlePacket primeSieveReciprocalPrimeTail
  rw [primeSieveQuotientSupport_truncatedPrimeCutoff_eq_Icc hK]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro d hd
  rw [primeSieveReciprocalPrimeCount_truncatedPrimeCutoff_eq_root hR hK hd]

/-- The canonical square endpoint really lies strictly below the root square.
This is exposed publicly here because the truncated cutoff needs to compose with
the generic post-square-root source theorems. -/
theorem squareRootEndpoint_sqrt_lt_root
    {R : ℕ} (hR : 2 ≤ R) :
    Nat.sqrt (squareRootEndpoint R) < R := by
  apply (Nat.sqrt_lt').2
  unfold squareRootEndpoint
  have hpos : 0 < R ^ 2 := by positivity
  omega

/-- A strict sub-root reciprocal depth produces a prime cutoff still strictly
above the true square root of the endpoint. -/
theorem squareRootEndpoint_sqrt_lt_truncatedPrimeCutoff
    {R K : ℕ} (hR : 2 ≤ R) (hK : K + 1 < R) :
    Nat.sqrt (squareRootEndpoint R) < squareRootTruncatedPrimeCutoff R K := by
  exact (squareRootEndpoint_sqrt_lt_root hR).trans
    (squareRoot_root_lt_truncatedPrimeCutoff (by omega) hK)

/-- **Unresolved-largest-prime form.**  The truncated packet is exactly the
ordinary Möbius mass of the sources whose canonical largest prime remains above
the corresponding high-prime cutoff. -/
theorem squareRootTruncatedUpperMiddlePacket_eq_highSourceMass
    (R K : ℕ) (hR : 2 ≤ R) (hK : K + 1 < R) :
    squareRootTruncatedUpperMiddlePacket R K =
      ∑ n ∈ primeSieveHighSourceSet (squareRootTruncatedPrimeCutoff R K)
          (squareRootEndpoint R),
        canonicalMoebiusWeight n := by
  have hroot :
      Nat.sqrt (squareRootEndpoint R) < squareRootTruncatedPrimeCutoff R K :=
    squareRootEndpoint_sqrt_lt_truncatedPrimeCutoff hR hK
  rw [squareRootTruncatedUpperMiddlePacket_eq_neg_mertensPrimeTail
    R K (by omega) hK]
  symm
  calc
    (∑ n ∈ primeSieveHighSourceSet (squareRootTruncatedPrimeCutoff R K)
        (squareRootEndpoint R), canonicalMoebiusWeight n) =
      ∑ cq ∈ primeSieveTransportPairSet (squareRootTruncatedPrimeCutoff R K)
          (squareRootEndpoint R),
        canonicalMoebiusWeight (cq.1 * cq.2) := by
      rw [sum_primeSieveHighSourceSet_eq_pairProducts _ _ hroot]
    _ = -primeSieveTransportCofactorMass
        (squareRootTruncatedPrimeCutoff R K) (squareRootEndpoint R) := by
      rw [sum_primeSieveTransportPairSet_eq_neg_cofactorMass _ _ hroot]
    _ = -primeSieveMertensPrimeTail
        (squareRootTruncatedPrimeCutoff R K) (squareRootEndpoint R) := by
      rw [primeSieveTransportCofactorMass_eq_mertensPrimeTail]

/-- The original all-plus flip visualization is the same packet with the fixed
factor `-2`: its gap to terminal Mertens is `-2 U_R(K)`. -/
theorem allPlus_truncatedPrimeCutoff_sub_mertens_eq_neg_two_packet
    (R K : ℕ) (hR : 2 ≤ R) (hK : K + 1 < R) :
    allPlusPrimeCombPrefixMass (squareRootTruncatedPrimeCutoff R K)
        (squareRootEndpoint R) - mertensSummatory (squareRootEndpoint R) =
      -2 * squareRootTruncatedUpperMiddlePacket R K := by
  have hroot :
      Nat.sqrt (squareRootEndpoint R) < squareRootTruncatedPrimeCutoff R K :=
    squareRootEndpoint_sqrt_lt_truncatedPrimeCutoff hR hK
  rw [allPlusPrimeCombPrefixMass_sub_mertens_eq_two_mertensPrimeTail _ _ hroot,
    squareRootTruncatedUpperMiddlePacket_eq_neg_mertensPrimeTail
      R K (by omega) hK]
  ring

/-! ## Ordered packet trajectory -/

/-- On a layer whose completed lower Mertens value is nonpositive, the ordered
packet can only move upward. -/
theorem squareRootTruncatedPacketInt_mono_step_of_mertens_nonpos
    {R K : ℕ} (hM : squareRootMertensInt (K + 1) ≤ 0) :
    squareRootTruncatedUpperMiddlePacketInt R K ≤
      squareRootTruncatedUpperMiddlePacketInt R (K + 1) := by
  rw [squareRootTruncatedUpperMiddlePacketInt_succ]
  have hN : 0 ≤ (squareRootReciprocalPrimeLayerCard R (K + 1) : ℤ) := by
    positivity
  have hprod :
      (squareRootReciprocalPrimeLayerCard R (K + 1) : ℤ) *
          squareRootMertensInt (K + 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hN hM
  linarith

/-- The increase is strict whenever the layer is nonempty and its lower
Mertens value is strictly negative. -/
theorem squareRootTruncatedPacketInt_strictMono_step
    {R K : ℕ}
    (hN : 0 < squareRootReciprocalPrimeLayerCard R (K + 1))
    (hM : squareRootMertensInt (K + 1) < 0) :
    squareRootTruncatedUpperMiddlePacketInt R K <
      squareRootTruncatedUpperMiddlePacketInt R (K + 1) := by
  rw [squareRootTruncatedUpperMiddlePacketInt_succ]
  have hNz : (0 : ℤ) < (squareRootReciprocalPrimeLayerCard R (K + 1) : ℤ) := by
    exact_mod_cast hN
  have hprod :
      (squareRootReciprocalPrimeLayerCard R (K + 1) : ℤ) *
          squareRootMertensInt (K + 1) < 0 :=
    mul_neg_of_pos_of_neg hNz hM
  linarith

end RHLean.Proof
