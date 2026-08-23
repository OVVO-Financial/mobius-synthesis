import Mathlib
import RHLean.Analysis.SquareRootPostCrossingTail
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm
import RHLean.Proof.ReplacementFibreCofactorWindows

/-!
# Renewal normal forms for the post-crossing tail

The crossing residual is not merely a bounded scalar.  Before any norm is
taken it is a shallow linear combination of the same lower-scale Mertens
states that occur in the exact recursive replacement row.  This file keeps
that signed structure intact.

For `1 ≤ K < R` it proves three exact descriptions of the coupled tail:

* a direct remaining-layer cap, with the unfilled part of layer `K` and every
  deeper reciprocal layer kept together with the smooth population;
* an Abel form, where the remaining transport is one signed Möbius/prime-prefix
  tail; and
* a lower-triangular renewal row obtained by subtracting the shallow crossing
  coefficients from the complete recursive replacement row before any norm.

The replacement-fibre dictionary then identifies the packet layer with the
negative cofactor-one prime face.  Consequently every fully admitted shallow
layer cancels its prime diagonal exactly, while the crossing layer retains
precisely `j - N_R(K)`, the negative number of unfilled seats.  The remaining
composite-root and smooth orientations recombine as one signed Type-II
cofactor-prime window mass (with the root cofactor range starting at two), and
that mass stays coupled to the strict descendants in one signed double Gram.
Both orientations are contracted to the native reciprocal-prime coordinates
at endpoint `X_R / c`, recombined into one canonical rough-prime count with
lower cutoff `P+(c)`, then centered exactly into deterministic Li density and
prime discrepancy channels without applying a norm.

Including `c = 1` gives the same canonical formula for every complementary
Möbius fibre.  Thus the universal post-crossing row is a full canonical
rough-prime renewal on strict descendants, with the packet deleting only the
admitted `c = 1` diagonal.  Its complete signed Gram is again exactly the
coupled-tail norm square.

The last form is the genuinely nonlocal bilinear proof object for a subsequent
energy argument.  No diagonal estimate, triangle inequality, RH hypothesis,
or critical tail bound is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators ComplexConjugate

namespace RHLean.Proof

open RHLean.Analysis

/-- Cast form of the partially filled crossing layer. -/
theorem squareRootCrossingLayerPartialPacketInt_cast_complex
    (R K j : ℕ) :
    ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) =
      squareRootTruncatedUpperMiddlePacket R (K - 1) -
        (j : ℂ) * mertensSummatory K := by
  unfold squareRootCrossingLayerPartialPacketInt
  push_cast
  rw [squareRootTruncatedUpperMiddlePacketInt_cast_complex,
    squareRootMertensInt_cast_complex]

private theorem sum_Icc_one_pred_split_at
    (f : ℕ → ℂ) {R K : ℕ} (hK : 1 ≤ K) (hKR : K < R) :
    (∑ d ∈ Finset.Icc 1 (R - 1), f d) =
      (∑ d ∈ Finset.Icc 1 (K - 1), f d) + f K +
        ∑ d ∈ Finset.Icc (K + 1) (R - 1), f d := by
  have hset₁ :
      Finset.Icc 1 (R - 1) =
        Finset.Icc 1 (K - 1) ∪ Finset.Icc K (R - 1) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj₁ :
      Disjoint (Finset.Icc 1 (K - 1)) (Finset.Icc K (R - 1)) := by
    rw [Finset.disjoint_left]
    intro d hd₁ hd₂
    simp only [Finset.mem_Icc] at hd₁ hd₂
    omega
  have hset₂ :
      Finset.Icc K (R - 1) =
        ({K} : Finset ℕ) ∪ Finset.Icc (K + 1) (R - 1) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj₂ :
      Disjoint ({K} : Finset ℕ) (Finset.Icc (K + 1) (R - 1)) := by
    rw [Finset.disjoint_left]
    intro d hd₁ hd₂
    rw [Finset.mem_singleton] at hd₁
    subst d
    simp at hd₂
  rw [hset₁, Finset.sum_union hdisj₁, hset₂,
    Finset.sum_union hdisj₂]
  simp
  ring

/-- The still-unfilled transport layers after `j` seats have been admitted in
layer `K`.  This is a signed cap, not a sum of separately normed pieces. -/
def squareRootPostCrossingRemainingLayerCap (R K j : ℕ) : ℂ :=
  -(primeSieveReciprocalPrimeCount R (squareRootEndpoint R) K - (j : ℂ)) *
      mertensSummatory K -
    ∑ d ∈ Finset.Icc (K + 1) (R - 1),
      primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
        mertensSummatory d

/-- Exact remaining-layer form of the raw transport tail. -/
theorem squareRootPostCrossingRawTransportTail_eq_remainingLayerCap
    (R K j : ℕ) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingRawTransportTail R K j =
      squareRootPostCrossingRemainingLayerCap R K j := by
  unfold squareRootPostCrossingRawTransportTail
    squareRootPostCrossingRemainingLayerCap
  rw [show ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) =
      squareRootTruncatedUpperMiddlePacket R (K - 1) -
        (j : ℂ) * mertensSummatory K by
      exact squareRootCrossingLayerPartialPacketInt_cast_complex R K j]
  unfold squareRootTruncatedUpperMiddlePacket
  rw [sum_Icc_one_pred_split_at
    (fun d =>
      primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
        mertensSummatory d) hK hKR]
  ring

/-- Direct coupled cap: the smooth population remains signed with every
unfilled reciprocal layer before any norm is taken. -/
def squareRootPostCrossingCoupledLayerCap (R K j : ℕ) : ℂ :=
  squareRootSmoothMass (R - 1) +
    squareRootPostCrossingRemainingLayerCap R K j

/-- The terminal coupled tail is exactly the direct remaining-layer cap. -/
theorem squareRootPostCrossingCoupledTail_eq_layerCap
    (R K j : ℕ) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingCoupledTail R K j =
      squareRootPostCrossingCoupledLayerCap R K j := by
  unfold squareRootPostCrossingCoupledTail
    squareRootPostCrossingCoupledLayerCap
  rw [squareRootPostCrossingRawTransportTail_eq_remainingLayerCap
    R K j hK hKR]

/-- The clipped post-root prime prefix vanishes at reciprocal depth `R`. -/
theorem squareRootPostRootPrimePrefix_self
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootPostRootPrimePrefix R R = 0 := by
  have hdiv : squareRootEndpoint R / R = R - 1 := by
    have hpred : R - 1 + 1 = R := Nat.sub_add_cancel hR
    have hsq : R * R = (R - 1) * R + R := by
      calc
        R * R = (R - 1 + 1) * R := by rw [hpred]
        _ = (R - 1) * R + R := by ring
    apply Nat.div_eq_of_lt_le
    · unfold squareRootEndpoint
      rw [pow_two]
      rw [hsq]
      omega
    · unfold squareRootEndpoint
      rw [hpred, pow_two, hsq]
      omega
  unfold squareRootPostRootPrimePrefix
  rw [hdiv, max_eq_left (by omega : R - 1 ≤ R)]
  ring

/-- Abel-coordinate version of the remaining transport.  The boundary term
`(j-P_R(K))M(K)` and the deeper Möbius/prime-prefix tail remain one signed
object. -/
def squareRootPostCrossingRemainingAbelCap (R K j : ℕ) : ℂ :=
  ((j : ℂ) - squareRootPostRootPrimePrefix R K) * mertensSummatory K -
    ∑ d ∈ Finset.Icc (K + 1) (R - 1),
      (((μ d : ℤ) : ℂ)) * squareRootPostRootPrimePrefix R d

/-- Exact Abel form of the raw post-crossing tail. -/
theorem squareRootPostCrossingRawTransportTail_eq_remainingAbelCap
    (R K j : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingRawTransportTail R K j =
      squareRootPostCrossingRemainingAbelCap R K j := by
  unfold squareRootPostCrossingRawTransportTail
    squareRootPostCrossingRemainingAbelCap
  rw [show ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) =
      squareRootTruncatedUpperMiddlePacket R (K - 1) -
        (j : ℂ) * mertensSummatory K by
      exact squareRootCrossingLayerPartialPacketInt_cast_complex R K j]
  rw [squareRootTruncatedUpperMiddlePacket_eq_abel R (R - 1) hR (by omega),
    squareRootTruncatedUpperMiddlePacket_eq_abel R (K - 1) hR (by omega)]
  rw [Nat.sub_add_cancel hR, Nat.sub_add_cancel hK,
    squareRootPostRootPrimePrefix_self R hR]
  simp only [mul_zero, add_zero]
  rw [sum_Icc_one_pred_split_at
    (fun d => (((μ d : ℤ) : ℂ)) * squareRootPostRootPrimePrefix R d)
    hK hKR]
  have hsucc := mertensSummatory_succ (K - 1)
  rw [Nat.sub_add_cancel hK] at hsucc
  rw [hsucc]
  ring

/-- Coupled Abel cap, retaining the smooth term and the remaining signed Abel
tail as one object. -/
def squareRootPostCrossingCoupledAbelCap (R K j : ℕ) : ℂ :=
  squareRootSmoothMass (R - 1) +
    squareRootPostCrossingRemainingAbelCap R K j

/-- The coupled tail is exactly the smooth-coupled Abel cap. -/
theorem squareRootPostCrossingCoupledTail_eq_abelCap
    (R K j : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingCoupledTail R K j =
      squareRootPostCrossingCoupledAbelCap R K j := by
  unfold squareRootPostCrossingCoupledTail
    squareRootPostCrossingCoupledAbelCap
  rw [squareRootPostCrossingRawTransportTail_eq_remainingAbelCap
    R K j hR hK hKR]

/-- At a square endpoint the complete Mertens value is `1` minus the unified
prime-indexed rough reciprocal transform. -/
theorem mertensSquareRootEndpoint_eq_one_sub_unifiedReciprocalTransform
    (R : ℕ) (hR : 2 ≤ R) :
    mertensSummatory (squareRootEndpoint R) =
      1 - squareRootUnifiedReciprocalTransform R := by
  have hsquare := squarePrefixMertens_eq_neg_positivePrimeTransform_add_matched
    R (by omega : 1 ≤ R)
  rw [squareRootMatchedBornSmoothTransport_eq_unifiedReciprocalForm R hR]
    at hsquare
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel (by omega : 1 ≤ R)
  simpa [squarePrefixMertens, squarePrefixEndpoint, hpred] using hsquare

/-- Unified reciprocal form of the post-crossing tail.  The shallow residual
is subtracted only after the complete prime-indexed reciprocal transform has
been assembled. -/
theorem squareRootPostCrossingCoupledTail_eq_unifiedReciprocal_sub_partial
    (R K j : ℕ) (hR : 3 ≤ R) :
    squareRootPostCrossingCoupledTail R K j =
      1 - squareRootUnifiedReciprocalTransform R -
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) := by
  rw [postCrossingCoupledTail_eq_mertens_sub_partial R K j hR,
    mertensSquareRootEndpoint_eq_one_sub_unifiedReciprocalTransform R
      (by omega)]

/-- Positive coefficient row removed from the complete replacement recurrence
by a partial shallow packet. -/
def squareRootCrossingRemovalCoefficient
    (R K j y : ℕ) : ℂ :=
  (if y ∈ Finset.Icc 1 (K - 1) then
      primeSieveReciprocalPrimeCount R (squareRootEndpoint R) y
    else 0) +
  if y = K then (j : ℂ) else 0

/-- The recursive replacement coefficient after subtracting the partial
crossing packet coefficientwise, before any norm or diagonalization. -/
def squareRootPostCrossingReplacementCoefficient
    (R K j y : ℕ) : ℂ :=
  squareRootReplacementCoefficient R y +
    squareRootCrossingRemovalCoefficient R K j y

/-! ## Prime-face cancellation inside the renewal row -/

/-- Away from the clipped terminal layer, the literal prime count on a
replacement fibre is the packet's reciprocal-layer cardinality. -/
theorem replacementFibrePrimeCount_eq_reciprocalPrimeLayerCard
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z + 1 < R) :
    replacementFibrePrimeCount R z =
      (squareRootReciprocalPrimeLayerCard R z : ℂ) := by
  have hroot : R ≤ squareRootEndpoint R / (z + 1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < z + 1)).2
    have hzle : z + 1 ≤ R - 1 := by omega
    have hmul : R * (z + 1) ≤ R * (R - 1) :=
      Nat.mul_le_mul_left R hzle
    have htail : R * (R - 1) ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      rw [pow_two, Nat.mul_sub_left_distrib]
      omega
    exact hmul.trans htail
  have hset :
      Finset.Icc
          (squareRootEndpoint R / (z + 1) + 1)
          (squareRootEndpoint R / z) =
        Finset.Ioc
          (squareRootEndpoint R / (z + 1))
          (squareRootEndpoint R / z) := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  unfold replacementFibrePrimeCount squareRootReciprocalPrimeLayerCard
    squareRootReplacementFibreLower squareRootReplacementFibreUpper
    primeSieveReciprocalInterval primeSieveReciprocalLower
    primeSieveReciprocalUpper
  rw [max_eq_right hroot, hset, ← Finset.sum_filter]
  simp

/-- The cofactor-one prime face of an unclipped reciprocal fibre is the
negative packet layer count. -/
theorem replacementFibrePrimeFaceMass_eq_neg_reciprocalPrimeLayerCard
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z + 1 < R) :
    replacementFibrePrimeFaceMass R z =
      -(squareRootReciprocalPrimeLayerCard R z : ℂ) := by
  rw [replacementFibrePrimeFaceMass_eq_neg_primeCount R z hR hz (by omega),
    replacementFibrePrimeCount_eq_reciprocalPrimeLayerCard R z hR hz hzR]

/-- The cofactor-one dilated prime window is the literal reciprocal-fibre
prime count. -/
theorem replacementFibreRootPrimeWindowCount_one_eq_primeCount
    (R z : ℕ) :
    replacementFibreRootPrimeWindowCount R z 1 =
      replacementFibrePrimeCount R z := by
  classical
  unfold replacementFibreRootPrimeWindowCount replacementFibrePrimeCount
    replacementDilatedFibreLower replacementDilatedFibreUpper
    squareRootReplacementFibreLower squareRootReplacementFibreUpper
  simp only [Nat.mul_one]
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hqPrime : q.Prime
  · simp [hqPrime, hqPrime.one_lt]
  · simp [hqPrime]

/-- Every strict-root cofactor window is an existing prime-sieve reciprocal
prime count at the contracted endpoint `X_R / c`, with the cofactor itself as
the lower prime cutoff.  This is the exact interface from the crossing tail to
the repository's reciprocal-prime analytic machinery. -/
theorem replacementFibreRootPrimeWindowCount_eq_reciprocalPrimeCount
    (R z c : ℕ) :
    replacementFibreRootPrimeWindowCount R z c =
      primeSieveReciprocalPrimeCount c (squareRootEndpoint R / c) z := by
  classical
  unfold replacementFibreRootPrimeWindowCount
    primeSieveReciprocalPrimeCount primeSievePrimeIndicator
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc,
    mem_primeSieveReciprocalInterval]
  unfold replacementDilatedFibreLower replacementDilatedFibreUpper
    primeSieveReciprocalLower primeSieveReciprocalUpper
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hprime, hcq⟩
    refine ⟨⟨max_lt hcq ?_, ?_⟩, hprime⟩
    · simpa [Nat.mul_comm, Nat.mul_left_comm] using
        (show squareRootEndpoint R / ((z + 1) * c) < q by omega)
    · simpa [Nat.mul_comm, Nat.mul_left_comm] using hupper
  · rintro ⟨⟨hlower, hupper⟩, hprime⟩
    rcases max_lt_iff.mp hlower with ⟨hcq, hquot⟩
    refine ⟨⟨?_, ?_⟩, hprime, hcq⟩
    · have : squareRootEndpoint R / ((z + 1) * c) < q := by
        simpa [Nat.mul_comm, Nat.mul_left_comm] using hquot
      omega
    · simpa [Nat.mul_comm, Nat.mul_left_comm] using hupper

/-- Smooth-oriented reciprocal prime count at the contracted endpoint.  The
canonical largest prime of the cofactor is the lower cutoff, while `q < c`
retains the smooth orientation inside the same prime interval. -/
def replacementFibreSmoothReciprocalPrimeCount (R z c : ℕ) : ℂ :=
  ∑ q ∈ primeSieveReciprocalInterval
      (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c) z,
    if q.Prime ∧ q < c then 1 else 0

/-- Every smooth cofactor window is the contracted reciprocal-prime interval
with the orientation cutoff `q < c` retained inside its signed summand. -/
theorem replacementFibreSmoothPrimeWindowCount_eq_reciprocalPrimeCount
    (R z c : ℕ) :
    replacementFibreSmoothPrimeWindowCount R z c =
      replacementFibreSmoothReciprocalPrimeCount R z c := by
  classical
  unfold replacementFibreSmoothPrimeWindowCount
    replacementFibreSmoothReciprocalPrimeCount
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc,
    mem_primeSieveReciprocalInterval]
  unfold replacementDilatedFibreLower replacementDilatedFibreUpper
    primeSieveReciprocalLower primeSieveReciprocalUpper
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hprime, hrough, hqc⟩
    refine ⟨⟨max_lt hrough ?_, ?_⟩, hprime, hqc⟩
    · simpa [Nat.mul_comm, Nat.mul_left_comm] using
        (show squareRootEndpoint R / ((z + 1) * c) < q by omega)
    · simpa [Nat.mul_comm, Nat.mul_left_comm] using hupper
  · rintro ⟨⟨hlower, hupper⟩, hprime, hqc⟩
    rcases max_lt_iff.mp hlower with ⟨hrough, hquot⟩
    refine ⟨⟨?_, ?_⟩, hprime, hrough, hqc⟩
    · have : squareRootEndpoint R / ((z + 1) * c) < q := by
        simpa [Nat.mul_comm, Nat.mul_left_comm] using hquot
      omega
    · simpa [Nat.mul_comm, Nat.mul_left_comm] using hupper

private theorem canonicalLargestPrimeFactor_le_self_of_two
    {c : ℕ} (hc : 2 ≤ c) :
    canonicalLargestPrimeFactor c ≤ c := by
  exact Nat.le_of_dvd (by omega) (canonicalLargestPrimeFactor_dvd (by omega))

/-- Root and smooth orientations recombine pointwise into the single canonical
rough-prime reciprocal count.  A prime in the full interval cannot equal its
cofactor: at equality its canonical largest prime would violate the strict
roughness cutoff. -/
theorem rootReciprocalPrimeCount_add_smooth_eq_roughPrimeCount
    (R z c : ℕ) (hc : 2 ≤ c) :
    primeSieveReciprocalPrimeCount c (squareRootEndpoint R / c) z +
        replacementFibreSmoothReciprocalPrimeCount R z c =
      primeSieveReciprocalPrimeCount (canonicalLargestPrimeFactor c)
        (squareRootEndpoint R / c) z := by
  classical
  have hPc : canonicalLargestPrimeFactor c ≤ c :=
    canonicalLargestPrimeFactor_le_self_of_two hc
  have hrootSet :
      primeSieveReciprocalInterval c (squareRootEndpoint R / c) z =
        (primeSieveReciprocalInterval (canonicalLargestPrimeFactor c)
          (squareRootEndpoint R / c) z).filter (fun q => c < q) := by
    ext q
    simp only [Finset.mem_filter, mem_primeSieveReciprocalInterval]
    unfold primeSieveReciprocalLower
    simp only [max_lt_iff]
    omega
  unfold primeSieveReciprocalPrimeCount primeSievePrimeIndicator
    replacementFibreSmoothReciprocalPrimeCount
  rw [hrootSet, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hprime : q.Prime
  · have hqne : q ≠ c := by
      intro heq
      subst q
      have hlower :=
        (mem_primeSieveReciprocalInterval.mp hq).1
      have hPlt : canonicalLargestPrimeFactor c < c :=
        lt_of_le_of_lt
          (le_max_left (canonicalLargestPrimeFactor c)
            ((squareRootEndpoint R / c) / (z + 1))) hlower
      have hPeq : canonicalLargestPrimeFactor c = c := by
        simpa using canonicalLargestPrimeFactor_mul_prime_eq
          (c := 1) (q := c) (by omega) hprime.one_lt hprime
      omega
    rcases lt_or_gt_of_ne hqne with hqc | hcq
    · simp [hprime, hqc, Nat.not_lt_of_ge hqc.le]
    · simp [hprime, hcq, Nat.not_lt_of_ge hcq.le]
  · simp [hprime]

/-- At the complete square endpoint, a root-oriented window with cofactor
`c >= R` is empty: its contracted endpoint is already strictly below `c`. -/
theorem rootReciprocalPrimeCount_eq_zero_of_root_le_cofactor
    (R z c : ℕ) (hR : 2 ≤ R) (hc : R ≤ c) :
    primeSieveReciprocalPrimeCount c (squareRootEndpoint R / c) z = 0 := by
  have hcpos : 0 < c := by omega
  have hendpointLt : squareRootEndpoint R < c * c := by
    have hrootLt : squareRootEndpoint R < R ^ 2 := by
      unfold squareRootEndpoint
      have hpos : 0 < R ^ 2 := by positivity
      omega
    have hpow : R ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left hc 2
    simpa [pow_two] using hrootLt.trans_le hpow
  have hcontracted : squareRootEndpoint R / c < c :=
    (Nat.div_lt_iff_lt_mul hcpos).2 hendpointLt
  have hupper :
      primeSieveReciprocalUpper (squareRootEndpoint R / c) z < c := by
    unfold primeSieveReciprocalUpper
    exact (Nat.div_le_self _ _).trans_lt hcontracted
  have hlower :
      c ≤ primeSieveReciprocalLower c (squareRootEndpoint R / c) z := by
    unfold primeSieveReciprocalLower
    exact le_max_left _ _
  unfold primeSieveReciprocalPrimeCount primeSieveReciprocalInterval
  rw [Finset.Ioc_eq_empty_of_le (hupper.le.trans hlower)]
  simp

/-- The smooth orientation has no cofactor-one contribution. -/
@[simp] theorem replacementFibreSmoothReciprocalPrimeCount_one
    (R z : ℕ) :
    replacementFibreSmoothReciprocalPrimeCount R z 1 = 0 := by
  unfold replacementFibreSmoothReciprocalPrimeCount
  apply Finset.sum_eq_zero
  intro q _hq
  by_cases hprime : q.Prime
  · have hq2 := hprime.two_le
    have hnlt : ¬q < 1 := by omega
    simp [hprime, hnlt]
  · simp [hprime]

/-- Deterministic PNT-density mass on the contracted smooth reciprocal
interval, with the orientation cutoff retained before summation. -/
def replacementFibreSmoothReciprocalLiMass (R z c : ℕ) : ℂ :=
  ∑ q ∈ primeSieveReciprocalInterval
      (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c) z,
    if q < c then primeSievePNTDensity q else 0

/-- Centered prime discrepancy on the same oriented smooth interval. -/
def replacementFibreSmoothReciprocalPrimeDiscrepancy
    (R z c : ℕ) : ℂ :=
  replacementFibreSmoothReciprocalPrimeCount R z c -
    replacementFibreSmoothReciprocalLiMass R z c

/-- Exact PNT centering of one oriented smooth reciprocal window. -/
theorem replacementFibreSmoothReciprocalPrimeCount_eq_li_add_discrepancy
    (R z c : ℕ) :
    replacementFibreSmoothReciprocalPrimeCount R z c =
      replacementFibreSmoothReciprocalLiMass R z c +
        replacementFibreSmoothReciprocalPrimeDiscrepancy R z c := by
  unfold replacementFibreSmoothReciprocalPrimeDiscrepancy
  ring

/-- Strict-root mass after removing the cofactor-one prime face. -/
def replacementFibreCompositeRootMass (R z : ℕ) : ℂ :=
  replacementFibreRootMass R z - replacementFibrePrimeFaceMass R z

/-- Removing the cofactor-one prime face from the root orientation leaves
exactly the signed Type-II prime windows with cofactors `c >= 2`. -/
theorem replacementFibreCompositeRootMass_eq_neg_cofactorPrimeWindows
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    replacementFibreCompositeRootMass R z =
      -∑ c ∈ Finset.Icc 2 (R - 1),
        canonicalMoebiusWeight c *
          replacementFibreRootPrimeWindowCount R z c := by
  classical
  unfold replacementFibreCompositeRootMass
  rw [replacementFibreRootMass_eq_neg_cofactorPrimeWindows R z hR hz hzR,
    replacementFibrePrimeFaceMass_eq_neg_primeCount R z hR hz hzR,
    ← replacementFibreRootPrimeWindowCount_one_eq_primeCount R z]
  have hset :
      Finset.Icc 1 (R - 1) =
        ({1} : Finset ℕ) ∪ Finset.Icc 2 (R - 1) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({1} : Finset ℕ) (Finset.Icc 2 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    rw [Finset.mem_singleton] at hc1
    subst c
    simp at hc2
  rw [hset, Finset.sum_union hdisj]
  simp [canonicalMoebiusWeight]

/-- The two non-prime orientations kept as one signed cofactor-prime object.
The root side starts at cofactor two because the packet has removed the
cofactor-one face; the smooth side retains its canonical roughness condition
inside `replacementFibreSmoothPrimeWindowCount`. -/
def replacementFibreTypeIIWindowMass (R z : ℕ) : ℂ :=
  -((∑ c ∈ Finset.Icc 2 (R - 1),
        canonicalMoebiusWeight c *
          primeSieveReciprocalPrimeCount c
            (squareRootEndpoint R / c) z) +
      ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c *
          replacementFibreSmoothReciprocalPrimeCount R z c)

/-- The orientation-free canonical rough-prime form of the residual Type-II
mass.  Every cofactor begins at two, and freshness is carried solely by the
canonical lower cutoff `P+(c)`. -/
def replacementFibreCanonicalRoughReciprocalMass (R z : ℕ) : ℂ :=
  -∑ c ∈ Finset.Icc 2 (squareRootEndpoint R),
    canonicalMoebiusWeight c *
      primeSieveReciprocalPrimeCount (canonicalLargestPrimeFactor c)
        (squareRootEndpoint R / c) z

/-- Full canonical rough-prime reciprocal fibre, including the cofactor-one
prime face. -/
def replacementFibreCanonicalRoughFullMass (R z : ℕ) : ℂ :=
  -∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
    canonicalMoebiusWeight c *
      primeSieveReciprocalPrimeCount (canonicalLargestPrimeFactor c)
        (squareRootEndpoint R / c) z

/-- **Orientation recombination after prime-face cancellation.**  The root and
smooth Type-II sectors are exactly one canonical rough-prime reciprocal sum.
The root range may be extended through `X_R` because every `c >= R` root window
is empty; the cofactor-one smooth term is empty as well. -/
theorem replacementFibreTypeIIWindowMass_eq_canonicalRoughReciprocalMass
    (R z : ℕ) (hR : 2 ≤ R) :
    replacementFibreTypeIIWindowMass R z =
      replacementFibreCanonicalRoughReciprocalMass R z := by
  classical
  have hRleX : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsquare : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  have hrootSet :
      Finset.Icc 2 (squareRootEndpoint R) =
        Finset.Icc 2 (R - 1) ∪
          Finset.Icc R (squareRootEndpoint R) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hrootDisj :
      Disjoint (Finset.Icc 2 (R - 1))
        (Finset.Icc R (squareRootEndpoint R)) := by
    rw [Finset.disjoint_left]
    intro c hcLow hcHigh
    rcases Finset.mem_Icc.mp hcLow with ⟨_hc2, hcPred⟩
    rcases Finset.mem_Icc.mp hcHigh with ⟨hcR, _hcX⟩
    omega
  have hrootZero :
      (∑ c ∈ Finset.Icc R (squareRootEndpoint R),
        canonicalMoebiusWeight c *
          primeSieveReciprocalPrimeCount c
            (squareRootEndpoint R / c) z) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    have hcR := (Finset.mem_Icc.mp hc).1
    rw [rootReciprocalPrimeCount_eq_zero_of_root_le_cofactor
      R z c hR hcR, mul_zero]
  have hrootExtend :
      (∑ c ∈ Finset.Icc 2 (R - 1),
        canonicalMoebiusWeight c *
          primeSieveReciprocalPrimeCount c
            (squareRootEndpoint R / c) z) =
        ∑ c ∈ Finset.Icc 2 (squareRootEndpoint R),
          canonicalMoebiusWeight c *
            primeSieveReciprocalPrimeCount c
              (squareRootEndpoint R / c) z := by
    rw [hrootSet, Finset.sum_union hrootDisj, hrootZero, add_zero]
  have hsmoothSet :
      Finset.Icc 1 (squareRootEndpoint R) =
        ({1} : Finset ℕ) ∪ Finset.Icc 2 (squareRootEndpoint R) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hsmoothDisj :
      Disjoint ({1} : Finset ℕ)
        (Finset.Icc 2 (squareRootEndpoint R)) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    rw [Finset.mem_singleton] at hc1
    subst c
    simp at hc2
  have hsmoothDrop :
      (∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c *
          replacementFibreSmoothReciprocalPrimeCount R z c) =
        ∑ c ∈ Finset.Icc 2 (squareRootEndpoint R),
          canonicalMoebiusWeight c *
            replacementFibreSmoothReciprocalPrimeCount R z c := by
    rw [hsmoothSet, Finset.sum_union hsmoothDisj]
    simp
  unfold replacementFibreTypeIIWindowMass
    replacementFibreCanonicalRoughReciprocalMass
  rw [hrootExtend, hsmoothDrop, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  have hc2 := (Finset.mem_Icc.mp hc).1
  rw [← mul_add,
    rootReciprocalPrimeCount_add_smooth_eq_roughPrimeCount R z c hc2]

/-- Deterministic PNT-density part of the prime-cancelled Type-II mass. -/
def replacementFibreTypeIILiMass (R z : ℕ) : ℂ :=
  -((∑ c ∈ Finset.Icc 2 (R - 1),
        canonicalMoebiusWeight c *
          primeSieveReciprocalLiMass c
            (squareRootEndpoint R / c) z) +
      ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c *
          replacementFibreSmoothReciprocalLiMass R z c)

/-- Centered reciprocal-prime discrepancy part of the same signed Type-II
mass.  Root and smooth orientations remain in one object. -/
def replacementFibreTypeIIDiscrepancyMass (R z : ℕ) : ℂ :=
  -((∑ c ∈ Finset.Icc 2 (R - 1),
        canonicalMoebiusWeight c *
          primeSieveReciprocalPrimeDiscrepancy c
            (squareRootEndpoint R / c) z) +
      ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c *
          replacementFibreSmoothReciprocalPrimeDiscrepancy R z c)

/-- Exact PNT centering of a native reciprocal prime count. -/
theorem primeSieveReciprocalPrimeCount_eq_li_add_discrepancy
    (y x d : ℕ) :
    primeSieveReciprocalPrimeCount y x d =
      primeSieveReciprocalLiMass y x d +
        primeSieveReciprocalPrimeDiscrepancy y x d := by
  unfold primeSieveReciprocalPrimeDiscrepancy
  ring

/-- Deterministic PNT-density channel of the orientation-free canonical rough
reciprocal mass. -/
def replacementFibreCanonicalRoughLiMass (R z : ℕ) : ℂ :=
  -∑ c ∈ Finset.Icc 2 (squareRootEndpoint R),
    canonicalMoebiusWeight c *
      primeSieveReciprocalLiMass (canonicalLargestPrimeFactor c)
        (squareRootEndpoint R / c) z

/-- Centered reciprocal-prime discrepancy channel of the same canonical rough
mass. -/
def replacementFibreCanonicalRoughDiscrepancyMass (R z : ℕ) : ℂ :=
  -∑ c ∈ Finset.Icc 2 (squareRootEndpoint R),
    canonicalMoebiusWeight c *
      primeSieveReciprocalPrimeDiscrepancy
        (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c) z

/-- Exact PNT centering after root/smooth orientation recombination. -/
theorem replacementFibreCanonicalRoughReciprocalMass_eq_li_add_discrepancy
    (R z : ℕ) :
    replacementFibreCanonicalRoughReciprocalMass R z =
      replacementFibreCanonicalRoughLiMass R z +
        replacementFibreCanonicalRoughDiscrepancyMass R z := by
  unfold replacementFibreCanonicalRoughReciprocalMass
    replacementFibreCanonicalRoughLiMass
    replacementFibreCanonicalRoughDiscrepancyMass
  simp_rw [primeSieveReciprocalPrimeCount_eq_li_add_discrepancy,
    mul_add, Finset.sum_add_distrib]
  ring

/-- The prime-cancelled Type-II diagonal in its final orientation-free,
PNT-centered form. -/
theorem replacementFibreTypeIIWindowMass_eq_canonical_li_add_discrepancy
    (R z : ℕ) (hR : 2 ≤ R) :
    replacementFibreTypeIIWindowMass R z =
      replacementFibreCanonicalRoughLiMass R z +
        replacementFibreCanonicalRoughDiscrepancyMass R z := by
  rw [replacementFibreTypeIIWindowMass_eq_canonicalRoughReciprocalMass
      R z hR,
    replacementFibreCanonicalRoughReciprocalMass_eq_li_add_discrepancy]

/-- **Signed Type-II PNT centering.**  The residual diagonal is exactly its
deterministic Li mass plus its centered reciprocal discrepancy mass, before
any norm or orientation split. -/
theorem replacementFibreTypeIIWindowMass_eq_li_add_discrepancy
    (R z : ℕ) :
    replacementFibreTypeIIWindowMass R z =
      replacementFibreTypeIILiMass R z +
        replacementFibreTypeIIDiscrepancyMass R z := by
  unfold replacementFibreTypeIIWindowMass replacementFibreTypeIILiMass
    replacementFibreTypeIIDiscrepancyMass
  simp_rw [primeSieveReciprocalPrimeCount_eq_li_add_discrepancy,
    replacementFibreSmoothReciprocalPrimeCount_eq_li_add_discrepancy,
    mul_add, Finset.sum_add_distrib]
  ring

/-- After prime-face removal, root-composite and smooth orientations are
exactly the single signed Type-II window mass. -/
theorem replacementFibreCompositeRoot_add_smooth_eq_typeIIWindowMass
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    replacementFibreCompositeRootMass R z +
        replacementFibreSmoothMass R z =
      replacementFibreTypeIIWindowMass R z := by
  rw [replacementFibreCompositeRootMass_eq_neg_cofactorPrimeWindows
      R z hR hz hzR,
    replacementFibreSmoothMass_eq_neg_cofactorPrimeWindows
      R z hR hz hzR]
  simp_rw [replacementFibreRootPrimeWindowCount_eq_reciprocalPrimeCount,
    replacementFibreSmoothPrimeWindowCount_eq_reciprocalPrimeCount]
  unfold replacementFibreTypeIIWindowMass
  ring

/-- The complementary Möbius fibre is the prime face, the remaining strict-root
mass, and the smooth-oriented mass, with all signs retained. -/
theorem squareRootReplacementTailMoebiusCoefficient_eq_prime_add_composite_add_smooth
    (R z : ℕ) (hR : 2 ≤ R) :
    squareRootReplacementTailMoebiusCoefficient R z =
      replacementFibrePrimeFaceMass R z +
        replacementFibreCompositeRootMass R z +
          replacementFibreSmoothMass R z := by
  rw [squareRootReplacementTailMoebiusCoefficient_eq_root_add_smooth R z hR]
  unfold replacementFibreCompositeRootMass
  ring

/-- **Full canonical rough-prime fibre dictionary.**  Adding the cofactor-one
prime face to the recombined Type-II mass gives the single rough-prime sum over
all positive cofactors. -/
theorem squareRootReplacementTailMoebiusCoefficient_eq_canonicalRoughFullMass
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    squareRootReplacementTailMoebiusCoefficient R z =
      replacementFibreCanonicalRoughFullMass R z := by
  rw [squareRootReplacementTailMoebiusCoefficient_eq_prime_add_composite_add_smooth
      R z hR,
    add_assoc,
    replacementFibreCompositeRoot_add_smooth_eq_typeIIWindowMass
      R z hR hz hzR,
    replacementFibreTypeIIWindowMass_eq_canonicalRoughReciprocalMass
      R z hR,
    replacementFibrePrimeFaceMass_eq_neg_primeCount R z hR hz hzR,
    ← replacementFibreRootPrimeWindowCount_one_eq_primeCount R z,
    replacementFibreRootPrimeWindowCount_eq_reciprocalPrimeCount R z 1]
  have hset :
      Finset.Icc 1 (squareRootEndpoint R) =
        ({1} : Finset ℕ) ∪ Finset.Icc 2 (squareRootEndpoint R) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    have hRX : 1 ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      have hpos : 1 < R ^ 2 := by nlinarith
      omega
    omega
  have hdisj :
      Disjoint ({1} : Finset ℕ)
        (Finset.Icc 2 (squareRootEndpoint R)) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    rw [Finset.mem_singleton] at hc1
    subst c
    simp at hc2
  unfold replacementFibreCanonicalRoughFullMass
    replacementFibreCanonicalRoughReciprocalMass
  rw [hset, Finset.sum_union hdisj]
  simp [canonicalMoebiusWeight, canonicalLargestPrimeFactor]
  ring

/-- The prime diagonal after adding the packet-removal row.  This is where the
crossing acts inside the reciprocal-fibre renewal, before any norm. -/
def squareRootPostCrossingPrimeDiagonal
    (R K j y : ℕ) : ℂ :=
  replacementFibrePrimeFaceMass R y +
    squareRootCrossingRemovalCoefficient R K j y

/-- Every completely admitted shallow layer cancels its entire cofactor-one
prime diagonal. -/
theorem squareRootPostCrossingPrimeDiagonal_eq_zero_of_lt
    (R K j y : ℕ) (hR : 2 ≤ R) (hK : K + 1 < R)
    (hy : 1 ≤ y) (hyK : y < K) :
    squareRootPostCrossingPrimeDiagonal R K j y = 0 := by
  have hyR : y + 1 < R := by omega
  unfold squareRootPostCrossingPrimeDiagonal
  rw [replacementFibrePrimeFaceMass_eq_neg_reciprocalPrimeLayerCard
    R y hR hy hyR]
  unfold squareRootCrossingRemovalCoefficient
  rw [squareRootReciprocalPrimeCount_eq_layerCard]
  have hyPred : y ≤ K - 1 := by omega
  have hyNe : y ≠ K := by omega
  simp [Finset.mem_Icc, hy, hyPred, hyNe]

/-- At the crossing layer, the surviving prime diagonal is exactly the signed
number of unfilled seats. -/
theorem squareRootPostCrossingPrimeDiagonal_eq_crossing_remainder
    (R K j : ℕ) (hR : 2 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingPrimeDiagonal R K j K =
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) := by
  unfold squareRootPostCrossingPrimeDiagonal
  rw [replacementFibrePrimeFaceMass_eq_neg_reciprocalPrimeLayerCard
    R K hR hK hKR]
  unfold squareRootCrossingRemovalCoefficient
  have hnotPred : ¬K ≤ K - 1 := by omega
  simp [Finset.mem_Icc, hnotPred]
  ring

/-- The shallow removal row is exactly the negative partial packet. -/
theorem sum_crossingRemovalCoefficient_mul_mertens
    (R K j : ℕ) (hK : 1 ≤ K) (hKR : K < R) :
    (∑ y ∈ Finset.range R,
        squareRootCrossingRemovalCoefficient R K j y *
          mertensSummatory y) =
      -((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) := by
  have hfilter :
      (Finset.range R).filter (fun y => y ∈ Finset.Icc 1 (K - 1)) =
        Finset.Icc 1 (K - 1) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have hKmem : K ∈ Finset.range R := Finset.mem_range.mpr hKR
  rw [squareRootCrossingLayerPartialPacketInt_cast_complex]
  unfold squareRootCrossingRemovalCoefficient
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ y ∈ Finset.range R,
          (if y ∈ Finset.Icc 1 (K - 1) then
              primeSieveReciprocalPrimeCount R (squareRootEndpoint R) y
            else 0) * mertensSummatory y) =
        ∑ y ∈ Finset.Icc 1 (K - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) y *
            mertensSummatory y := by
    calc
      (∑ y ∈ Finset.range R,
          (if y ∈ Finset.Icc 1 (K - 1) then
              primeSieveReciprocalPrimeCount R (squareRootEndpoint R) y
            else 0) * mertensSummatory y) =
          ∑ y ∈ Finset.range R,
            if y ∈ Finset.Icc 1 (K - 1) then
              primeSieveReciprocalPrimeCount R (squareRootEndpoint R) y *
                mertensSummatory y
            else 0 := by
              apply Finset.sum_congr rfl
              intro y _hy
              by_cases hy : y ∈ Finset.Icc 1 (K - 1) <;> simp [hy]
      _ = ∑ y ∈ (Finset.range R).filter
            (fun y => y ∈ Finset.Icc 1 (K - 1)),
            primeSieveReciprocalPrimeCount R (squareRootEndpoint R) y *
              mertensSummatory y := by
              rw [Finset.sum_filter]
      _ = ∑ y ∈ Finset.Icc 1 (K - 1),
            primeSieveReciprocalPrimeCount R (squareRootEndpoint R) y *
              mertensSummatory y := by rw [hfilter]
  rw [hfirst]
  have hsecond :
      (∑ y ∈ Finset.range R,
          (if y = K then (j : ℂ) else 0) * mertensSummatory y) =
        (j : ℂ) * mertensSummatory K := by
    simp [hKmem]
  rw [hsecond]
  unfold squareRootTruncatedUpperMiddlePacket
  ring

/-- The strict-descendant part of the complementary fibre transform.  The
cofactor-one prime face, composite strict-root face, and smooth face stay
inside the same signed summand. -/
def squareRootOrientedStrictDescendantTransform (R y : ℕ) : ℂ :=
  ∑ z ∈ Finset.Icc (y + 1) (R - 1),
    (replacementFibrePrimeFaceMass R z +
        replacementFibreCompositeRootMass R z +
          replacementFibreSmoothMass R z) *
      squareRootReplacementQuotientKernel z y

/-- Strict descendants in the orientation-free canonical rough-prime
coordinates.  Unlike the shallow diagonal, descendants retain the `c = 1`
prime face. -/
def squareRootCanonicalRoughStrictDescendantTransform (R y : ℕ) : ℂ :=
  ∑ z ∈ Finset.Icc (y + 1) (R - 1),
    replacementFibreCanonicalRoughFullMass R z *
      squareRootReplacementQuotientKernel z y

/-- The oriented descendant transform is exactly the full canonical
rough-prime transform on every strict lower-triangular row. -/
theorem squareRootOrientedStrictDescendantTransform_eq_canonicalRough
    (R y : ℕ) (hR : 2 ≤ R) :
    squareRootOrientedStrictDescendantTransform R y =
      squareRootCanonicalRoughStrictDescendantTransform R y := by
  unfold squareRootOrientedStrictDescendantTransform
    squareRootCanonicalRoughStrictDescendantTransform
  apply Finset.sum_congr rfl
  intro z hz
  rcases Finset.mem_Icc.mp hz with ⟨hzLower, hzUpper⟩
  have hz1 : 1 ≤ z := by omega
  have hzR : z < R := by omega
  rw [← squareRootReplacementTailMoebiusCoefficient_eq_prime_add_composite_add_smooth
      R z hR,
    squareRootReplacementTailMoebiusCoefficient_eq_canonicalRoughFullMass
      R z hR hz1 hzR]

/-- Lower triangularity splits the complete quotient transform into its
diagonal fibre and its strict descendants. -/
theorem sum_tailMoebius_mul_quotientKernel_eq_diagonal_add_strict
    (R y : ℕ) (hy : 1 ≤ y) (hyR : y < R) :
    (∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z *
          squareRootReplacementQuotientKernel z y) =
      squareRootReplacementTailMoebiusCoefficient R y +
        ∑ z ∈ Finset.Icc (y + 1) (R - 1),
          squareRootReplacementTailMoebiusCoefficient R z *
            squareRootReplacementQuotientKernel z y := by
  let f : ℕ → ℂ := fun z =>
    squareRootReplacementTailMoebiusCoefficient R z *
      squareRootReplacementQuotientKernel z y
  have hzero : (∑ z ∈ Finset.range y, f z) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    have hzy : z < y := Finset.mem_range.mp hz
    unfold f
    rw [squareRootReplacementQuotientKernel_eq_zero_of_lt hzy]
    ring
  have hset :
      Finset.Ico (y + 1) R = Finset.Icc (y + 1) (R - 1) := by
    ext z
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  calc
    (∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z *
          squareRootReplacementQuotientKernel z y) =
        (∑ z ∈ Finset.range (y + 1), f z) +
          ∑ z ∈ Finset.Ico (y + 1) R, f z := by
            simpa [f] using
              (Finset.sum_range_add_sum_Ico f
                (Nat.succ_le_of_lt hyR)).symm
    _ = ((∑ z ∈ Finset.range y, f z) + f y) +
          ∑ z ∈ Finset.Ico (y + 1) R, f z := by
            rw [Finset.sum_range_succ]
    _ = f y + ∑ z ∈ Finset.Ico (y + 1) R, f z := by rw [hzero, zero_add]
    _ = squareRootReplacementTailMoebiusCoefficient R y +
          ∑ z ∈ Finset.Icc (y + 1) (R - 1),
            squareRootReplacementTailMoebiusCoefficient R z *
              squareRootReplacementQuotientKernel z y := by
      unfold f
      rw [squareRootReplacementQuotientKernel_self hy, hset]
      ring

/-- Renewal coefficient after the packet has canceled the shallow prime
diagonal.  Only the remaining prime diagonal, the two non-prime orientations,
and strict quotient descendants occur. -/
def squareRootPostCrossingPrimeCancelledCoefficient
    (R K j y : ℕ) : ℂ :=
  (if y = R - 1 then 1 else 0) +
    squareRootPostCrossingPrimeDiagonal R K j y +
      replacementFibreCompositeRootMass R y +
        replacementFibreSmoothMass R y +
          squareRootOrientedStrictDescendantTransform R y

/-- Universal orientation-free coefficient row.  Packet removal is added to
the full canonical rough-prime diagonal; strict descendants retain their full
canonical rough mass. -/
def squareRootPostCrossingCanonicalRoughCoefficient
    (R K j y : ℕ) : ℂ :=
  (if y = R - 1 then 1 else 0) +
    squareRootCrossingRemovalCoefficient R K j y +
      replacementFibreCanonicalRoughFullMass R y +
        squareRootCanonicalRoughStrictDescendantTransform R y

/-- **Coefficientwise prime-diagonal cancellation.**  The post-crossing
replacement row is exactly the oriented prime-cancelled quotient row. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_primeCancelled
    (R K j y : ℕ) (hR : 2 ≤ R) (hy : 1 ≤ y) (hyR : y < R) :
    squareRootPostCrossingReplacementCoefficient R K j y =
      squareRootPostCrossingPrimeCancelledCoefficient R K j y := by
  unfold squareRootPostCrossingReplacementCoefficient
  rw [show squareRootReplacementCoefficient R y =
      (if y = R - 1 then 1 else 0) +
        ∑ z ∈ Finset.range R,
          squareRootReplacementTailMoebiusCoefficient R z *
            squareRootReplacementQuotientKernel z y by
      unfold squareRootReplacementCoefficient
      rw [squareRootReplacementTailCoefficient_eq_neg_tailMoebiusKernel
        R y hR]
      ring]
  rw [sum_tailMoebius_mul_quotientKernel_eq_diagonal_add_strict R y hy hyR,
    squareRootReplacementTailMoebiusCoefficient_eq_prime_add_composite_add_smooth
      R y hR]
  unfold squareRootPostCrossingPrimeCancelledCoefficient
    squareRootPostCrossingPrimeDiagonal
    squareRootOrientedStrictDescendantTransform
  simp_rw [squareRootReplacementTailMoebiusCoefficient_eq_prime_add_composite_add_smooth
    R _ hR]
  ring

/-- **Universal canonical rough-prime row.**  Every positive lower scale of
the post-crossing replacement is one packet-removal coefficient plus the full
canonical rough-prime lower-triangular renewal. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_canonicalRough
    (R K j y : ℕ) (hR : 2 ≤ R) (hy : 1 ≤ y) (hyR : y < R) :
    squareRootPostCrossingReplacementCoefficient R K j y =
      squareRootPostCrossingCanonicalRoughCoefficient R K j y := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_primeCancelled
    R K j y hR hy hyR]
  have hfull :
      replacementFibrePrimeFaceMass R y +
          replacementFibreCompositeRootMass R y +
            replacementFibreSmoothMass R y =
        replacementFibreCanonicalRoughFullMass R y := by
    rw [← squareRootReplacementTailMoebiusCoefficient_eq_prime_add_composite_add_smooth
        R y hR,
      squareRootReplacementTailMoebiusCoefficient_eq_canonicalRoughFullMass
        R y hR hy hyR]
  unfold squareRootPostCrossingPrimeCancelledCoefficient
    squareRootPostCrossingPrimeDiagonal
    squareRootPostCrossingCanonicalRoughCoefficient
  rw [squareRootOrientedStrictDescendantTransform_eq_canonicalRough R y hR]
  linear_combination hfull

/-- Below the crossing, the complete prime diagonal has disappeared from the
renewal coefficient; no estimate or absolute value is used. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_belowCrossing
    (R K j y : ℕ) (hR : 2 ≤ R) (hKR : K + 1 < R)
    (hy : 1 ≤ y) (hyK : y < K) :
    squareRootPostCrossingReplacementCoefficient R K j y =
      replacementFibreCompositeRootMass R y +
        replacementFibreSmoothMass R y +
          squareRootOrientedStrictDescendantTransform R y := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_primeCancelled
    R K j y hR hy (by omega)]
  unfold squareRootPostCrossingPrimeCancelledCoefficient
  rw [squareRootPostCrossingPrimeDiagonal_eq_zero_of_lt
    R K j y hR hKR hy hyK]
  have hpredNe : y ≠ R - 1 := by omega
  simp [hpredNe]

/-- Below the crossing, the residual coefficient is one signed Type-II
cofactor-window mass plus the strict lower-triangular descendants. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_belowCrossing_typeII
    (R K j y : ℕ) (hR : 2 ≤ R) (hKR : K + 1 < R)
    (hy : 1 ≤ y) (hyK : y < K) :
    squareRootPostCrossingReplacementCoefficient R K j y =
      replacementFibreTypeIIWindowMass R y +
        squareRootOrientedStrictDescendantTransform R y := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_belowCrossing
      R K j y hR hKR hy hyK,
    replacementFibreCompositeRoot_add_smooth_eq_typeIIWindowMass
      R y hR hy (by omega)]

/-- Below the crossing, PNT centering happens inside the signed coefficient:
deterministic Li mass, centered discrepancy, and strict descendants remain
coupled until the eventual row sum. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_belowCrossing_centered
    (R K j y : ℕ) (hR : 2 ≤ R) (hKR : K + 1 < R)
    (hy : 1 ≤ y) (hyK : y < K) :
    squareRootPostCrossingReplacementCoefficient R K j y =
      replacementFibreTypeIILiMass R y +
        replacementFibreTypeIIDiscrepancyMass R y +
          squareRootOrientedStrictDescendantTransform R y := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_belowCrossing_typeII
      R K j y hR hKR hy hyK,
    replacementFibreTypeIIWindowMass_eq_li_add_discrepancy]

/-- Final orientation-free centered shallow row.  Freshness is encoded only by
the canonical largest-prime cutoff in the rough reciprocal mass. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_belowCrossing_canonicalCentered
    (R K j y : ℕ) (hR : 2 ≤ R) (hKR : K + 1 < R)
    (hy : 1 ≤ y) (hyK : y < K) :
    squareRootPostCrossingReplacementCoefficient R K j y =
      replacementFibreCanonicalRoughLiMass R y +
        replacementFibreCanonicalRoughDiscrepancyMass R y +
          squareRootOrientedStrictDescendantTransform R y := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_belowCrossing_typeII
      R K j y hR hKR hy hyK,
    replacementFibreTypeIIWindowMass_eq_canonical_li_add_discrepancy
      R y hR]

/-- Orientation-free lower-triangular shallow row: `c = 1` is absent only on
the diagonal and is retained inside every strict descendant. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_belowCrossing_canonicalRough
    (R K j y : ℕ) (hR : 2 ≤ R) (hKR : K + 1 < R)
    (hy : 1 ≤ y) (hyK : y < K) :
    squareRootPostCrossingReplacementCoefficient R K j y =
      replacementFibreCanonicalRoughReciprocalMass R y +
        squareRootCanonicalRoughStrictDescendantTransform R y := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_belowCrossing_typeII
      R K j y hR hKR hy hyK,
    replacementFibreTypeIIWindowMass_eq_canonicalRoughReciprocalMass
      R y hR,
    squareRootOrientedStrictDescendantTransform_eq_canonicalRough R y hR]

/-- At the crossing depth, the only cofactor-one diagonal left in the renewal
row is `j-N_R(K)`, the negative of the unfilled prime seats. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_atCrossing
    (R K j : ℕ) (hR : 2 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingReplacementCoefficient R K j K =
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
        replacementFibreCompositeRootMass R K +
          replacementFibreSmoothMass R K +
            squareRootOrientedStrictDescendantTransform R K := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_primeCancelled
    R K j K hR hK (by omega)]
  unfold squareRootPostCrossingPrimeCancelledCoefficient
  rw [squareRootPostCrossingPrimeDiagonal_eq_crossing_remainder
    R K j hR hK hKR]
  have hpredNe : K ≠ R - 1 := by omega
  simp [hpredNe]

/-- At the crossing, the residual row is the exact unfilled-seat remainder,
the same signed Type-II window mass, and the strict descendants. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_atCrossing_typeII
    (R K j : ℕ) (hR : 2 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingReplacementCoefficient R K j K =
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
        replacementFibreTypeIIWindowMass R K +
          squareRootOrientedStrictDescendantTransform R K := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_atCrossing
      R K j hR hK hKR,
    add_assoc
      ((j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ))
      (replacementFibreCompositeRootMass R K)
      (replacementFibreSmoothMass R K),
    replacementFibreCompositeRoot_add_smooth_eq_typeIIWindowMass
      R K hR hK (by omega)]

/-- Centered crossing row: the unfilled-seat term, deterministic Li mass,
centered discrepancy, and strict descendants are retained in one coefficient. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_atCrossing_centered
    (R K j : ℕ) (hR : 2 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingReplacementCoefficient R K j K =
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
        replacementFibreTypeIILiMass R K +
          replacementFibreTypeIIDiscrepancyMass R K +
            squareRootOrientedStrictDescendantTransform R K := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_atCrossing_typeII
      R K j hR hK hKR,
    replacementFibreTypeIIWindowMass_eq_li_add_discrepancy]
  ring

/-- Final orientation-free centered crossing row. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_atCrossing_canonicalCentered
    (R K j : ℕ) (hR : 2 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingReplacementCoefficient R K j K =
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
        replacementFibreCanonicalRoughLiMass R K +
          replacementFibreCanonicalRoughDiscrepancyMass R K +
            squareRootOrientedStrictDescendantTransform R K := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_atCrossing_typeII
      R K j hR hK hKR,
    replacementFibreTypeIIWindowMass_eq_canonical_li_add_discrepancy
      R K hR]
  ring

/-- Orientation-free crossing row with the exact unfilled-seat remainder. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_atCrossing_canonicalRough
    (R K j : ℕ) (hR : 2 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingReplacementCoefficient R K j K =
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
        replacementFibreCanonicalRoughReciprocalMass R K +
          squareRootCanonicalRoughStrictDescendantTransform R K := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_atCrossing_typeII
      R K j hR hK hKR,
    replacementFibreTypeIIWindowMass_eq_canonicalRoughReciprocalMass
      R K hR,
    squareRootOrientedStrictDescendantTransform_eq_canonicalRough R K hR]

/-- **Exact post-crossing lower-triangular renewal row.**  The terminal tail is
one signed combination of Mertens states at scales `y < R`; the shallow packet
has modified the same row coefficientwise before any norm is taken. -/
theorem squareRootPostCrossingCoupledTail_eq_replacementRow
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingCoupledTail R K j =
      ∑ y ∈ Finset.range R,
        squareRootPostCrossingReplacementCoefficient R K j y *
          mertensSummatory y := by
  rw [postCrossingCoupledTail_eq_mertens_sub_partial R K j hR,
    mertensEndpoint_eq_recombinedReplacementRow R (by omega)]
  have hremove := sum_crossingRemovalCoefficient_mul_mertens
    R K j hK hKR
  unfold squareRootPostCrossingReplacementCoefficient
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, hremove]
  ring

/-- The terminal tail written on the positive lower scales after the
prime-diagonal cancellation has been performed coefficientwise. -/
theorem squareRootPostCrossingCoupledTail_eq_primeCancelledRow
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingCoupledTail R K j =
      ∑ y ∈ Finset.Icc 1 (R - 1),
        squareRootPostCrossingPrimeCancelledCoefficient R K j y *
          mertensSummatory y := by
  rw [squareRootPostCrossingCoupledTail_eq_replacementRow
    R K j hR hK hKR]
  have hset :
      Finset.range R = ({0} : Finset ℕ) ∪ Finset.Icc 1 (R - 1) := by
    ext y
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_Icc]
    omega
  have hdisj :
      Disjoint ({0} : Finset ℕ) (Finset.Icc 1 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro y hy0 hyIcc
    rw [Finset.mem_singleton] at hy0
    subst y
    simp at hyIcc
  rw [hset, Finset.sum_union hdisj]
  simp only [Finset.sum_singleton]
  rw [mertensSummatory_zero, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro y hy
  rcases Finset.mem_Icc.mp hy with ⟨hy1, hyR⟩
  rw [squareRootPostCrossingReplacementCoefficient_eq_primeCancelled
    R K j y (by omega) hy1 (by omega)]

/-- **Canonical rough-prime lower-triangular row.**  The complete coupled tail
is expressed without prime/root/smooth orientation labels. -/
theorem squareRootPostCrossingCoupledTail_eq_canonicalRoughRow
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingCoupledTail R K j =
      ∑ y ∈ Finset.Icc 1 (R - 1),
        squareRootPostCrossingCanonicalRoughCoefficient R K j y *
          mertensSummatory y := by
  rw [squareRootPostCrossingCoupledTail_eq_primeCancelledRow
    R K j hR hK hKR]
  apply Finset.sum_congr rfl
  intro y hy
  rcases Finset.mem_Icc.mp hy with ⟨hy1, hyR⟩
  rw [← squareRootPostCrossingReplacementCoefficient_eq_primeCancelled
      R K j y (by omega) hy1 (by omega),
    squareRootPostCrossingReplacementCoefficient_eq_canonicalRough
      R K j y (by omega) hy1 (by omega)]

/-- **Exact crossing split of the prime-cancelled renewal.**  Every completed
shallow prime diagonal is absent, the crossing row contains only the unfilled
prime seats, and the deeper oriented quotient tail remains one signed sum. -/
theorem squareRootPostCrossingCoupledTail_eq_primeCancelledCrossingSplit
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingCoupledTail R K j =
      (∑ y ∈ Finset.Icc 1 (K - 1),
        (replacementFibreCompositeRootMass R y +
            replacementFibreSmoothMass R y +
              squareRootOrientedStrictDescendantTransform R y) *
          mertensSummatory y) +
      ((j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreCompositeRootMass R K +
            replacementFibreSmoothMass R K +
              squareRootOrientedStrictDescendantTransform R K) *
        mertensSummatory K +
      ∑ y ∈ Finset.Icc (K + 1) (R - 1),
        squareRootPostCrossingPrimeCancelledCoefficient R K j y *
          mertensSummatory y := by
  rw [squareRootPostCrossingCoupledTail_eq_primeCancelledRow
    R K j hR hK (by omega)]
  rw [sum_Icc_one_pred_split_at
    (fun y => squareRootPostCrossingPrimeCancelledCoefficient R K j y *
      mertensSummatory y) hK (by omega)]
  have hbelow :
      (∑ y ∈ Finset.Icc 1 (K - 1),
        squareRootPostCrossingPrimeCancelledCoefficient R K j y *
          mertensSummatory y) =
        ∑ y ∈ Finset.Icc 1 (K - 1),
          (replacementFibreCompositeRootMass R y +
              replacementFibreSmoothMass R y +
                squareRootOrientedStrictDescendantTransform R y) *
            mertensSummatory y := by
    apply Finset.sum_congr rfl
    intro y hy
    rcases Finset.mem_Icc.mp hy with ⟨hy1, hyK⟩
    have hyLt : y < K := by omega
    rw [← squareRootPostCrossingReplacementCoefficient_eq_primeCancelled
      R K j y (by omega) hy1 (by omega),
      squareRootPostCrossingReplacementCoefficient_eq_belowCrossing
        R K j y (by omega) hKR hy1 hyLt]
  have hat :
      squareRootPostCrossingPrimeCancelledCoefficient R K j K =
        (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreCompositeRootMass R K +
            replacementFibreSmoothMass R K +
              squareRootOrientedStrictDescendantTransform R K := by
    rw [← squareRootPostCrossingReplacementCoefficient_eq_primeCancelled
      R K j K (by omega) hK (by omega),
      squareRootPostCrossingReplacementCoefficient_eq_atCrossing
        R K j (by omega) hK hKR]
  rw [hbelow, hat]

/-- **Type-II crossing normal form.**  The completed shallow rows contain no
cofactor-one prime term: their whole diagonal contribution is the single
signed cofactor-window mass.  The crossing row differs only by its exact
unfilled-seat remainder, while the deep tail remains coupled. -/
theorem squareRootPostCrossingCoupledTail_eq_typeIICrossingSplit
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingCoupledTail R K j =
      (∑ y ∈ Finset.Icc 1 (K - 1),
        (replacementFibreTypeIIWindowMass R y +
            squareRootOrientedStrictDescendantTransform R y) *
          mertensSummatory y) +
      ((j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreTypeIIWindowMass R K +
            squareRootOrientedStrictDescendantTransform R K) *
        mertensSummatory K +
      ∑ y ∈ Finset.Icc (K + 1) (R - 1),
        squareRootPostCrossingPrimeCancelledCoefficient R K j y *
          mertensSummatory y := by
  rw [squareRootPostCrossingCoupledTail_eq_primeCancelledCrossingSplit
    R K j hR hK hKR]
  have hbelow :
      (∑ y ∈ Finset.Icc 1 (K - 1),
        (replacementFibreCompositeRootMass R y +
            replacementFibreSmoothMass R y +
              squareRootOrientedStrictDescendantTransform R y) *
          mertensSummatory y) =
        ∑ y ∈ Finset.Icc 1 (K - 1),
          (replacementFibreTypeIIWindowMass R y +
              squareRootOrientedStrictDescendantTransform R y) *
            mertensSummatory y := by
    apply Finset.sum_congr rfl
    intro y hy
    rcases Finset.mem_Icc.mp hy with ⟨hy1, hyK⟩
    rw [replacementFibreCompositeRoot_add_smooth_eq_typeIIWindowMass
      R y (by omega) hy1 (by omega)]
  have hat :
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreCompositeRootMass R K +
            replacementFibreSmoothMass R K +
              squareRootOrientedStrictDescendantTransform R K =
        (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreTypeIIWindowMass R K +
            squareRootOrientedStrictDescendantTransform R K := by
    calc
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
            replacementFibreCompositeRootMass R K +
              replacementFibreSmoothMass R K +
                squareRootOrientedStrictDescendantTransform R K =
          squareRootPostCrossingReplacementCoefficient R K j K :=
            (squareRootPostCrossingReplacementCoefficient_eq_atCrossing
              R K j (by omega) hK hKR).symm
      _ = (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
            replacementFibreTypeIIWindowMass R K +
              squareRootOrientedStrictDescendantTransform R K :=
          squareRootPostCrossingReplacementCoefficient_eq_atCrossing_typeII
            R K j (by omega) hK hKR
  rw [hbelow, hat]

/-- **Centered Type-II crossing normal form.**  This is the analytic handoff:
the deterministic PNT-density channel and the centered reciprocal discrepancy
channel remain signed together with all strict descendants and the deep tail.
No triangle inequality or separate channel bound has been applied. -/
theorem squareRootPostCrossingCoupledTail_eq_centeredTypeIICrossingSplit
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingCoupledTail R K j =
      (∑ y ∈ Finset.Icc 1 (K - 1),
        (replacementFibreTypeIILiMass R y +
            replacementFibreTypeIIDiscrepancyMass R y +
              squareRootOrientedStrictDescendantTransform R y) *
          mertensSummatory y) +
      ((j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreTypeIILiMass R K +
            replacementFibreTypeIIDiscrepancyMass R K +
              squareRootOrientedStrictDescendantTransform R K) *
        mertensSummatory K +
      ∑ y ∈ Finset.Icc (K + 1) (R - 1),
        squareRootPostCrossingPrimeCancelledCoefficient R K j y *
          mertensSummatory y := by
  rw [squareRootPostCrossingCoupledTail_eq_typeIICrossingSplit
    R K j hR hK hKR]
  have hbelow :
      (∑ y ∈ Finset.Icc 1 (K - 1),
        (replacementFibreTypeIIWindowMass R y +
            squareRootOrientedStrictDescendantTransform R y) *
          mertensSummatory y) =
        ∑ y ∈ Finset.Icc 1 (K - 1),
          (replacementFibreTypeIILiMass R y +
              replacementFibreTypeIIDiscrepancyMass R y +
                squareRootOrientedStrictDescendantTransform R y) *
            mertensSummatory y := by
    apply Finset.sum_congr rfl
    intro y _hy
    rw [replacementFibreTypeIIWindowMass_eq_li_add_discrepancy]
  have hat :
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreTypeIIWindowMass R K +
            squareRootOrientedStrictDescendantTransform R K =
        (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreTypeIILiMass R K +
            replacementFibreTypeIIDiscrepancyMass R K +
              squareRootOrientedStrictDescendantTransform R K := by
    rw [replacementFibreTypeIIWindowMass_eq_li_add_discrepancy]
    ring
  rw [hbelow, hat]

/-- **Canonical centered crossing normal form.**  Root and smooth orientations
have now disappeared completely.  Each shallow diagonal is one Möbius-weighted
rough reciprocal count, centered into Li density and prime discrepancy, while
strict descendants and the deep tail remain coupled. -/
theorem squareRootPostCrossingCoupledTail_eq_canonicalCenteredCrossingSplit
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingCoupledTail R K j =
      (∑ y ∈ Finset.Icc 1 (K - 1),
        (replacementFibreCanonicalRoughLiMass R y +
            replacementFibreCanonicalRoughDiscrepancyMass R y +
              squareRootOrientedStrictDescendantTransform R y) *
          mertensSummatory y) +
      ((j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreCanonicalRoughLiMass R K +
            replacementFibreCanonicalRoughDiscrepancyMass R K +
              squareRootOrientedStrictDescendantTransform R K) *
        mertensSummatory K +
      ∑ y ∈ Finset.Icc (K + 1) (R - 1),
        squareRootPostCrossingPrimeCancelledCoefficient R K j y *
          mertensSummatory y := by
  rw [squareRootPostCrossingCoupledTail_eq_typeIICrossingSplit
    R K j hR hK hKR]
  have hbelow :
      (∑ y ∈ Finset.Icc 1 (K - 1),
        (replacementFibreTypeIIWindowMass R y +
            squareRootOrientedStrictDescendantTransform R y) *
          mertensSummatory y) =
        ∑ y ∈ Finset.Icc 1 (K - 1),
          (replacementFibreCanonicalRoughLiMass R y +
              replacementFibreCanonicalRoughDiscrepancyMass R y +
                squareRootOrientedStrictDescendantTransform R y) *
            mertensSummatory y := by
    apply Finset.sum_congr rfl
    intro y _hy
    rw [replacementFibreTypeIIWindowMass_eq_canonical_li_add_discrepancy
      R y (by omega)]
  have hat :
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreTypeIIWindowMass R K +
            squareRootOrientedStrictDescendantTransform R K =
        (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreCanonicalRoughLiMass R K +
            replacementFibreCanonicalRoughDiscrepancyMass R K +
              squareRootOrientedStrictDescendantTransform R K := by
    rw [replacementFibreTypeIIWindowMass_eq_canonical_li_add_discrepancy
      R K (by omega)]
    ring
  rw [hbelow, hat]

/-- One summand of the oriented prime-cancelled renewal row. -/
def squareRootPostCrossingPrimeCancelledTerm
    (R K j y : ℕ) : ℂ :=
  squareRootPostCrossingPrimeCancelledCoefficient R K j y *
    mertensSummatory y

/-- Full signed Gram after the cofactor-one prime diagonal has been canceled
inside the coefficient row.  Strict descendants and both non-prime
orientations remain coupled in the double sum. -/
def squareRootPostCrossingPrimeCancelledGram
    (R K j : ℕ) : ℂ :=
  ∑ y ∈ Finset.Icc 1 (R - 1),
    ∑ z ∈ Finset.Icc 1 (R - 1),
      squareRootPostCrossingPrimeCancelledTerm R K j y *
        conj (squareRootPostCrossingPrimeCancelledTerm R K j z)

/-- The oriented, prime-cancelled Gram is exactly the coupled-tail energy. -/
theorem squareRootPostCrossingPrimeCancelledGram_eq_tail_mul_conj
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingPrimeCancelledGram R K j =
      squareRootPostCrossingCoupledTail R K j *
        conj (squareRootPostCrossingCoupledTail R K j) := by
  rw [squareRootPostCrossingCoupledTail_eq_primeCancelledRow
    R K j hR hK hKR]
  unfold squareRootPostCrossingPrimeCancelledGram
    squareRootPostCrossingPrimeCancelledTerm
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]

/-- Real norm-square form of the exact prime-cancelled Gram identity. -/
theorem squareRootPostCrossingPrimeCancelledGram_eq_tail_norm_sq
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingPrimeCancelledGram R K j =
      ((‖squareRootPostCrossingCoupledTail R K j‖ ^ 2 : ℝ) : ℂ) := by
  rw [squareRootPostCrossingPrimeCancelledGram_eq_tail_mul_conj
    R K j hR hK hKR, Complex.mul_conj']
  norm_cast

/-- One summand of the universal canonical rough-prime row. -/
def squareRootPostCrossingCanonicalRoughTerm
    (R K j y : ℕ) : ℂ :=
  squareRootPostCrossingCanonicalRoughCoefficient R K j y *
    mertensSummatory y

/-- The final orientation-free nonlocal Gram.  The `c = 1` diagonal deletion,
all canonical rough-prime descendants, and every cross-scale interaction stay
inside this double sum. -/
def squareRootPostCrossingCanonicalRoughGram
    (R K j : ℕ) : ℂ :=
  ∑ y ∈ Finset.Icc 1 (R - 1),
    ∑ z ∈ Finset.Icc 1 (R - 1),
      squareRootPostCrossingCanonicalRoughTerm R K j y *
        conj (squareRootPostCrossingCanonicalRoughTerm R K j z)

/-- The canonical rough-prime Gram is exactly the coupled-tail energy. -/
theorem squareRootPostCrossingCanonicalRoughGram_eq_tail_mul_conj
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingCanonicalRoughGram R K j =
      squareRootPostCrossingCoupledTail R K j *
        conj (squareRootPostCrossingCoupledTail R K j) := by
  rw [squareRootPostCrossingCoupledTail_eq_canonicalRoughRow
    R K j hR hK hKR]
  unfold squareRootPostCrossingCanonicalRoughGram
    squareRootPostCrossingCanonicalRoughTerm
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]

/-- Real norm-square form of the canonical rough-prime Gram identity. -/
theorem squareRootPostCrossingCanonicalRoughGram_eq_tail_norm_sq
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingCanonicalRoughGram R K j =
      ((‖squareRootPostCrossingCoupledTail R K j‖ ^ 2 : ℝ) : ℂ) := by
  rw [squareRootPostCrossingCanonicalRoughGram_eq_tail_mul_conj
    R K j hR hK hKR, Complex.mul_conj']
  norm_cast

/-- One lower-scale summand in the post-crossing replacement row. -/
def squareRootPostCrossingReplacementTerm
    (R K j y : ℕ) : ℂ :=
  squareRootPostCrossingReplacementCoefficient R K j y *
    mertensSummatory y

/-- The complete signed Gram of the post-crossing replacement row.  Both
indices remain inside one double sum, so no diagonal/off-diagonal separation
has occurred. -/
def squareRootPostCrossingReplacementGram
    (R K j : ℕ) : ℂ :=
  ∑ y ∈ Finset.range R,
    ∑ z ∈ Finset.range R,
      squareRootPostCrossingReplacementTerm R K j y *
        conj (squareRootPostCrossingReplacementTerm R K j z)

/-- The nonlocal replacement Gram is exactly the coupled-tail energy before
coercing the real norm square into an inequality. -/
theorem squareRootPostCrossingReplacementGram_eq_tail_mul_conj
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingReplacementGram R K j =
      squareRootPostCrossingCoupledTail R K j *
        conj (squareRootPostCrossingCoupledTail R K j) := by
  rw [squareRootPostCrossingCoupledTail_eq_replacementRow
    R K j hR hK hKR]
  unfold squareRootPostCrossingReplacementGram
    squareRootPostCrossingReplacementTerm
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]

/-- Real-energy form of the exact signed Gram identity. -/
theorem squareRootPostCrossingReplacementGram_eq_tail_norm_sq
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingReplacementGram R K j =
      ((‖squareRootPostCrossingCoupledTail R K j‖ ^ 2 : ℝ) : ℂ) := by
  rw [squareRootPostCrossingReplacementGram_eq_tail_mul_conj
    R K j hR hK hKR, Complex.mul_conj']
  norm_cast

end RHLean.Proof
