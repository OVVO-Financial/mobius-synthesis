import Mathlib
import RHLean.Analysis.NativePNTErdosContraction

/-!
# Elementary `psi`/`theta`/`pi` transfer

The Selberg--Erdos endgame runs on the prime-power mass `psi`.  The prime
number theorem is a statement about the prime mass `theta`, and then about the
prime counting function.  This module supplies the elementary bridge, using
only the square-root confinement of repeated prime powers, the native
Chebyshev upper bound, and finite prime-set decompositions.

No theorem asserting PNT is imported or used here.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace RHLean.Analysis

/-- Every prime at most `N` carries multiplicity at least one in `psi`, so the
prime layer never exceeds the prime-power layer. -/
theorem nativeTheta_le_psi (N : ℕ) : nativeTheta N ≤ nativePsi N := by
  rw [nativePsi_eq_sum_mul_log_prime]
  unfold nativeTheta
  apply Finset.sum_le_sum
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpPrime⟩
  have hpN : p ≤ N := (Finset.mem_Icc.mp hpIcc).2
  have hlogpos : 0 < p.log N := Nat.log_pos hpPrime.one_lt hpN
  have hone : (1 : ℝ) ≤ ((p.log N : ℕ) : ℝ) := by exact_mod_cast hlogpos
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
  have hmul := mul_le_mul_of_nonneg_right hone hlogp
  linarith

/-- `log x / sqrt x -> 0`, the only limit input needed by the transfer. -/
theorem nativeLog_div_sqrt_atTop :
    Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  have h := isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)
  have htend := h.tendsto_div_nhds_zero
  simpa only [← Real.sqrt_eq_rpow] using htend

/-- The same limit read along the natural numbers. -/
theorem nativeLog_div_sqrt_natCast_atTop :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / Real.sqrt (N : ℝ)) atTop (𝓝 0) :=
  nativeLog_div_sqrt_atTop.comp tendsto_natCast_atTop_atTop

/-- **The prime-power correction is `o(N)`.**  All repeated prime powers live
below the square-root cutoff, so `psi - theta` is at most `sqrt N log N`. -/
theorem nativePsi_sub_theta_div_atTop :
    Tendsto (fun N : ℕ => (nativePsi N - nativeTheta N) / (N : ℝ))
      atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ nativeLog_div_sqrt_natCast_atTop
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact div_nonneg (sub_nonneg.mpr (nativeTheta_le_psi N)) hNpos.le
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hbound := nativePsi_le_theta_add_sqrt_log N hN
    have hlogN : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    have hsqrtpos : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
    have hsplit : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
      Real.mul_self_sqrt hNpos.le
    have hsqrtNat : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
      have hsqrtNatSq : (Nat.sqrt N) ^ 2 ≤ N := Nat.sqrt_le' N
      have hsq : ((Nat.sqrt N : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) := by
        exact_mod_cast hsqrtNatSq
      have hrealSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := by
        rw [Real.sq_sqrt]
        positivity
      have hleft : 0 ≤ ((Nat.sqrt N : ℕ) : ℝ) := by positivity
      have hright : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      nlinarith
    have h1 : nativePsi N - nativeTheta N ≤
        ((Nat.sqrt N : ℕ) : ℝ) * Real.log (N : ℝ) := by linarith
    have h2 : ((Nat.sqrt N : ℕ) : ℝ) * Real.log (N : ℝ) ≤
        Real.sqrt (N : ℝ) * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right hsqrtNat hlogN
    have h3 : nativePsi N - nativeTheta N ≤
        Real.sqrt (N : ℝ) * Real.log (N : ℝ) := h1.trans h2
    rw [div_le_div_iff₀ hNpos hsqrtpos]
    calc (nativePsi N - nativeTheta N) * Real.sqrt (N : ℝ)
        ≤ (Real.sqrt (N : ℝ) * Real.log (N : ℝ)) * Real.sqrt (N : ℝ) :=
          mul_le_mul_of_nonneg_right h3 hsqrtpos.le
      _ = Real.log (N : ℝ) * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by ring
      _ = Real.log (N : ℝ) * (N : ℝ) := by rw [hsplit]

/-- **`theta ~ N` if and only if `psi ~ N`.**  The endgame may therefore be run
on whichever of the two masses is more convenient. -/
theorem nativeTheta_div_atTop_one_iff :
    Tendsto (fun N : ℕ => nativeTheta N / (N : ℝ)) atTop (𝓝 1) ↔
      Tendsto (fun N : ℕ => nativePsi N / (N : ℝ)) atTop (𝓝 1) := by
  have hfwd : ∀ N : ℕ,
      nativeTheta N / (N : ℝ) + (nativePsi N - nativeTheta N) / (N : ℝ) =
        nativePsi N / (N : ℝ) := by
    intro N
    rw [← add_div]
    congr 1
    ring
  have hback : ∀ N : ℕ,
      nativePsi N / (N : ℝ) - (nativePsi N - nativeTheta N) / (N : ℝ) =
        nativeTheta N / (N : ℝ) := by
    intro N
    rw [div_sub_div_same]
    congr 1
    ring
  constructor
  · intro h
    have hsum := h.add nativePsi_sub_theta_div_atTop
    rw [add_zero] at hsum
    simpa only [hfwd] using hsum
  · intro h
    have hdiff := h.sub nativePsi_sub_theta_div_atTop
    rw [sub_zero] at hdiff
    simpa only [hback] using hdiff

/-- **Native theta PNT:** `theta(N) / N -> 1`. -/
theorem nativeTheta_div_atTop_one :
    Tendsto (fun N : ℕ => nativeTheta N / (N : ℝ)) atTop (𝓝 1) :=
  nativeTheta_div_atTop_one_iff.2 nativePsi_div_atTop_one

/-! ## Elementary transfer from `theta` to `pi` -/

/-- The native finite prime set has exactly `pi(N)` elements. -/
theorem nativePrimeSet_card_eq_primeCounting (N : ℕ) :
    (nativePrimeSet N).card = Nat.primeCounting N := by
  have hset :
      nativePrimeSet N = (Finset.range (N + 1)).filter Nat.Prime := by
    unfold nativePrimeSet
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
      Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨_hp1, hpN⟩, hpPrime⟩
      exact ⟨hpN, hpPrime⟩
    · rintro ⟨hpN, hpPrime⟩
      exact ⟨⟨hpPrime.one_le, hpN⟩, hpPrime⟩
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  exact congrArg Finset.card hset

/-- The weighted prime mass is bounded by the prime count times the endpoint
logarithm. -/
theorem nativeTheta_le_primeCounting_mul_log (N : ℕ) :
    nativeTheta N ≤
      (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) := by
  unfold nativeTheta
  calc
    (∑ p ∈ nativePrimeSet N, Real.log (p : ℝ)) ≤
        ∑ _p ∈ nativePrimeSet N, Real.log (N : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpPrime⟩
      have hpN : p ≤ N := (Finset.mem_Icc.mp hpIcc).2
      exact Real.log_le_log
        (by exact_mod_cast hpPrime.pos)
        (by exact_mod_cast hpN)
    _ = (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) := by
      rw [← nativePrimeSet_card_eq_primeCounting]
      simp

/-- Square-root splitting gives the classical weak Chebyshev bound needed to
control the small-prime part of the final transfer. -/
private theorem nativePrimeCounting_mul_log_sqrt_le
    (N : ℕ) (hN : 1 ≤ N) :
    (Nat.primeCounting N : ℝ) * Real.log (Real.sqrt (N : ℝ)) ≤
      Real.log 4 * (N : ℝ) +
        Real.sqrt (N : ℝ) * Real.log (Real.sqrt (N : ℝ)) := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  calc
    (Nat.primeCounting N : ℝ) * Real.log (Real.sqrt (N : ℝ)) =
        ∑ _p ∈ nativePrimeSet N, Real.log (Real.sqrt (N : ℝ)) := by
      rw [← nativePrimeSet_card_eq_primeCounting]
      simp
    _ ≤ ∑ p ∈ nativePrimeSet N,
        (Real.log (p : ℝ) +
          if (p : ℝ) ≤ Real.sqrt (N : ℝ) then
            Real.log (Real.sqrt (N : ℝ)) else 0) := by
      apply Finset.sum_le_sum
      intro p _hp
      split_ifs with hpSqrt
      · have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
        linarith
      · have hsqrtpos : 0 < Real.sqrt (N : ℝ) :=
          Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))
        have hlt : Real.sqrt (N : ℝ) < (p : ℝ) := lt_of_not_ge hpSqrt
        have hloglt := Real.log_lt_log hsqrtpos hlt
        linarith
    _ ≤ Real.log 4 * (N : ℝ) +
        Real.sqrt (N : ℝ) * Real.log (Real.sqrt (N : ℝ)) := by
      rw [Finset.sum_add_distrib]
      change nativeTheta N +
          (∑ p ∈ nativePrimeSet N,
            if (p : ℝ) ≤ Real.sqrt (N : ℝ) then
              Real.log (Real.sqrt (N : ℝ)) else 0) ≤
        Real.log 4 * (N : ℝ) +
          Real.sqrt (N : ℝ) * Real.log (Real.sqrt (N : ℝ))
      apply add_le_add (nativeTheta_le_log4_mul N)
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hlogSqrt : 0 ≤ Real.log (Real.sqrt (N : ℝ)) :=
        Real.log_nonneg (by
          have : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (N : ℝ) by positivity),
              Real.sqrt_nonneg (N : ℝ)]
          exact this)
      have hcardNat :
          ((nativePrimeSet N).filter
            (fun p : ℕ => (p : ℝ) ≤ Real.sqrt (N : ℝ))).card ≤
            ⌊Real.sqrt (N : ℝ)⌋₊ := by
        have hsubset :
            (nativePrimeSet N).filter
                (fun p : ℕ => (p : ℝ) ≤ Real.sqrt (N : ℝ)) ⊆
              Finset.Icc 1 ⌊Real.sqrt (N : ℝ)⌋₊ := by
          intro p hp
          rcases Finset.mem_filter.mp hp with ⟨hpSet, hpSqrt⟩
          have hpPrime : p.Prime := (Finset.mem_filter.mp hpSet).2
          exact Finset.mem_Icc.mpr ⟨hpPrime.one_le, Nat.le_floor hpSqrt⟩
        calc
          ((nativePrimeSet N).filter
              (fun p : ℕ => (p : ℝ) ≤ Real.sqrt (N : ℝ))).card ≤
              (Finset.Icc 1 ⌊Real.sqrt (N : ℝ)⌋₊).card :=
            Finset.card_le_card hsubset
          _ = ⌊Real.sqrt (N : ℝ)⌋₊ := by simp
      have hcardReal :
          (((nativePrimeSet N).filter
            (fun p : ℕ => (p : ℝ) ≤ Real.sqrt (N : ℝ))).card : ℝ) ≤
            Real.sqrt (N : ℝ) := by
        have hcardFloorReal :
            (((nativePrimeSet N).filter
              (fun p : ℕ => (p : ℝ) ≤ Real.sqrt (N : ℝ))).card : ℝ) ≤
              (⌊Real.sqrt (N : ℝ)⌋₊ : ℝ) := by
          exact_mod_cast hcardNat
        have hfloorReal :
            (⌊Real.sqrt (N : ℝ)⌋₊ : ℝ) ≤ Real.sqrt (N : ℝ) :=
          Nat.floor_le (Real.sqrt_nonneg _)
        exact hcardFloorReal.trans hfloorReal
      exact mul_le_mul_of_nonneg_right hcardReal hlogSqrt

/-- A fixed weak Chebyshev estimate, sufficient for the cutoff argument below. -/
theorem nativePrimeCounting_mul_log_eventually_le_eight :
    ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) ≤ 8 * (N : ℝ) := by
  have htail : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) / Real.sqrt (N : ℝ) < 1 :=
    (tendsto_order.1 nativeLog_div_sqrt_natCast_atTop).2 1 zero_lt_one
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at this ⊢
    exact this
  filter_upwards [eventually_ge_atTop 2, htail] with N hN htailN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
  have hsqrtpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hroot := nativePrimeCounting_mul_log_sqrt_le N (by omega)
  have hlogsqrt :
      Real.log (Real.sqrt (N : ℝ)) = Real.log (N : ℝ) / 2 :=
    Real.log_sqrt hNnonneg
  rw [hlogsqrt] at hroot
  have hbasic :
      (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) ≤
        2 * Real.log 4 * (N : ℝ) +
          Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
    nlinarith
  have hlogle : Real.log (N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have h := (div_lt_iff₀ hsqrtpos).mp htailN
    linarith
  have hsqrtlog :
      Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤ (N : ℝ) := by
    calc
      Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤
          Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
        mul_le_mul_of_nonneg_left hlogle (Real.sqrt_nonneg _)
      _ = (N : ℝ) := Real.mul_self_sqrt hNnonneg
  have hmain : 2 * Real.log 4 * (N : ℝ) ≤ 6 * (N : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hlog4 hNnonneg
    nlinarith
  calc
    (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) ≤
        2 * Real.log 4 * (N : ℝ) +
          Real.sqrt (N : ℝ) * Real.log (N : ℝ) := hbasic
    _ ≤ 6 * (N : ℝ) + (N : ℝ) := add_le_add hmain hsqrtlog
    _ ≤ 8 * (N : ℝ) := by linarith

/-- Division by a fixed positive natural tends to infinity. -/
private theorem nativeNatDiv_tendsto_atTop (K : ℕ) (hK : 0 < K) :
    Tendsto (fun N : ℕ => N / K) atTop atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop (b * K)] with N hN
  exact (Nat.le_div_iff_mul_le hK).2 (by simpa [Nat.mul_comm] using hN)

/-- Once `N / K` is at least `2K`, its logarithm is at least half the
logarithm of `N`.  This is the only floor-loss estimate needed in the cutoff. -/
private theorem nativeLog_le_two_log_natDiv
    (N K : ℕ) (hK : 1 ≤ K) (hM : 2 * K ≤ N / K) :
    Real.log (N : ℝ) ≤ 2 * Real.log ((N / K : ℕ) : ℝ) := by
  let M : ℕ := N / K
  have hKpos : 0 < K := by omega
  have hM' : 2 * K ≤ M := by simpa [M] using hM
  have hMpos : 0 < M := by omega
  have hdiv : K * M + N % K = N := by
    dsimp [M]
    exact Nat.div_add_mod N K
  have hrem : N % K < K := Nat.mod_lt N hKpos
  have hNlt : N < (2 * K) * M := by
    calc
      N = K * M + N % K := hdiv.symm
      _ < K * M + K := Nat.add_lt_add_left hrem _
      _ = K * (M + 1) := by ring
      _ ≤ K * (2 * M) := Nat.mul_le_mul_left K (by omega)
      _ = (2 * K) * M := by ring
  have hKMle : K * M ≤ N := by
    dsimp [M]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self N K
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hKMpos : 0 < K * M := Nat.mul_pos hKpos hMpos
    have hNposNat : 0 < N := lt_of_lt_of_le hKMpos hKMle
    exact_mod_cast hNposNat
  have hcast :
      (N : ℝ) < (((2 * K : ℕ) : ℝ) * (M : ℝ)) := by
    exact_mod_cast hNlt
  have hloglt := Real.log_lt_log hNpos hcast
  have h2Kpos : (0 : ℝ) < ((2 * K : ℕ) : ℝ) := by positivity
  have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hlogmul :
      Real.log (((2 * K : ℕ) : ℝ) * (M : ℝ)) =
        Real.log ((2 * K : ℕ) : ℝ) + Real.log (M : ℝ) :=
    Real.log_mul (ne_of_gt h2Kpos) (ne_of_gt hMposR)
  rw [hlogmul] at hloglt
  have h2KleM : ((2 * K : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM'
  have hlogle := Real.log_le_log h2Kpos h2KleM
  change Real.log (N : ℝ) ≤ 2 * Real.log (M : ℝ)
  linarith

/-- A finite multiplicative cutoff inequality.  Primes with `K p > N` each
carry almost the full endpoint logarithm; the remaining primes are counted at
`N / K`. -/
private theorem nativePrimeCounting_mul_log_le_scaledTheta_add_small
    (N K : ℕ) (A : ℝ)
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hA : 1 ≤ A)
    (hlogK :
      A * Real.log (K : ℝ) ≤
        (A - 1) * Real.log (N : ℝ)) :
    (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) ≤
      A * nativeTheta N +
        (Nat.primeCounting (N / K) : ℝ) * Real.log (N : ℝ) := by
  have hKpos : 0 < K := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hsum :
      (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) ≤
        A * nativeTheta N +
          (((nativePrimeSet N).filter (fun p => K * p ≤ N)).card : ℕ) *
            Real.log (N : ℝ) := by
    calc
      (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) =
          ∑ _p ∈ nativePrimeSet N, Real.log (N : ℝ) := by
        rw [← nativePrimeSet_card_eq_primeCounting]
        simp
      _ ≤ ∑ p ∈ nativePrimeSet N,
          (A * Real.log (p : ℝ) +
            if K * p ≤ N then Real.log (N : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
        split_ifs with hsmall
        · have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
          have hmul : 0 ≤ A * Real.log (p : ℝ) := mul_nonneg hApos.le hlogp
          linarith
        · have hlarge : N < K * p := lt_of_not_ge hsmall
          have hpPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
          have hKPosR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
          have hcast : (N : ℝ) < (K : ℝ) * (p : ℝ) := by exact_mod_cast hlarge
          have hloglt := Real.log_lt_log hNpos hcast
          have hlogmul :
              Real.log ((K : ℝ) * (p : ℝ)) =
                Real.log (K : ℝ) + Real.log (p : ℝ) :=
            Real.log_mul (ne_of_gt hKPosR) (ne_of_gt hpPos)
          rw [hlogmul] at hloglt
          have hmul := mul_lt_mul_of_pos_left hloglt hApos
          linarith
      _ = A * nativeTheta N +
          (((nativePrimeSet N).filter (fun p => K * p ≤ N)).card : ℕ) *
            Real.log (N : ℝ) := by
        rw [Finset.sum_add_distrib]
        have hfirst :
            (∑ p ∈ nativePrimeSet N, A * Real.log (p : ℝ)) =
              A * nativeTheta N := by
          unfold nativeTheta
          rw [Finset.mul_sum]
        rw [hfirst]
        congr 1
        rw [← Finset.sum_filter]
        simp
  have hsmallCard :
      ((nativePrimeSet N).filter (fun p => K * p ≤ N)).card ≤
        Nat.primeCounting (N / K) := by
    rw [← nativePrimeSet_card_eq_primeCounting]
    apply Finset.card_le_card
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpSet, hsmall⟩
    rcases Finset.mem_filter.mp hpSet with ⟨hpIcc, hpPrime⟩
    refine Finset.mem_filter.mpr ⟨?_, hpPrime⟩
    refine Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hpIcc).1, ?_⟩
    exact (Nat.le_div_iff_mul_le hKpos).2 (by simpa [Nat.mul_comm] using hsmall)
  have hsmallReal :
      ((((nativePrimeSet N).filter (fun p => K * p ≤ N)).card : ℕ) : ℝ) ≤
        (Nat.primeCounting (N / K) : ℝ) := by exact_mod_cast hsmallCard
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  exact hsum.trans (add_le_add_left
    (mul_le_mul_of_nonneg_right hsmallReal hlogN) (A * nativeTheta N))

/-- **Prime Number Theorem.**  The native Selberg--Erdos proof gives
`theta(N) / N -> 1`.  A finite multiplicative cutoff, together with the weak
Chebyshev estimate above, then squeezes `pi(N) log N / N` to the same limit. -/
theorem nativePrimeNumberTheorem :
    Tendsto
      (fun N : ℕ =>
        (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hthetaLow : ∀ᶠ N : ℕ in atTop,
        a < nativeTheta N / (N : ℝ) :=
      (tendsto_order.1 nativeTheta_div_atTop_one).1 a ha
    filter_upwards [eventually_ge_atTop 1, hthetaLow] with N hN hlow
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hthetaPi := nativeTheta_le_primeCounting_mul_log N
    have hnorm :
        nativeTheta N / (N : ℝ) ≤
          ((Nat.primeCounting N : ℝ) * Real.log (N : ℝ)) / (N : ℝ) :=
      div_le_div_of_nonneg_right hthetaPi hNpos.le
    exact hlow.trans_le hnorm
  · intro b hb
    let gap : ℝ := b - 1
    have hgap : 0 < gap := by dsimp [gap]; linarith
    let delta : ℝ := min (gap / 8) (1 / 2)
    have hdelta : 0 < delta := by
      dsimp [delta]
      exact lt_min (div_pos hgap (by norm_num)) (by norm_num)
    have hdeltaGap : delta ≤ gap / 8 := by
      dsimp [delta]
      exact min_le_left _ _
    have hdeltaOne : delta ≤ 1 := by
      have hhalf : delta ≤ (1 / 2 : ℝ) := by
        dsimp [delta]
        exact min_le_right _ _
      linarith
    let A : ℝ := 1 + delta
    have hAone : 1 ≤ A := by dsimp [A]; linarith
    have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hAone
    obtain ⟨K : ℕ, hKnat⟩ := exists_nat_gt (32 / gap)
    have hKreal : 32 / gap < (K : ℝ) := by exact_mod_cast hKnat
    have hKpos : 0 < K := by
      have hquot : 0 < (32 / gap : ℝ) := div_pos (by norm_num) hgap
      have : (0 : ℝ) < K := hquot.trans hKreal
      exact_mod_cast this
    have hKone : 1 ≤ K := Nat.one_le_iff_ne_zero.2 hKpos.ne'
    have hMtop := nativeNatDiv_tendsto_atTop K hKpos
    have hcheb : ∀ᶠ N : ℕ in atTop,
        (Nat.primeCounting (N / K) : ℝ) *
            Real.log ((N / K : ℕ) : ℝ) ≤
          8 * ((N / K : ℕ) : ℝ) :=
      hMtop.eventually nativePrimeCounting_mul_log_eventually_le_eight
    have hMlarge : ∀ᶠ N : ℕ in atTop, 2 * K ≤ N / K :=
      hMtop.eventually (eventually_ge_atTop (2 * K))
    have hthetaUp : ∀ᶠ N : ℕ in atTop,
        nativeTheta N / (N : ℝ) < 1 + delta :=
      (tendsto_order.1 nativeTheta_div_atTop_one).2 (1 + delta) (by linarith)
    have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hlogLarge : ∀ᶠ N : ℕ in atTop,
        A * Real.log (K : ℝ) / delta ≤ Real.log (N : ℝ) :=
      hlogTop.eventually_ge_atTop (A * Real.log (K : ℝ) / delta)
    filter_upwards [eventually_ge_atTop 1, hcheb, hMlarge, hthetaUp, hlogLarge]
      with N hN hchebN hMlargeN hthetaN hlogN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hdeltaNe : delta ≠ 0 := ne_of_gt hdelta
    have hlogMul := mul_le_mul_of_nonneg_left hlogN hdelta.le
    have hleft :
        delta * (A * Real.log (K : ℝ) / delta) =
          A * Real.log (K : ℝ) := by
      field_simp [hdeltaNe]
    rw [hleft] at hlogMul
    have hlogCond :
        A * Real.log (K : ℝ) ≤
          (A - 1) * Real.log (N : ℝ) := by
      have hAdelta : A - 1 = delta := by dsimp [A]; ring
      rw [hAdelta]
      exact hlogMul
    have hsplit := nativePrimeCounting_mul_log_le_scaledTheta_add_small
      N K A hN hKone hAone hlogCond
    have hlogDiv := nativeLog_le_two_log_natDiv N K hKone hMlargeN
    have hsmall :
        (Nat.primeCounting (N / K) : ℝ) * Real.log (N : ℝ) ≤
          gap / 2 * (N : ℝ) := by
      have hpiNonneg : 0 ≤ (Nat.primeCounting (N / K) : ℝ) := by positivity
      have hKMnat : K * (N / K) ≤ N := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self N K
      have hKM : (K : ℝ) * ((N / K : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hKMnat
      have hKg : 32 < gap * (K : ℝ) := by
        have := (div_lt_iff₀ hgap).mp hKreal
        simpa [mul_comm] using this
      have hcoef : (16 : ℝ) ≤ gap / 2 * (K : ℝ) := by
        nlinarith
      calc
        (Nat.primeCounting (N / K) : ℝ) * Real.log (N : ℝ) ≤
            (Nat.primeCounting (N / K) : ℝ) *
              (2 * Real.log ((N / K : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogDiv hpiNonneg
        _ = 2 * ((Nat.primeCounting (N / K) : ℝ) *
              Real.log ((N / K : ℕ) : ℝ)) := by ring
        _ ≤ 2 * (8 * ((N / K : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hchebN (by norm_num)
        _ = 16 * ((N / K : ℕ) : ℝ) := by ring
        _ ≤ (gap / 2 * (K : ℝ)) * ((N / K : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ = gap / 2 * ((K : ℝ) * ((N / K : ℕ) : ℝ)) := by ring
        _ ≤ gap / 2 * (N : ℝ) :=
          mul_le_mul_of_nonneg_left hKM (by positivity)
    have hthetaScale :
        nativeTheta N ≤ (1 + delta) * (N : ℝ) := by
      exact ((div_lt_iff₀ hNpos).mp hthetaN).le
    have hscaled :
        A * nativeTheta N ≤ A * ((1 + delta) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hthetaScale hApos.le
    have hdeltaSq : delta ^ 2 ≤ delta := by
      have := mul_nonneg hdelta.le (sub_nonneg.mpr hdeltaOne)
      nlinarith
    have hcoefFinal : A * (1 + delta) + gap / 2 < 1 + gap := by
      dsimp [A]
      nlinarith [hdeltaGap, hdeltaSq, hgap]
    have htotal :
        (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) <
          (1 + gap) * (N : ℝ) := by
      calc
        (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) ≤
            A * nativeTheta N +
              (Nat.primeCounting (N / K) : ℝ) * Real.log (N : ℝ) := hsplit
        _ ≤ A * ((1 + delta) * (N : ℝ)) + gap / 2 * (N : ℝ) :=
          add_le_add hscaled hsmall
        _ = (A * (1 + delta) + gap / 2) * (N : ℝ) := by ring
        _ < (1 + gap) * (N : ℝ) :=
          mul_lt_mul_of_pos_right hcoefFinal hNpos
    have hbgap : 1 + gap = b := by dsimp [gap]; ring
    rw [div_lt_iff₀ hNpos]
    simpa [hbgap] using htotal

end RHLean.Analysis
