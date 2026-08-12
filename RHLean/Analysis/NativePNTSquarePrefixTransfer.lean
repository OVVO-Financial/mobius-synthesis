import Mathlib
import RHLean.Analysis.NativePNTTransfer
import RHLean.Analysis.NativePNTSquarePrefixPNT

/-!
# Square-prefix Möbius transfer from `psi` to the prime-counting PNT

`NativePNTSquarePrefixPNT` closes the fully rederived square-prefix Möbius
architecture at the Chebyshev endpoint `psi(N) / N -> 1`.  This file performs
the remaining elementary transfer to `theta` and then to `pi` without invoking
the pre-existing `nativeTheta_div_atTop_one` or `nativePrimeNumberTheorem`.

The only imported transfer facts used below are elementary statements proved
independently of PNT: the `psi - theta = o(N)` bridge, the weak Chebyshev bound,
the finite prime-set cardinality identity, and `theta <= pi log`.

The three private cutoff lemmas from `NativePNTTransfer` are re-established
locally so that the final theorem has an explicit dependency path from
`nativePNTSquarePrefixPsi_div_atTop_one` all the way to the prime-counting PNT.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace RHLean.Analysis

/-- **Square-prefix Möbius theta PNT:** the fully rederived `psi` limit transfers
through the elementary prime-power correction to `theta(N) / N -> 1`. -/
theorem nativePNTSquarePrefixTheta_div_atTop_one :
    Tendsto (fun N : ℕ => nativeTheta N / (N : ℝ)) atTop (𝓝 1) :=
  nativeTheta_div_atTop_one_iff.2 nativePNTSquarePrefixPsi_div_atTop_one

/-! ## Elementary multiplicative cutoff, re-established locally -/

/-- Division by a fixed positive natural tends to infinity. -/
private theorem nativePNTSquarePrefixNatDiv_tendsto_atTop
    (K : ℕ) (hK : 0 < K) :
    Tendsto (fun N : ℕ => N / K) atTop atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop (b * K)] with N hN
  exact (Nat.le_div_iff_mul_le hK).2 (by simpa [Nat.mul_comm] using hN)

/-- Once `N / K` is at least `2K`, its logarithm is at least half the
logarithm of `N`.  This is the only floor-loss estimate needed below. -/
private theorem nativePNTSquarePrefixLog_le_two_log_natDiv
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
private theorem nativePNTSquarePrefixPrimeCounting_mul_log_le_scaledTheta_add_small
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

/-- Elementary `theta -> pi` transfer parameterized by the sole asymptotic
input it needs.  This theorem does not invoke either pre-existing PNT endpoint. -/
theorem nativePrimeNumberTheorem_of_theta_div_atTop_one
    (htheta : Tendsto (fun N : ℕ => nativeTheta N / (N : ℝ)) atTop (𝓝 1)) :
    Tendsto
      (fun N : ℕ =>
        (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hthetaLow : ∀ᶠ N : ℕ in atTop,
        a < nativeTheta N / (N : ℝ) :=
      (tendsto_order.1 htheta).1 a ha
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
    have hMtop := nativePNTSquarePrefixNatDiv_tendsto_atTop K hKpos
    have hcheb : ∀ᶠ N : ℕ in atTop,
        (Nat.primeCounting (N / K) : ℝ) *
            Real.log ((N / K : ℕ) : ℝ) ≤
          8 * ((N / K : ℕ) : ℝ) :=
      hMtop.eventually nativePrimeCounting_mul_log_eventually_le_eight
    have hMlarge : ∀ᶠ N : ℕ in atTop, 2 * K ≤ N / K :=
      hMtop.eventually (eventually_ge_atTop (2 * K))
    have hthetaUp : ∀ᶠ N : ℕ in atTop,
        nativeTheta N / (N : ℝ) < 1 + delta :=
      (tendsto_order.1 htheta).2 (1 + delta) (by linarith)
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
    have hsplit :=
      nativePNTSquarePrefixPrimeCounting_mul_log_le_scaledTheta_add_small
        N K A hN hKone hAone hlogCond
    have hlogDiv :=
      nativePNTSquarePrefixLog_le_two_log_natDiv N K hKone hMlargeN
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

/-- **Fully wired square-prefix Möbius Prime Number Theorem:**
`pi(N) log N / N -> 1`, with the asymptotic input coming from the fully
rederived square-prefix reciprocal-fibre architecture. -/
theorem nativePNTSquarePrefixPrimeNumberTheorem :
    Tendsto
      (fun N : ℕ =>
        (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 1) :=
  nativePrimeNumberTheorem_of_theta_div_atTop_one
    nativePNTSquarePrefixTheta_div_atTop_one

end RHLean.Analysis
