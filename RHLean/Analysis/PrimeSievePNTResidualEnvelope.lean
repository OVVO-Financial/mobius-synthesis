import Mathlib
import RHLean.Analysis.NativePNTTransfer
import RHLean.Analysis.PrimeSieveLipschitzExcursion
import RHLean.Analysis.PrimeSieveDyadicPacketShallowDeep

/-!
# Native PNT residual transport into the recursive packet tree

The native Selberg--Erdos development already proves the prime number theorem,
while the prime-sieve packet route is written in the clipped classical discrepancy

`R(t) = pi(t) - Li(t)`.

This module reconnects those two pieces without introducing another coordinate.
It proves unconditionally that

`||R(t)|| / (t + 1) -> 0`,

then transports that asymptotic uniformly to every clipped reciprocal value
`R(max y (x / d))` once the prime cutoff `y` is large.

The second half defines a dimensionless recursive packet-residual envelope.  A
separate deep envelope skips the first `J` midpoint levels and measures the
largest normalized residual left below the cutoff.  The exact recursion is
public, and the native PNT implies that this entire deep envelope is arbitrarily
small once `y` is large, uniformly in `x`, interval, tree depth, and cutoff.

This is only a qualitative localization theorem.  It does **not** turn
`o(x)` into the critical packet-energy estimate.  The remaining analytic task is
quantitative contraction of the already-small deep residual envelope strongly
enough to sum its energy at the `X^(1+epsilon)` scale.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace RHLean.Analysis

/-! ## The classical prime discrepancy is relatively small -/

/-- The prime-sieve prefix count is the ordinary prime-counting function. -/
theorem primeSievePrefixPrimeCount_eq_primeCounting (N : ℕ) :
    primeSievePrefixPrimeCount N = (Nat.primeCounting N : ℂ) := by
  have hset :
      (Finset.Ioc 0 N).filter Nat.Prime = nativePrimeSet N := by
    unfold nativePrimeSet
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp0, hpN⟩, hpPrime⟩
      exact ⟨⟨by omega, hpN⟩, hpPrime⟩
    · rintro ⟨⟨hp1, hpN⟩, hpPrime⟩
      exact ⟨⟨by omega, hpN⟩, hpPrime⟩
  have hcard : ((Finset.Ioc 0 N).filter Nat.Prime).card = Nat.primeCounting N := by
    rw [hset, nativePrimeSet_card_eq_primeCounting]
  rw [primeSievePrefixPrimeCount_eq_card]
  exact_mod_cast hcard

/-- The ordinary prime count itself is `o(N)`.  This is read from the native
PNT through the already-proved eventual Chebyshev bound.  The denominator
`N+1` avoids a special case at zero and is the normalization used below. -/
theorem nativePrimeCounting_div_succ_atTop_zero :
    Tendsto
      (fun N : ℕ => (Nat.primeCounting N : ℝ) / ((N : ℝ) + 1))
      atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [] with N
    exact ha.trans_le (div_nonneg (by positivity) (by positivity))
  · intro b hb
    have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hlogLarge : ∀ᶠ N : ℕ in atTop,
        8 / b < Real.log (N : ℝ) :=
      hlogTop.eventually (eventually_gt_atTop (8 / b))
    filter_upwards [eventually_ge_atTop 2,
      nativePrimeCounting_mul_log_eventually_le_eight, hlogLarge]
      with N hN hpi hlog
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have h8 : (8 : ℝ) < b * Real.log (N : ℝ) := by
      have := (div_lt_iff₀ hb).mp hlog
      nlinarith
    have h8N : (8 : ℝ) * (N : ℝ) <
        (b * (N : ℝ)) * Real.log (N : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right h8 hNpos
      nlinarith
    have hpiN : (Nat.primeCounting N : ℝ) < b * (N : ℝ) := by
      have hmul :
          (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) <
            (b * (N : ℝ)) * Real.log (N : ℝ) := hpi.trans_lt h8N
      by_contra hnot
      have hge : b * (N : ℝ) ≤ (Nat.primeCounting N : ℝ) := le_of_not_gt hnot
      have hge' := mul_le_mul_of_nonneg_right hge hlogpos.le
      exact (not_lt_of_ge hge') hmul
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    have hbN : b * (N : ℝ) < b * ((N : ℝ) + 1) := by
      nlinarith
    exact hpiN.trans hbN

/-- The repository's logarithmic integral is also `o(N)`.  The proof uses a
fixed split point depending on the requested error: the initial integral is a
fixed constant, while the tail has density at most `1 / log A`. -/
theorem logarithmicIntegralFromTwo_abs_div_succ_atTop_zero :
    Tendsto
      (fun N : ℕ =>
        |logarithmicIntegralFromTwo (N : ℝ)| / ((N : ℝ) + 1))
      atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [] with N
    exact ha.trans_le (div_nonneg (abs_nonneg _) (by positivity))
  · intro b hb
    have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hlogLarge : ∀ᶠ A : ℕ in atTop,
        2 / b < Real.log (A : ℝ) :=
      hlogTop.eventually (eventually_gt_atTop (2 / b))
    rcases (eventually_atTop.1 hlogLarge) with ⟨A0, hA0⟩
    let A : ℕ := max 2 A0
    have hA2 : 2 ≤ A := by dsimp [A]; exact le_max_left _ _
    have hA0A : A0 ≤ A := by dsimp [A]; exact le_max_right _ _
    have hlogA : 2 / b < Real.log (A : ℝ) := hA0 A hA0A
    have hlogApos : 0 < Real.log (A : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < A by omega))
    let C : ℝ := |logarithmicIntegralFromTwo (A : ℝ)|
    have hC0 : 0 ≤ C := by dsimp [C]; positivity
    obtain ⟨M : ℕ, hMnat⟩ := exists_nat_gt (2 * C / b)
    have hM : 2 * C / b < (M : ℝ) := by exact_mod_cast hMnat
    filter_upwards [eventually_ge_atTop (max A M)] with N hN
    have hAN : A ≤ N := (le_max_left A M).trans hN
    have hMN : M ≤ N := (le_max_right A M).trans hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hdiff := abs_logarithmicIntegralFromTwo_sub_le
      (a := (A : ℝ)) (b := (N : ℝ))
      (by exact_mod_cast hA2) (by exact_mod_cast hAN)
    have hdiff' :
        |logarithmicIntegralFromTwo (N : ℝ) -
            logarithmicIntegralFromTwo (A : ℝ)| ≤
          (N : ℝ) / Real.log (A : ℝ) := by
      calc
        |logarithmicIntegralFromTwo (N : ℝ) -
            logarithmicIntegralFromTwo (A : ℝ)| ≤
            ((N : ℝ) - (A : ℝ)) / Real.log (A : ℝ) := hdiff
        _ ≤ (N : ℝ) / Real.log (A : ℝ) := by
          have hnum : (N : ℝ) - (A : ℝ) ≤ (N : ℝ) := by
            have hA0R : (0 : ℝ) ≤ (A : ℝ) := by positivity
            linarith
          exact div_le_div_of_nonneg_right hnum hlogApos.le
    have hLi :
        |logarithmicIntegralFromTwo (N : ℝ)| ≤
          C + (N : ℝ) / Real.log (A : ℝ) := by
      have htri := abs_add_le
        (logarithmicIntegralFromTwo (N : ℝ) -
          logarithmicIntegralFromTwo (A : ℝ))
        (logarithmicIntegralFromTwo (A : ℝ))
      have heq :
          logarithmicIntegralFromTwo (N : ℝ) -
              logarithmicIntegralFromTwo (A : ℝ) +
            logarithmicIntegralFromTwo (A : ℝ) =
          logarithmicIntegralFromTwo (N : ℝ) := by ring
      rw [heq] at htri
      dsimp [C]
      linarith [hdiff']
    have hMreal : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
    have hCsmall : C < (b / 2) * ((N : ℝ) + 1) := by
      have hraw0 := (div_lt_iff₀ hb).mp hM
      have hraw : 2 * C < b * (M : ℝ) := by
        simpa [mul_comm] using hraw0
      have hrawN : 2 * C < b * (N : ℝ) :=
        hraw.trans_le (mul_le_mul_of_nonneg_left hMreal hb.le)
      nlinarith
    have hfactor : 1 < (b / 2) * Real.log (A : ℝ) := by
      have hraw0 := (div_lt_iff₀ hb).mp hlogA
      have hraw : (2 : ℝ) < b * Real.log (A : ℝ) := by
        simpa [mul_comm] using hraw0
      nlinarith
    have hvar :
        (N : ℝ) / Real.log (A : ℝ) < (b / 2) * (N : ℝ) := by
      rw [div_lt_iff₀ hlogApos]
      have hmul := mul_lt_mul_of_pos_left hfactor hNpos
      nlinarith
    have htarget :
        |logarithmicIntegralFromTwo (N : ℝ)| < b * ((N : ℝ) + 1) := by
      nlinarith [hLi]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    exact htarget

/-- **Relative classical discrepancy vanishes.**  This is the exact `pi-Li`
field used by the reciprocal packet development, not the Chebyshev residual. -/
theorem primeSievePrimeDiscrepancy_norm_div_succ_atTop_zero :
    Tendsto
      (fun N : ℕ => ‖primeSievePrimeDiscrepancy N‖ / ((N : ℝ) + 1))
      atTop (𝓝 0) := by
  have hsum := nativePrimeCounting_div_succ_atTop_zero.add
    logarithmicIntegralFromTwo_abs_div_succ_atTop_zero
  rw [add_zero] at hsum
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [] with N
    exact div_nonneg (norm_nonneg _) (by positivity)
  · filter_upwards [] with N
    have hnorm :
        ‖primeSievePrimeDiscrepancy N‖ ≤
          (Nat.primeCounting N : ℝ) +
            |logarithmicIntegralFromTwo (N : ℝ)| := by
      unfold primeSievePrimeDiscrepancy
      rw [primeSievePrefixPrimeCount_eq_primeCounting]
      calc
        ‖(Nat.primeCounting N : ℂ) -
            ((logarithmicIntegralFromTwo (N : ℝ) : ℝ) : ℂ)‖ ≤
            ‖(Nat.primeCounting N : ℂ)‖ +
              ‖((logarithmicIntegralFromTwo (N : ℝ) : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
        _ = (Nat.primeCounting N : ℝ) +
            |logarithmicIntegralFromTwo (N : ℝ)| := by simp
    rw [← add_div]
    exact div_le_div_of_nonneg_right hnorm (by positivity)

/-- Eventual uniform form of the relative discrepancy limit. -/
theorem exists_primeSievePrimeDiscrepancy_relative_cutoff
    (η : ℝ) (hη : 0 < η) :
    ∃ Y : ℕ, ∀ t : ℕ, Y ≤ t →
      ‖primeSievePrimeDiscrepancy t‖ ≤ η * ((t : ℝ) + 1) := by
  have hev : ∀ᶠ t : ℕ in atTop,
      ‖primeSievePrimeDiscrepancy t‖ / ((t : ℝ) + 1) < η :=
    (tendsto_order.1 primeSievePrimeDiscrepancy_norm_div_succ_atTop_zero).2
      η hη
  rcases (eventually_atTop.1 hev) with ⟨Y, hY⟩
  refine ⟨Y, ?_⟩
  intro t ht
  have h := hY t ht
  exact ((div_lt_iff₀ (by positivity : (0 : ℝ) < (t : ℝ) + 1)).mp h).le

/-! ## Uniform transport to the clipped reciprocal field -/

/-- Once the prime cutoff `y` lies beyond a relative-discrepancy threshold,
every clipped reciprocal value is controlled by one global `x+y+1` scale.
This deliberately avoids any support hypothesis; it is valid for every `d`. -/
theorem primeSieveDyadicClippedDiscrepancy_norm_le_globalScale
    {η : ℝ} {Y y x d : ℕ}
    (hη : 0 ≤ η)
    (hEnv : ∀ t : ℕ, Y ≤ t →
      ‖primeSievePrimeDiscrepancy t‖ ≤ η * ((t : ℝ) + 1))
    (hy : Y ≤ y) :
    ‖primeSieveDyadicClippedDiscrepancy y x d‖ ≤
      η * (((x + y : ℕ) : ℝ) + 1) := by
  let t : ℕ := max y (x / d)
  have hYt : Y ≤ t := hy.trans (le_max_left _ _)
  have ht : t ≤ x + y := by
    dsimp [t]
    apply max_le
    · omega
    · exact (Nat.div_le_self x d).trans (by omega)
  have h := hEnv t hYt
  have htSucc : t + 1 ≤ x + y + 1 := Nat.add_le_add_right ht 1
  have htR : (t : ℝ) + 1 ≤ ((x + y : ℕ) : ℝ) + 1 := by
    exact_mod_cast htSucc
  unfold primeSieveDyadicClippedDiscrepancy
  dsimp [t] at h ⊢
  exact h.trans (mul_le_mul_of_nonneg_left htR hη)

/-- Uniform clipped-discrepancy smallness, directly from the native PNT. -/
theorem exists_primeSieveDyadicClippedDiscrepancy_globalScale
    (η : ℝ) (hη : 0 < η) :
    ∃ Y : ℕ, ∀ (y x d : ℕ), Y ≤ y →
      ‖primeSieveDyadicClippedDiscrepancy y x d‖ ≤
        η * (((x + y : ℕ) : ℝ) + 1) := by
  obtain ⟨Y, hEnv⟩ :=
    exists_primeSievePrimeDiscrepancy_relative_cutoff η hη
  refine ⟨Y, ?_⟩
  intro y x d hy
  exact primeSieveDyadicClippedDiscrepancy_norm_le_globalScale
    hη.le hEnv hy

/-! ## Dimensionless packet residuals -/

private theorem packetNatCast_ratio_norm_le_one
    {p q : ℕ} (hpq : p ≤ q) (hq : 0 < q) :
    ‖((p : ℂ) * ((q : ℂ)⁻¹))‖ ≤ 1 := by
  rw [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
  simpa [div_eq_mul_inv] using (div_le_one hqR).2 hpqR

private theorem primeSieveSignedSiblingPacketResidual_eq_affine_left
    {y x a m b : ℕ}
    (ham : a ≤ m) (hmb : m ≤ b) (hab : a < b) :
    primeSieveSignedSiblingPacketResidual y x a m b =
      primeSieveDyadicClippedDiscrepancy y x m -
        primeSieveDyadicClippedDiscrepancy y x a -
        ((((m - a : ℕ) : ℂ) * (((b - a : ℕ) : ℂ)⁻¹)) *
          (primeSieveDyadicClippedDiscrepancy y x b -
            primeSieveDyadicClippedDiscrepancy y x a)) := by
  have hab0 : ((((b - a : ℕ) : ℂ))) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < b - a))
  have hwidthNat : b - a = (b - m) + (m - a) := by omega
  have hwidth :
      (((b - a : ℕ) : ℂ)) =
        ((b - m : ℕ) : ℂ) + ((m - a : ℕ) : ℂ) := by
    exact_mod_cast hwidthNat
  unfold primeSieveSignedSiblingPacketResidual primeSieveSignedSiblingPacket
  field_simp [hab0]
  rw [hwidth]
  ring

/-- If the three discrepancy values at a packet node have norm at most `H`, the
width-normalized sibling residual has norm at most `4H`.  The constant is not
optimized; the point is that it is absolute and survives arbitrary recursion. -/
theorem primeSieveSignedSiblingPacketResidual_norm_le_four
    {y x a m b : ℕ} {H : ℝ}
    (hH : 0 ≤ H) (ham : a ≤ m) (hmb : m ≤ b)
    (ha : ‖primeSieveDyadicClippedDiscrepancy y x a‖ ≤ H)
    (hm : ‖primeSieveDyadicClippedDiscrepancy y x m‖ ≤ H)
    (hb : ‖primeSieveDyadicClippedDiscrepancy y x b‖ ≤ H) :
    ‖primeSieveSignedSiblingPacketResidual y x a m b‖ ≤ 4 * H := by
  by_cases hab : a < b
  · rw [primeSieveSignedSiblingPacketResidual_eq_affine_left ham hmb hab]
    have hma :
        ‖primeSieveDyadicClippedDiscrepancy y x m -
            primeSieveDyadicClippedDiscrepancy y x a‖ ≤ 2 * H := by
      calc
        ‖primeSieveDyadicClippedDiscrepancy y x m -
            primeSieveDyadicClippedDiscrepancy y x a‖ ≤
            ‖primeSieveDyadicClippedDiscrepancy y x m‖ +
              ‖primeSieveDyadicClippedDiscrepancy y x a‖ := norm_sub_le _ _
        _ ≤ H + H := add_le_add hm ha
        _ = 2 * H := by ring
    have hba :
        ‖primeSieveDyadicClippedDiscrepancy y x b -
            primeSieveDyadicClippedDiscrepancy y x a‖ ≤ 2 * H := by
      calc
        ‖primeSieveDyadicClippedDiscrepancy y x b -
            primeSieveDyadicClippedDiscrepancy y x a‖ ≤
            ‖primeSieveDyadicClippedDiscrepancy y x b‖ +
              ‖primeSieveDyadicClippedDiscrepancy y x a‖ := norm_sub_le _ _
        _ ≤ H + H := add_le_add hb ha
        _ = 2 * H := by ring
    have hratio :
        ‖(((m - a : ℕ) : ℂ) * (((b - a : ℕ) : ℂ)⁻¹))‖ ≤ 1 :=
      packetNatCast_ratio_norm_le_one (by omega) (by omega)
    have hterm :
        ‖((((m - a : ℕ) : ℂ) * (((b - a : ℕ) : ℂ)⁻¹)) *
          (primeSieveDyadicClippedDiscrepancy y x b -
            primeSieveDyadicClippedDiscrepancy y x a))‖ ≤ 2 * H := by
      rw [norm_mul]
      calc
        ‖(((m - a : ℕ) : ℂ) * (((b - a : ℕ) : ℂ)⁻¹))‖ *
            ‖primeSieveDyadicClippedDiscrepancy y x b -
              primeSieveDyadicClippedDiscrepancy y x a‖ ≤
            1 * ‖primeSieveDyadicClippedDiscrepancy y x b -
              primeSieveDyadicClippedDiscrepancy y x a‖ :=
          mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
        _ ≤ 1 * (2 * H) := mul_le_mul_of_nonneg_left hba (by norm_num)
        _ = 2 * H := by ring
    calc
      ‖(primeSieveDyadicClippedDiscrepancy y x m -
          primeSieveDyadicClippedDiscrepancy y x a) -
          ((((m - a : ℕ) : ℂ) * (((b - a : ℕ) : ℂ)⁻¹)) *
            (primeSieveDyadicClippedDiscrepancy y x b -
              primeSieveDyadicClippedDiscrepancy y x a))‖ ≤
          ‖primeSieveDyadicClippedDiscrepancy y x m -
            primeSieveDyadicClippedDiscrepancy y x a‖ +
          ‖((((m - a : ℕ) : ℂ) * (((b - a : ℕ) : ℂ)⁻¹)) *
            (primeSieveDyadicClippedDiscrepancy y x b -
              primeSieveDyadicClippedDiscrepancy y x a))‖ := norm_sub_le _ _
      _ ≤ 2 * H + 2 * H := add_le_add hma hterm
      _ = 4 * H := by ring
  · have hba : b = a := by omega
    have hma : m = a := by omega
    subst b
    subst m
    simpa [primeSieveSignedSiblingPacketResidual, primeSieveSignedSiblingPacket]
      using hH

/-- Dimensionless root residual of one midpoint node.  The global scale is
chosen deliberately: it is uniform over every descendant and therefore makes a
single recursive envelope possible without changing normalization at children. -/
def primeSieveDyadicPacketRelativeResidual
    (y x a m b : ℕ) : ℝ :=
  ‖primeSieveSignedSiblingPacketResidual y x a m b‖ /
    (((x + y : ℕ) : ℝ) + 1)

/-- The PNT relative envelope controls every packet node with an absolute factor
`4`, uniformly in its interval. -/
theorem primeSieveDyadicPacketRelativeResidual_le_four
    {η : ℝ} {Y y x a m b : ℕ}
    (hη : 0 ≤ η)
    (hEnv : ∀ t : ℕ, Y ≤ t →
      ‖primeSievePrimeDiscrepancy t‖ ≤ η * ((t : ℝ) + 1))
    (hy : Y ≤ y) (ham : a ≤ m) (hmb : m ≤ b) :
    primeSieveDyadicPacketRelativeResidual y x a m b ≤ 4 * η := by
  let S : ℝ := ((x + y : ℕ) : ℝ) + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have hnode := primeSieveSignedSiblingPacketResidual_norm_le_four
    (H := η * S) (mul_nonneg hη hS.le) ham hmb
    (primeSieveDyadicClippedDiscrepancy_norm_le_globalScale hη hEnv hy)
    (primeSieveDyadicClippedDiscrepancy_norm_le_globalScale hη hEnv hy)
    (primeSieveDyadicClippedDiscrepancy_norm_le_globalScale hη hEnv hy)
  unfold primeSieveDyadicPacketRelativeResidual
  dsimp [S] at hS hnode ⊢
  rw [div_le_iff₀ hS]
  nlinarith

/-! ## Recursive full and deep residual envelopes -/

/-- Maximum dimensionless packet residual appearing in the first `depth` levels
of the midpoint tree on `[a,b]`. -/
def primeSieveDyadicPacketIntervalRelativeEnvelope
    (y x : ℕ) : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 0
  | depth + 1, a, b =>
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        max (primeSieveDyadicPacketRelativeResidual y x a m b)
          (max
            (primeSieveDyadicPacketIntervalRelativeEnvelope y x depth a m)
            (primeSieveDyadicPacketIntervalRelativeEnvelope y x depth m b))
      else 0

@[simp] theorem primeSieveDyadicPacketIntervalRelativeEnvelope_zero
    (y x a b : ℕ) :
    primeSieveDyadicPacketIntervalRelativeEnvelope y x 0 a b = 0 := by
  rfl

/-- Exact recursion of the full residual envelope. -/
theorem primeSieveDyadicPacketIntervalRelativeEnvelope_succ
    (y x depth a b : ℕ) :
    primeSieveDyadicPacketIntervalRelativeEnvelope y x (depth + 1) a b =
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        max (primeSieveDyadicPacketRelativeResidual y x a m b)
          (max
            (primeSieveDyadicPacketIntervalRelativeEnvelope y x depth a m)
            (primeSieveDyadicPacketIntervalRelativeEnvelope y x depth m b))
      else 0 := by
  rfl

/-- Every node in the recursive tree inherits the same relative PNT envelope. -/
theorem primeSieveDyadicPacketIntervalRelativeEnvelope_le_four
    {η : ℝ} {Y y x : ℕ}
    (hη : 0 ≤ η)
    (hEnv : ∀ t : ℕ, Y ≤ t →
      ‖primeSievePrimeDiscrepancy t‖ ≤ η * ((t : ℝ) + 1))
    (hy : Y ≤ y) :
    ∀ (depth a b : ℕ),
      primeSieveDyadicPacketIntervalRelativeEnvelope y x depth a b ≤ 4 * η := by
  intro depth
  induction depth with
  | zero =>
      intro a b
      simp
      positivity
  | succ depth ih =>
      intro a b
      rw [primeSieveDyadicPacketIntervalRelativeEnvelope_succ]
      by_cases hsplit : a + 1 < b
      · simp only [hsplit, if_true]
        let m := dyadicPacketMidpoint a b
        have hm : a ≤ m ∧ m ≤ b := by
          dsimp [m, dyadicPacketMidpoint]
          omega
        apply max_le
        · exact primeSieveDyadicPacketRelativeResidual_le_four
            hη hEnv hy hm.1 hm.2
        · exact max_le (ih _ _) (ih _ _)
      · simp [hsplit]
        positivity

/-- Deep residual envelope after skipping the first `cutoff` midpoint levels.
When `cutoff = 0` this is the full envelope.  When the cutoff reaches the tree
depth the envelope is zero. -/
def primeSieveDyadicPacketIntervalDeepRelativeEnvelope
    (y x : ℕ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | _, 0, _, _ => 0
  | 0, depth + 1, a, b =>
      primeSieveDyadicPacketIntervalRelativeEnvelope y x (depth + 1) a b
  | cutoff + 1, depth + 1, a, b =>
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        max
          (primeSieveDyadicPacketIntervalDeepRelativeEnvelope
            y x cutoff depth a m)
          (primeSieveDyadicPacketIntervalDeepRelativeEnvelope
            y x cutoff depth m b)
      else 0

@[simp] theorem primeSieveDyadicPacketIntervalDeepRelativeEnvelope_depth_zero
    (y x cutoff a b : ℕ) :
    primeSieveDyadicPacketIntervalDeepRelativeEnvelope y x cutoff 0 a b = 0 := by
  cases cutoff <;> rfl

@[simp] theorem primeSieveDyadicPacketIntervalDeepRelativeEnvelope_cutoff_zero
    (y x depth a b : ℕ) :
    primeSieveDyadicPacketIntervalDeepRelativeEnvelope y x 0 depth a b =
      primeSieveDyadicPacketIntervalRelativeEnvelope y x depth a b := by
  cases depth <;> rfl

/-- Exact child recursion after one skipped level. -/
theorem primeSieveDyadicPacketIntervalDeepRelativeEnvelope_succ
    (y x cutoff depth a b : ℕ) :
    primeSieveDyadicPacketIntervalDeepRelativeEnvelope
        y x (cutoff + 1) (depth + 1) a b =
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        max
          (primeSieveDyadicPacketIntervalDeepRelativeEnvelope
            y x cutoff depth a m)
          (primeSieveDyadicPacketIntervalDeepRelativeEnvelope
            y x cutoff depth m b)
      else 0 := by
  rfl

/-- The qualitative PNT localization survives after any number of skipped
levels. -/
theorem primeSieveDyadicPacketIntervalDeepRelativeEnvelope_le_four
    {η : ℝ} {Y y x : ℕ}
    (hη : 0 ≤ η)
    (hEnv : ∀ t : ℕ, Y ≤ t →
      ‖primeSievePrimeDiscrepancy t‖ ≤ η * ((t : ℝ) + 1))
    (hy : Y ≤ y) :
    ∀ (cutoff depth a b : ℕ),
      primeSieveDyadicPacketIntervalDeepRelativeEnvelope
        y x cutoff depth a b ≤ 4 * η := by
  intro cutoff
  induction cutoff with
  | zero =>
      intro depth a b
      rw [primeSieveDyadicPacketIntervalDeepRelativeEnvelope_cutoff_zero]
      exact primeSieveDyadicPacketIntervalRelativeEnvelope_le_four
        hη hEnv hy depth a b
  | succ cutoff ih =>
      intro depth a b
      cases depth with
      | zero =>
          simp
          positivity
      | succ depth =>
          rw [primeSieveDyadicPacketIntervalDeepRelativeEnvelope_succ]
          by_cases hsplit : a + 1 < b
          · simp only [hsplit, if_true]
            exact max_le (ih _ _ _) (ih _ _ _)
          · simp [hsplit]
            positivity

/-- The deep residual envelope attached to one occupied #324 block.  It skips
exactly the same `min J j` shallow levels used by the #324 deep-energy split. -/
def primeSieveDyadicPacketBlockDeepRelativeEnvelope
    (y x j J : ℕ) : ℝ :=
  primeSieveDyadicPacketIntervalDeepRelativeEnvelope y x (min J j) j
    (primeSieveDyadicBlockLeft j)
    (primeSieveDyadicBlockRight y x j + 1)

/-- **PNT localization in the exact #324 deep coordinate.**  For every target
`eta`, one cutoff in the prime variable makes every remaining deep packet
residual at every block, tree depth, and shallow cutoff at most `eta` in the
global relative normalization. -/
theorem primeSieveDyadicPacketBlockDeepRelativeEnvelope_arbitrarily_small
    (η : ℝ) (hη : 0 < η) :
    ∃ Y : ℕ, ∀ (y x j J : ℕ), Y ≤ y →
      primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J ≤ η := by
  have hquarter : 0 < η / 4 := by linarith
  obtain ⟨Y, hEnv⟩ :=
    exists_primeSievePrimeDiscrepancy_relative_cutoff (η / 4) hquarter
  refine ⟨Y, ?_⟩
  intro y x j J hy
  unfold primeSieveDyadicPacketBlockDeepRelativeEnvelope
  have h := primeSieveDyadicPacketIntervalDeepRelativeEnvelope_le_four
    (x := x) hquarter.le hEnv hy (min J j) j
      (primeSieveDyadicBlockLeft j)
      (primeSieveDyadicBlockRight y x j + 1)
  nlinarith

/-- Ordinary proposition naming the next analytic question.  It does not assert
that a contraction has been proved: it records the desired strict quantitative
improvement of the already-localized deep envelope as the shallow cutoff moves
one level deeper. -/
def DyadicPacketDeepEnvelopeCubicContractionStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ Y : ℕ, ∀ (y x j J : ℕ),
    Y ≤ y → J < j →
      primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j (J + 1) ≤
        primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J -
          c * (primeSieveDyadicPacketBlockDeepRelativeEnvelope y x j J) ^ 3

end RHLean.Analysis