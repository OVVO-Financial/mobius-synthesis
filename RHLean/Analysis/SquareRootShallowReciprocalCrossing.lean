import Mathlib
import RHLean.Analysis.NativePNTTransfer
import RHLean.Analysis.SquareRootPrimeCountGap
import RHLean.Proof.LargePrimeTerminalFlipLayers

/-!
# Endpoint-parametric shallow reciprocal-depth crossing

The analytic mechanism is independent of the square parametrization and of any
particular certified depth.  For endpoint and cutoff sequences `x n` and `y n`,
assume that `x n -> infinity` and that a fixed reciprocal depth `K₀` lies above
the cutoff eventually, in the exact form `y n ≤ x n / (K₀ + 1)`.  If the finite
reciprocal coefficient at `K₀` is negative, then the intact upper-middle packet
eventually crosses at some depth `K ≤ K₀`.  For every `C > 0`, that depth is
eventually at most `C * log (x n)`.

The square geometry is recovered by `x R = R^2 - 1` and `y R = R`.  The number
`18800` appears only in a final exact witness: its rational coefficient is
checked by `native_decide`.  It is not part of the general theorem statement.
No decimal approximation or externally generated data enters the proof.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Proof

open RHLean.Analysis

/-! ## Exact finite coefficient certificate -/

/-- Rational Abel-boundary form of the fixed-depth reciprocal coefficient.

This form is computationally linear in the depth, unlike recomputing every
Mertens prefix in the weighted-sum form. -/
def squareRootPacketReciprocalBoundaryRat (K : ℕ) : ℚ :=
  (∑ d ∈ Finset.Icc 1 K, ((μ d : ℤ) : ℚ) / (d : ℚ)) -
    (squareRootMertensInt K : ℚ) / ((K + 1 : ℕ) : ℚ)

/-- Integer Mertens prefixes advance by the next Möbius value. -/
theorem squareRootMertensInt_succ (K : ℕ) :
    squareRootMertensInt (K + 1) =
      squareRootMertensInt K + μ (K + 1) := by
  unfold squareRootMertensInt
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1)]

/-- Rational summation by parts identifies the weighted reciprocal coefficient
with its efficient Möbius-boundary form. -/
theorem squareRootPacketReciprocalWeightRat_eq_boundary (K : ℕ) :
    (∑ d ∈ Finset.Icc 1 K,
        (squareRootMertensInt d : ℚ) *
          ((1 : ℚ) / (d : ℚ) - (1 : ℚ) / ((d + 1 : ℕ) : ℚ))) =
      squareRootPacketReciprocalBoundaryRat K := by
  unfold squareRootPacketReciprocalBoundaryRat
  induction K with
  | zero => simp [squareRootMertensInt]
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), ih,
        squareRootMertensInt_succ]
      push_cast
      ring

/-- Exact certificate: the fixed-depth coefficient at `18800` is negative. -/
theorem squareRootPacketReciprocalBoundaryRat_18800_neg :
    squareRootPacketReciprocalBoundaryRat 18800 < 0 := by
  native_decide

/-- Any exact rational boundary certificate supplies the corresponding real
coefficient sign used by the PNT limit. -/
theorem squareRootPacketReciprocalWeightReal_neg_of_boundaryRat_neg
    (K : ℕ) (hK : squareRootPacketReciprocalBoundaryRat K < 0) :
    (∑ d ∈ Finset.Icc 1 K,
        (squareRootMertensInt d : ℝ) *
          ((1 : ℝ) / (d : ℝ) - (1 : ℝ) / ((d + 1 : ℕ) : ℝ))) < 0 := by
  have hcast : (squareRootPacketReciprocalBoundaryRat K : ℝ) < 0 := by
    exact_mod_cast hK
  rw [← squareRootPacketReciprocalWeightRat_eq_boundary] at hcast
  simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_sub, Rat.cast_div,
    Rat.cast_one, Rat.cast_intCast, Rat.cast_natCast] using hcast

/-- Real form of the concrete witness, retained only as a convenience
corollary. -/
theorem squareRootPacketReciprocalWeightReal_18800_neg :
    (∑ d ∈ Finset.Icc 1 18800,
        (squareRootMertensInt d : ℝ) *
          ((1 : ℝ) / (d : ℝ) - (1 : ℝ) / ((d + 1 : ℕ) : ℝ))) < 0 :=
  squareRootPacketReciprocalWeightReal_neg_of_boundaryRat_neg 18800
    squareRootPacketReciprocalBoundaryRat_18800_neg

/-! ## Fixed-dilation consequences of the native PNT -/

/-- The square endpoint `R^2 - 1` tends to infinity. -/
theorem squareRootEndpoint_tendsto_atTop :
    Tendsto squareRootEndpoint atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro B
  filter_upwards [eventually_ge_atTop (max 2 B)] with R hR
  have hR2 : 2 ≤ R := le_trans (le_max_left 2 B) hR
  have hBR : B ≤ R := le_trans (le_max_right 2 B) hR
  have hsq : R + 1 ≤ R ^ 2 := by
    calc
      R + 1 ≤ R + R := Nat.add_le_add_left (by omega : 1 ≤ R) R
      _ = 2 * R := by omega
      _ ≤ R * R := Nat.mul_le_mul_right R hR2
      _ = R ^ 2 := by ring
  unfold squareRootEndpoint
  omega

/-- Natural division by a fixed positive denominator has the expected real
ratio. -/
theorem natDiv_cast_div_cast_tendsto
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / (N : ℝ)) atTop
      (𝓝 ((1 : ℝ) / (d : ℝ))) := by
  have hscaled : Tendsto (fun N : ℕ => (N : ℝ) / (d : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_div_const (by exact_mod_cast hd))
  have hequiv := Asymptotics.isEquivalent_nat_floor.comp_tendsto hscaled
  have hequiv' : Asymptotics.IsEquivalent atTop
      (fun N : ℕ => ((N / d : ℕ) : ℝ))
      (fun N : ℕ => (N : ℝ) / (d : ℝ)) := by
    simpa [Function.comp_def, Nat.floor_div_eq_div] using hequiv
  have hden : ∀ᶠ N : ℕ in atTop, (N : ℝ) / (d : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    positivity
  have hratio :
      Tendsto
        (fun N : ℕ =>
          ((N / d : ℕ) : ℝ) / ((N : ℝ) / (d : ℝ)))
        atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hden).1 hequiv'
  have hmul := hratio.mul_const ((1 : ℝ) / (d : ℝ))
  have heq :
      (fun N : ℕ =>
        ((N / d : ℕ) : ℝ) / ((N : ℝ) / (d : ℝ)) *
          ((1 : ℝ) / (d : ℝ))) =ᶠ[atTop]
        (fun N : ℕ => ((N / d : ℕ) : ℝ) / (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  simpa using hmul.congr' heq

/-- The logarithms of `N/d` and `N` are asymptotically equal for fixed `d`. -/
theorem log_natDiv_div_log_tendsto_one
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun N : ℕ =>
        Real.log ((N / d : ℕ) : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
  have hratio := natDiv_cast_div_cast_tendsto d hd
  have hc : (0 : ℝ) < (1 : ℝ) / (d : ℝ) := by positivity
  have hlogRatio :
      Tendsto
        (fun N : ℕ =>
          Real.log (((N / d : ℕ) : ℝ) / (N : ℝ)))
        atTop (𝓝 (Real.log ((1 : ℝ) / (d : ℝ)))) :=
    (Real.continuousAt_log hc.ne').tendsto.comp hratio
  have hdiff :
      Tendsto
        (fun N : ℕ =>
          Real.log ((N / d : ℕ) : ℝ) - Real.log (N : ℝ))
        atTop (𝓝 (Real.log ((1 : ℝ) / (d : ℝ)))) := by
    apply hlogRatio.congr'
    filter_upwards [eventually_ge_atTop (2 * d)] with N hN
    have hNpos : 0 < N := by omega
    have hdivpos : 0 < N / d :=
      (Nat.one_le_div_iff hd).2 (by omega)
    rw [Real.log_div (by positivity) (by positivity)]
  have hlogTop :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := hdiff.div_atTop hlogTop
  have hadd := hsmall.add_const 1
  have heq :
      (fun N : ℕ =>
        (Real.log ((N / d : ℕ) : ℝ) - Real.log (N : ℝ)) /
            Real.log (N : ℝ) + 1) =ᶠ[atTop]
        (fun N : ℕ =>
          Real.log ((N / d : ℕ) : ℝ) / Real.log (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog0 : Real.log (N : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by exact_mod_cast hN))
    field_simp
    ring
  simpa using hadd.congr' heq

/-- Native PNT at a fixed reciprocal dilation, normalized at the undilated
endpoint. -/
theorem nativePrimeCounting_natDiv_mul_log_div_tendsto
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun N : ℕ =>
        (Nat.primeCounting (N / d) : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 ((1 : ℝ) / (d : ℝ))) := by
  have hdivTop : Tendsto (fun N : ℕ => N / d) atTop atTop :=
    Nat.tendsto_div_const_atTop hd.ne'
  have hpnt := nativePrimeNumberTheorem.comp hdivTop
  have hratio := natDiv_cast_div_cast_tendsto d hd
  have hlog := log_natDiv_div_log_tendsto_one d hd
  have hlogInv := hlog.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hprod := (hpnt.mul hratio).mul hlogInv
  have heq :
      (fun N : ℕ =>
        (((Nat.primeCounting (N / d) : ℝ) *
              Real.log ((N / d : ℕ) : ℝ) /
                ((N / d : ℕ) : ℝ)) *
            (((N / d : ℕ) : ℝ) / (N : ℝ))) *
          (Real.log ((N / d : ℕ) : ℝ) /
            Real.log (N : ℝ))⁻¹) =ᶠ[atTop]
        (fun N : ℕ =>
          (Nat.primeCounting (N / d) : ℝ) * Real.log (N : ℝ) /
            (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop (max 2 (2 * d))] with N hN
    have hN2 : 2 ≤ N := (le_max_left 2 (2 * d)).trans hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hdiv2 : 2 ≤ N / d := by
      apply (Nat.le_div_iff_mul_le hd).2
      omega
    have hdiv0 : ((N / d : ℕ) : ℝ) ≠ 0 := by positivity
    have hlog0 : Real.log ((N / d : ℕ) : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by exact_mod_cast hdiv2))
    field_simp
  simpa [Function.comp_def] using hprod.congr' heq

/-! ## Endpoint- and cutoff-parametric packet -/

/-- Honest prime population of reciprocal layer `d` for an arbitrary lower
cutoff `y` and endpoint `x`. -/
def endpointReciprocalPrimeLayerCard (y x d : ℕ) : ℕ :=
  ((primeSieveReciprocalInterval y x d).filter Nat.Prime).card

/-- Integer upper-middle packet at arbitrary cutoff `y` and endpoint `x`. -/
def endpointTruncatedUpperMiddlePacketInt (y x K : ℕ) : ℤ :=
  -∑ d ∈ Finset.Icc 1 K,
    (endpointReciprocalPrimeLayerCard y x d : ℤ) * squareRootMertensInt d

/-- A sign crossing for the endpoint-parametric packet. -/
def EndpointPacketCrossesAt (y x K : ℕ) : Prop :=
  1 ≤ K ∧
    endpointTruncatedUpperMiddlePacketInt y x (K - 1) < 0 ∧
      0 ≤ endpointTruncatedUpperMiddlePacketInt y x K

/-- The former square-root layer is exactly the endpoint-parametric layer at
`y = R` and `x = R^2 - 1`. -/
@[simp] theorem endpointReciprocalPrimeLayerCard_squareRootEndpoint
    (R d : ℕ) :
    endpointReciprocalPrimeLayerCard R (squareRootEndpoint R) d =
      squareRootReciprocalPrimeLayerCard R d := rfl

/-- The former square-root packet is the corresponding specialization. -/
@[simp] theorem endpointTruncatedUpperMiddlePacketInt_squareRootEndpoint
    (R K : ℕ) :
    endpointTruncatedUpperMiddlePacketInt R (squareRootEndpoint R) K =
      squareRootTruncatedUpperMiddlePacketInt R K := rfl

/-- The endpoint-parametric crossing predicate specializes definitionally to
the existing square-root predicate. -/
@[simp] theorem endpointPacketCrossesAt_squareRootEndpoint
    (R K : ℕ) :
    EndpointPacketCrossesAt R (squareRootEndpoint R) K ↔
      SquareRootPacketCrossesAt R K := by
  rfl

/-- Once the lower cutoff is below the reciprocal boundary, a generic layer is
exactly the difference of two ordinary prime counts. -/
theorem endpointReciprocalPrimeLayerCard_add_primeCounting
    {y x d : ℕ} (hd : 0 < d) (hy : y ≤ x / (d + 1)) :
    endpointReciprocalPrimeLayerCard y x d +
        Nat.primeCounting (x / (d + 1)) =
      Nat.primeCounting (x / d) := by
  have hmono : x / (d + 1) ≤ x / d :=
    Nat.div_le_div_left (by omega) (by omega)
  unfold endpointReciprocalPrimeLayerCard primeSieveReciprocalInterval
    primeSieveReciprocalLower primeSieveReciprocalUpper
  rw [max_eq_right hy]
  exact primeCard_Ioc_add_primeCounting_eq hmono

/-- A fixed reciprocal layer has its PNT density along every endpoint sequence
that tends to infinity, provided the independent lower cutoff is eventually
below that layer. -/
theorem endpointReciprocalPrimeLayerCard_mul_log_div_tendsto
    (y x : ℕ → ℕ) (d : ℕ) (hd : 0 < d)
    (hx : Tendsto x atTop atTop)
    (hy : ∀ᶠ n : ℕ in atTop, y n ≤ x n / (d + 1)) :
    Tendsto
      (fun n : ℕ =>
        (endpointReciprocalPrimeLayerCard (y n) (x n) d : ℝ) *
          Real.log (x n : ℝ) / (x n : ℝ))
      atTop
      (𝓝 ((1 : ℝ) / (d : ℝ) -
        (1 : ℝ) / ((d + 1 : ℕ) : ℝ))) := by
  have hu :
      Tendsto
        (fun n : ℕ =>
          (Nat.primeCounting (x n / d) : ℝ) * Real.log (x n : ℝ) /
            (x n : ℝ))
        atTop (𝓝 ((1 : ℝ) / (d : ℝ))) := by
    simpa [Function.comp_def] using
      (nativePrimeCounting_natDiv_mul_log_div_tendsto d hd).comp hx
  have hl :
      Tendsto
        (fun n : ℕ =>
          (Nat.primeCounting (x n / (d + 1)) : ℝ) *
              Real.log (x n : ℝ) / (x n : ℝ))
        atTop (𝓝 ((1 : ℝ) / ((d + 1 : ℕ) : ℝ))) := by
    simpa [Function.comp_def] using
      (nativePrimeCounting_natDiv_mul_log_div_tendsto (d + 1) (by omega)).comp hx
  have hdiff := hu.sub hl
  apply hdiff.congr'
  filter_upwards [hy] with n hyn
  have hadd := endpointReciprocalPrimeLayerCard_add_primeCounting hd hyn
  have hreal :
      (endpointReciprocalPrimeLayerCard (y n) (x n) d : ℝ) +
          (Nat.primeCounting (x n / (d + 1)) : ℝ) =
        (Nat.primeCounting (x n / d) : ℝ) := by
    exact_mod_cast hadd
  rw [← hreal]
  ring

/-- For every fixed depth, the generic packet has the same reciprocal Mertens
coefficient along every admissible endpoint/cutoff pair. -/
theorem endpointTruncatedUpperMiddlePacketInt_mul_log_div_tendsto
    (y x : ℕ → ℕ) (K : ℕ)
    (hx : Tendsto x atTop atTop)
    (hy : ∀ᶠ n : ℕ in atTop, y n ≤ x n / (K + 1)) :
    Tendsto
      (fun n : ℕ =>
        (endpointTruncatedUpperMiddlePacketInt (y n) (x n) K : ℝ) *
          Real.log (x n : ℝ) / (x n : ℝ))
      atTop
      (𝓝 (-∑ d ∈ Finset.Icc 1 K,
        (squareRootMertensInt d : ℝ) *
          ((1 : ℝ) / (d : ℝ) -
            (1 : ℝ) / ((d + 1 : ℕ) : ℝ)))) := by
  have hsum :
      Tendsto
        (fun n : ℕ => ∑ d ∈ Finset.Icc 1 K,
          (-(squareRootMertensInt d : ℝ)) *
            ((endpointReciprocalPrimeLayerCard (y n) (x n) d : ℝ) *
              Real.log (x n : ℝ) / (x n : ℝ)))
        atTop
        (𝓝 (∑ d ∈ Finset.Icc 1 K,
          (-(squareRootMertensInt d : ℝ)) *
            ((1 : ℝ) / (d : ℝ) -
              (1 : ℝ) / ((d + 1 : ℕ) : ℝ)))) := by
    apply tendsto_finset_sum
    intro d hdMem
    have hd : 0 < d := (Finset.mem_Icc.mp hdMem).1
    have hdK : d ≤ K := (Finset.mem_Icc.mp hdMem).2
    have hyD : ∀ᶠ n : ℕ in atTop, y n ≤ x n / (d + 1) := by
      filter_upwards [hy] with n hyn
      exact hyn.trans
        (Nat.div_le_div_left (Nat.add_le_add_right hdK 1) (by omega))
    exact tendsto_const_nhds.mul
      (endpointReciprocalPrimeLayerCard_mul_log_div_tendsto y x d hd hx hyD)
  have hsum' :
      Tendsto
        (fun n : ℕ => ∑ d ∈ Finset.Icc 1 K,
          (-(squareRootMertensInt d : ℝ)) *
            ((endpointReciprocalPrimeLayerCard (y n) (x n) d : ℝ) *
              Real.log (x n : ℝ) / (x n : ℝ)))
        atTop
        (𝓝 (-∑ d ∈ Finset.Icc 1 K,
          (squareRootMertensInt d : ℝ) *
            ((1 : ℝ) / (d : ℝ) -
              (1 : ℝ) / ((d + 1 : ℕ) : ℝ)))) := by
    simpa only [neg_mul, Finset.sum_neg_distrib] using hsum
  refine hsum'.congr' ?_
  filter_upwards with n
  unfold endpointTruncatedUpperMiddlePacketInt
  push_cast
  calc
    (∑ d ∈ Finset.Icc 1 K,
        -(squareRootMertensInt d : ℝ) *
          ((endpointReciprocalPrimeLayerCard (y n) (x n) d : ℝ) *
            Real.log (x n : ℝ) / (x n : ℝ))) =
        ∑ d ∈ Finset.Icc 1 K,
          (Real.log (x n : ℝ) / (x n : ℝ)) *
            (-((endpointReciprocalPrimeLayerCard (y n) (x n) d : ℝ) *
              (squareRootMertensInt d : ℝ))) := by
          apply Finset.sum_congr rfl
          intro d _hd
          ring
    _ = (Real.log (x n : ℝ) / (x n : ℝ)) *
        ∑ d ∈ Finset.Icc 1 K,
          (-((endpointReciprocalPrimeLayerCard (y n) (x n) d : ℝ) *
            (squareRootMertensInt d : ℝ))) := by
          rw [Finset.mul_sum]
    _ = (-∑ d ∈ Finset.Icc 1 K,
          (endpointReciprocalPrimeLayerCard (y n) (x n) d : ℝ) *
            (squareRootMertensInt d : ℝ)) *
        Real.log (x n : ℝ) / (x n : ℝ) := by
          rw [Finset.sum_neg_distrib]
          ring

/-- A negative fixed-depth coefficient forces positivity of the generic packet
at that depth along every admissible endpoint/cutoff sequence. -/
theorem eventually_endpointTruncatedUpperMiddlePacketInt_pos_of_coefficient_neg
    (y x : ℕ → ℕ) (K₀ : ℕ)
    (hx : Tendsto x atTop atTop)
    (hy : ∀ᶠ n : ℕ in atTop, y n ≤ x n / (K₀ + 1))
    (hcoeff :
      (∑ d ∈ Finset.Icc 1 K₀,
        (squareRootMertensInt d : ℝ) *
          ((1 : ℝ) / (d : ℝ) -
            (1 : ℝ) / ((d + 1 : ℕ) : ℝ))) < 0) :
    ∀ᶠ n : ℕ in atTop,
      0 < endpointTruncatedUpperMiddlePacketInt (y n) (x n) K₀ := by
  let S : ℝ :=
    ∑ d ∈ Finset.Icc 1 K₀,
      (squareRootMertensInt d : ℝ) *
        ((1 : ℝ) / (d : ℝ) -
          (1 : ℝ) / ((d + 1 : ℕ) : ℝ))
  have hS : S < 0 := by simpa [S] using hcoeff
  have hlimit :
      Tendsto
        (fun n : ℕ =>
          (endpointTruncatedUpperMiddlePacketInt (y n) (x n) K₀ : ℝ) *
            Real.log (x n : ℝ) / (x n : ℝ))
        atTop (𝓝 (-S)) := by
    simpa [S] using
      endpointTruncatedUpperMiddlePacketInt_mul_log_div_tendsto y x K₀ hx hy
  have hnormPos :
      ∀ᶠ n : ℕ in atTop,
        0 < (endpointTruncatedUpperMiddlePacketInt (y n) (x n) K₀ : ℝ) *
          Real.log (x n : ℝ) / (x n : ℝ) :=
    (tendsto_order.1 hlimit).1 0 (by linarith)
  filter_upwards [hx.eventually_ge_atTop 2, hnormPos] with n hxn hpos
  have hlog : 0 < Real.log (x n : ℝ) :=
    Real.log_pos (by exact_mod_cast hxn)
  have hxreal : 0 < (x n : ℝ) := by positivity
  have hmul :
      0 < (endpointTruncatedUpperMiddlePacketInt (y n) (x n) K₀ : ℝ) *
        Real.log (x n : ℝ) :=
    ((div_pos_iff.mp hpos).resolve_right
      (fun hneg => (not_lt_of_ge hxreal.le) hneg.2)).1
  have hcast :
      0 < (endpointTruncatedUpperMiddlePacketInt (y n) (x n) K₀ : ℝ) :=
    ((mul_pos_iff.mp hmul).resolve_right
      (fun hneg => (not_lt_of_ge hlog.le) hneg.2)).1
  exact_mod_cast hcast

/-- If the cutoff lies below `x/2`, the first generic layer is the nonempty
Bertrand block `(x/2,x]`, so the packet is strictly negative. -/
theorem endpointTruncatedUpperMiddlePacketInt_one_neg
    {y x : ℕ} (hx : 3 ≤ x) (hy : y ≤ x / 2) :
    endpointTruncatedUpperMiddlePacketInt y x 1 < 0 := by
  have hhalf : x / 2 ≠ 0 := by omega
  obtain ⟨p, hpPrime, hplow, hphigh⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (x / 2) hhalf
  have hpX : p ≤ x := by omega
  have hcard : 0 < endpointReciprocalPrimeLayerCard y x 1 := by
    apply Finset.card_pos.mpr
    refine ⟨p, ?_⟩
    unfold primeSieveReciprocalInterval primeSieveReciprocalLower
      primeSieveReciprocalUpper
    rw [max_eq_right hy]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hplow, by simpa using hpX⟩, hpPrime⟩
  have hM1 : squareRootMertensInt 1 = 1 := by
    simp [squareRootMertensInt]
  unfold endpointTruncatedUpperMiddlePacketInt
  rw [show Finset.Icc 1 1 = ({1} : Finset ℕ) by decide]
  simp [hM1]
  exact_mod_cast hcard

/-- Pure discrete extraction: a negative first packet and a nonnegative packet
at `K₀` produce a genuine first crossing no deeper than `K₀`. -/
theorem exists_endpointPacketCrossesAt_le_of_one_neg_of_nonneg
    {y x K₀ : ℕ} (hK₀ : 1 ≤ K₀)
    (hone : endpointTruncatedUpperMiddlePacketInt y x 1 < 0)
    (htop : 0 ≤ endpointTruncatedUpperMiddlePacketInt y x K₀) :
    ∃ K : ℕ, K ≤ K₀ ∧ EndpointPacketCrossesAt y x K := by
  let P : ℕ → Prop := fun K =>
    1 ≤ K ∧ K ≤ K₀ ∧ 0 ≤ endpointTruncatedUpperMiddlePacketInt y x K
  have hex : ∃ K, P K := ⟨K₀, hK₀, le_rfl, htop⟩
  let K := Nat.find hex
  have hK : P K := Nat.find_spec hex
  have hKgt : 1 < K := by
    by_contra hnot
    have hK1 : K = 1 := by omega
    have hbad := hK.2.2
    rw [hK1] at hbad
    linarith
  have hprev : endpointTruncatedUpperMiddlePacketInt y x (K - 1) < 0 := by
    by_contra hnot
    have hprevNonneg :
        0 ≤ endpointTruncatedUpperMiddlePacketInt y x (K - 1) :=
      le_of_not_gt hnot
    have hpredP : P (K - 1) :=
      ⟨by omega, (Nat.sub_le K 1).trans hK.2.1, hprevNonneg⟩
    have hmin := Nat.find_min' hex hpredP
    have : K ≤ K - 1 := by simpa [K] using hmin
    omega
  exact ⟨K, hK.2.1, hK.1, hprev, hK.2.2⟩

/-- General shallow crossing theorem.  The depth certificate `K₀`, endpoint
sequence, and lower cutoff are all parameters. -/
theorem eventually_exists_endpointPacketCrossesAt_le_of_coefficient_neg
    (y x : ℕ → ℕ) (K₀ : ℕ) (hK₀ : 1 ≤ K₀)
    (hx : Tendsto x atTop atTop)
    (hy : ∀ᶠ n : ℕ in atTop, y n ≤ x n / (K₀ + 1))
    (hcoeff :
      (∑ d ∈ Finset.Icc 1 K₀,
        (squareRootMertensInt d : ℝ) *
          ((1 : ℝ) / (d : ℝ) -
            (1 : ℝ) / ((d + 1 : ℕ) : ℝ))) < 0) :
    ∀ᶠ n : ℕ in atTop,
      ∃ K : ℕ, K ≤ K₀ ∧ EndpointPacketCrossesAt (y n) (x n) K := by
  have hpos :=
    eventually_endpointTruncatedUpperMiddlePacketInt_pos_of_coefficient_neg
      y x K₀ hx hy hcoeff
  filter_upwards [hx.eventually_ge_atTop 3, hy, hpos] with n hxn hyn htop
  have hyHalf : y n ≤ x n / 2 :=
    hyn.trans (Nat.div_le_div_left (by omega) (by omega))
  exact exists_endpointPacketCrossesAt_le_of_one_neg_of_nonneg hK₀
    (endpointTruncatedUpperMiddlePacketInt_one_neg hxn hyHalf) htop.le

/-- Endpoint form of the logarithmic theorem.  Once a fixed-depth coefficient
is negative, every positive logarithmic constant works eventually. -/
theorem endpointPacket_eventual_log_crossing_of_coefficient_neg
    (y x : ℕ → ℕ) (K₀ : ℕ) (hK₀ : 1 ≤ K₀)
    (hx : Tendsto x atTop atTop)
    (hy : ∀ᶠ n : ℕ in atTop, y n ≤ x n / (K₀ + 1))
    (hdepth : ∀ᶠ n : ℕ in atTop, K₀ < y n)
    (hcoeff :
      (∑ d ∈ Finset.Icc 1 K₀,
        (squareRootMertensInt d : ℝ) *
          ((1 : ℝ) / (d : ℝ) -
            (1 : ℝ) / ((d + 1 : ℕ) : ℝ))) < 0)
    (C : ℝ) (hC : 0 < C) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ K : ℕ,
        K < y n ∧
        (K : ℝ) ≤ C * Real.log (x n : ℝ) ∧
        endpointTruncatedUpperMiddlePacketInt (y n) (x n) (K - 1) < 0 ∧
        0 ≤ endpointTruncatedUpperMiddlePacketInt (y n) (x n) K := by
  have hcross : ∀ᶠ n : ℕ in atTop,
      ∃ K : ℕ, K ≤ K₀ ∧ EndpointPacketCrossesAt (y n) (x n) K :=
    eventually_exists_endpointPacketCrossesAt_le_of_coefficient_neg
      y x K₀ hK₀ hx hy hcoeff
  have hxReal : Tendsto (fun n : ℕ => (x n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hx
  have hlogTop : Tendsto (fun n : ℕ => Real.log (x n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hxReal
  have hlogLarge :
      ∀ᶠ n : ℕ in atTop, (K₀ : ℝ) / C ≤ Real.log (x n : ℝ) :=
    hlogTop.eventually_ge_atTop ((K₀ : ℝ) / C)
  have hall : ∀ᶠ n : ℕ in atTop,
      K₀ < y n ∧
      (K₀ : ℝ) ≤ C * Real.log (x n : ℝ) ∧
      ∃ K : ℕ, K ≤ K₀ ∧ EndpointPacketCrossesAt (y n) (x n) K := by
    filter_upwards [hdepth, hlogLarge, hcross] with n hK₀y hlog hcrossN
    have hK₀log : (K₀ : ℝ) ≤ C * Real.log (x n : ℝ) := by
      calc
        (K₀ : ℝ) = C * ((K₀ : ℝ) / C) := by field_simp
        _ ≤ C * Real.log (x n : ℝ) :=
          mul_le_mul_of_nonneg_left hlog hC.le
    exact ⟨hK₀y, hK₀log, hcrossN⟩
  rw [eventually_atTop] at hall
  rcases hall with ⟨n₀, hn₀⟩
  refine ⟨n₀, ?_⟩
  intro n hn
  rcases hn₀ n hn with ⟨hK₀y, hK₀log, K, hKK₀, hcrossK⟩
  have hKreal : (K : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hKK₀
  exact ⟨K, hKK₀.trans_lt hK₀y, hKreal.trans hK₀log,
    hcrossK.2.1, hcrossK.2.2⟩

/-! ## Square-endpoint specialization -/

/-- Every fixed reciprocal depth eventually lies strictly above the root
cutoff for `x = R^2 - 1`. -/
theorem eventually_squareRoot_le_endpoint_div (K : ℕ) :
    ∀ᶠ R : ℕ in atTop, R ≤ squareRootEndpoint R / (K + 1) := by
  filter_upwards [eventually_ge_atTop (K + 2)] with R hR
  apply (Nat.le_div_iff_mul_le (by omega : 0 < K + 1)).2
  have hKR : K + 1 ≤ R - 1 := by omega
  calc
    R * (K + 1) ≤ R * (R - 1) := Nat.mul_le_mul_left R hKR
    _ ≤ R ^ 2 - 1 := by
      rw [pow_two, Nat.mul_sub_left_distrib]
      simpa using Nat.sub_le_sub_left (by omega : 1 ≤ R) (R * R)

/-- Any exact negative coefficient certificate gives an eventual square-root
crossing bounded by its certified depth. -/
theorem eventually_exists_squareRootPacketCrossesAt_le_of_boundaryRat_neg
    (K₀ : ℕ) (hK₀ : 1 ≤ K₀)
    (hcoeff : squareRootPacketReciprocalBoundaryRat K₀ < 0) :
    ∀ᶠ R : ℕ in atTop,
      ∃ K : ℕ, K ≤ K₀ ∧ SquareRootPacketCrossesAt R K := by
  have hreal :=
    squareRootPacketReciprocalWeightReal_neg_of_boundaryRat_neg K₀ hcoeff
  simpa only [endpointPacketCrossesAt_squareRootEndpoint] using
    (eventually_exists_endpointPacketCrossesAt_le_of_coefficient_neg
      (fun R : ℕ => R) squareRootEndpoint K₀ hK₀
      squareRootEndpoint_tendsto_atTop
      (eventually_squareRoot_le_endpoint_div K₀) hreal)

/-- General square-root corollary stated in the natural endpoint variable
`x = R^2 - 1`.  Every `C > 0` works; neither `C` nor the statement exposes a
particular numerical certificate. -/
theorem squareRootPacket_eventual_log_endpoint_crossing_of_boundaryRat_neg
    (K₀ : ℕ) (hK₀ : 1 ≤ K₀)
    (hcoeff : squareRootPacketReciprocalBoundaryRat K₀ < 0)
    (C : ℝ) (hC : 0 < C) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ∃ K : ℕ,
        K < R ∧
        (K : ℝ) ≤ C * Real.log (squareRootEndpoint R : ℝ) ∧
        squareRootTruncatedUpperMiddlePacketInt R (K - 1) < 0 ∧
        0 ≤ squareRootTruncatedUpperMiddlePacketInt R K := by
  have hreal :=
    squareRootPacketReciprocalWeightReal_neg_of_boundaryRat_neg K₀ hcoeff
  simpa only [endpointTruncatedUpperMiddlePacketInt_squareRootEndpoint] using
    (endpointPacket_eventual_log_crossing_of_coefficient_neg
      (fun R : ℕ => R) squareRootEndpoint K₀ hK₀
      squareRootEndpoint_tendsto_atTop
      (eventually_squareRoot_le_endpoint_div K₀)
      (eventually_gt_atTop K₀) hreal C hC)

/-- Unconditional endpoint-form crossing theorem.  The exact finite witness is
used only internally; the public theorem is in `x` and works for every positive
logarithmic constant. -/
theorem squareRootPacket_eventual_log_endpoint_crossing
    (C : ℝ) (hC : 0 < C) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ∃ K : ℕ,
        K < R ∧
        (K : ℝ) ≤ C * Real.log (squareRootEndpoint R : ℝ) ∧
        squareRootTruncatedUpperMiddlePacketInt R (K - 1) < 0 ∧
        0 ≤ squareRootTruncatedUpperMiddlePacketInt R K :=
  squareRootPacket_eventual_log_endpoint_crossing_of_boundaryRat_neg
    18800 (by norm_num) squareRootPacketReciprocalBoundaryRat_18800_neg C hC

/-- The same fixed-dilation PNT limit along the square endpoints. -/
theorem nativePrimeCounting_squareRootEndpoint_div_mul_log_div_tendsto
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun R : ℕ =>
        (Nat.primeCounting (squareRootEndpoint R / d) : ℝ) *
          Real.log (squareRootEndpoint R : ℝ) /
            (squareRootEndpoint R : ℝ))
      atTop (𝓝 ((1 : ℝ) / (d : ℝ))) := by
  simpa [Function.comp_def] using
    (nativePrimeCounting_natDiv_mul_log_div_tendsto d hd).comp
      squareRootEndpoint_tendsto_atTop

/-! ## Reciprocal layers and the fixed packet -/

/-- At a fixed depth below the root, a reciprocal layer is exactly the
difference of the two ordinary prime counts at its reciprocal endpoints. -/
theorem squareRootReciprocalPrimeLayerCard_add_primeCounting
    {R d : ℕ} (hR : 1 ≤ R) (hd : 1 ≤ d) (hdR : d + 1 < R) :
    squareRootReciprocalPrimeLayerCard R d +
        Nat.primeCounting (squareRootEndpoint R / (d + 1)) =
      Nat.primeCounting (squareRootEndpoint R / d) := by
  have htop : squareRootEndpoint R / (R + 1) = R - 1 :=
    squareRootQuotientSupportTop_eq_pred R hR
  have hdSupport :
      d + 1 ∈ primeSieveQuotientSupport R (squareRootEndpoint R) := by
    unfold primeSieveQuotientSupport
    rw [htop]
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hRle : R ≤ squareRootEndpoint R / (d + 1) :=
    (lt_div_of_mem_primeSieveQuotientSupport hdSupport).le
  have hmono :
      squareRootEndpoint R / (d + 1) ≤ squareRootEndpoint R / d :=
    Nat.div_le_div_left (by omega) (by omega)
  unfold squareRootReciprocalPrimeLayerCard primeSieveReciprocalInterval
    primeSieveReciprocalLower primeSieveReciprocalUpper
  rw [max_eq_right hRle]
  exact primeCard_Ioc_add_primeCounting_eq hmono

/-- One fixed reciprocal layer has limiting density `1/d - 1/(d+1)` under
the square-endpoint PNT normalization. -/
theorem squareRootReciprocalPrimeLayerCard_mul_log_div_tendsto
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun R : ℕ =>
        (squareRootReciprocalPrimeLayerCard R d : ℝ) *
          Real.log (squareRootEndpoint R : ℝ) /
            (squareRootEndpoint R : ℝ))
      atTop
      (𝓝 ((1 : ℝ) / (d : ℝ) -
        (1 : ℝ) / ((d + 1 : ℕ) : ℝ))) := by
  have hu := nativePrimeCounting_squareRootEndpoint_div_mul_log_div_tendsto d hd
  have hl := nativePrimeCounting_squareRootEndpoint_div_mul_log_div_tendsto
    (d + 1) (by omega)
  have hdiff := hu.sub hl
  apply hdiff.congr'
  filter_upwards [eventually_ge_atTop (d + 2)] with R hR
  have hadd := squareRootReciprocalPrimeLayerCard_add_primeCounting
    (R := R) (d := d) (by omega) (by omega) (by omega)
  have hreal :
      (squareRootReciprocalPrimeLayerCard R d : ℝ) +
          (Nat.primeCounting (squareRootEndpoint R / (d + 1)) : ℝ) =
        (Nat.primeCounting (squareRootEndpoint R / d) : ℝ) := by
    exact_mod_cast hadd
  rw [← hreal]
  ring

/-- For every fixed `K`, the normalized packet tends to the negative of its
reciprocal Mertens coefficient. -/
theorem squareRootTruncatedUpperMiddlePacketInt_mul_log_div_tendsto
    (K : ℕ) :
    Tendsto
      (fun R : ℕ =>
        (squareRootTruncatedUpperMiddlePacketInt R K : ℝ) *
          Real.log (squareRootEndpoint R : ℝ) /
            (squareRootEndpoint R : ℝ))
      atTop
      (𝓝 (-∑ d ∈ Finset.Icc 1 K,
        (squareRootMertensInt d : ℝ) *
          ((1 : ℝ) / (d : ℝ) -
            (1 : ℝ) / ((d + 1 : ℕ) : ℝ)))) := by
  have hsum :
      Tendsto
        (fun R : ℕ => ∑ d ∈ Finset.Icc 1 K,
          (-(squareRootMertensInt d : ℝ)) *
            ((squareRootReciprocalPrimeLayerCard R d : ℝ) *
              Real.log (squareRootEndpoint R : ℝ) /
                (squareRootEndpoint R : ℝ)))
        atTop
        (𝓝 (∑ d ∈ Finset.Icc 1 K,
          (-(squareRootMertensInt d : ℝ)) *
            ((1 : ℝ) / (d : ℝ) -
              (1 : ℝ) / ((d + 1 : ℕ) : ℝ)))) := by
    apply tendsto_finset_sum
    intro d hdMem
    have hd : 0 < d := (Finset.mem_Icc.mp hdMem).1
    exact tendsto_const_nhds.mul
      (squareRootReciprocalPrimeLayerCard_mul_log_div_tendsto d hd)
  have hsum' :
      Tendsto
        (fun R : ℕ => ∑ d ∈ Finset.Icc 1 K,
          (-(squareRootMertensInt d : ℝ)) *
            ((squareRootReciprocalPrimeLayerCard R d : ℝ) *
              Real.log (squareRootEndpoint R : ℝ) /
                (squareRootEndpoint R : ℝ)))
        atTop
        (𝓝 (-∑ d ∈ Finset.Icc 1 K,
          (squareRootMertensInt d : ℝ) *
            ((1 : ℝ) / (d : ℝ) -
              (1 : ℝ) / ((d + 1 : ℕ) : ℝ)))) := by
    simpa only [neg_mul, Finset.sum_neg_distrib] using hsum
  refine hsum'.congr' ?_
  filter_upwards with R
  unfold squareRootTruncatedUpperMiddlePacketInt
  push_cast
  calc
    (∑ d ∈ Finset.Icc 1 K,
        -(squareRootMertensInt d : ℝ) *
          ((squareRootReciprocalPrimeLayerCard R d : ℝ) *
            Real.log (squareRootEndpoint R : ℝ) /
              (squareRootEndpoint R : ℝ))) =
        ∑ d ∈ Finset.Icc 1 K,
          (Real.log (squareRootEndpoint R : ℝ) /
            (squareRootEndpoint R : ℝ)) *
              (-((squareRootReciprocalPrimeLayerCard R d : ℝ) *
                (squareRootMertensInt d : ℝ))) := by
          apply Finset.sum_congr rfl
          intro d _hd
          ring
    _ = (Real.log (squareRootEndpoint R : ℝ) /
          (squareRootEndpoint R : ℝ)) *
        ∑ d ∈ Finset.Icc 1 K,
          (-((squareRootReciprocalPrimeLayerCard R d : ℝ) *
            (squareRootMertensInt d : ℝ))) := by
          rw [Finset.mul_sum]
    _ = (-∑ d ∈ Finset.Icc 1 K,
          (squareRootReciprocalPrimeLayerCard R d : ℝ) *
            (squareRootMertensInt d : ℝ)) *
        Real.log (squareRootEndpoint R : ℝ) /
          (squareRootEndpoint R : ℝ) := by
          rw [Finset.sum_neg_distrib]
          ring

/-- The exact negative coefficient at depth `18800` forces the packet to be
strictly positive there for every sufficiently large square endpoint. -/
theorem eventually_squareRootTruncatedUpperMiddlePacketInt_18800_pos :
    ∀ᶠ R : ℕ in atTop,
      0 < squareRootTruncatedUpperMiddlePacketInt R 18800 := by
  simpa only [endpointTruncatedUpperMiddlePacketInt_squareRootEndpoint] using
    (eventually_endpointTruncatedUpperMiddlePacketInt_pos_of_coefficient_neg
      (fun R : ℕ => R) squareRootEndpoint 18800
      squareRootEndpoint_tendsto_atTop
      (eventually_squareRoot_le_endpoint_div 18800)
      squareRootPacketReciprocalWeightReal_18800_neg)

/-! ## First-crossing extraction -/

/-- The first reciprocal layer is the nonempty same-sign top block, hence the
integer packet is strictly negative there. -/
theorem squareRootTruncatedUpperMiddlePacketInt_one_neg
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootTruncatedUpperMiddlePacketInt R 1 < 0 := by
  have hpow : R ^ 2 = R * R := by ring
  have hge : 3 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
  have hhalf : R ≤ squareRootEndpoint R / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num)).2
    unfold squareRootEndpoint
    omega
  have hcard :
      squareRootReciprocalPrimeLayerCard R 1 =
        (squareRootTopFibrePrimes R).card := by
    simp [squareRootReciprocalPrimeLayerCard, primeSieveReciprocalInterval,
      primeSieveReciprocalLower, primeSieveReciprocalUpper,
      squareRootTopFibrePrimes, hhalf]
  have hnonempty := one_le_card_squareRootTopFibrePrimes R (by omega)
  have hM1 : squareRootMertensInt 1 = 1 := by
    simp [squareRootMertensInt]
  unfold squareRootTruncatedUpperMiddlePacketInt
  rw [show Finset.Icc 1 1 = ({1} : Finset ℕ) by decide]
  simp [hM1, hcard]
  exact Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one hnonempty)

/-- Eventually the packet has a genuine crossing at a depth bounded by the
absolute constant `18800`. -/
theorem eventually_exists_squareRootPacketCrossesAt_le_18800 :
    ∀ᶠ R : ℕ in atTop,
      ∃ K : ℕ, K ≤ 18800 ∧ SquareRootPacketCrossesAt R K := by
  exact eventually_exists_squareRootPacketCrossesAt_le_of_boundaryRat_neg
    18800 (by norm_num) squareRootPacketReciprocalBoundaryRat_18800_neg

/-- The exact eventual theorem requested by the shallow-depth architecture.
The proof actually supplies a constant-depth crossing. -/
theorem squareRootPacket_eventual_log_crossing :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ,
      ∀ R : ℕ, R₀ ≤ R →
        ∃ K : ℕ,
          K < R ∧
          (K : ℝ) ≤ C * Real.log (R : ℝ) ∧
          squareRootTruncatedUpperMiddlePacketInt R (K - 1) < 0 ∧
          0 ≤ squareRootTruncatedUpperMiddlePacketInt R K := by
  have hlogTop : Tendsto (fun R : ℕ => Real.log (R : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLarge : ∀ᶠ R : ℕ in atTop, (18800 : ℝ) ≤ Real.log (R : ℝ) :=
    hlogTop.eventually_ge_atTop 18800
  have hcross : ∀ᶠ R : ℕ in atTop,
      ∃ K : ℕ, K ≤ 18800 ∧ SquareRootPacketCrossesAt R K :=
    eventually_exists_squareRootPacketCrossesAt_le_18800
  have hall : ∀ᶠ R : ℕ in atTop,
      18800 < R ∧ (18800 : ℝ) ≤ Real.log (R : ℝ) ∧
        ∃ K : ℕ, K ≤ 18800 ∧ SquareRootPacketCrossesAt R K := by
    filter_upwards [eventually_gt_atTop 18800, hlogLarge, hcross]
      with R hR hlog hK
    exact ⟨hR, hlog, hK⟩
  rw [eventually_atTop] at hall
  rcases hall with ⟨R₀, hR₀⟩
  refine ⟨1, by norm_num, R₀, ?_⟩
  intro R hR
  rcases hR₀ R hR with ⟨h18800R, hlog, K, hK18800, hcrossK⟩
  have hKreal : (K : ℝ) ≤ 18800 := by exact_mod_cast hK18800
  have hKlog : (K : ℝ) ≤ Real.log (R : ℝ) := hKreal.trans hlog
  exact ⟨K, hK18800.trans_lt h18800R,
    by simpa using hKlog,
    hcrossK.2.1, hcrossK.2.2⟩

end RHLean.Proof
