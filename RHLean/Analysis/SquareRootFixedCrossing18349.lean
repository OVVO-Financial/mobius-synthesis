import Mathlib
import RHLean.Analysis.SquareRootShallowReciprocalCrossing
import RHLean.Analysis.SquareRootCanonicalRoughCovariance
import RHLean.Analysis.NativePNTAxer

/-!
# Fixed eventual reciprocal crossing at depth 18349

The existing shallow-crossing argument uses the exact negative coefficient at
`18800` only to extract some crossing `K <= 18800`.  The finite coefficient
actually changes sign between the adjacent depths `18348` and `18349`.

This file records that exact finite fact and combines it with the already-proved
fixed-depth PNT limit.  Consequently the square-root packet crosses at the
single fixed depth `18349` for every sufficiently large endpoint.

This is quantitatively useful for the terminal Eulerian problem: every fresh
prime processed after the crossing is then strictly larger than `18349`.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Proof

open RHLean.Analysis

/-- Exact finite certificate immediately before the fixed crossing. -/
theorem squareRootPacketReciprocalBoundaryRat_18348_pos :
    0 < squareRootPacketReciprocalBoundaryRat 18348 := by
  native_decide

/-- Exact finite certificate at the fixed crossing depth. -/
theorem squareRootPacketReciprocalBoundaryRat_18349_neg :
    squareRootPacketReciprocalBoundaryRat 18349 < 0 := by
  native_decide

/-- Positive rational boundary coefficient gives the corresponding positive
real fixed-depth coefficient. -/
theorem squareRootPacketReciprocalWeightReal_pos_of_boundaryRat_pos
    (K : ℕ) (hK : 0 < squareRootPacketReciprocalBoundaryRat K) :
    0 < ∑ d ∈ Finset.Icc 1 K,
      (squareRootMertensInt d : ℝ) *
        ((1 : ℝ) / (d : ℝ) - (1 : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
  have hcast : (0 : ℝ) < (squareRootPacketReciprocalBoundaryRat K : ℝ) := by
    exact_mod_cast hK
  rw [← squareRootPacketReciprocalWeightRat_eq_boundary] at hcast
  simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_sub, Rat.cast_div,
    Rat.cast_one, Rat.cast_intCast, Rat.cast_natCast] using hcast

/-- A positive fixed-depth coefficient forces the square-root packet to be
strictly negative eventually.  This is the sign-dual of the existing
negative-coefficient/positive-packet lemma. -/
theorem eventually_squareRootTruncatedUpperMiddlePacketInt_neg_of_coefficient_pos
    (K : ℕ)
    (hcoeff :
      0 < ∑ d ∈ Finset.Icc 1 K,
        (squareRootMertensInt d : ℝ) *
          ((1 : ℝ) / (d : ℝ) -
            (1 : ℝ) / ((d + 1 : ℕ) : ℝ))) :
    ∀ᶠ R : ℕ in atTop,
      squareRootTruncatedUpperMiddlePacketInt R K < 0 := by
  let S : ℝ :=
    ∑ d ∈ Finset.Icc 1 K,
      (squareRootMertensInt d : ℝ) *
        ((1 : ℝ) / (d : ℝ) -
          (1 : ℝ) / ((d + 1 : ℕ) : ℝ))
  have hS : 0 < S := by simpa [S] using hcoeff
  have hlimit :
      Tendsto
        (fun R : ℕ =>
          (squareRootTruncatedUpperMiddlePacketInt R K : ℝ) *
            Real.log (squareRootEndpoint R : ℝ) /
              (squareRootEndpoint R : ℝ))
        atTop (𝓝 (-S)) := by
    simpa [S] using squareRootTruncatedUpperMiddlePacketInt_mul_log_div_tendsto K
  have hnormNeg :
      ∀ᶠ R : ℕ in atTop,
        (squareRootTruncatedUpperMiddlePacketInt R K : ℝ) *
            Real.log (squareRootEndpoint R : ℝ) /
              (squareRootEndpoint R : ℝ) < 0 :=
    (tendsto_order.1 hlimit).2 0 (by linarith)
  filter_upwards [squareRootEndpoint_tendsto_atTop.eventually_ge_atTop 2,
    hnormNeg] with R hXR hneg
  have hlog : 0 < Real.log (squareRootEndpoint R : ℝ) :=
    Real.log_pos (by exact_mod_cast hXR)
  have hXreal : 0 < (squareRootEndpoint R : ℝ) := by positivity
  have hmul :
      (squareRootTruncatedUpperMiddlePacketInt R K : ℝ) *
          Real.log (squareRootEndpoint R : ℝ) < 0 :=
    ((div_neg_iff.mp hneg).resolve_left
      (fun hbad => (not_lt_of_ge hXreal.le) hbad.2)).1
  have hcast :
      (squareRootTruncatedUpperMiddlePacketInt R K : ℝ) < 0 :=
    ((mul_neg_iff.mp hmul).resolve_left
      (fun hbad => (not_lt_of_ge hlog.le) hbad.2)).1
  exact_mod_cast hcast

/-- The depth immediately before `18349` is eventually strictly negative. -/
theorem eventually_squareRootTruncatedUpperMiddlePacketInt_18348_neg :
    ∀ᶠ R : ℕ in atTop,
      squareRootTruncatedUpperMiddlePacketInt R 18348 < 0 := by
  apply eventually_squareRootTruncatedUpperMiddlePacketInt_neg_of_coefficient_pos
  exact squareRootPacketReciprocalWeightReal_pos_of_boundaryRat_pos 18348
    squareRootPacketReciprocalBoundaryRat_18348_pos

/-- The packet at depth `18349` is eventually strictly positive. -/
theorem eventually_squareRootTruncatedUpperMiddlePacketInt_18349_pos :
    ∀ᶠ R : ℕ in atTop,
      0 < squareRootTruncatedUpperMiddlePacketInt R 18349 := by
  have hcoeff :=
    squareRootPacketReciprocalWeightReal_neg_of_boundaryRat_neg 18349
      squareRootPacketReciprocalBoundaryRat_18349_neg
  simpa only [endpointTruncatedUpperMiddlePacketInt_squareRootEndpoint] using
    (eventually_endpointTruncatedUpperMiddlePacketInt_pos_of_coefficient_neg
      (fun R : ℕ => R) squareRootEndpoint 18349
      squareRootEndpoint_tendsto_atTop
      (eventually_squareRoot_le_endpoint_div 18349) hcoeff)

/-- **The reciprocal packet crosses at the fixed depth `18349` eventually.** -/
theorem eventually_squareRootPacketCrossesAt_18349 :
    ∀ᶠ R : ℕ in atTop, SquareRootPacketCrossesAt R 18349 := by
  filter_upwards
    [eventually_squareRootTruncatedUpperMiddlePacketInt_18348_neg,
      eventually_squareRootTruncatedUpperMiddlePacketInt_18349_pos]
    with R hprev hcurr
  refine ⟨by norm_num, ?_, hcurr.le⟩
  norm_num
  exact hprev

/-! ## PNT floor on the exact canonical rough covariance seam -/

/-- The elementary native PNT is the minimum acceptable asymptotic baseline.
For every fixed shallow-depth cap and every `eta > 0`, the exact coupled
mean-plus-covariance seam is eventually at most `eta * X_R + K₀`, uniformly over
all valid crossing interpolation seats below the cap.

This is just the repository's elementary Axer conclusion `M(X)=o(X)` pushed
through the exact identity

`coupledTail = M(X_R) - partial`

and then through the exact canonical covariance coordinate change. -/
def SquareRootCanonicalRoughCovarianceNativePNTStatement (K₀ : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∀ᶠ R : ℕ in atTop,
      ∀ K j : ℕ,
        K ≤ K₀ →
        SquareRootPacketCrossesAt R K →
        j ≤ squareRootReciprocalPrimeLayerCard R K →
        0 ≤ squareRootCrossingLayerPartialPacketInt R K j →
        squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ) →
        ‖squareRootPostCrossingCanonicalBaseline R K j -
            (squareRootCanonicalRoughCofactorCard R : ℂ) *
              (squareRootCanonicalRoughParityMean R *
                  squareRootCanonicalRoughResponseMean R +
                squareRootCanonicalRoughCovariance R)‖ ≤
          η * (squareRootEndpoint R : ℝ) + (K₀ : ℝ)

/-- **Native-PNT floor for the covariance seam.**  No zero-free region or
strong-Mertens estimate is used. -/
theorem squareRootCanonicalRoughCovarianceNativePNT
    (K₀ : ℕ) :
    SquareRootCanonicalRoughCovarianceNativePNTStatement K₀ := by
  intro η hη
  have hratio :
      Tendsto
        (fun R : ℕ =>
          nativeMertensSummatory (squareRootEndpoint R) /
            (squareRootEndpoint R : ℝ))
        atTop (𝓝 0) :=
    nativeMertens_div_atTop_zero.comp squareRootEndpoint_tendsto_atTop
  have hupper :
      ∀ᶠ R : ℕ in atTop,
        nativeMertensSummatory (squareRootEndpoint R) /
            (squareRootEndpoint R : ℝ) < η :=
    (tendsto_order.1 hratio).2 η hη
  have hlower :
      ∀ᶠ R : ℕ in atTop,
        -η < nativeMertensSummatory (squareRootEndpoint R) /
            (squareRootEndpoint R : ℝ) :=
    (tendsto_order.1 hratio).1 (-η) (by linarith)
  have hsmall :
      ∀ᶠ R : ℕ in atTop,
        |nativeMertensSummatory (squareRootEndpoint R) /
            (squareRootEndpoint R : ℝ)| < η := by
    filter_upwards [hlower, hupper] with R hlo hhi
    exact abs_lt.mpr ⟨hlo, hhi⟩
  filter_upwards [hsmall, eventually_ge_atTop (3 : ℕ)] with R hsmallR hR
  intro K j hK hcross _hj hV0 hVK
  have hendpoint : 3 ≤ squareRootEndpoint R := by
    have hsquare : 2 ^ 2 ≤ R ^ 2 :=
      Nat.pow_le_pow_left (by omega : 2 ≤ R) 2
    unfold squareRootEndpoint
    omega
  have hXpos : 0 < (squareRootEndpoint R : ℝ) := by
    exact_mod_cast (show 0 < squareRootEndpoint R by omega)
  have hMdiv :
      |nativeMertensSummatory (squareRootEndpoint R)| /
          (squareRootEndpoint R : ℝ) < η := by
    simpa [abs_div, abs_of_pos hXpos] using hsmallR
  have hMreal :
      |nativeMertensSummatory (squareRootEndpoint R)| ≤
        η * (squareRootEndpoint R : ℝ) := by
    exact ((div_lt_iff₀ hXpos).mp hMdiv).le
  have hM :
      ‖mertensSummatory (squareRootEndpoint R)‖ ≤
        η * (squareRootEndpoint R : ℝ) := by
    rw [norm_mertensSummatory_eq_abs_nativeMertensSummatory]
    exact hMreal
  have hV :
      ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ ≤
        (K₀ : ℝ) := by
    rw [Complex.norm_intCast, abs_of_nonneg]
    · exact_mod_cast
        (le_trans (Int.le_of_lt hVK)
          (by exact_mod_cast hK : (K : ℤ) ≤ K₀))
    · exact_mod_cast hV0
  have hKR : K < R := by
    rcases squareRootPacketCrossing_has_postRootPrime hcross with
      ⟨q, _hqPrime, hRq, _hqX, hqK⟩
    rw [← hqK]
    exact squareRootEndpoint_div_lt_root_of_root_le (by omega) (by omega)
  have htail :
      ‖squareRootPostCrossingCoupledTail R K j‖ ≤
        η * (squareRootEndpoint R : ℝ) + (K₀ : ℝ) := by
    rw [postCrossingCoupledTail_eq_mertens_sub_partial R K j hR]
    calc
      ‖mertensSummatory (squareRootEndpoint R) -
          ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ ≤
          ‖mertensSummatory (squareRootEndpoint R)‖ +
            ‖((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ)‖ :=
        norm_sub_le _ _
      _ ≤ η * (squareRootEndpoint R : ℝ) + (K₀ : ℝ) :=
        add_le_add hM hV
  rw [squareRootPostCrossingCoupledTail_eq_baseline_sub_mean_covariance
    R K j hR hcross.1 hKR] at htail
  exact htail

/-- Squared form of the native-PNT floor.  In particular the exact covariance
seam has energy `o(X_R^2) = o(R^4)` for every fixed shallow cap. -/
def SquareRootCanonicalRoughCovarianceNativePNTEnergyStatement (K₀ : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∀ᶠ R : ℕ in atTop,
      ∀ K j : ℕ,
        K ≤ K₀ →
        SquareRootPacketCrossesAt R K →
        j ≤ squareRootReciprocalPrimeLayerCard R K →
        0 ≤ squareRootCrossingLayerPartialPacketInt R K j →
        squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ) →
        ‖squareRootPostCrossingCanonicalBaseline R K j -
            (squareRootCanonicalRoughCofactorCard R : ℂ) *
              (squareRootCanonicalRoughParityMean R *
                  squareRootCanonicalRoughResponseMean R +
                squareRootCanonicalRoughCovariance R)‖ ^ 2 ≤
          (η * (squareRootEndpoint R : ℝ) + (K₀ : ℝ)) ^ 2

/-- **Native-PNT energy floor for the covariance seam.** -/
theorem squareRootCanonicalRoughCovarianceNativePNTEnergy
    (K₀ : ℕ) :
    SquareRootCanonicalRoughCovarianceNativePNTEnergyStatement K₀ := by
  intro η hη
  have hnormEventually := squareRootCanonicalRoughCovarianceNativePNT K₀ η hη
  filter_upwards [hnormEventually] with R hnormR
  intro K j hK hcross hj hV0 hVK
  have hnorm := hnormR K j hK hcross hj hV0 hVK
  have hright :
      0 ≤ η * (squareRootEndpoint R : ℝ) + (K₀ : ℝ) := by
    positivity
  exact (sq_le_sq₀ (norm_nonneg _) hright).2 hnorm

/-! ## Fixed-depth residual sharpening -/

/-- Exact finite Mertens step at the certified crossing depth.  The first
interpolation overshoot at `18349` is therefore strictly smaller than `21`, not
merely smaller than the generic depth cap `18349`. -/
theorem squareRootMertensInt_18349_eq_neg_twentyOne :
    squareRootMertensInt 18349 = -21 := by
  native_decide

/-- A genuine crossing at `18349` has an interpolation seat with residual in
`[0,21)`. -/
theorem squareRootPacketCrossing18349_exists_partialResidual_lt_twentyOne
    {R : ℕ} (hcross : SquareRootPacketCrossesAt R 18349) :
    ∃ j : ℕ,
      j ≤ squareRootReciprocalPrimeLayerCard R 18349 ∧
        0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j ∧
        squareRootCrossingLayerPartialPacketInt R 18349 j < 21 := by
  rcases squareRootPacketCrossing_exists_partial_residual hcross with
    ⟨j, hj, hV0, hVstep⟩
  rw [squareRootMertensInt_18349_eq_neg_twentyOne] at hVstep
  norm_num at hVstep
  exact ⟨j, hj, hV0, hVstep⟩

/-- **PNT floor with the actual fixed-depth overshoot.**  At the certified
crossing, the exact canonical rough seam eventually obeys `eta * X_R + 21` for
one genuine interpolation seat.  The former generic `+18349` charge disappears. -/
theorem eventually_exists_squareRootCanonicalRoughCovarianceNativePNT_18349_twentyOne
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ R : ℕ in atTop,
      ∃ j : ℕ,
        j ≤ squareRootReciprocalPrimeLayerCard R 18349 ∧
          0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j ∧
          squareRootCrossingLayerPartialPacketInt R 18349 j < 21 ∧
          ‖squareRootPostCrossingCanonicalBaseline R 18349 j -
              (squareRootCanonicalRoughCofactorCard R : ℂ) *
                (squareRootCanonicalRoughParityMean R *
                    squareRootCanonicalRoughResponseMean R +
                  squareRootCanonicalRoughCovariance R)‖ ≤
            η * (squareRootEndpoint R : ℝ) + 21 := by
  have hratio :
      Tendsto
        (fun R : ℕ =>
          nativeMertensSummatory (squareRootEndpoint R) /
            (squareRootEndpoint R : ℝ))
        atTop (𝓝 0) :=
    nativeMertens_div_atTop_zero.comp squareRootEndpoint_tendsto_atTop
  have hupper :
      ∀ᶠ R : ℕ in atTop,
        nativeMertensSummatory (squareRootEndpoint R) /
            (squareRootEndpoint R : ℝ) < η :=
    (tendsto_order.1 hratio).2 η hη
  have hlower :
      ∀ᶠ R : ℕ in atTop,
        -η < nativeMertensSummatory (squareRootEndpoint R) /
            (squareRootEndpoint R : ℝ) :=
    (tendsto_order.1 hratio).1 (-η) (by linarith)
  have hsmall :
      ∀ᶠ R : ℕ in atTop,
        |nativeMertensSummatory (squareRootEndpoint R) /
            (squareRootEndpoint R : ℝ)| < η := by
    filter_upwards [hlower, hupper] with R hlo hhi
    exact abs_lt.mpr ⟨hlo, hhi⟩
  filter_upwards [hsmall, eventually_squareRootPacketCrossesAt_18349,
    eventually_ge_atTop (18350 : ℕ)] with R hsmallR hcross hRlarge
  rcases squareRootPacketCrossing18349_exists_partialResidual_lt_twentyOne hcross with
    ⟨j, hj, hV0, hV21⟩
  have hR : 3 ≤ R := by omega
  have hXnat : 0 < squareRootEndpoint R := by
    have hsquare : 2 ^ 2 ≤ R ^ 2 :=
      Nat.pow_le_pow_left (by omega : 2 ≤ R) 2
    unfold squareRootEndpoint
    omega
  have hXpos : 0 < (squareRootEndpoint R : ℝ) := by
    exact_mod_cast hXnat
  have hMdiv :
      |nativeMertensSummatory (squareRootEndpoint R)| /
          (squareRootEndpoint R : ℝ) < η := by
    simpa [abs_div, abs_of_pos hXpos] using hsmallR
  have hM :
      ‖mertensSummatory (squareRootEndpoint R)‖ ≤
        η * (squareRootEndpoint R : ℝ) := by
    rw [norm_mertensSummatory_eq_abs_nativeMertensSummatory]
    exact ((div_lt_iff₀ hXpos).mp hMdiv).le
  have hVInt :
      squareRootCrossingLayerPartialPacketInt R 18349 j ≤ (21 : ℤ) :=
    Int.le_of_lt hV21
  have hVReal :
      ((squareRootCrossingLayerPartialPacketInt R 18349 j : ℤ) : ℝ) ≤ 21 := by
    exact_mod_cast hVInt
  have hVNonnegReal :
      0 ≤ ((squareRootCrossingLayerPartialPacketInt R 18349 j : ℤ) : ℝ) := by
    exact_mod_cast hV0
  have hV :
      ‖((squareRootCrossingLayerPartialPacketInt R 18349 j : ℤ) : ℂ)‖ ≤
        (21 : ℝ) := by
    simpa [Complex.norm_intCast, abs_of_nonneg hVNonnegReal] using hVReal
  have htail :
      ‖squareRootPostCrossingCoupledTail R 18349 j‖ ≤
        η * (squareRootEndpoint R : ℝ) + 21 := by
    rw [postCrossingCoupledTail_eq_mertens_sub_partial R 18349 j hR]
    exact (norm_sub_le _ _).trans (add_le_add hM hV)
  have hKR : 18349 < R := by omega
  rw [squareRootPostCrossingCoupledTail_eq_baseline_sub_mean_covariance
    R 18349 j hR hcross.1 hKR] at htail
  exact ⟨j, hj, hV0, hV21, htail⟩

/-- Energy form of the fixed-depth PNT floor with the exact `21` overshoot. -/
theorem eventually_exists_squareRootCanonicalRoughCovarianceNativePNTEnergy_18349_twentyOne
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ R : ℕ in atTop,
      ∃ j : ℕ,
        j ≤ squareRootReciprocalPrimeLayerCard R 18349 ∧
          0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j ∧
          squareRootCrossingLayerPartialPacketInt R 18349 j < 21 ∧
          ‖squareRootPostCrossingCanonicalBaseline R 18349 j -
              (squareRootCanonicalRoughCofactorCard R : ℂ) *
                (squareRootCanonicalRoughParityMean R *
                    squareRootCanonicalRoughResponseMean R +
                  squareRootCanonicalRoughCovariance R)‖ ^ 2 ≤
            (η * (squareRootEndpoint R : ℝ) + 21) ^ 2 := by
  filter_upwards
    [eventually_exists_squareRootCanonicalRoughCovarianceNativePNT_18349_twentyOne
      η hη] with R hR
  rcases hR with ⟨j, hj, hV0, hV21, hnorm⟩
  refine ⟨j, hj, hV0, hV21, ?_⟩
  have hright : 0 ≤ η * (squareRootEndpoint R : ℝ) + 21 := by positivity
  exact (sq_le_sq₀ (norm_nonneg _) hright).2 hnorm

/-! ## Strict subexponential benchmark on the same seam -/

/-- The exact mean-plus-covariance seam also inherits the repository's
premise-free strong-Mertens subexponential envelope.  This is retained only as
a stronger classical benchmark above the native-PNT floor:

`(C * X_R * exp (-c * (log X_R)^(1/10)) + K₀)^2`.

The seam remains fully coupled; no mean/covariance split or support replacement
is used. -/
def SquareRootCanonicalRoughCovarianceSubexpEnergyStatement (K₀ : ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ R K j : ℕ,
      3 ≤ R →
      K ≤ K₀ →
      SquareRootPacketCrossesAt R K →
      j ≤ squareRootReciprocalPrimeLayerCard R K →
      0 ≤ squareRootCrossingLayerPartialPacketInt R K j →
      squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ) →
      ‖squareRootPostCrossingCanonicalBaseline R K j -
          (squareRootCanonicalRoughCofactorCard R : ℂ) *
            (squareRootCanonicalRoughParityMean R *
                squareRootCanonicalRoughResponseMean R +
              squareRootCanonicalRoughCovariance R)‖ ^ 2 ≤
        (C * (squareRootEndpoint R : ℝ) *
            Real.exp
              (-c *
                (Real.log (squareRootEndpoint R : ℝ)) ^ ((1 : ℝ) / 10)) +
          (K₀ : ℝ)) ^ 2

/-- **Strictly reduced covariance-seam energy bound.** -/
theorem squareRootCanonicalRoughCovarianceSubexpEnergy
    (K₀ : ℕ) :
    SquareRootCanonicalRoughCovarianceSubexpEnergyStatement K₀ := by
  rcases postCrossingCoupledTailSubexp K₀ with ⟨c, C, hc, hC, htail⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro R K j hR hK hcross hj hV0 hVK
  have hKR : K < R := by
    rcases squareRootPacketCrossing_has_postRootPrime hcross with
      ⟨q, _hqPrime, hRq, _hqX, hqK⟩
    rw [← hqK]
    exact squareRootEndpoint_div_lt_root_of_root_le (by omega) (by omega)
  have hnorm := htail R K j hR hK hcross hj hV0 hVK
  rw [squareRootPostCrossingCoupledTail_eq_baseline_sub_mean_covariance
    R K j hR hcross.1 hKR] at hnorm
  have hright :
      0 ≤ C * (squareRootEndpoint R : ℝ) *
          Real.exp
            (-c *
              (Real.log (squareRootEndpoint R : ℝ)) ^ ((1 : ℝ) / 10)) +
        (K₀ : ℝ) := by
    positivity
  exact (sq_le_sq₀ (norm_nonneg _) hright).2 hnorm

end RHLean.Proof
