import Mathlib
import RHLean.Analysis.SquareRootShallowReciprocalCrossing

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

end RHLean.Proof
