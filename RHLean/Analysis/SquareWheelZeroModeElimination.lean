import Mathlib
import RHLean.Analysis.SquareWheelQuadraticSampling

/-!
# Exact elimination of the square-wheel zero frequency

At a complete-square sample, the actual wheel residual is the sum of:

* the nonzero quadratic response; and
* the additive zero mode, which is a strict finite self-coupling to the complete
  wheel endpoint residual.

This file removes that self-coupling by exact algebra. It also records the
incomplete-square interpolation bound for the concrete primorial wheel. The
interpolation error is bounded by one square gap, whose square is `O(x)`.

No analytic estimate for the remaining nonzero response is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- The part of the square-sampled corrected wheel response carried only by
nonzero additive frequencies. Signs are left untouched. -/
def squareWheelNonzeroSampleResponse
    (W : PrimeWheelFiniteSystem) (n : ℕ) : ℂ :=
  ∑ r : ZMod W.modulus,
    if r = 0 then 0 else squareWheelQuadraticFrequencyAtom W n r

/-- Complex zero-mode coupling coefficient at the `n`th square sample. -/
def squareWheelSampleRatio
    (W : PrimeWheelFiniteSystem) (n : ℕ) : ℂ :=
  ((W.modulus : ℂ)⁻¹) * (squareWheelSampleLength W n : ℂ)

/-- The full square response splits exactly into its signed nonzero response and
the zero-frequency self-coupling. -/
theorem squareWheelSampleResponse_eq_nonzero_add_zero
    (W : PrimeWheelFiniteSystem) (n : ℕ) :
    squareWheelSampleResponse W n =
      squareWheelNonzeroSampleResponse W n +
        squareWheelSampleRatio W n *
          (((W.residual W.upper : ℤ) : ℂ)) := by
  classical
  unfold squareWheelSampleResponse squareWheelNonzeroSampleResponse
  calc
    (∑ r : ZMod W.modulus, squareWheelSampleFrequencyAtom W n r) =
        ∑ r : ZMod W.modulus,
          ((if r = 0 then 0 else squareWheelQuadraticFrequencyAtom W n r) +
          (if r = 0 then
            ((W.modulus : ℂ)⁻¹) * (((W.residual W.upper : ℤ) : ℂ)) *
              (squareWheelSampleLength W n : ℂ)
          else 0)) := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hr0 : r = 0
      · subst r
        simp [squareWheelSampleFrequencyAtom]
      · simp [squareWheelSampleFrequencyAtom, hr0]
    _ =
        (∑ r : ZMod W.modulus,
          if r = 0 then 0 else squareWheelQuadraticFrequencyAtom W n r) +
        (∑ r : ZMod W.modulus,
          if r = 0 then
            ((W.modulus : ℂ)⁻¹) * (((W.residual W.upper : ℤ) : ℂ)) *
              (squareWheelSampleLength W n : ℂ)
          else 0) := by
      rw [Finset.sum_add_distrib]
    _ = squareWheelNonzeroSampleResponse W n +
        squareWheelSampleRatio W n *
          (((W.residual W.upper : ℤ) : ℂ)) := by
      simp [squareWheelNonzeroSampleResponse, squareWheelSampleRatio]
      ring

/-- A square sample lying below the wheel endpoint has coupling coefficient
strictly different from one. -/
theorem squareWheelSampleRatio_ne_one
    (W : PrimeWheelFiniteSystem) (n : ℕ)
    (hupper : squarePrefixEndpoint n ≤ W.upper) :
    squareWheelSampleRatio W n ≠ 1 := by
  have hNle : squareWheelSampleLength W n ≤ squarePrefixEndpoint n := by
    exact Nat.sub_le _ _
  have hNlt : squareWheelSampleLength W n < W.modulus :=
    lt_of_le_of_lt (hNle.trans hupper) W.upper_lt_modulus
  have hQne : (W.modulus : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt W.modulus_pos)
  intro hratio
  unfold squareWheelSampleRatio at hratio
  have hcast :
      (squareWheelSampleLength W n : ℂ) = (W.modulus : ℂ) := by
    calc
      (squareWheelSampleLength W n : ℂ) =
          (W.modulus : ℂ) *
            ((W.modulus : ℂ)⁻¹ * (squareWheelSampleLength W n : ℂ)) := by
        field_simp [hQne]
      _ = (W.modulus : ℂ) * 1 := by rw [hratio]
      _ = (W.modulus : ℂ) := by ring
  have hreal :
      (squareWheelSampleLength W n : ℝ) = (W.modulus : ℝ) := by
    simpa using congrArg Complex.re hcast
  have hnat : squareWheelSampleLength W n = W.modulus := by
    exact_mod_cast hreal
  exact (Nat.ne_of_lt hNlt) hnat

/-- The actual arithmetic residual at a square endpoint is the nonzero response
plus the explicit endpoint self-coupling. -/
theorem primeWheelResidual_squareEndpoint_eq_nonzero_add_zero
    (W : PrimeWheelFiniteSystem) (n : ℕ)
    (hlower : W.lower < squarePrefixEndpoint n)
    (hupper : squarePrefixEndpoint n ≤ W.upper) :
    (((W.residual (squarePrefixEndpoint n) : ℤ) : ℂ)) =
      squareWheelNonzeroSampleResponse W n +
        squareWheelSampleRatio W n *
          (((W.residual W.upper : ℤ) : ℂ)) := by
  rw [primeWheelResidual_squareEndpoint_eq_squareWheelSampleResponse
    W n hlower hupper]
  exact squareWheelSampleResponse_eq_nonzero_add_zero W n

/-- Tail from a complete-square sample to the complete wheel endpoint. -/
def squareWheelEndpointTail
    (W : PrimeWheelFiniteSystem) (n : ℕ) : ℂ :=
  (((W.residual W.upper : ℤ) : ℂ)) -
    (((W.residual (squarePrefixEndpoint n) : ℤ) : ℂ))

/-- Exact zero-mode elimination at a distinguished square sample. The endpoint
residual is expressed only through the nonzero response and the final short
tail. -/
theorem primeWheelEndpointResidual_eq_eliminated
    (W : PrimeWheelFiniteSystem) (nStar : ℕ)
    (hlower : W.lower < squarePrefixEndpoint nStar)
    (hupper : squarePrefixEndpoint nStar ≤ W.upper) :
    (((W.residual W.upper : ℤ) : ℂ)) =
      (squareWheelNonzeroSampleResponse W nStar +
        squareWheelEndpointTail W nStar) /
      (1 - squareWheelSampleRatio W nStar) := by
  have hsample :=
    primeWheelResidual_squareEndpoint_eq_nonzero_add_zero
      W nStar hlower hupper
  have hden : (1 : ℂ) - squareWheelSampleRatio W nStar ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (squareWheelSampleRatio_ne_one W nStar hupper))
  apply (eq_div_iff hden).2
  unfold squareWheelEndpointTail
  rw [hsample]
  ring

/-- After eliminating the endpoint zero mode at `nStar`, every other square
sample depends only on the two nonzero responses and the same short endpoint
tail. -/
theorem primeWheelResidual_squareEndpoint_eq_eliminated
    (W : PrimeWheelFiniteSystem) (n nStar : ℕ)
    (hlower : W.lower < squarePrefixEndpoint n)
    (hupper : squarePrefixEndpoint n ≤ W.upper)
    (hlowerStar : W.lower < squarePrefixEndpoint nStar)
    (hupperStar : squarePrefixEndpoint nStar ≤ W.upper) :
    (((W.residual (squarePrefixEndpoint n) : ℤ) : ℂ)) =
      squareWheelNonzeroSampleResponse W n +
        squareWheelSampleRatio W n *
          ((squareWheelNonzeroSampleResponse W nStar +
            squareWheelEndpointTail W nStar) /
            (1 - squareWheelSampleRatio W nStar)) := by
  rw [primeWheelResidual_squareEndpoint_eq_nonzero_add_zero
    W n hlower hupper]
  rw [primeWheelEndpointResidual_eq_eliminated
    W nStar hlowerStar hupperStar]

/-- Consecutive complete-square endpoints differ by the exact gap `2n+3`. -/
theorem squarePrefixEndpoint_succ_eq_add_gap
    (n : ℕ) :
    squarePrefixEndpoint (n + 1) = squarePrefixEndpoint n + (2 * n + 3) := by
  have hthis := squarePrefixEndpoint_add_one n
  have hnext := squarePrefixEndpoint_add_one (n + 1)
  have hidx : n + 1 + 1 = n + 2 := by omega
  have hsquare : (n + 2) ^ 2 = (n + 1) ^ 2 + (2 * n + 3) := by
    ring
  rw [hidx, hsquare, ← hthis] at hnext
  omega

/-- A point between consecutive square samples is less than one square gap from
the previous sample. -/
theorem sub_squarePrefixEndpoint_lt_gap
    (n x : ℕ)
    (hleft : squarePrefixEndpoint n ≤ x)
    (hright : x < squarePrefixEndpoint (n + 1)) :
    x - squarePrefixEndpoint n < 2 * n + 3 := by
  rw [squarePrefixEndpoint_succ_eq_add_gap n] at hright
  omega

/-- The square of one square-gap length is at most `9(x+1)` whenever the left
square endpoint is at most `x`. This is an explicit square-root-scale bound. -/
theorem squareGap_sq_le_nine_mul_succ
    (n x : ℕ)
    (hleft : squarePrefixEndpoint n ≤ x) :
    (2 * n + 3) ^ 2 ≤ 9 * (x + 1) := by
  have hsquare : (n + 1) ^ 2 ≤ x + 1 := by
    have hclock := squarePrefixEndpoint_add_one n
    omega
  have hgap : 2 * n + 3 ≤ 3 * (n + 1) := by omega
  calc
    (2 * n + 3) ^ 2 ≤ (3 * (n + 1)) ^ 2 := by
      gcongr
    _ = 9 * (n + 1) ^ 2 := by ring
    _ ≤ 9 * (x + 1) := Nat.mul_le_mul_left 9 hsquare

/-- Inside one primorial block, changing the endpoint from a complete square to
an arbitrary later point costs at most the interval length. -/
theorem norm_primorialWheelResidual_sub_squareEndpoint_le_gap
    (k n x : ℕ)
    (hsampleLower : primorialBlockLower k ≤ squarePrefixEndpoint n)
    (hleft : squarePrefixEndpoint n ≤ x)
    (hxUpper : x ≤ primorialBlockUpper k) :
    ‖((((primorialWheelSystem k).residual x : ℤ) : ℂ)) -
        ((((primorialWheelSystem k).residual
          (squarePrefixEndpoint n) : ℤ) : ℂ))‖ ≤
      ((x - squarePrefixEndpoint n : ℕ) : ℝ) := by
  have hxLower : primorialBlockLower k ≤ x := hsampleLower.trans hleft
  have hsampleUpper : squarePrefixEndpoint n ≤ primorialBlockUpper k :=
    hleft.trans hxUpper
  rw [RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
      k hxLower hxUpper,
    RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
      k hsampleLower hsampleUpper]
  calc
    ‖(mertensSummatory x - mertensSummatory (primorialBlockLower k)) -
        (mertensSummatory (squarePrefixEndpoint n) -
          mertensSummatory (primorialBlockLower k))‖ =
        ‖mertensSummatory x - mertensSummatory (squarePrefixEndpoint n)‖ := by
      congr 1
      ring
    _ ≤ ((x - squarePrefixEndpoint n : ℕ) : ℝ) :=
      norm_mertensSummatory_sub_le (squarePrefixEndpoint n) x hleft

/-- Interpolation from square samples to arbitrary points in the same primorial
block loses less than one complete square gap. -/
theorem norm_primorialWheelResidual_sub_squareEndpoint_lt_squareGap
    (k n x : ℕ)
    (hsampleLower : primorialBlockLower k ≤ squarePrefixEndpoint n)
    (hleft : squarePrefixEndpoint n ≤ x)
    (hright : x < squarePrefixEndpoint (n + 1))
    (hxUpper : x ≤ primorialBlockUpper k) :
    ‖((((primorialWheelSystem k).residual x : ℤ) : ℂ)) -
        ((((primorialWheelSystem k).residual
          (squarePrefixEndpoint n) : ℤ) : ℂ))‖ <
      ((2 * n + 3 : ℕ) : ℝ) := by
  have hnorm :=
    norm_primorialWheelResidual_sub_squareEndpoint_le_gap
      k n x hsampleLower hleft hxUpper
  have hgap := sub_squarePrefixEndpoint_lt_gap n x hleft hright
  exact hnorm.trans_lt (by exact_mod_cast hgap)

/-- Squared interpolation form: the incomplete-square fragment is bounded by
`9(x+1)`, hence is exactly at square-root scale before squaring. -/
theorem norm_sq_primorialWheelResidual_sub_squareEndpoint_lt_nine_mul_succ
    (k n x : ℕ)
    (hsampleLower : primorialBlockLower k ≤ squarePrefixEndpoint n)
    (hleft : squarePrefixEndpoint n ≤ x)
    (hright : x < squarePrefixEndpoint (n + 1))
    (hxUpper : x ≤ primorialBlockUpper k) :
    ‖((((primorialWheelSystem k).residual x : ℤ) : ℂ)) -
        ((((primorialWheelSystem k).residual
          (squarePrefixEndpoint n) : ℤ) : ℂ))‖ ^ 2 <
      9 * ((x + 1 : ℕ) : ℝ) := by
  let d : ℝ :=
    ‖((((primorialWheelSystem k).residual x : ℤ) : ℂ)) -
      ((((primorialWheelSystem k).residual
        (squarePrefixEndpoint n) : ℤ) : ℂ))‖
  have hd : d < ((2 * n + 3 : ℕ) : ℝ) := by
    dsimp [d]
    exact norm_primorialWheelResidual_sub_squareEndpoint_lt_squareGap
      k n x hsampleLower hleft hright hxUpper
  have hd0 : 0 ≤ d := by
    dsimp [d]
    exact norm_nonneg _
  have hgap0 : 0 ≤ ((2 * n + 3 : ℕ) : ℝ) := by positivity
  have hsq : d ^ 2 < ((2 * n + 3 : ℕ) : ℝ) ^ 2 := by
    nlinarith
  have hgapNat := squareGap_sq_le_nine_mul_succ n x hleft
  have hgapReal :
      ((2 * n + 3 : ℕ) : ℝ) ^ 2 ≤ 9 * ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast hgapNat
  exact hsq.trans_le hgapReal

/-- If `nStar` is the last complete square endpoint in a primorial block, the
endpoint tail appearing in the zero-mode elimination is itself square-root
scale. -/
theorem norm_sq_primorialSquareWheelEndpointTail_lt_nine_mul_succ
    (k nStar : ℕ)
    (hsampleLower : primorialBlockLower k ≤ squarePrefixEndpoint nStar)
    (hsampleUpper : squarePrefixEndpoint nStar ≤ primorialBlockUpper k)
    (hlast : primorialBlockUpper k < squarePrefixEndpoint (nStar + 1)) :
    ‖squareWheelEndpointTail (primorialWheelSystem k) nStar‖ ^ 2 <
      9 * (((primorialBlockUpper k) + 1 : ℕ) : ℝ) := by
  unfold squareWheelEndpointTail
  change
    ‖((((primorialWheelSystem k).residual (primorialBlockUpper k) : ℤ) : ℂ)) -
        ((((primorialWheelSystem k).residual
          (squarePrefixEndpoint nStar) : ℤ) : ℂ))‖ ^ 2 <
      9 * (((primorialBlockUpper k) + 1 : ℕ) : ℝ)
  exact norm_sq_primorialWheelResidual_sub_squareEndpoint_lt_nine_mul_succ
    k nStar (primorialBlockUpper k) hsampleLower hsampleUpper hlast le_rfl

end RHLean.Analysis