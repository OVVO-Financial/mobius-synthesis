import Mathlib
import RHLean.Analysis.AffineExcursion
import RHLean.Analysis.PrimeSieveBackwardAffineExcursion

/-!
# Sharp affine excursion for the Abel face at the canonical pin

`RHLean.Analysis.PrimeSieveBackwardAffineExcursion` runs the backward
excursion at the canonical pin with the *crude* Lipschitz constant
`C = 1 + K/log(y+1)`, `K = x/(y+1)` — the `K*(h+1)` relaxation of the floor
increment sum (`primeSieveFloorIncrementSum_le`).  This module replaces that
relaxation by the harmonic bound

```text
sum_{d <= K} (floor((x+h)/d) - floor(x/d))  <=  h * H_K + K,
    H_K = sum_{d <= K} 1/d,
```

which follows from the per-`d` bound `h/d + 1` (`floor_add_div_sub_le`, until
now recorded but unused).  Threaded through the sharp increment bound
`primeSieveMoebiusPrefixSum_increment_norm_le` this yields the genuine affine
increment shape `A*h + B` with

```text
A = primeSieveAffineSlope y K     = 1 + H_K / log (y+1),
B = primeSieveAffineIntercept y K = K / log (y+1),
```

the record-023 constants: at the canonical pin `K = y`, so `A = 2 + o(1)`
(explicitly `A <= 2 + 1/log(y+1)`, `primeSieveAffineSlope_le`) while
`B ~ 2 sqrt x / log x` remains of `sqrt x` scale.

## Why the intercept is unavoidable

The unit-step floor jump is exactly the divisor indicator
(`floor_succ_div_sub_eq_divisor_indicator`), so a unit step costs the full
truncated divisor count `tau_{<=K}(x+1)`
(`sum_floor_succ_div_sub_eq_card_divisors`), which along divisor-rich `x+1`
exceeds every fixed power of `log x`.  No slope-only (`B = 0`) uniform bound
exists; in the per-`d` bound `h/d + 1` the `h/d` term is the density of
multiples of `d` (the slope, aggregating to `h*H_K`) and the `+1` absorbs the
at-most-one extra floor jump from the phase `x mod d` (the intercept,
aggregating to `K`).  The exact multiple count is
`floor_add_div_sub_eq_card_multiples`.

## The repaired window

At the canonical pin the quotient is exactly stable on every backward step
`t <= y` (`primeSieveCanonicalPin_backward_stable`), so slope and intercept
are *constant* along the whole backward walk and the abstract affine
excursion applies with cap `y`.  The window is

```text
W = primeSieveAffineBackwardWindow y = min y (floor ((H/2 - B)/A)),
```

inclusive convention `t <= W`.  Honesty notes:

* the excursion and moment theorems carry the *explicit* height hypothesis
  `2B < H` — they visibly do not fire for free;
* nonemptiness is certified separately (`one_le_primeSieveAffineBackwardWindow`
  at threshold `H >= 2(A+B) ~ 4 sqrt x / log x`, and `n <= W` under
  `H >= 2(A*n + B)`); the threshold is unchanged from the crude module — the
  gain is growth past the threshold (`W ~ min(sqrt x, H/4)` instead of
  `H log x / (4 sqrt x)`), not the threshold itself;
* when `H >= x^(1/2+eps)` the cap `y` binds and the `2k`-th moment lower
  bound is `(H/2)^(2k) * (y+1)`, not `H^(2k+1)`-scale.

Everything is unconditional arithmetic; no hypothesis on `pi`, `Li`, or the
Moebius sum is used anywhere.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## The harmonic weight and the affine constants -/

/-- The truncated harmonic sum `H_K = Σ_{d=1}^{K} 1/d`, as a real. -/
def harmonicWeight (K : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 K, ((d : ℝ))⁻¹

theorem harmonicWeight_nonneg (K : ℕ) : 0 ≤ harmonicWeight K := by
  unfold harmonicWeight
  refine Finset.sum_nonneg ?_
  intro d _
  positivity

/-- Bridge to mathlib's harmonic number. -/
theorem harmonicWeight_eq_harmonic (K : ℕ) :
    harmonicWeight K = ((harmonic K : ℚ) : ℝ) := by
  unfold harmonicWeight
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- The affine slope at prime cutoff `y` and support size `K`:
`A = 1 + H_K / log (y+1)`.  At the canonical pin `K = y` and this is `2 + o(1)`. -/
def primeSieveAffineSlope (y K : ℕ) : ℝ :=
  1 + harmonicWeight K / Real.log ((y : ℝ) + 1)

/-- The affine intercept `B = K / log (y+1)` (the record-023 constant; at
`y ≍ √x` this is `≈ 2√x / log x`). -/
def primeSieveAffineIntercept (y K : ℕ) : ℝ :=
  (K : ℝ) / Real.log ((y : ℝ) + 1)

theorem one_le_primeSieveAffineSlope (y K : ℕ) (hy : 1 ≤ y) :
    1 ≤ primeSieveAffineSlope y K := by
  have hy' : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : 0 < Real.log ((y : ℝ) + 1) := Real.log_pos (by linarith)
  have hdiv : 0 ≤ harmonicWeight K / Real.log ((y : ℝ) + 1) :=
    div_nonneg (harmonicWeight_nonneg K) (le_of_lt hlogy)
  unfold primeSieveAffineSlope
  linarith

theorem primeSieveAffineSlope_pos (y K : ℕ) (hy : 1 ≤ y) :
    0 < primeSieveAffineSlope y K :=
  lt_of_lt_of_le zero_lt_one (one_le_primeSieveAffineSlope y K hy)

theorem primeSieveAffineIntercept_nonneg (y K : ℕ) (hy : 1 ≤ y) :
    0 ≤ primeSieveAffineIntercept y K := by
  have hy' : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : 0 < Real.log ((y : ℝ) + 1) := Real.log_pos (by linarith)
  unfold primeSieveAffineIntercept
  positivity

/-! ## The exact divisor-count content of the floor increments -/

/-- **A unit step costs the truncated divisor count.**  Summing the exact
unit-step floor jump (`floor_succ_div_sub_eq_divisor_indicator`) over the
support: `Σ_{d ≤ K} (⌊(x+1)/d⌋ − ⌊x/d⌋) = τ_{≤K}(x+1)`.  This is why no
slope-only affine bound exists and the intercept `K/log(y+1)` is unavoidable. -/
theorem sum_floor_succ_div_sub_eq_card_divisors (x K : ℕ) :
    (∑ d ∈ Finset.Icc 1 K, ((x + 1) / d - x / d))
      = ((Finset.Icc 1 K).filter (· ∣ x + 1)).card := by
  classical
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl fun d _ => floor_succ_div_sub_eq_divisor_indicator x d

/-- The floor increment counts multiples exactly:
`⌊(x+h)/d⌋ − ⌊x/d⌋ = #{n ∈ (x, x+h] : d ∣ n}`. -/
theorem floor_add_div_sub_eq_card_multiples (x h d : ℕ) (hd : 0 < d) :
    (x + h) / d - x / d = ((Finset.Ioc x (x + h)).filter (d ∣ ·)).card := by
  classical
  have hdisj : Disjoint ((Finset.Ioc 0 x).filter (d ∣ ·))
      ((Finset.Ioc x (x + h)).filter (d ∣ ·)) := by
    refine Finset.disjoint_filter_filter ?_
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_Ioc] at ha hb
    omega
  have hsplit : ((Finset.Ioc 0 (x + h)).filter (d ∣ ·)).card
      = ((Finset.Ioc 0 x).filter (d ∣ ·)).card
        + ((Finset.Ioc x (x + h)).filter (d ∣ ·)).card := by
    rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le x) (Nat.le_add_right x h),
      Finset.filter_union, Finset.card_union_of_disjoint hdisj]
  have h1 := Nat.Ioc_filter_dvd_card_eq_div (x + h) d
  have h2 := Nat.Ioc_filter_dvd_card_eq_div x d
  rw [h1, h2] at hsplit
  rw [hsplit, Nat.add_sub_cancel_left]

/-! ## The harmonic floor-increment bound -/

/-- **Harmonic relaxation of the floor-increment sum.**  Refines the crude
`K·(h+1)` bound (`primeSieveFloorIncrementSum_le`) to `h·H_K + K`, by using the
per-`d` bound `⌊(x+h)/d⌋ − ⌊x/d⌋ ≤ ⌊h/d⌋ + 1` (`floor_add_div_sub_le`) instead
of the per-`d` bound `h + 1`. -/
theorem primeSieveFloorIncrementSum_le_harmonic (x h K : ℕ) :
    (∑ d ∈ Finset.Icc 1 K, ((((x + h) / d : ℕ) : ℝ) - ((x / d : ℕ) : ℝ)))
      ≤ (h : ℝ) * harmonicWeight K + (K : ℝ) := by
  classical
  have hterm : ∀ d ∈ Finset.Icc 1 K,
      ((((x + h) / d : ℕ) : ℝ) - ((x / d : ℕ) : ℝ))
        ≤ (h : ℝ) * ((d : ℝ))⁻¹ + 1 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : 0 < d := hd.1
    have hnat : (x + h) / d ≤ h / d + 1 + x / d :=
      Nat.sub_le_iff_le_add.mp (floor_add_div_sub_le x h d hdpos)
    have hcast : (((x + h) / d : ℕ) : ℝ)
        ≤ ((h / d : ℕ) : ℝ) + 1 + ((x / d : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hdivle : ((h / d : ℕ) : ℝ) ≤ (h : ℝ) / (d : ℝ) := Nat.cast_div_le
    rw [div_eq_mul_inv] at hdivle
    linarith
  have hsum : (∑ d ∈ Finset.Icc 1 K, ((h : ℝ) * ((d : ℝ))⁻¹ + 1))
      = (h : ℝ) * harmonicWeight K + (K : ℝ) := by
    unfold harmonicWeight
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  exact le_trans (Finset.sum_le_sum hterm) (le_of_eq hsum)

/-! ## The affine increment bound, frozen support -/

/-- **Affine increment bound, frozen support.**  `‖S(y,x+h) − S(y,x)‖ ≤ A·h + B`
with `A = 1 + H_K/log(y+1)`, `B = K/log(y+1)`, `K = x/(y+1)` — the record-023
constants. -/
theorem primeSieveMoebiusDiscrepancySum_increment_norm_le_affine
    (y x h : ℕ) (hy : 1 ≤ y) (hsq : x + h < (y + 1) ^ 2)
    (hsupp : (x + h) / (y + 1) = x / (y + 1)) :
    ‖primeSieveMoebiusDiscrepancySum y (x + h) - primeSieveMoebiusDiscrepancySum y x‖
      ≤ primeSieveAffineSlope y (x / (y + 1)) * (h : ℝ)
        + primeSieveAffineIntercept y (x / (y + 1)) := by
  have hy' : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : 0 < Real.log ((y : ℝ) + 1) := Real.log_pos (by linarith)
  have hrewrite : primeSieveMoebiusDiscrepancySum y (x + h)
      = primeSieveMoebiusPrefixSum (x / (y + 1)) (x + h) := by
    rw [primeSieveMoebiusDiscrepancySum_eq_prefixSum, hsupp]
  rw [hrewrite, primeSieveMoebiusDiscrepancySum_eq_prefixSum]
  refine le_trans (primeSieveMoebiusPrefixSum_increment_norm_le y x h hy hsq) ?_
  have hfloor := primeSieveFloorIncrementSum_le_harmonic x h (x / (y + 1))
  have hinv : (0 : ℝ) ≤ (Real.log ((y : ℝ) + 1))⁻¹ := le_of_lt (inv_pos.2 hlogy)
  have hdiv : (∑ d ∈ Finset.Icc 1 (x / (y + 1)),
        ((((x + h) / d : ℕ) : ℝ) - ((x / d : ℕ) : ℝ))) / Real.log ((y : ℝ) + 1)
      ≤ ((h : ℝ) * harmonicWeight (x / (y + 1)) + ((x / (y + 1) : ℕ) : ℝ))
          / Real.log ((y : ℝ) + 1) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hfloor hinv
  unfold primeSieveAffineSlope primeSieveAffineIntercept
  have hexp : (1 + harmonicWeight (x / (y + 1)) / Real.log ((y : ℝ) + 1)) * (h : ℝ)
        + ((x / (y + 1) : ℕ) : ℝ) / Real.log ((y : ℝ) + 1)
      = (h : ℝ) + ((h : ℝ) * harmonicWeight (x / (y + 1))
          + ((x / (y + 1) : ℕ) : ℝ)) / Real.log ((y : ℝ) + 1) := by
    ring
  rw [hexp]
  linarith [hdiv]

/-! ## The backward affine increment at the canonical pin -/

/-- **Backward affine increment at the canonical pin**: slope `1 + H_y/log(y+1)`
(`= 2 + o(1)`), intercept `y/log(y+1)`.  At the pin the quotient is exactly
stable on the whole backward walk, so no monotonicity step is needed and the
constants are frozen at `K = y`. -/
theorem primeSieveMoebiusDiscrepancySum_backward_increment_norm_le_affine
    (y t : ℕ) (hy : 1 ≤ y) (ht : t ≤ y) :
    ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y) -
        primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y - t)‖
      ≤ primeSieveAffineSlope y y * (t : ℝ) + primeSieveAffineIntercept y y := by
  have htx : t ≤ primeSieveCanonicalPin y :=
    le_trans ht (le_primeSieveCanonicalPin y)
  have hcancel : primeSieveCanonicalPin y - t + t = primeSieveCanonicalPin y :=
    Nat.sub_add_cancel htx
  have hsq : primeSieveCanonicalPin y - t + t < (y + 1) ^ 2 := by
    rw [hcancel]; exact primeSieveCanonicalPin_lt_sq y
  have hsupp : (primeSieveCanonicalPin y - t + t) / (y + 1)
      = (primeSieveCanonicalPin y - t) / (y + 1) := by
    rw [hcancel, primeSieveCanonicalPin_div y,
      primeSieveCanonicalPin_backward_stable y t ht]
  have hmain := primeSieveMoebiusDiscrepancySum_increment_norm_le_affine
    y (primeSieveCanonicalPin y - t) t hy hsq hsupp
  rw [hcancel, primeSieveCanonicalPin_backward_stable y t ht] at hmain
  exact hmain

/-- The backward affine step in the orientation the abstract excursion wants. -/
private theorem primeSieveBackwardAffineStep (y : ℕ) (hy : 1 ≤ y) :
    ∀ t : ℕ, t ≤ y →
      ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y - t)
          - primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖
        ≤ primeSieveAffineSlope y y * (t : ℝ) + primeSieveAffineIntercept y y := by
  intro t ht
  have h := primeSieveMoebiusDiscrepancySum_backward_increment_norm_le_affine y t hy ht
  rw [norm_sub_rev] at h
  exact h

/-! ## The repaired window, excursion, and moments -/

/-- The affine backward window at the canonical pin:
`W = min y ⌊(H/2 − B)/A⌋₊` with `H = ‖S(y, x₀)‖`, `A = primeSieveAffineSlope y y`,
`B = primeSieveAffineIntercept y y`.  Inclusive convention: the excursion holds
for `t ≤ W`, and `t ≤ y` is exactly the backward stability range. -/
def primeSieveAffineBackwardWindow (y : ℕ) : ℕ :=
  affineExcursionWindow (primeSieveAffineSlope y y) (primeSieveAffineIntercept y y)
    ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ y

/-- **Backward affine excursion at the canonical pin.**  Under the explicit
height hypothesis `2B < H` the pinned height persists at half strength on
`t ≤ W`. -/
theorem primeSieveMoebiusDiscrepancySum_backward_affine_excursion
    (y : ℕ) (hy : 1 ≤ y)
    (hH : 2 * primeSieveAffineIntercept y y
        < ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖) :
    ∀ t : ℕ, t ≤ primeSieveAffineBackwardWindow y →
      ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ / 2
        ≤ ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y - t)‖ :=
  affineExcursion_backward_norm_le (f := primeSieveMoebiusDiscrepancySum y)
    (primeSieveAffineSlope_pos y y hy) hH (primeSieveBackwardAffineStep y hy)

/-- **Backward affine moment lower bound.**
`(H/2)^{2k} · (W+1) ≤ Σ_{t ≤ W} ‖S‖^{2k}`. -/
theorem primeSieveMoebiusDiscrepancySum_backward_affine_excursion_moment
    (y k : ℕ) (hy : 1 ≤ y)
    (hH : 2 * primeSieveAffineIntercept y y
        < ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖) :
    (‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ / 2) ^ (2 * k)
        * ((primeSieveAffineBackwardWindow y : ℝ) + 1)
      ≤ ∑ t ∈ Finset.range (primeSieveAffineBackwardWindow y + 1),
          ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y - t)‖
            ^ (2 * k) :=
  affineExcursion_backward_moment_le (f := primeSieveMoebiusDiscrepancySum y)
    (primeSieveAffineSlope_pos y y hy) hH (primeSieveBackwardAffineStep y hy) k

/-! ## Nonemptiness certificates -/

/-- **Nonemptiness certificate**: the backward window reaches at least `t = 1`
as soon as `H ≥ 2(A + B)`.  At `y ≍ √x` the threshold is
`2(A+B) ≈ 4√x/log x` — the same threshold as the crude window's `2C`, but past
it the affine window grows like `H/(2A) ≈ H/4` instead of `H·log x/(4√x)`:
improvement factor `C/A ≈ y/(2 log y)`. -/
theorem one_le_primeSieveAffineBackwardWindow (y : ℕ) (hy : 1 ≤ y)
    (hH : 2 * (primeSieveAffineSlope y y + primeSieveAffineIntercept y y)
        ≤ ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖) :
    1 ≤ primeSieveAffineBackwardWindow y :=
  one_le_affineExcursionWindow (primeSieveAffineSlope_pos y y hy) hy hH

/-- General-strength certificate: `W ≥ n` under `H ≥ 2(A·n + B)` (and `n ≤ y`,
since the cap always binds at `y`). -/
theorem le_primeSieveAffineBackwardWindow (y n : ℕ) (hy : 1 ≤ y) (hn : n ≤ y)
    (hH : 2 * (primeSieveAffineSlope y y * (n : ℝ) + primeSieveAffineIntercept y y)
        ≤ ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖) :
    n ≤ primeSieveAffineBackwardWindow y := by
  have hA : 0 < primeSieveAffineSlope y y := primeSieveAffineSlope_pos y y hy
  unfold primeSieveAffineBackwardWindow affineExcursionWindow
  refine le_min hn (Nat.le_floor ?_)
  rw [le_div_iff₀ hA]
  linarith

/-! ## The `2 + o(1)` slope certificate (explicit form) -/

/-- **The slope is `2 + o(1)` in explicit form**: `A_y ≤ 2 + (log (y+1))⁻¹`. -/
theorem primeSieveAffineSlope_le (y : ℕ) (hy : 1 ≤ y) :
    primeSieveAffineSlope y y ≤ 2 + (Real.log ((y : ℝ) + 1))⁻¹ := by
  have hy' : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : 0 < Real.log ((y : ℝ) + 1) := Real.log_pos (by linarith)
  have hinv : (0 : ℝ) ≤ (Real.log ((y : ℝ) + 1))⁻¹ := le_of_lt (inv_pos.2 hlogy)
  have hharm : harmonicWeight y ≤ 1 + Real.log ((y : ℝ) + 1) := by
    rw [harmonicWeight_eq_harmonic]
    have h1 := harmonic_le_one_add_log y
    have h2 : Real.log (y : ℝ) ≤ Real.log ((y : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hdiv : harmonicWeight y / Real.log ((y : ℝ) + 1)
      ≤ (1 + Real.log ((y : ℝ) + 1)) / Real.log ((y : ℝ) + 1) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hharm hinv
  have heq : (1 + Real.log ((y : ℝ) + 1)) / Real.log ((y : ℝ) + 1)
      = (Real.log ((y : ℝ) + 1))⁻¹ + 1 := by
    rw [add_div, div_self (ne_of_gt hlogy), one_div]
  rw [heq] at hdiv
  unfold primeSieveAffineSlope
  linarith

end RHLean.Analysis

end
