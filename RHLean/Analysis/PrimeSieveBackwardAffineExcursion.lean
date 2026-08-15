import Mathlib
import RHLean.Analysis.PrimeSieveLipschitzExcursion

/-!
# Backward affine excursion at the canonical square pin

`RHLean.Analysis.PrimeSieveLipschitzExcursion` proves a forward increment bound
for the Moebius discrepancy sum `S(y, x)` and transfers a pinned height into a
windowed moment lower bound.  Its stability hypothesis
`x % (y+1) + h < y + 1` is, however, vacuous at the canonical square pin

```text
x0 = (y+1)^2 - 1,
```

because `x0 % (y+1) = y` forces the forward window to be empty.  This module
supplies the backward counterpart: the quotient `x / (y+1)` is exactly stable
on the whole backward interval `[x0 - y, x0]`, so the affine increment bound
applies to every backward step `t <= y`.  The excursion window certified in
THIS module is `min (y+1) (floor (H/(2C)))` with the crude constant
`C = primeSieveLipschitzConstant ~ 2 sqrt x / log x`, so the window is only
`Theta(log x)` at `H ~ sqrt x`; the sharp affine window (slope `2 + o(1)`,
intercept of `sqrt x` scale, window `~ min(sqrt x, H/4)`) is delivered in
`RHLean.Analysis.PrimeSieveAffineExcursion`.

The module also records two exact floor facts
(`floor_succ_div_sub_eq_divisor_indicator`, `floor_add_div_sub_le`): the
unit-step floor jump is precisely the divisor indicator of `x + 1`, and a
general step obeys the per-`d` bound `h/d + 1` (one above the exact maximum
`ceil (h/d)` when `d` divides `h`).  Both are consumed in
`PrimeSieveAffineExcursion`: the general bound by the sharp affine slope
`1 + H_K/log(y+1)`, the unit-step fact by the divisor-count identity behind
the intercept.  Finally the module isolates the exact support-insertion
identity: at the transition `x + 1 = (K+1)(y+1)` the quotient support grows
by the single term `mu(K+1) * R(y+1)`.

Everything here is unconditional; no hypothesis on `pi`, `Li`, or the Moebius
sum is used anywhere.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## Exact floor facts for the unit and general step -/

/-- The unit-step floor jump is exactly the divisor indicator of `x + 1`. -/
theorem floor_succ_div_sub_eq_divisor_indicator (x d : ℕ) :
    (x + 1) / d - x / d = if d ∣ x + 1 then 1 else 0 := by
  rw [Nat.succ_div]
  split <;> simp

/-- The per-`d` floor increment bound `h/d + 1`, refining the crude
`h + 1` bound used by the forward Lipschitz constant. -/
theorem floor_add_div_sub_le (x h d : ℕ) (hd : 0 < d) :
    (x + h) / d - x / d ≤ h / d + 1 := by
  have hite : (if d ≤ x % d + h % d then 1 else 0) ≤ 1 := by split <;> simp
  have h1 : (x + h) / d ≤ x / d + h / d + 1 := by
    rw [Nat.add_div hd]
    exact Nat.add_le_add_left hite _
  have h2 : x / d + h / d + 1 = h / d + 1 + x / d := by ring
  exact Nat.sub_le_iff_le_add.mpr (h2 ▸ h1)

/-! ## The canonical square pin and backward stability -/

/-- The canonical square pin `x0 = (y+1)^2 - 1`, the synchronized sample point
of the square-block development. -/
def primeSieveCanonicalPin (y : ℕ) : ℕ :=
  (y + 1) ^ 2 - 1

theorem primeSieveCanonicalPin_eq (y : ℕ) :
    primeSieveCanonicalPin y = (y + 1) * y + y := by
  have h : (y + 1) ^ 2 = (y + 1) * y + (y + 1) := by ring
  unfold primeSieveCanonicalPin
  omega

/-- Every backward step `t <= y` from the canonical pin lands in the same
quotient class: `floor ((x0 - t)/(y+1)) = y` exactly. -/
theorem primeSieveCanonicalPin_backward_stable (y t : ℕ) (ht : t ≤ y) :
    (primeSieveCanonicalPin y - t) / (y + 1) = y := by
  have hpos : 0 < y + 1 := Nat.succ_pos y
  have hkey : primeSieveCanonicalPin y - t = (y + 1) * y + (y - t) := by
    have h := primeSieveCanonicalPin_eq y
    omega
  rw [hkey, Nat.mul_add_div hpos, Nat.div_eq_of_lt (by omega)]
  omega

/-- The pin itself sits in quotient class `y`. -/
theorem primeSieveCanonicalPin_div (y : ℕ) :
    primeSieveCanonicalPin y / (y + 1) = y := by
  have h := primeSieveCanonicalPin_backward_stable y 0 (Nat.zero_le y)
  simpa using h

/-- The backward step stays inside the square block. -/
theorem primeSieveCanonicalPin_lt_sq (y : ℕ) :
    primeSieveCanonicalPin y < (y + 1) ^ 2 := by
  have h : 0 < (y + 1) ^ 2 := by positivity
  unfold primeSieveCanonicalPin
  omega

theorem le_primeSieveCanonicalPin (y : ℕ) : y ≤ primeSieveCanonicalPin y := by
  have h := primeSieveCanonicalPin_eq y
  omega

/-! ## Monotonicity of the affine constant -/

/-- The Lipschitz constant is monotone in the pin: a smaller starting point
never has a larger constant. -/
theorem primeSieveLipschitzConstant_mono (y : ℕ) (hy : 1 ≤ y) {x x' : ℕ}
    (hxx : x ≤ x') :
    primeSieveLipschitzConstant y x ≤ primeSieveLipschitzConstant y x' := by
  have hy' : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlog : 0 < Real.log ((y : ℝ) + 1) := Real.log_pos (by linarith)
  have hdiv : x / (y + 1) ≤ x' / (y + 1) := Nat.div_le_div_right hxx
  have hcast : ((x / (y + 1) : ℕ) : ℝ) ≤ ((x' / (y + 1) : ℕ) : ℝ) := by
    exact_mod_cast hdiv
  have hinv : (0 : ℝ) ≤ (Real.log ((y : ℝ) + 1))⁻¹ := le_of_lt (inv_pos.2 hlog)
  have h2 := mul_le_mul_of_nonneg_right hcast hinv
  unfold primeSieveLipschitzConstant
  rw [div_eq_mul_inv, div_eq_mul_inv]
  linarith

/-! ## The backward increment bound -/

/-- **Backward affine increment bound at the canonical pin.**  For every
backward step `t <= y`,

```text
|S(y, x0) - S(y, x0 - t)| <= C(y, x0) * (t + 1),
```

with the constant evaluated at the pin itself.  Unconditional. -/
theorem primeSieveMoebiusDiscrepancySum_backward_increment_norm_le
    (y t : ℕ) (hy : 1 ≤ y) (ht : t ≤ y) :
    ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y) -
        primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y - t)‖
      ≤ primeSieveLipschitzConstant y (primeSieveCanonicalPin y)
          * ((t : ℝ) + 1) := by
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
  have hmain := primeSieveMoebiusDiscrepancySum_increment_norm_le
    y (primeSieveCanonicalPin y - t) t hy hsq hsupp
  rw [hcancel] at hmain
  refine le_trans hmain ?_
  have hmono := primeSieveLipschitzConstant_mono y hy
    (Nat.sub_le (primeSieveCanonicalPin y) t)
  have ht1 : (0 : ℝ) ≤ (t : ℝ) + 1 := by positivity
  exact mul_le_mul_of_nonneg_right hmono ht1

/-! ## The backward excursion window -/

/-- The backward excursion window at the canonical pin with the crude
Lipschitz constant, capped by the exactly-stable backward range `y + 1`.
For the genuine affine window see `primeSieveAffineBackwardWindow`. -/
def primeSieveBackwardWindow (y : ℕ) : ℕ :=
  min (y + 1)
    ⌊‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ /
      (2 * primeSieveLipschitzConstant y (primeSieveCanonicalPin y))⌋₊

/-- **Backward excursion at the canonical pin.**  The pinned height persists at
half strength on the whole backward window.  No stability hypothesis appears:
the canonical pin supplies it for free.  The window may be empty:
`primeSieveBackwardWindow y = 0` whenever `H < 2C ~ 4 sqrt x / log x`, and
this module certifies no lower bound on it; see
`one_le_primeSieveAffineBackwardWindow` for a certificate under an explicit
height hypothesis. -/
theorem primeSieveMoebiusDiscrepancySum_backward_excursion (y : ℕ) (hy : 1 ≤ y) :
    ∀ t : ℕ, t < primeSieveBackwardWindow y →
      ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ / 2
        ≤ ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y - t)‖ := by
  intro t ht
  have hC : 0 < primeSieveLipschitzConstant y (primeSieveCanonicalPin y) :=
    primeSieveLipschitzConstant_pos y (primeSieveCanonicalPin y) hy
  have hty : t ≤ y := by
    have := lt_of_lt_of_le ht (min_le_left _ _)
    omega
  have htw : t < ⌊‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ /
      (2 * primeSieveLipschitzConstant y (primeSieveCanonicalPin y))⌋₊ :=
    lt_of_lt_of_le ht (min_le_right _ _)
  have hstep := primeSieveMoebiusDiscrepancySum_backward_increment_norm_le
    y t hy hty
  have hnn : (0 : ℝ) ≤ ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ /
      (2 * primeSieveLipschitzConstant y (primeSieveCanonicalPin y)) := by
    positivity
  have hfloor := Nat.floor_le hnn
  have ht1 : ((t : ℝ) + 1) ≤
      ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ /
        (2 * primeSieveLipschitzConstant y (primeSieveCanonicalPin y)) := by
    have : (t : ℝ) + 1 ≤ ((⌊‖primeSieveMoebiusDiscrepancySum y
        (primeSieveCanonicalPin y)‖ /
        (2 * primeSieveLipschitzConstant y (primeSieveCanonicalPin y))⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast htw
    linarith
  have hhalf : ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y) -
      primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y - t)‖
      ≤ ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ / 2 := by
    refine le_trans hstep ?_
    calc primeSieveLipschitzConstant y (primeSieveCanonicalPin y) * ((t : ℝ) + 1)
        ≤ primeSieveLipschitzConstant y (primeSieveCanonicalPin y) *
          (‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ /
            (2 * primeSieveLipschitzConstant y (primeSieveCanonicalPin y))) :=
          mul_le_mul_of_nonneg_left ht1 (le_of_lt hC)
      _ = ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ / 2 := by
          field_simp
  have htri := norm_sub_norm_le
    (primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y))
    (primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y - t))
  linarith

/-- **The backward moment lower bound.**  For every `k`, the pinned height at
the canonical pin produces a `2k`-th moment lower bound over the backward
window — the pinned-height transfer with the vacuous forward hypotheses removed
(vacuous when the window is empty; cf. the nonemptiness certificate in
`PrimeSieveAffineExcursion`). -/
theorem primeSieveMoebiusDiscrepancySum_backward_excursion_moment
    (y k : ℕ) (hy : 1 ≤ y) :
    (‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ / 2) ^ (2 * k)
        * ((primeSieveBackwardWindow y : ℕ) : ℝ)
      ≤ ∑ t ∈ Finset.range (primeSieveBackwardWindow y),
          ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y - t)‖
            ^ (2 * k) := by
  have hpt := primeSieveMoebiusDiscrepancySum_backward_excursion y hy
  have hbound : ∀ t ∈ Finset.range (primeSieveBackwardWindow y),
      (‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ / 2) ^ (2 * k)
        ≤ ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y - t)‖
            ^ (2 * k) := by
    intro t ht
    have h := hpt t (Finset.mem_range.1 ht)
    have hnn : (0 : ℝ) ≤
        ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ / 2 := by
      positivity
    exact pow_le_pow_left₀ hnn h (2 * k)
  have := Finset.card_nsmul_le_sum (Finset.range (primeSieveBackwardWindow y))
    (fun t => ‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y - t)‖
      ^ (2 * k))
    ((‖primeSieveMoebiusDiscrepancySum y (primeSieveCanonicalPin y)‖ / 2) ^ (2 * k))
    hbound
  rw [Finset.card_range, nsmul_eq_mul] at this
  linarith [this]

/-! ## The exact support-insertion identity -/

/-- **Support insertion is a single exact term.**  At the transition
`x + 1 = (K+1)(y+1)` the quotient support grows from `Icc 1 K` to
`Icc 1 (K+1)`, and the increment of the Moebius discrepancy sum decomposes as
the frozen-support increment plus exactly `mu(K+1) * R(y+1)`. -/
theorem primeSieveMoebiusDiscrepancySum_support_insertion (y K : ℕ) :
    primeSieveMoebiusDiscrepancySum y ((K + 1) * (y + 1) - 1 + 1) -
        primeSieveMoebiusDiscrepancySum y ((K + 1) * (y + 1) - 1)
      = (∑ d ∈ Finset.Icc 1 K, (((μ d : ℤ) : ℂ)) *
            (primeSievePrimeDiscrepancy (((K + 1) * (y + 1) - 1 + 1) / d) -
              primeSievePrimeDiscrepancy (((K + 1) * (y + 1) - 1) / d)))
          + (((μ (K + 1) : ℤ) : ℂ)) * primeSievePrimeDiscrepancy (y + 1) := by
  have hpos : 0 < (K + 1) * (y + 1) := by positivity
  have hcancel : (K + 1) * (y + 1) - 1 + 1 = (K + 1) * (y + 1) := by omega
  have hdivnew : ((K + 1) * (y + 1)) / (y + 1) = K + 1 :=
    Nat.mul_div_cancel _ (Nat.succ_pos y)
  have hdivold : ((K + 1) * (y + 1) - 1) / (y + 1) = K := by
    have hkey : (K + 1) * (y + 1) - 1 = (y + 1) * K + y := by
      have h : (K + 1) * (y + 1) = (y + 1) * K + (y + 1) := by ring
      omega
    rw [hkey, Nat.mul_add_div (Nat.succ_pos y), Nat.div_eq_of_lt (by omega)]
    omega
  have hdivtop : ((K + 1) * (y + 1)) / (K + 1) = y + 1 :=
    Nat.mul_div_cancel_left _ (Nat.succ_pos K)
  unfold primeSieveMoebiusDiscrepancySum primeSieveQuotientSupport
  rw [hcancel, hdivnew, hdivold,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), hdivtop]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end RHLean.Analysis

end
