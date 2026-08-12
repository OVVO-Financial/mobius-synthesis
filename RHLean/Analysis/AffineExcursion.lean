import Mathlib

/-!
# Abstract affine excursion

An affine excursion lemma for a sequence `g : ℕ → ℂ` pinned at `t = 0`: if
the increment from the pin obeys an affine modulus,

```text
|g t - g 0| <= A * t + B        for all t <= cap,
```

and the pinned height `H = |g 0|` clears the intercept (`2B < H`), then the
height persists at half strength on the whole window

```text
t <= affineExcursionWindow A B H cap = min cap (floor ((H/2 - B) / A)).
```

The `cap` records the range on which the affine modulus is known; for the
prime-sieve instantiation it is the backward stability range `y`.  The window
uses the *inclusive* convention `t <= W`, so the moment sums below run over
`Finset.range (W + 1)`, which has `W + 1` points.

The module is fully abstract (no arithmetic input): the core statement is in
excursion coordinates `g t = f (x0 +/- t)`, and one-line wrappers give the
forward and backward directions for a sequence `f` pinned at `x0`.  Both the
norm and the `2k`-th moment bounds hold unconditionally; they are vacuous
only when the window is empty, and `one_le_affineExcursionWindow` certifies
nonemptiness under the explicit height hypothesis `H >= 2(A + B)`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Window length of an affine excursion: from a pinned height `H` and an affine
increment modulus `A·t + B`, the height persists at half strength for
`t ≤ min cap ⌊(H/2 − B)/A⌋₊`.  The `cap` records the range on which the modulus
is known (for the prime-sieve instantiation: the backward stability range `y`). -/
def affineExcursionWindow (A B H : ℝ) (cap : ℕ) : ℕ :=
  min cap ⌊(H / 2 - B) / A⌋₊

/-- **Abstract affine excursion, core form.**  If `‖g t − g 0‖ ≤ A·t + B` for all
`t ≤ cap`, and `2B < H := ‖g 0‖`, then `‖g t‖ ≥ H/2` on the whole window. -/
theorem affineExcursion_norm_le {g : ℕ → ℂ} {A B : ℝ} {cap : ℕ}
    (hA : 0 < A) (hH : 2 * B < ‖g 0‖)
    (hstep : ∀ t : ℕ, t ≤ cap → ‖g t - g 0‖ ≤ A * (t : ℝ) + B) :
    ∀ t : ℕ, t ≤ affineExcursionWindow A B ‖g 0‖ cap →
      ‖g 0‖ / 2 ≤ ‖g t‖ := by
  intro t ht
  have htcap : t ≤ cap := le_trans ht (min_le_left _ _)
  have htfloor : t ≤ ⌊(‖g 0‖ / 2 - B) / A⌋₊ := le_trans ht (min_le_right _ _)
  have hnn : (0 : ℝ) ≤ (‖g 0‖ / 2 - B) / A :=
    div_nonneg (by linarith) (le_of_lt hA)
  have hfloor : ((⌊(‖g 0‖ / 2 - B) / A⌋₊ : ℕ) : ℝ) ≤ (‖g 0‖ / 2 - B) / A :=
    Nat.floor_le hnn
  have htR : (t : ℝ) ≤ (‖g 0‖ / 2 - B) / A := by
    have h1 : (t : ℝ) ≤ ((⌊(‖g 0‖ / 2 - B) / A⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast htfloor
    linarith
  have hAt : A * (t : ℝ) + B ≤ ‖g 0‖ / 2 := by
    have h1 := mul_le_mul_of_nonneg_left htR (le_of_lt hA)
    rw [mul_div_cancel₀ _ (ne_of_gt hA)] at h1
    linarith
  have hhalf : ‖g t - g 0‖ ≤ ‖g 0‖ / 2 := le_trans (hstep t htcap) hAt
  have htri := norm_sub_norm_le (g 0) (g t)
  have hsymm : ‖g 0 - g t‖ = ‖g t - g 0‖ := norm_sub_rev _ _
  rw [hsymm] at htri
  linarith

/-- **Abstract affine moment corollary.**  `2k`-th moment lower bound over the
window (which has `W + 1` points under the inclusive convention). -/
theorem affineExcursion_moment_le {g : ℕ → ℂ} {A B : ℝ} {cap : ℕ}
    (hA : 0 < A) (hH : 2 * B < ‖g 0‖)
    (hstep : ∀ t : ℕ, t ≤ cap → ‖g t - g 0‖ ≤ A * (t : ℝ) + B) (k : ℕ) :
    (‖g 0‖ / 2) ^ (2 * k) * ((affineExcursionWindow A B ‖g 0‖ cap : ℝ) + 1)
      ≤ ∑ t ∈ Finset.range (affineExcursionWindow A B ‖g 0‖ cap + 1),
          ‖g t‖ ^ (2 * k) := by
  have hpt := affineExcursion_norm_le hA hH hstep
  have hbound : ∀ t ∈ Finset.range (affineExcursionWindow A B ‖g 0‖ cap + 1),
      (‖g 0‖ / 2) ^ (2 * k) ≤ ‖g t‖ ^ (2 * k) := by
    intro t ht
    have ht' : t ≤ affineExcursionWindow A B ‖g 0‖ cap :=
      Nat.lt_succ_iff.mp (Finset.mem_range.1 ht)
    have h := hpt t ht'
    have hnn : (0 : ℝ) ≤ ‖g 0‖ / 2 := by positivity
    exact pow_le_pow_left₀ hnn h (2 * k)
  have hsum := Finset.card_nsmul_le_sum
    (Finset.range (affineExcursionWindow A B ‖g 0‖ cap + 1))
    (fun t => ‖g t‖ ^ (2 * k)) ((‖g 0‖ / 2) ^ (2 * k)) hbound
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  have hcast : ((affineExcursionWindow A B ‖g 0‖ cap + 1 : ℕ) : ℝ)
      = ((affineExcursionWindow A B ‖g 0‖ cap : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [hcast] at hsum
  linarith [hsum]

/-- The window is nonempty (contains `t = 1`) once `H ≥ 2(A + B)` and the cap
allows it. -/
theorem one_le_affineExcursionWindow {A B H : ℝ} {cap : ℕ}
    (hA : 0 < A) (hcap : 1 ≤ cap) (hH : 2 * (A + B) ≤ H) :
    1 ≤ affineExcursionWindow A B H cap := by
  refine le_min hcap (Nat.le_floor ?_)
  rw [Nat.cast_one, le_div_iff₀ hA]
  linarith

/-- Forward direction. -/
theorem affineExcursion_forward_norm_le {f : ℕ → ℂ} {x₀ : ℕ} {A B : ℝ} {cap : ℕ}
    (hA : 0 < A) (hH : 2 * B < ‖f x₀‖)
    (hstep : ∀ t : ℕ, t ≤ cap → ‖f (x₀ + t) - f x₀‖ ≤ A * (t : ℝ) + B) :
    ∀ t : ℕ, t ≤ affineExcursionWindow A B ‖f x₀‖ cap →
      ‖f x₀‖ / 2 ≤ ‖f (x₀ + t)‖ :=
  affineExcursion_norm_le (g := fun s => f (x₀ + s)) hA hH hstep

/-- Backward direction (ℕ-subtraction; for `t ≤ x₀` this is the honest backward
walk, and the statement is unconditional because `x₀ - t` truncates). -/
theorem affineExcursion_backward_norm_le {f : ℕ → ℂ} {x₀ : ℕ} {A B : ℝ} {cap : ℕ}
    (hA : 0 < A) (hH : 2 * B < ‖f x₀‖)
    (hstep : ∀ t : ℕ, t ≤ cap → ‖f (x₀ - t) - f x₀‖ ≤ A * (t : ℝ) + B) :
    ∀ t : ℕ, t ≤ affineExcursionWindow A B ‖f x₀‖ cap →
      ‖f x₀‖ / 2 ≤ ‖f (x₀ - t)‖ :=
  affineExcursion_norm_le (g := fun s => f (x₀ - s)) hA hH hstep

/-- Forward moment wrapper. -/
theorem affineExcursion_forward_moment_le {f : ℕ → ℂ} {x₀ : ℕ} {A B : ℝ} {cap : ℕ}
    (hA : 0 < A) (hH : 2 * B < ‖f x₀‖)
    (hstep : ∀ t : ℕ, t ≤ cap → ‖f (x₀ + t) - f x₀‖ ≤ A * (t : ℝ) + B) (k : ℕ) :
    (‖f x₀‖ / 2) ^ (2 * k) * ((affineExcursionWindow A B ‖f x₀‖ cap : ℝ) + 1)
      ≤ ∑ t ∈ Finset.range (affineExcursionWindow A B ‖f x₀‖ cap + 1),
          ‖f (x₀ + t)‖ ^ (2 * k) :=
  affineExcursion_moment_le (g := fun s => f (x₀ + s)) hA hH hstep k

/-- Backward moment wrapper. -/
theorem affineExcursion_backward_moment_le {f : ℕ → ℂ} {x₀ : ℕ} {A B : ℝ} {cap : ℕ}
    (hA : 0 < A) (hH : 2 * B < ‖f x₀‖)
    (hstep : ∀ t : ℕ, t ≤ cap → ‖f (x₀ - t) - f x₀‖ ≤ A * (t : ℝ) + B) (k : ℕ) :
    (‖f x₀‖ / 2) ^ (2 * k) * ((affineExcursionWindow A B ‖f x₀‖ cap : ℝ) + 1)
      ≤ ∑ t ∈ Finset.range (affineExcursionWindow A B ‖f x₀‖ cap + 1),
          ‖f (x₀ - t)‖ ^ (2 * k) :=
  affineExcursion_moment_le (g := fun s => f (x₀ - s)) hA hH hstep k

end RHLean.Analysis

end
