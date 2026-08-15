import Mathlib
import RHLean.Analysis.PrimeSieveAbelIdentity

/-!
# Lipschitz increments of the Abel face, and the pinned-to-windowed excursion

`RHLean.Analysis.PrimeSieveAbelIdentity` isolates the Abel face of the
prime-sieve PNT error,

```text
primeSieveMoebiusDiscrepancySum y x
  = sum_{d = 1}^{x/(y+1)} mu(d) * (pi(x/d) - Li(x/d)).
```

This module proves two unconditional, fully explicit facts about that object.

## 1. The increment (Lipschitz) bound

For `1 <= y` and `x + h < (y+1)^2`, and *provided the quotient support does not
grow* across the step (`(x+h)/(y+1) = x/(y+1)`),

```text
|S(y, x+h) - S(y, x)| <= C(y,x) * (h + 1),
    C(y,x) = 1 + (x/(y+1)) / log (y+1).
```

The two halves of the constant have different characters and it is worth being
precise about which part of the informal argument survives.

* The **prime-count half is genuinely `O(1)`**, with constant `1` — better than
  the informally predicted `2`.  The exact statement proved is
  `primeSieveIntervalPrimeCount_sum_le`:

  ```text
  sum_{d <= x/(y+1)} #{p prime : x/d < p <= (x+h)/d}  <=  h
  ```

  whenever `x + h < (y+1)^2`.  The proof is the honest discrete version of the
  informal counting: the pair `(d,p)` is sent to `n = d*p`, which lands in
  `(x, x+h]`; every such `p` exceeds `y`, and under `x + h < (y+1)^2` a single
  `n` cannot carry two prime factors above `y` (with multiplicity), so the map
  is *injective* — not merely two-to-one.  Hence the total prime-side jump is at
  most the number of integers in the window.

* The **Li half is not `O(1)`** in the discrete setting, and this is a real
  deviation from the informal sketch.  The informal argument estimates
  `Li(x/d)` at the *real* point `x/d`, where the drift is
  `sum_{d<=K} h/(d log(x/d)) = O(h)`.  The repository's object evaluates `Li` at
  the *integer* point `floor (x/d)`, and those floors move in unit jumps: for
  `h = 1` the Li half is a sum over the divisors of `x+1` below `K`, of size
  `tau(x+1)/log(y+1)`, and no absolute constant bounds it.  What is proved here
  is the honest explicit bound

  ```text
  |Li half|  <=  (sum_{d <= K} (floor((x+h)/d) - floor(x/d))) / log (y+1)
             <=  K * (h + 1) / log (y+1),
  ```

  the first line being sharp and the second the crude uniform relaxation used to
  reach the advertised `C * (h+1)` shape.  With `y = floor (sqrt x)` one has
  `K ~ sqrt x`, so `C(y,x) ~ 1 + 2 sqrt x / log x`: the Abel face is Lipschitz
  with an explicit constant, but that constant is `O(sqrt x / log x)` and not
  `O(1)`.  Recovering `O(1)` would need the real-argument Li comparison plus a
  divisor-sum input, neither of which is elementary in the present conventions;
  see the deviation note in `results/020`.

* The support-growth hypothesis `(x+h)/(y+1) = x/(y+1)` is likewise honest.  A
  step that enlarges the support inserts terms `mu(d) * R(floor((x+h)/d))` with
  `floor((x+h)/d)` near `y`, and elementary bounds only give `|R| <= O(y)` for
  those; the informal `sqrt x exp(-c (log x)^{3/5})` bound is PNT-strength input,
  not elementary arithmetic.  `primeSieveQuotientTop_stable` gives a checkable
  sufficient condition (`x % (y+1) + h < y+1`) for the hypothesis, and the
  window used by the excursion lemma is short enough for it to be typical.

## 2. The excursion (pinned to windowed) transfer

`excursionWindow_norm_le` and `excursionWindow_moment_le` are pure arithmetic
consequences of a `C*(h+1)` increment bound at a single pinned point `x0`: with
`H = |f x0|` one gets `|f (x0 + t)| >= H/2` for every `t < floor (H / (2C))`,
hence for every `k`

```text
(H/2)^(2k) * floor (H / (2C))  <=  sum_{t < floor (H/(2C))} |f (x0+t)|^(2k).
```

The hypothesis `H >= 2C` is needed only to make the window nonempty
(`one_le_excursionWindow`); the two bounds themselves hold unconditionally, and
are vacuous when the window is empty.
`primeSieveMoebiusDiscrepancySum_excursion_moment` is the instantiation at the
Abel face.  No estimate on the Abel face is asserted anywhere: the transfer is
conditional on a pinned height, exactly as intended.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## Elementary increment bounds for the logarithmic integral -/

private theorem invLog_intervalIntegrable {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun u : ℝ => (Real.log u)⁻¹) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  have hu2 : 2 ≤ u := by
    rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have hune : u ≠ 0 := by linarith
  have hlog : Real.log u ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  exact ((Real.continuousAt_log hune).inv₀ hlog).continuousWithinAt

/-- Above `2` the normalized logarithmic integral is an honest interval
integral of `1 / log`. -/
theorem logarithmicIntegralFromTwo_sub_eq {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    logarithmicIntegralFromTwo b - logarithmicIntegralFromTwo a
      = ∫ u in a..b, (Real.log u)⁻¹ := by
  have h1 : IntervalIntegrable (fun u : ℝ => (Real.log u)⁻¹) MeasureTheory.volume 2 a :=
    invLog_intervalIntegrable (by norm_num) ha
  have h2 : IntervalIntegrable (fun u : ℝ => (Real.log u)⁻¹) MeasureTheory.volume a b :=
    invLog_intervalIntegrable ha hb
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  unfold logarithmicIntegralFromTwo
  linarith [hadd]

/-- **Li drift is elementary.**  On `[a,b]` with `2 <= a` the logarithmic
integral moves by at most `(b - a) / log a`. -/
theorem abs_logarithmicIntegralFromTwo_sub_le {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    |logarithmicIntegralFromTwo b - logarithmicIntegralFromTwo a|
      ≤ (b - a) / Real.log a := by
  have hb : 2 ≤ b := le_trans ha hab
  rw [logarithmicIntegralFromTwo_sub_eq ha hb]
  have hlogpos : 0 < Real.log a := Real.log_pos (by linarith)
  have key : ∀ u ∈ Set.uIoc a b, ‖(Real.log u)⁻¹‖ ≤ (Real.log a)⁻¹ := by
    intro u hu
    rw [Set.uIoc_of_le hab] at hu
    have hau : a ≤ u := le_of_lt hu.1
    have hlu : 0 < Real.log u := Real.log_pos (by linarith)
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hlogpos (Real.log_le_log (by linarith) hau)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const key
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at hnorm
  calc |∫ u in a..b, (Real.log u)⁻¹| ≤ (Real.log a)⁻¹ * (b - a) := hnorm
    _ = (b - a) / Real.log a := by
        field_simp

/-- The form used below: the denominator is relaxed to `log (y+1)` once the
lower endpoint is known to sit above `y`. -/
theorem abs_logarithmicIntegralFromTwo_sub_le_log_succ {y : ℕ} {a b : ℝ}
    (hy : 1 ≤ y) (hya : (y : ℝ) + 1 ≤ a) (hab : a ≤ b) :
    |logarithmicIntegralFromTwo b - logarithmicIntegralFromTwo a|
      ≤ (b - a) / Real.log ((y : ℝ) + 1) := by
  have hy1 : (2 : ℝ) ≤ (y : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    linarith
  have ha : (2 : ℝ) ≤ a := le_trans hy1 hya
  have hlogy : 0 < Real.log ((y : ℝ) + 1) := Real.log_pos (by linarith)
  have hlogle : Real.log ((y : ℝ) + 1) ≤ Real.log a :=
    Real.log_le_log (by linarith) hya
  have hla : 0 < Real.log a := lt_of_lt_of_le hlogy hlogle
  refine le_trans (abs_logarithmicIntegralFromTwo_sub_le ha hab) ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hinvle : (Real.log a)⁻¹ ≤ (Real.log ((y : ℝ) + 1))⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hlogy hlogle
  exact mul_le_mul_of_nonneg_left hinvle (by linarith)

/-! ## Prime counts on an interval -/

/-- Number of primes in `(a, b]`. -/
def primeSieveIntervalPrimeCount (a b : ℕ) : ℕ :=
  ((Finset.Ioc a b).filter Nat.Prime).card

/-- The prefix prime count differences by the interval prime count. -/
theorem primeSievePrefixPrimeCount_sub_eq {a b : ℕ} (hab : a ≤ b) :
    primeSievePrefixPrimeCount b - primeSievePrefixPrimeCount a
      = ((primeSieveIntervalPrimeCount a b : ℕ) : ℂ) := by
  classical
  have hsplit :=
    Finset.sum_Ioc_consecutive (f := primeSievePrimeIndicator) (Nat.zero_le a) hab
  have hcard : (∑ q ∈ Finset.Ioc a b, primeSievePrimeIndicator q)
      = ((primeSieveIntervalPrimeCount a b : ℕ) : ℂ) := by
    simp [primeSievePrimeIndicator, primeSieveIntervalPrimeCount, Finset.sum_boole]
  unfold primeSievePrefixPrimeCount
  rw [← hsplit, ← hcard]
  ring

/-! ## The counting core: total prime-side jump over the quotient support -/

/-- Pairs `(d, p)` with `d` in the quotient support and `p` a prime entering the
`d`-th prefix count when `x` moves to `x + h`. -/
private def primeSieveIncrementPairs (y x h : ℕ) : Finset ((_ : ℕ) × ℕ) :=
  (Finset.Icc 1 (x / (y + 1))).sigma fun d =>
    (Finset.Ioc (x / d) ((x + h) / d)).filter Nat.Prime

private theorem primeSieveIncrementPairs_mem_facts {y x h : ℕ} {z : (_ : ℕ) × ℕ}
    (hz : z ∈ primeSieveIncrementPairs y x h) :
    0 < z.1 ∧ z.2.Prime ∧ x < z.1 * z.2 ∧ z.1 * z.2 ≤ x + h ∧ y + 1 ≤ z.2 := by
  classical
  rw [primeSieveIncrementPairs, Finset.mem_sigma] at hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [Finset.mem_Icc] at hz1
  rw [Finset.mem_filter, Finset.mem_Ioc] at hz2
  obtain ⟨hd1, hdK⟩ := hz1
  obtain ⟨⟨hlow, hhigh⟩, hprime⟩ := hz2
  have hdpos : 0 < z.1 := hd1
  have hgt : x < z.2 * z.1 := (Nat.div_lt_iff_lt_mul hdpos).1 hlow
  have hle : z.2 * z.1 ≤ x + h := (Nat.le_div_iff_mul_le hdpos).1 hhigh
  have hgt' : x < z.1 * z.2 := by rw [Nat.mul_comm]; exact hgt
  have hle' : z.1 * z.2 ≤ x + h := by rw [Nat.mul_comm]; exact hle
  have hK : z.1 * (y + 1) ≤ x := (Nat.le_div_iff_mul_le (Nat.succ_pos y)).1 hdK
  have hylt : y + 1 < z.2 := by
    have : z.1 * (y + 1) < z.1 * z.2 := lt_of_le_of_lt hK hgt'
    exact Nat.lt_of_mul_lt_mul_left this
  exact ⟨hdpos, hprime, hgt', hle', le_of_lt hylt⟩

/-- **The honest discrete counting core.**  Under `x + h < (y+1)^2` the total
prime-side jump of the whole Abel face over a step `x -> x + h` is at most `h`.

The informal argument predicted a factor `2` (two representations `n = d p`);
the discrete truth is better: the representation is *unique*, because two prime
factors above `y` would force `n >= (y+1)^2 > x + h`. -/
theorem primeSieveIntervalPrimeCount_sum_le (y x h : ℕ) (hsq : x + h < (y + 1) ^ 2) :
    (∑ d ∈ Finset.Icc 1 (x / (y + 1)),
        primeSieveIntervalPrimeCount (x / d) ((x + h) / d)) ≤ h := by
  classical
  have hcard : (primeSieveIncrementPairs y x h).card
      = ∑ d ∈ Finset.Icc 1 (x / (y + 1)),
          primeSieveIntervalPrimeCount (x / d) ((x + h) / d) := by
    rw [primeSieveIncrementPairs, Finset.card_sigma]
    rfl
  rw [← hcard]
  have hmaps : ∀ z ∈ primeSieveIncrementPairs y x h,
      z.1 * z.2 ∈ Finset.Ioc x (x + h) := by
    intro z hz
    obtain ⟨_, _, hgt, hle, _⟩ := primeSieveIncrementPairs_mem_facts hz
    exact Finset.mem_Ioc.2 ⟨hgt, hle⟩
  have hinj : Set.InjOn (fun z : (_ : ℕ) × ℕ => z.1 * z.2)
      (primeSieveIncrementPairs y x h : Set ((_ : ℕ) × ℕ)) := by
    intro z hz w hw hzw
    obtain ⟨hz1, hzp, hzgt, hzle, hzy⟩ :=
      primeSieveIncrementPairs_mem_facts (Finset.mem_coe.1 hz)
    obtain ⟨hw1, hwp, hwgt, hwle, hwy⟩ :=
      primeSieveIncrementPairs_mem_facts (Finset.mem_coe.1 hw)
    simp only at hzw
    have hsame : z.2 = w.2 := by
      by_contra hne
      have hcop : Nat.Coprime z.2 w.2 := (Nat.coprime_primes hzp hwp).2 hne
      have hdvd1 : z.2 ∣ z.1 * z.2 := Dvd.intro_left _ rfl
      have hdvd2 : w.2 ∣ z.1 * z.2 := by
        rw [hzw]; exact Dvd.intro_left _ rfl
      have hmul : z.2 * w.2 ∣ z.1 * z.2 := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdvd1 hdvd2
      have hpos : 0 < z.1 * z.2 := lt_of_le_of_lt (Nat.zero_le x) hzgt
      have hle2 : z.2 * w.2 ≤ z.1 * z.2 := Nat.le_of_dvd hpos hmul
      have hbig : (y + 1) * (y + 1) ≤ z.2 * w.2 := Nat.mul_le_mul hzy hwy
      have : (y + 1) ^ 2 ≤ x + h := by
        rw [pow_two]
        exact le_trans hbig (le_trans hle2 hzle)
      omega
    have hd : z.1 = w.1 := by
      have hne : z.2 ≠ 0 := hzp.ne_zero
      have : z.1 * z.2 = w.1 * z.2 := by rw [hzw, hsame]
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) this
    exact Sigma.ext hd (heq_of_eq hsame)
  have hcard2 : (Finset.Ioc x (x + h)).card = h := by
    rw [Nat.card_Ioc]; omega
  have hfin := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [hcard2] at hfin
  exact hfin

/-! ## The increment bound for the Abel face -/

/-- `|mu(d)| <= 1` in the complex normalization used by the Abel face. -/
private theorem norm_moebius_le_one (d : ℕ) : ‖(((μ d : ℤ)) : ℂ)‖ ≤ 1 := by
  by_cases hd : Squarefree d
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hd]
    push_cast
    simp [norm_pow]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
    simp

/-- Increment of the classical discrepancy `R = pi - Li` between two integer
cutoffs above `y`: the prime jump is exact, the Li drift is elementary. -/
theorem primeSievePrimeDiscrepancy_sub_norm_le {y a b : ℕ} (hy : 1 ≤ y)
    (hya : y + 1 ≤ a) (hab : a ≤ b) :
    ‖primeSievePrimeDiscrepancy b - primeSievePrimeDiscrepancy a‖
      ≤ (primeSieveIntervalPrimeCount a b : ℝ)
        + ((b : ℝ) - (a : ℝ)) / Real.log ((y : ℝ) + 1) := by
  have hsplit : primeSievePrimeDiscrepancy b - primeSievePrimeDiscrepancy a
      = ((primeSieveIntervalPrimeCount a b : ℕ) : ℂ)
        - (((logarithmicIntegralFromTwo (b : ℝ)
              - logarithmicIntegralFromTwo (a : ℝ) : ℝ)) : ℂ) := by
    have hcount := primeSievePrefixPrimeCount_sub_eq hab
    unfold primeSievePrimeDiscrepancy
    push_cast
    linear_combination hcount
  rw [hsplit]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖((primeSieveIntervalPrimeCount a b : ℕ) : ℂ)‖
      = (primeSieveIntervalPrimeCount a b : ℝ) := by
    simp
  have h2 : ‖(((logarithmicIntegralFromTwo (b : ℝ)
        - logarithmicIntegralFromTwo (a : ℝ) : ℝ)) : ℂ)‖
      = |logarithmicIntegralFromTwo (b : ℝ) - logarithmicIntegralFromTwo (a : ℝ)| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2]
  have hya' : (y : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hya
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have := abs_logarithmicIntegralFromTwo_sub_le_log_succ (y := y) hy hya' hab'
  linarith

/-- The Abel face with the quotient support frozen at `K`. -/
def primeSieveMoebiusPrefixSum (K x : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 K, (((μ d : ℤ) : ℂ)) * primeSievePrimeDiscrepancy (x / d)

theorem primeSieveMoebiusDiscrepancySum_eq_prefixSum (y x : ℕ) :
    primeSieveMoebiusDiscrepancySum y x = primeSieveMoebiusPrefixSum (x / (y + 1)) x := rfl

/-- **Frozen-support increment bound, sharp form.**  The prime side contributes
at most `h`; the Li side contributes the exact floor-increment sum divided by
`log (y+1)`. -/
theorem primeSieveMoebiusPrefixSum_increment_norm_le (y x h : ℕ) (hy : 1 ≤ y)
    (hsq : x + h < (y + 1) ^ 2) :
    ‖primeSieveMoebiusPrefixSum (x / (y + 1)) (x + h)
        - primeSieveMoebiusPrefixSum (x / (y + 1)) x‖
      ≤ (h : ℝ)
        + (∑ d ∈ Finset.Icc 1 (x / (y + 1)),
            ((((x + h) / d : ℕ) : ℝ) - ((x / d : ℕ) : ℝ))) / Real.log ((y : ℝ) + 1) := by
  classical
  have hlogy : 0 < Real.log ((y : ℝ) + 1) := by
    have : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    exact Real.log_pos (by linarith)
  have hdiff : primeSieveMoebiusPrefixSum (x / (y + 1)) (x + h)
        - primeSieveMoebiusPrefixSum (x / (y + 1)) x
      = ∑ d ∈ Finset.Icc 1 (x / (y + 1)), (((μ d : ℤ) : ℂ)) *
          (primeSievePrimeDiscrepancy ((x + h) / d) - primeSievePrimeDiscrepancy (x / d)) := by
    unfold primeSieveMoebiusPrefixSum
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  rw [hdiff]
  have hterm : ∀ d ∈ Finset.Icc 1 (x / (y + 1)),
      ‖(((μ d : ℤ) : ℂ)) *
        (primeSievePrimeDiscrepancy ((x + h) / d) - primeSievePrimeDiscrepancy (x / d))‖
        ≤ (primeSieveIntervalPrimeCount (x / d) ((x + h) / d) : ℝ)
          + ((((x + h) / d : ℕ) : ℝ) - ((x / d : ℕ) : ℝ)) / Real.log ((y : ℝ) + 1) := by
    intro d hd
    have hmem : d ∈ primeSieveQuotientSupport y x := by
      simpa [primeSieveQuotientSupport] using hd
    have hylt : y < x / d := lt_div_of_mem_primeSieveQuotientSupport hmem
    have hmono : x / d ≤ (x + h) / d := Nat.div_le_div_right (Nat.le_add_right x h)
    have hbase := primeSievePrimeDiscrepancy_sub_norm_le (y := y) (a := x / d)
      (b := (x + h) / d) hy hylt hmono
    calc ‖(((μ d : ℤ) : ℂ)) *
        (primeSievePrimeDiscrepancy ((x + h) / d) - primeSievePrimeDiscrepancy (x / d))‖
        = ‖(((μ d : ℤ) : ℂ))‖ *
            ‖primeSievePrimeDiscrepancy ((x + h) / d)
              - primeSievePrimeDiscrepancy (x / d)‖ := norm_mul _ _
      _ ≤ 1 * ‖primeSievePrimeDiscrepancy ((x + h) / d)
              - primeSievePrimeDiscrepancy (x / d)‖ := by
            gcongr
            exact norm_moebius_le_one d
      _ = ‖primeSievePrimeDiscrepancy ((x + h) / d)
              - primeSievePrimeDiscrepancy (x / d)‖ := one_mul _
      _ ≤ _ := hbase
  refine le_trans (norm_sum_le_of_le _ hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_div]
  have hprime : (∑ d ∈ Finset.Icc 1 (x / (y + 1)),
      (primeSieveIntervalPrimeCount (x / d) ((x + h) / d) : ℝ)) ≤ (h : ℝ) := by
    have := primeSieveIntervalPrimeCount_sum_le y x h hsq
    have hcast : ((∑ d ∈ Finset.Icc 1 (x / (y + 1)),
        primeSieveIntervalPrimeCount (x / d) ((x + h) / d) : ℕ) : ℝ)
        = ∑ d ∈ Finset.Icc 1 (x / (y + 1)),
            (primeSieveIntervalPrimeCount (x / d) ((x + h) / d) : ℝ) := by
      push_cast
      rfl
    rw [← hcast]
    exact_mod_cast this
  linarith

/-! ## Crude uniform relaxation of the floor-increment sum -/

private theorem floor_increment_le (x h d : ℕ) (hd : 0 < d) :
    (x + h) / d ≤ x / d + h + 1 := by
  have hadd : (x + h) / d = x / d + h / d + if d ≤ x % d + h % d then 1 else 0 :=
    Nat.add_div hd
  have hle : h / d ≤ h := Nat.div_le_self h d
  split_ifs at hadd <;> omega

/-- The floor-increment sum over the quotient support is at most `K * (h+1)`.
This is the crude step: it is what turns the sharp bound into the advertised
`C * (h+1)` shape, at the cost of a constant of size `K ~ sqrt x`. -/
theorem primeSieveFloorIncrementSum_le (x h K : ℕ) :
    (∑ d ∈ Finset.Icc 1 K, ((((x + h) / d : ℕ) : ℝ) - ((x / d : ℕ) : ℝ)))
      ≤ (K : ℝ) * ((h : ℝ) + 1) := by
  classical
  have hterm : ∀ d ∈ Finset.Icc 1 K,
      ((((x + h) / d : ℕ) : ℝ) - ((x / d : ℕ) : ℝ)) ≤ (h : ℝ) + 1 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : 0 < d := hd.1
    have := floor_increment_le x h d hdpos
    have hcast : (((x + h) / d : ℕ) : ℝ) ≤ ((x / d : ℕ) : ℝ) + (h : ℝ) + 1 := by
      exact_mod_cast this
    linarith
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
  rw [nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]

/-! ## The Lipschitz theorem -/

/-- The explicit Lipschitz constant `1 + K / log (y+1)`, `K = x / (y+1)`. -/
def primeSieveLipschitzConstant (y x : ℕ) : ℝ :=
  1 + ((x / (y + 1) : ℕ) : ℝ) / Real.log ((y : ℝ) + 1)

theorem one_le_primeSieveLipschitzConstant (y x : ℕ) (hy : 1 ≤ y) :
    1 ≤ primeSieveLipschitzConstant y x := by
  have hy' : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : 0 < Real.log ((y : ℝ) + 1) := Real.log_pos (by linarith)
  unfold primeSieveLipschitzConstant
  have : 0 ≤ ((x / (y + 1) : ℕ) : ℝ) / Real.log ((y : ℝ) + 1) := by positivity
  linarith

theorem primeSieveLipschitzConstant_pos (y x : ℕ) (hy : 1 ≤ y) :
    0 < primeSieveLipschitzConstant y x :=
  lt_of_lt_of_le zero_lt_one (one_le_primeSieveLipschitzConstant y x hy)

/-- A checkable sufficient condition for the quotient support to be frozen
across the step `x -> x + h`. -/
theorem primeSieveQuotientTop_stable (y x h : ℕ) (hmod : x % (y + 1) + h < y + 1) :
    (x + h) / (y + 1) = x / (y + 1) := by
  have hpos : 0 < y + 1 := Nat.succ_pos y
  have hadd : (x + h) / (y + 1)
      = x / (y + 1) + h / (y + 1) + if y + 1 ≤ x % (y + 1) + h % (y + 1) then 1 else 0 :=
    Nat.add_div hpos
  have hhd : h / (y + 1) = 0 := Nat.div_eq_of_lt (by omega)
  have hhm : h % (y + 1) = h := Nat.mod_eq_of_lt (by omega)
  rw [hhd, hhm] at hadd
  have : ¬ (y + 1 ≤ x % (y + 1) + h) := by omega
  rw [if_neg this] at hadd
  omega

/-- **The Lipschitz bound for the Abel face.**

For `1 <= y`, `x + h < (y+1)^2`, and a step that does not enlarge the quotient
support,

```text
|S(y, x+h) - S(y, x)| <= (1 + (x/(y+1)) / log (y+1)) * (h + 1).
```

Unconditional: no hypothesis on `pi`, on `Li`, or on the Mobius sum is used. -/
theorem primeSieveMoebiusDiscrepancySum_increment_norm_le (y x h : ℕ) (hy : 1 ≤ y)
    (hsq : x + h < (y + 1) ^ 2) (hsupp : (x + h) / (y + 1) = x / (y + 1)) :
    ‖primeSieveMoebiusDiscrepancySum y (x + h) - primeSieveMoebiusDiscrepancySum y x‖
      ≤ primeSieveLipschitzConstant y x * ((h : ℝ) + 1) := by
  have hy' : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : 0 < Real.log ((y : ℝ) + 1) := Real.log_pos (by linarith)
  have hrewrite : primeSieveMoebiusDiscrepancySum y (x + h)
      = primeSieveMoebiusPrefixSum (x / (y + 1)) (x + h) := by
    rw [primeSieveMoebiusDiscrepancySum_eq_prefixSum, hsupp]
  rw [hrewrite, primeSieveMoebiusDiscrepancySum_eq_prefixSum]
  refine le_trans (primeSieveMoebiusPrefixSum_increment_norm_le y x h hy hsq) ?_
  have hfloor := primeSieveFloorIncrementSum_le x h (x / (y + 1))
  have hinv : (0 : ℝ) ≤ (Real.log ((y : ℝ) + 1))⁻¹ := le_of_lt (inv_pos.2 hlogy)
  have hdiv : (∑ d ∈ Finset.Icc 1 (x / (y + 1)),
      ((((x + h) / d : ℕ) : ℝ) - ((x / d : ℕ) : ℝ))) / Real.log ((y : ℝ) + 1)
      ≤ (((x / (y + 1) : ℕ) : ℝ) / Real.log ((y : ℝ) + 1)) * ((h : ℝ) + 1) := by
    rw [div_eq_mul_inv]
    have := mul_le_mul_of_nonneg_right hfloor hinv
    calc (∑ d ∈ Finset.Icc 1 (x / (y + 1)),
            ((((x + h) / d : ℕ) : ℝ) - ((x / d : ℕ) : ℝ))) * (Real.log ((y : ℝ) + 1))⁻¹
        ≤ ((x / (y + 1) : ℕ) : ℝ) * ((h : ℝ) + 1) * (Real.log ((y : ℝ) + 1))⁻¹ := this
      _ = (((x / (y + 1) : ℕ) : ℝ) / Real.log ((y : ℝ) + 1)) * ((h : ℝ) + 1) := by
          rw [div_eq_mul_inv]; ring
  unfold primeSieveLipschitzConstant
  have hexp : (1 + (((x / (y + 1) : ℕ) : ℝ) / Real.log ((y : ℝ) + 1))) * ((h : ℝ) + 1)
      = ((h : ℝ) + 1)
        + (((x / (y + 1) : ℕ) : ℝ) / Real.log ((y : ℝ) + 1)) * ((h : ℝ) + 1) := by
    ring
  rw [hexp]
  linarith [hdiv]

/-! ## The excursion transfer -/

/-- **Excursion lemma.**  A `C*(t+1)` increment bound at a pinned point of
height `H = |f x0|` forces `|f| >= H/2` throughout the window
`[x0, x0 + floor (H / (2C)))`.  No lower bound on `H` is needed: when `H < 2C`
the window is empty and the statement is vacuous. -/
theorem excursionWindow_norm_le {f : ℕ → ℂ} {x₀ : ℕ} {C : ℝ} (hC : 0 < C)
    (hlip : ∀ t : ℕ, t < ⌊‖f x₀‖ / (2 * C)⌋₊ →
      ‖f (x₀ + t) - f x₀‖ ≤ C * ((t : ℝ) + 1)) :
    ∀ t : ℕ, t < ⌊‖f x₀‖ / (2 * C)⌋₊ → ‖f x₀‖ / 2 ≤ ‖f (x₀ + t)‖ := by
  intro t ht
  have hnn : (0 : ℝ) ≤ ‖f x₀‖ / (2 * C) := by positivity
  have hfloor : ((⌊‖f x₀‖ / (2 * C)⌋₊ : ℕ) : ℝ) ≤ ‖f x₀‖ / (2 * C) := Nat.floor_le hnn
  have htle : ((t : ℝ) + 1) ≤ ‖f x₀‖ / (2 * C) := by
    have : (t : ℝ) + 1 ≤ ((⌊‖f x₀‖ / (2 * C)⌋₊ : ℕ) : ℝ) := by exact_mod_cast ht
    linarith
  have hstep : ‖f (x₀ + t) - f x₀‖ ≤ ‖f x₀‖ / 2 := by
    refine le_trans (hlip t ht) ?_
    have h2C : (0 : ℝ) < 2 * C := by linarith
    calc C * ((t : ℝ) + 1) ≤ C * (‖f x₀‖ / (2 * C)) := by
          exact mul_le_mul_of_nonneg_left htle (le_of_lt hC)
      _ = ‖f x₀‖ / 2 := by field_simp
  have := norm_sub_norm_le (f x₀) (f (x₀ + t))
  have hsymm : ‖f x₀ - f (x₀ + t)‖ = ‖f (x₀ + t) - f x₀‖ := norm_sub_rev _ _
  rw [hsymm] at this
  linarith

/-- The window is nonempty once `H >= 2C`. -/
theorem one_le_excursionWindow {f : ℕ → ℂ} {x₀ : ℕ} {C : ℝ} (hC : 0 < C)
    (hH : 2 * C ≤ ‖f x₀‖) : 1 ≤ ⌊‖f x₀‖ / (2 * C)⌋₊ := by
  have h2C : (0 : ℝ) < 2 * C := by linarith
  have : (1 : ℝ) ≤ ‖f x₀‖ / (2 * C) := by
    rw [le_div_iff₀ h2C]
    linarith
  exact Nat.le_floor (by exact_mod_cast this)

/-- **The pinned-to-windowed moment transfer.**  For every `k`, a pinned height
`H` produces a `2k`-th moment lower bound on the excursion window. -/
theorem excursionWindow_moment_le {f : ℕ → ℂ} {x₀ : ℕ} {C : ℝ} (hC : 0 < C)
    (hlip : ∀ t : ℕ, t < ⌊‖f x₀‖ / (2 * C)⌋₊ →
      ‖f (x₀ + t) - f x₀‖ ≤ C * ((t : ℝ) + 1)) (k : ℕ) :
    (‖f x₀‖ / 2) ^ (2 * k) * ((⌊‖f x₀‖ / (2 * C)⌋₊ : ℕ) : ℝ)
      ≤ ∑ t ∈ Finset.range ⌊‖f x₀‖ / (2 * C)⌋₊, ‖f (x₀ + t)‖ ^ (2 * k) := by
  have hpt := excursionWindow_norm_le hC hlip
  have hbound : ∀ t ∈ Finset.range ⌊‖f x₀‖ / (2 * C)⌋₊,
      (‖f x₀‖ / 2) ^ (2 * k) ≤ ‖f (x₀ + t)‖ ^ (2 * k) := by
    intro t ht
    have h := hpt t (Finset.mem_range.1 ht)
    have hnn : (0 : ℝ) ≤ ‖f x₀‖ / 2 := by positivity
    exact pow_le_pow_left₀ hnn h (2 * k)
  have := Finset.card_nsmul_le_sum (Finset.range ⌊‖f x₀‖ / (2 * C)⌋₊)
    (fun t => ‖f (x₀ + t)‖ ^ (2 * k)) ((‖f x₀‖ / 2) ^ (2 * k)) hbound
  rw [Finset.card_range, nsmul_eq_mul] at this
  linarith [this]

/-! ## Instantiation at the Abel face -/

/-- The excursion window length attached to a pinned point of the Abel face. -/
def primeSieveExcursionWindow (y x₀ : ℕ) : ℕ :=
  ⌊‖primeSieveMoebiusDiscrepancySum y x₀‖ / (2 * primeSieveLipschitzConstant y x₀)⌋₊

/-- **Pinned to windowed, at the Abel face.**  A pinned height
`H = |S(y,x0)| >= 2 C(y,x0)` forces `|S(y, ·)| >= H/2` on the whole window
`[x0, x0 + W)`, `W = floor (H / (2 C(y,x0)))`, provided the window stays inside
the range where the increment bound applies. -/
theorem primeSieveMoebiusDiscrepancySum_excursion (y x₀ : ℕ) (hy : 1 ≤ y)
    (hsq : x₀ + primeSieveExcursionWindow y x₀ < (y + 1) ^ 2)
    (hmod : x₀ % (y + 1) + primeSieveExcursionWindow y x₀ < y + 1) :
    ∀ t : ℕ, t < primeSieveExcursionWindow y x₀ →
      ‖primeSieveMoebiusDiscrepancySum y x₀‖ / 2
        ≤ ‖primeSieveMoebiusDiscrepancySum y (x₀ + t)‖ := by
  intro t ht
  refine excursionWindow_norm_le (f := fun n => primeSieveMoebiusDiscrepancySum y n)
    (primeSieveLipschitzConstant_pos y x₀ hy) ?_ t ht
  intro s hs
  replace hs : s < primeSieveExcursionWindow y x₀ := hs
  have h1 : x₀ + s < (y + 1) ^ 2 := by omega
  have h2 : (x₀ + s) / (y + 1) = x₀ / (y + 1) :=
    primeSieveQuotientTop_stable y x₀ s (by omega)
  exact primeSieveMoebiusDiscrepancySum_increment_norm_le y x₀ s hy h1 h2

/-- **The discrete moment lower bound.**  For every `k`, a pinned height `H` at
`x0` forces `(H/2)^(2k) * W <= sum_{t < W} |S(y, x0+t)|^(2k)` on the excursion
window `W`.  This is the pinned-to-averaged transfer: a pointwise spike is
converted into a windowed `2k`-th moment. -/
theorem primeSieveMoebiusDiscrepancySum_excursion_moment (y x₀ k : ℕ) (hy : 1 ≤ y)
    (hsq : x₀ + primeSieveExcursionWindow y x₀ < (y + 1) ^ 2)
    (hmod : x₀ % (y + 1) + primeSieveExcursionWindow y x₀ < y + 1) :
    (‖primeSieveMoebiusDiscrepancySum y x₀‖ / 2) ^ (2 * k)
        * ((primeSieveExcursionWindow y x₀ : ℕ) : ℝ)
      ≤ ∑ t ∈ Finset.range (primeSieveExcursionWindow y x₀),
          ‖primeSieveMoebiusDiscrepancySum y (x₀ + t)‖ ^ (2 * k) := by
  refine excursionWindow_moment_le (f := fun n => primeSieveMoebiusDiscrepancySum y n)
    (primeSieveLipschitzConstant_pos y x₀ hy) ?_ k
  intro s hs
  replace hs : s < primeSieveExcursionWindow y x₀ := hs
  have h1 : x₀ + s < (y + 1) ^ 2 := by omega
  have h2 : (x₀ + s) / (y + 1) = x₀ / (y + 1) :=
    primeSieveQuotientTop_stable y x₀ s (by omega)
  exact primeSieveMoebiusDiscrepancySum_increment_norm_le y x₀ s hy h1 h2

/-- The window is nonempty whenever the pin exceeds `2 C`. -/
theorem one_le_primeSieveExcursionWindow (y x₀ : ℕ) (hy : 1 ≤ y)
    (hH : 2 * primeSieveLipschitzConstant y x₀
      ≤ ‖primeSieveMoebiusDiscrepancySum y x₀‖) :
    1 ≤ primeSieveExcursionWindow y x₀ :=
  one_le_excursionWindow (f := fun n => primeSieveMoebiusDiscrepancySum y n)
    (primeSieveLipschitzConstant_pos y x₀ hy) hH

end RHLean.Analysis
